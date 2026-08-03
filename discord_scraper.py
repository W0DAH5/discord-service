# discord_scraper.py
from __future__ import annotations

import asyncio
import gc
import logging
import random
import re
import shutil
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Coroutine, Optional
from urllib.parse import urlparse, unquote

import psutil
from playwright.async_api import async_playwright, BrowserContext, Page

from models import SourceInfo
from utils import sanitize_filename, unlink_quiet

logger = logging.getLogger(__name__)

# ---------- Final tested JavaScript extraction ----------
_EXTRACT_JS = r"""
() => {
    const CDN_HOSTS = [
        'cdn.discordapp.com',
        'media.discordapp.net',
        'discord.com/assets',
        'images-ext-1.discordapp.net',
        'images-ext-2.discordapp.net',
    ];

    function isMediaUrl(url) {
        if (!url) return false;
        if (!url.startsWith('http') && !url.startsWith('//')) return false;
        if (url.includes('/stickers/')) return false;
        const fromCdn = CDN_HOSTS.some(h => url.includes(h));
        const isAttachment = url.includes('/attachments/');
        return fromCdn || isAttachment;
    }

    function cleanUrl(url) {
        if (!url) return null;
        if (url.startsWith('//')) url = 'https:' + url;
        return url.split('#')[0];
    }

    function extractUrls(element) {
        const urls = new Set();
        element.querySelectorAll('a[href]').forEach(a => {
            const href = a.getAttribute('href');
            if (href && isMediaUrl(href)) urls.add(cleanUrl(href));
        });
        element.querySelectorAll('img[src]').forEach(img => {
            const src = img.getAttribute('src');
            if (src && isMediaUrl(src)) urls.add(cleanUrl(src));
        });
        element.querySelectorAll('video[src]').forEach(video => {
            const src = video.getAttribute('src');
            if (src && isMediaUrl(src)) urls.add(cleanUrl(src));
        });
        element.querySelectorAll('[data-attachment-url]').forEach(el => {
            const url = el.getAttribute('data-attachment-url');
            if (url && isMediaUrl(url)) urls.add(cleanUrl(url));
        });
        element.querySelectorAll('[style*="discordapp"]').forEach(el => {
            const style = el.getAttribute('style') || '';
            const matches = style.match(/url\(['"]?([^'")\s]+)['"]?\)/g) || [];
            matches.forEach(m => {
                const inner = m.replace(/^url\(['"]?/, '').replace(/['"]?\)$/, '');
                if (isMediaUrl(inner)) urls.add(cleanUrl(inner));
            });
        });
        return [...urls];
    }

    const messages = [];
    const seenIds = new Set();

    // ----- Strategy 1: use timestamp elements as anchors -----
    const timeElements = document.querySelectorAll('time[datetime]');
    if (timeElements.length > 0) {
        timeElements.forEach(timeEl => {
            let container = timeEl.closest('div[class*="message"], li[role="article"], div[class*="container"]');
            if (!container) container = timeEl.parentElement;

            let msgId = container.id || container.getAttribute('data-list-item-id') || '';
            if (!msgId) {
                const idEl = container.querySelector('[id^="message-"]');
                if (idEl) msgId = idEl.id.replace(/[^0-9]/g, '');
            }
            // Extract numeric ID (last digits)
            const numericMatch = msgId.match(/\d+$/);
            if (numericMatch) msgId = numericMatch[0];
            if (!msgId) msgId = Math.random().toString(36).substr(2, 9);
            if (seenIds.has(msgId)) return;
            seenIds.add(msgId);

            const ts = timeEl.getAttribute('datetime') || '';
            const textEl = container.querySelector('[class*="messageContent"], [id^="message-content-"]');
            const text = textEl ? (textEl.innerText || '').slice(0, 2000) : '';

            const attachments = extractUrls(container);
            container.querySelectorAll('[class*="embed"], [class*="attachment"], [class*="imageContainer"], [class*="visualMediaItem"]').forEach(embed => {
                extractUrls(embed).forEach(u => {
                    if (!attachments.includes(u)) attachments.push(u);
                });
            });

            messages.push({ id: msgId, timestamp: ts, text, attachments });
        });
    } else {
        // ----- Strategy 2: fallback to data-list-item-id -----
        document.querySelectorAll('[data-list-item-id]').forEach(el => {
            let rawId = el.getAttribute('data-list-item-id') || '';
            let msgId = rawId;
            if (msgId.includes('___')) msgId = msgId.split('___').pop();
            const segments = msgId.split('-');
            const last = segments[segments.length - 1];
            if (/^\d+$/.test(last)) msgId = last;
            if (!msgId || seenIds.has(msgId)) return;
            seenIds.add(msgId);

            let ts = el.getAttribute('data-timestamp') || '';
            if (!ts) {
                const timeEl = el.querySelector('time[datetime]');
                if (timeEl) ts = timeEl.getAttribute('datetime') || '';
            }
            let text = '';
            const textEl = el.querySelector('[class*="messageContent"], [id^="message-content-"]');
            if (textEl) text = (textEl.innerText || '').slice(0, 2000);
            const attachments = extractUrls(el);
            el.querySelectorAll('[class*="embed"], [class*="attachment"], [class*="imageContainer"]').forEach(embed => {
                extractUrls(embed).forEach(u => {
                    if (!attachments.includes(u)) attachments.push(u);
                });
            });
            messages.push({ id: msgId, timestamp: ts, text, attachments });
        });
    }

    return messages;
}
"""


class DiscordScraper:
    # Fallback guild ID (used when no mapping is provided)
    GUILD_ID = "1510277023694590062"

    DISCORD_CDN_DOMAINS = {
        "cdn.discordapp.com",
        "media.discordapp.net",
        "discord.com",
        "images-ext-1.discordapp.net",
        "images-ext-2.discordapp.net",
    }

    def __init__(
        self,
        email: str,
        password: str | None,
        channels: list[str],
        transformer: MediaTransformer,
        on_message_callback: Callable[[Any, SourceInfo], Coroutine[Any, Any, bool]],
        data_dir: Path,
        headless: bool = False,
        start_date: str | None = None,
        store: Optional[Store] = None,
        run_lock: Optional[asyncio.Lock] = None,
        channel_guilds: Optional[dict[str, str]] = None,
        debug_dir: Optional[Path] = None,
    ):
        self.email = email
        self.password = password
        self.channels = channels
        self.transformer = transformer
        self.on_message = on_message_callback
        self.data_dir = data_dir
        self.headless = headless
        self.store = store
        self.run_lock = run_lock or asyncio.Lock()
        self._channel_guilds: dict[str, str] = dict(channel_guilds or {})
        self.debug_dir = debug_dir or data_dir

        self.start_date: datetime | None = None
        if start_date:
            try:
                self.start_date = datetime.fromisoformat(start_date).replace(tzinfo=timezone.utc)
                logger.info(f"Start date set: {self.start_date}")
            except Exception as e:
                logger.warning(f"Invalid DISCORD_START_DATE: {start_date} – ignoring ({e})")

        self.context: BrowserContext | None = None
        self._page: Page | None = None
        self._running = False
        self._known_message_ids: dict[str, set[str]] = {}
        self._last_poll: dict[str, float] = {}
        self._initial_load_done: dict[str, bool] = {}

        self._ch_stats: dict[str, dict[str, int]] = {}
        self._download_stats = {"success": 0, "failed": 0, "total_bytes": 0}
        self.user_data_dir = data_dir / "chrome_user_data"
        self.user_data_dir.mkdir(parents=True, exist_ok=True)

        self._browser_ready = False
        self._playwright = None

        # In-memory last processed message ID per channel
        self._last_processed: dict[str, int] = {}

    # ------------------------------------------------------------------
    # Browser lifecycle
    # ------------------------------------------------------------------
    def _get_browser_args(self) -> list[str]:
        return [
            "--disable-blink-features=AutomationControlled",
            "--disable-features=IsolateOrigins,site-per-process",
            "--disable-web-security",
            "--disable-gpu",
            "--disable-dev-shm-usage",
            "--no-sandbox",
            "--disable-setuid-sandbox",
            "--window-size=1280,720",
            "--disable-automation",
        ]

    async def _create_browser_context(self, playwright_instance) -> BrowserContext:
        return await playwright_instance.chromium.launch_persistent_context(
            user_data_dir=str(self.user_data_dir),
            headless=self.headless,
            args=self._get_browser_args(),
            viewport={"width": 1280, "height": 800},
            user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/119.0.0.0 Safari/537.36"
            ),
            locale="en-US",
            timezone_id="America/New_York",
        )

    # ------------------------------------------------------------------
    # Ensure browser and login (AGGRESSIVE CHECK - URL-independent)
    # ------------------------------------------------------------------
    async def _ensure_browser_and_login(self):
        if self._browser_ready and self.context is not None:
            return

        logger.info("Launching Discord browser...")

        # If chrome_user_data exists but is stale, purge it before launching.
        lock_file = self.user_data_dir / "SingletonLock"
        if lock_file.exists():
            logger.warning(
                "SingletonLock found in chrome_user_data – "
                "previous browser did not shut down cleanly. Removing lock."
            )
            try:
                lock_file.unlink()
            except Exception as e:
                logger.warning(f"Could not remove SingletonLock: {e}")

        self._playwright = await async_playwright().start()

        try:
            self.context = await self._create_browser_context(self._playwright)
        except Exception as e:
            # If context creation fails (e.g. corrupted profile), wipe and retry
            logger.warning(f"Browser context creation failed ({e}) – wiping user data and retrying")
            try:
                shutil.rmtree(self.user_data_dir, ignore_errors=True)
                self.user_data_dir.mkdir(parents=True, exist_ok=True)
            except Exception as wipe_err:
                logger.error(f"Could not wipe user_data_dir: {wipe_err}")
            self.context = await self._create_browser_context(self._playwright)

        self._page = await self.context.new_page()

        # Determine test URL
        test_channel = self.channels[0] if self.channels else None
        guild_id = (
            self._channel_guilds.get(test_channel, self.GUILD_ID)
            if test_channel else self.GUILD_ID
        )
        test_url = (
            f"https://discord.com/channels/{guild_id}/{test_channel}"
            if test_channel
            else "https://discord.com/channels/@me"
        )
        logger.info(f"Navigating to test URL: {test_url}")

        await self._page.goto(test_url, wait_until="domcontentloaded", timeout=30000)
        await asyncio.sleep(3)

        # Real check: message list in DOM
        message_list = await self._page.query_selector('[data-list-id="chat-messages"]')
        if message_list:
            logger.info("✓ Message list found – session valid")
            self._browser_ready = True
            return

        logger.info("Message list not found – performing login...")
        await self._perform_login(self._page)

        # Post-login: navigate to the actual channel
        if test_channel:
            await self._page.goto(
                f"https://discord.com/channels/{guild_id}/{test_channel}",
                wait_until="domcontentloaded",
                timeout=30000,
            )
            await asyncio.sleep(3)

        message_list_after = await self._page.query_selector('[data-list-id="chat-messages"]')
        if not message_list_after:
            await self._save_debug_snapshot(self._page, "post_login_verify_failed")
            raise RuntimeError(
                f"Login appeared to succeed but message list not found. URL: {self._page.url}"
            )

        logger.info("✓ Login confirmed – ready to poll")
        self._browser_ready = True

    async def _close_browser(self):
        if self.context is not None:
            try:
                if self._page:
                    await self._page.close()
                await self.context.close()
            except Exception as e:
                logger.warning(f"Error closing browser: {e}")
            self.context = None
            self._page = None
            self._browser_ready = False
            if self._playwright:
                try:
                    await self._playwright.stop()
                except Exception:
                    pass
                self._playwright = None
            gc.collect()
            logger.info("Discord browser closed")

    # ------------------------------------------------------------------
    # Robust login with multiple fallbacks and debug snapshots
    # ------------------------------------------------------------------
    async def _perform_login(self, page: Page):
        logger.info("Navigating to Discord login page...")

        # ----------------------------------------------------------------
        # Step 1: Clear stale session storage
        # ----------------------------------------------------------------
        try:
            await page.goto("about:blank", wait_until="commit", timeout=5000)
            await asyncio.sleep(0.5)
        except Exception:
            pass

        # ----------------------------------------------------------------
        # Step 2: Navigate to login page
        # ----------------------------------------------------------------
        for nav_attempt in range(3):
            try:
                await page.goto(
                    "https://discord.com/login",
                    wait_until="domcontentloaded",
                    timeout=30000,
                )
                break
            except Exception as e:
                logger.warning(f"Navigation attempt {nav_attempt+1} failed: {e}")
                await asyncio.sleep(2)
        else:
            raise RuntimeError("Failed to navigate to Discord login page after 3 attempts")

        # ----------------------------------------------------------------
        # Step 3: Wait for the email input with extended timeout + fallbacks
        # ----------------------------------------------------------------
        email_input_found = False

        for wait_attempt in range(15):
            await asyncio.sleep(2)

            el = await page.query_selector('input[name="email"]')
            if el:
                email_input_found = True
                logger.info(f"Email input found after {(wait_attempt+1)*2}s")
                break

            el = await page.query_selector('input[type="email"]')
            if el:
                email_input_found = True
                logger.info("Email input found via type=email fallback")
                break

            el = await page.query_selector('input[type="text"]:visible')
            if el:
                email_input_found = True
                logger.info("Email input found via text input fallback")
                break

            current_url = page.url
            logger.debug(f"Waiting for login form... attempt {wait_attempt+1}/15 | URL: {current_url}")

            if "/channels/" in current_url:
                chat = await page.query_selector('[data-list-id="chat-messages"]')
                if chat:
                    logger.info("✓ Discord redirected to channels – already logged in, skipping login")
                    return

            captcha = await page.query_selector('iframe[src*="captcha"], div[class*="captcha"]')
            if captcha:
                logger.warning("⚠ CAPTCHA detected on login page – waiting for it to clear...")

        if not email_input_found:
            await self._save_debug_snapshot(page, "login_form_not_found")
            raise RuntimeError(
                f"Login form not found after 30 seconds. "
                f"URL: {page.url}. "
                "Check debug snapshot for what Discord is showing."
            )

        # ----------------------------------------------------------------
        # Step 4: Fill and submit the form
        # ----------------------------------------------------------------
        await asyncio.sleep(0.3)

        await page.fill('input[name="email"], input[type="email"]', "")
        await asyncio.sleep(0.2)
        await page.type(
            'input[name="email"], input[type="email"]',
            self.email,
            delay=50,
        )

        await asyncio.sleep(0.4)

        pwd_el = await page.query_selector('input[name="password"], input[type="password"]')
        if not pwd_el:
            await self._save_debug_snapshot(page, "password_field_not_found")
            raise RuntimeError("Password field not found after filling email")

        await page.fill('input[name="password"], input[type="password"]', "")
        await asyncio.sleep(0.2)
        await page.type(
            'input[name="password"], input[type="password"]',
            self.password,
            delay=50,
        )

        await asyncio.sleep(0.5)

        submit_btn = await page.query_selector('button[type="submit"]')
        if submit_btn:
            await submit_btn.click()
        else:
            logger.warning("Submit button not found – pressing Enter")
            await page.keyboard.press("Enter")

        logger.info("Login form submitted – waiting for Discord to respond...")

        # ----------------------------------------------------------------
        # Step 5: Wait for login confirmation (DOM-based, not URL-based)
        # ----------------------------------------------------------------
        for attempt in range(40):
            await asyncio.sleep(2)

            message_list = await page.query_selector('[data-list-id="chat-messages"]')
            if message_list:
                logger.info(f"✓ Login successful (confirmed after {(attempt+1)*2}s)")
                return

            sidebar = await page.query_selector(
                'nav[aria-label="Servers sidebar"], '
                'nav[aria-label="Servers"], '
                'div[class*="guilds-"]'
            )
            if sidebar:
                logger.info(f"✓ Login successful – sidebar visible (after {(attempt+1)*2}s)")
                return

            twofa_input = await page.query_selector(
                'input[name="code"], '
                'input[placeholder*="6-digit"], '
                'input[placeholder*="auth"]'
            )
            if twofa_input:
                logger.warning("⚠ 2FA required – waiting up to 120s for manual code entry...")
                for twofa_attempt in range(60):
                    await asyncio.sleep(2)
                    if await page.query_selector('[data-list-id="chat-messages"]'):
                        logger.info(f"✓ 2FA completed (after {(twofa_attempt+1)*2}s)")
                        return
                    sidebar2 = await page.query_selector(
                        'nav[aria-label="Servers sidebar"], div[class*="guilds-"]'
                    )
                    if sidebar2:
                        logger.info("✓ 2FA completed – sidebar visible")
                        return
                raise RuntimeError("2FA not completed within 120 second timeout")

            for err_sel in [
                '[class*="errorMessage"]',
                '[class*="error-message"]',
                'div[class*="toast-"][class*="error"]',
                'span[class*="errorMessage"]',
            ]:
                error_el = await page.query_selector(err_sel)
                if error_el:
                    error_text = (await error_el.text_content() or "").strip()
                    if error_text:
                        raise RuntimeError(f"Discord login error: {error_text}")

            logger.debug(f"Awaiting login confirmation {attempt+1}/40 | URL: {page.url}")

        await self._save_debug_snapshot(page, "login_timeout")
        raise RuntimeError(
            f"Login failed after 80 seconds. "
            f"Final URL: {page.url}. "
            "See debug snapshot."
        )

    # ------------------------------------------------------------------
    # Debug helper – saves HTML + screenshot for diagnosis
    # ------------------------------------------------------------------
    async def _save_debug_snapshot(self, page: Page, label: str):
        """Save a HTML + PNG snapshot for diagnosing login failures."""
        if not self.debug_dir:
            return
        try:
            self.debug_dir.mkdir(parents=True, exist_ok=True)
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            base = self.debug_dir / f"{label}_{ts}"

            await page.screenshot(path=str(base.with_suffix(".png")), full_page=True)
            html = await page.content()
            base.with_suffix(".html").write_text(html, encoding="utf-8")

            logger.error(
                f"Debug snapshot saved: {base}.png / .html  "
                f"(URL at time of save: {page.url})"
            )
        except Exception as e:
            logger.warning(f"Could not save debug snapshot '{label}': {e}")

    # ------------------------------------------------------------------
    # is_logged_in – thin wrapper (used by _navigate_to_channel)
    # ------------------------------------------------------------------
    async def _is_logged_in(self, page: Page) -> bool:
        try:
            if "/login" in page.url:
                return False

            message_list = await page.query_selector('[data-list-id="chat-messages"]')
            if message_list:
                return True

            sidebar = await page.query_selector(
                'nav[aria-label="Servers sidebar"], '
                'div[class*="sidebar-"] nav, '
                'div[aria-label="Servers"]'
            )
            return sidebar is not None

        except Exception as e:
            logger.debug(f"_is_logged_in check failed: {e}")
            return False

    # ------------------------------------------------------------------
    # Navigation
    # ------------------------------------------------------------------
    async def _page_alive(self, page: Page) -> bool:
        try:
            await page.evaluate("1")
            return True
        except Exception:
            return False

    async def _navigate_to_channel(self, channel_id: str) -> Page:
        if self._page is None or not await self._page_alive(self._page):
            logger.warning("Page is dead – recreating")
            self._page = await self.context.new_page()

        page = self._page

        if channel_id in page.url and await page.query_selector('[data-list-id="chat-messages"]'):
            logger.debug(f"Already on channel {channel_id} with messages visible")
            return page

        guild_id = self._channel_guilds.get(channel_id, self.GUILD_ID)
        if not guild_id:
            raise ValueError(f"No guild ID for channel {channel_id}")

        target = f"https://discord.com/channels/{guild_id}/{channel_id}"
        logger.info(f"Navigating to: {target}")
        await page.goto(target, wait_until="networkidle", timeout=30000)
        await asyncio.sleep(1)

        message_list = await page.query_selector('[data-list-id="chat-messages"]')
        if not message_list:
            logger.warning(
                f"Message list not found after navigating to {channel_id} "
                f"(URL: {page.url}) – session may have expired, re-logging in..."
            )
            await self._perform_login(page)
            await page.goto(target, wait_until="networkidle", timeout=30000)
            await asyncio.sleep(1)

        await self._wait_for_chat(page)

        m = re.search(r"/channels/(\d+)/(\d+)", page.url)
        if m:
            self._channel_guilds[channel_id] = m.group(1)

        logger.info(f"✓ Navigated to channel {channel_id}")
        return page

    async def _wait_for_chat(self, page: Page):
        for sel in [
            '[data-list-id="chat-messages"]',
            'div[class*="scroller-"][class*="messages"]',
            'div[class*="messagesWrapper"]',
            'div[class*="chat-"]',
            'main[class*="chatContent"]',
        ]:
            try:
                await page.wait_for_selector(sel, timeout=8000, state="visible")
                return
            except Exception:
                continue
        logger.warning("Chat container not found after navigation")

    async def _dismiss_modals(self, page: Page):
        for btn in [
            'button:has-text("Accept")', 'button:has-text("Continue")',
            'button:has-text("I understand")', 'button:has-text("Got it")',
            'button:has-text("Okay")', 'button[class*="confirmButton"]',
        ]:
            try:
                if await page.locator(btn).count() > 0:
                    await page.click(btn, timeout=2000)
                    await asyncio.sleep(0.5)
                    return
            except Exception:
                continue

    # ------------------------------------------------------------------
    # Message loading
    # ------------------------------------------------------------------
    async def _find_scroller(self, page: Page):
        selectors = [
            'div[data-list-id="chat-messages"]',
            'div[class*="scroller-"][class*="messages"]',
            'div[class*="scroller-"][role="list"]',
            'div[class*="scroller-"]',
            'div[role="list"]',
            'main[class*="chatContent"] div[class*="scroller"]',
            'div[class*="chatContent"] div[class*="scroller"]',
        ]
        for sel in selectors:
            try:
                el = await page.query_selector(sel)
                if el:
                    scrollable = await el.evaluate(
                        "e => e.scrollHeight > e.clientHeight + 5"
                    )
                    if scrollable:
                        logger.info(f"Scroller found using selector: {sel}")
                        return el
                    parent = await el.evaluate_handle("e => e.parentElement")
                    if parent:
                        parent_scrollable = await parent.evaluate(
                            "e => e.scrollHeight > e.clientHeight + 5"
                        )
                        if parent_scrollable:
                            logger.info(f"Scroller found as parent of: {sel}")
                            return parent
            except Exception:
                continue

        el = await page.evaluate_handle("""
            () => {
                let best = null, bestH = 0;
                for (const el of document.querySelectorAll('div')) {
                    const s = getComputedStyle(el);
                    const scrollable =
                        s.overflowY === 'auto' || s.overflowY === 'scroll' ||
                        s.overflow === 'auto' || s.overflow === 'scroll';
                    if (scrollable && el.scrollHeight > el.clientHeight + 10
                            && el.scrollHeight > bestH) {
                        best = el; bestH = el.scrollHeight;
                    }
                }
                return best;
            }
        """)
        try:
            is_null = await el.evaluate("e => e === null")
            if not is_null:
                logger.info("Scroller found via fallback")
                return el
        except Exception:
            pass

        logger.warning("No scroller found – falling back to window scroll")
        return None

    async def _load_messages(self, page: Page, max_scrolls: int = 10) -> list[dict]:
        if not await self._page_alive(page):
            logger.warning("Page is closed – skipping _load_messages")
            return []

        await self._dismiss_modals(page)
        scroller = await self._find_scroller(page)
        if not scroller:
            logger.warning("Scroller not found – falling back to window scroll")

        seen_ids: set[str] = set()
        collected: list[dict] = []
        no_new_streak = 0
        top_stuck_streak = 0
        scroll_step = 3000
        prev_top: float = -1

        for i in range(max_scrolls):
            try:
                if scroller:
                    top_before = await scroller.evaluate("e => e.scrollTop")
                    await scroller.evaluate(f"e => e.scrollBy(0, -{scroll_step})")
                else:
                    top_before = await page.evaluate("window.scrollY")
                    await page.evaluate(f"window.scrollBy(0, -{scroll_step})")
            except Exception as e:
                logger.warning(f"Scroll error at {i}: {e}")
                scroller = None
                continue

            await asyncio.sleep(0.8)
            try:
                await page.wait_for_load_state("networkidle", timeout=2000)
            except Exception:
                pass
            await asyncio.sleep(0.3)

            for btn_text in ["Load More", "Jump to Beginning", "Oldest"]:
                try:
                    btn = page.locator(f'button:has-text("{btn_text}")')
                    if await btn.count() > 0:
                        await btn.first.click(timeout=2000)
                        await asyncio.sleep(1.5)
                except Exception:
                    pass

            try:
                message_data: list[dict] = await page.evaluate(_EXTRACT_JS)
            except Exception as e:
                logger.warning(f"JS extraction error at scroll {i}: {e}")
                message_data = []

            if not message_data and self.debug_dir:
                self.debug_dir.mkdir(parents=True, exist_ok=True)
                html = await page.content()
                debug_html_path = self.debug_dir / "debug.html"
                with open(debug_html_path, "w", encoding="utf-8") as f:
                    f.write(html)
                await page.screenshot(path=str(self.debug_dir / "debug.png"))
                logger.warning(f"No messages extracted. Saved HTML and screenshot to {self.debug_dir}")

            new_count = 0
            for data in message_data:
                msg_id = data.get("id", "")
                if not msg_id or msg_id in seen_ids:
                    continue
                seen_ids.add(msg_id)
                new_count += 1

                ts = data.get("timestamp", "")
                try:
                    if ts:
                        ts = ts.replace("Z", "+00:00")
                        parsed_ts = datetime.fromisoformat(ts).isoformat()
                    else:
                        parsed_ts = datetime.now(timezone.utc).isoformat()
                except Exception:
                    parsed_ts = datetime.now(timezone.utc).isoformat()

                raw_urls: list[str] = data.get("attachments", [])
                clean_urls = []
                for u in raw_urls:
                    u = self._normalize_url(u)
                    if self._validate_attachment_url(u) and u not in clean_urls:
                        clean_urls.append(u)

                collected.append({
                    "id": msg_id,
                    "timestamp": parsed_ts,
                    "text": data.get("text", ""),
                    "attachments": clean_urls,
                })

            if i % 100 == 0 and i > 0:
                logger.info(f"Scroll {i}/{max_scrolls} | unique msgs: {len(seen_ids)}")

            if new_count == 0:
                no_new_streak += 1
            else:
                no_new_streak = 0

            try:
                if scroller:
                    cur_top = await scroller.evaluate("e => e.scrollTop")
                else:
                    cur_top = await page.evaluate("window.scrollY")
            except Exception:
                cur_top = -1

            if cur_top == prev_top:
                top_stuck_streak += 1
            else:
                top_stuck_streak = 0
            prev_top = cur_top

            if cur_top == 0:
                await asyncio.sleep(1.0)
                try:
                    confirm_top = (
                        await scroller.evaluate("e => e.scrollTop")
                        if scroller else await page.evaluate("window.scrollY")
                    )
                except Exception:
                    confirm_top = 0
                if confirm_top == 0:
                    top_stuck_streak += 1

            if top_stuck_streak >= 5:
                logger.info(f"Reached top of channel after {i} scrolls")
                break
            if no_new_streak >= 300:
                logger.info(f"No new messages after 300 scrolls ({i}) – assuming top reached")
                break

        logger.info(f"_load_messages done: {len(collected)} unique messages")
        return collected

    async def _get_new_messages(self, channel_id: str, page: Page) -> list[dict]:
        initial_load = not self._initial_load_done.get(channel_id, False)
        last_id = self._last_processed.get(channel_id, 0)

        max_scrolls = 500 if initial_load else 50
        all_msgs = await self._load_messages(page, max_scrolls=max_scrolls)

        if not all_msgs:
            if initial_load:
                self._initial_load_done[channel_id] = True
            return []

        new_msgs = []
        for msg in all_msgs:
            try:
                msg_id_int = int(msg["id"])
            except ValueError:
                msg_id_int = 0
            if msg_id_int <= last_id:
                continue
            new_msgs.append(msg)

        new_msgs.sort(key=lambda m: int(m["id"]) if m["id"].isdigit() else 0)

        if initial_load:
            self._initial_load_done[channel_id] = True

        if channel_id not in self._known_message_ids:
            self._known_message_ids[channel_id] = set()
        for msg in new_msgs:
            self._known_message_ids[channel_id].add(msg["id"])

        if new_msgs:
            max_id = max(int(m["id"]) for m in new_msgs)
            self._last_processed[channel_id] = max_id

        logger.info(f"Channel {channel_id}: {len(new_msgs)} new messages (last_id={last_id})")
        return new_msgs

    # ------------------------------------------------------------------
    # Download
    # ------------------------------------------------------------------
    async def _download_attachment(
        self, url: str, dest: Path, retries: int = 5
    ) -> Path | None:
        url = self._normalize_url(url)
        dest.parent.mkdir(parents=True, exist_ok=True)

        for attempt in range(1, retries + 1):
            try:
                response = await self.context.request.get(url, timeout=60_000)
                if response.status == 200:
                    body = await response.body()
                    if body:
                        dest.write_bytes(body)
                        self._download_stats["success"] += 1
                        self._download_stats["total_bytes"] += len(body)
                        logger.info(f"[OK] Downloaded {dest.name} ({len(body)/1024/1024:.2f} MB)")
                        return dest
                elif response.status in (403, 404, 410):
                    logger.error(f"Permanent HTTP {response.status} for {url}")
                    self._download_stats["failed"] += 1
                    return None
                else:
                    logger.warning(f"HTTP {response.status} attempt {attempt}")
            except asyncio.TimeoutError:
                logger.warning(f"Timeout downloading {url} (attempt {attempt})")
            except Exception as e:
                logger.warning(f"Download error (attempt {attempt}): {e}")

            if attempt < retries:
                wait = min(2 ** attempt, 30)
                logger.info(f"Retrying in {wait}s …")
                await asyncio.sleep(wait)

        self._download_stats["failed"] += 1
        logger.error(f"[FAIL] Could not download after {retries} attempts: {url}")
        return None

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------
    def _normalize_url(self, url: str) -> str:
        if not url:
            return ""
        url = url.split("#")[0]
        url = url.replace("media.discordapp.net", "cdn.discordapp.com")
        if url.startswith("//"):
            url = "https:" + url
        elif not url.startswith("http"):
            url = "https://" + url
        return url

    def _validate_attachment_url(self, url: str) -> bool:
        if not url:
            return False
        if "/stickers/" in url:
            return False
        return any(domain in url for domain in self.DISCORD_CDN_DOMAINS)

    def _track(self, channel_id: str, key: str, delta: int = 1):
        if channel_id not in self._ch_stats:
            self._ch_stats[channel_id] = {"collected": 0, "with_media": 0, "forwarded": 0, "failed": 0}
        self._ch_stats[channel_id][key] += delta

    def _print_channel_summary(self, channel_id: str):
        s = self._ch_stats.get(channel_id, {})
        logger.info(f"[STATS] Channel {channel_id}: collected={s.get('collected',0)} "
                    f"with_media={s.get('with_media',0)} forwarded={s.get('forwarded',0)} "
                    f"failed={s.get('failed',0)}")

    def reset_seen(self, channel_id: str):
        self._known_message_ids[channel_id] = set()
        self._initial_load_done[channel_id] = False

    # ------------------------------------------------------------------
    # Process message
    # ------------------------------------------------------------------
    async def _process_message(self, msg: dict, source_info: SourceInfo):
        class _MsgWrapper:
            def __init__(self, d):
                self.id = d["id"]
                self.content = d["text"]
                self.attachments = d["attachments"]
                self.author = "Scraped User"
                self.timestamp = d.get("timestamp", "")

        wrapper = _MsgWrapper(msg)
        channel_id = source_info.channel_id
        has_media = bool(msg["attachments"])

        self._track(channel_id, "collected")
        if has_media:
            self._track(channel_id, "with_media")

        try:
            success = await self.on_message(wrapper, source_info)
            if has_media:
                if success:
                    self._track(channel_id, "forwarded")
                    ok = self._ch_stats[channel_id]["forwarded"]
                    if ok % 50 == 0:
                        logger.info(f"[STATS] {channel_id}: {ok} media messages forwarded so far")
                else:
                    self._track(channel_id, "failed")
        except Exception as e:
            logger.error(f"Error in message callback for {msg['id']}: {e}", exc_info=True)
            if has_media:
                self._track(channel_id, "failed")

    # ------------------------------------------------------------------
    # Public methods
    # ------------------------------------------------------------------
    async def start(self):
        self._running = True
        logger.info("Discord scraper initialized (browser will launch on first poll)")

    async def poll_channels(self):
        if not self._running:
            raise RuntimeError("Scraper not started – call start() first")

        logger.info(f"[POLL] Starting poll loop for {len(self.channels)} channels")
        poll_count = 0

        while self._running:
            async with self.run_lock:
                poll_count += 1
                logger.info(f"=== Discord Poll cycle #{poll_count} ===")

                try:
                    await self._ensure_browser_and_login()

                    for channel_id in self.channels:
                        now = time.time()
                        if now - self._last_poll.get(channel_id, 0) < 10:
                            continue
                        self._last_poll[channel_id] = now

                        try:
                            page = await self._navigate_to_channel(channel_id)
                            if not await self._page_alive(page):
                                logger.warning(f"Page not alive for {channel_id} – skipping")
                                self._page = await self.context.new_page()
                                continue

                            try:
                                await page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                            except Exception:
                                pass
                            await asyncio.sleep(random.uniform(0.5, 1.5))

                            messages = await self._get_new_messages(channel_id, page)
                            if messages:
                                logger.info(f"[MSG] Processing {len(messages)} new messages from {channel_id}")
                                for msg in messages:
                                    info = SourceInfo(
                                        platform="discord",
                                        channel_id=channel_id,
                                        channel_name=f"Channel-{channel_id}",
                                        author="Discord Scraper",
                                    )
                                    await self._process_message(msg, info)
                                self._print_channel_summary(channel_id)
                            else:
                                logger.debug(f"No new messages in {channel_id}")

                        except Exception:
                            logger.exception(f"Error polling channel {channel_id}")
                            try:
                                await self._page.close()
                            except Exception:
                                pass
                            self._page = await self.context.new_page()
                            await asyncio.sleep(5)

                        await asyncio.sleep(random.uniform(1, 3))

                except Exception as e:
                    logger.exception(f"Error in poll cycle: {e}")

                finally:
                    await self._close_browser()

            await asyncio.sleep(random.uniform(60, 120))

    async def stop(self):
        logger.info("[STOP] Stopping scraper …")
        self._running = False
        await self._close_browser()
        logger.info("[OK] Scraper stopped")