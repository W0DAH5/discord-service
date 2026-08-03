# discord_scraper.py
from __future__ import annotations

import asyncio
import gc
import logging
import random
import re
import shutil
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Coroutine, Optional

import psutil
from playwright.async_api import async_playwright, BrowserContext, Page

from models import SourceInfo
from utils import sanitize_filename, unlink_quiet

logger = logging.getLogger(__name__)

# ---------- JavaScript message extraction ----------
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

    const timeElements = document.querySelectorAll('time[datetime]');
    if (timeElements.length > 0) {
        timeElements.forEach(timeEl => {
            let container = timeEl.closest(
                'div[class*="message"], li[role="article"], div[class*="container"]'
            );
            if (!container) container = timeEl.parentElement;

            let msgId = container.id || container.getAttribute('data-list-item-id') || '';
            if (!msgId) {
                const idEl = container.querySelector('[id^="message-"]');
                if (idEl) msgId = idEl.id.replace(/[^0-9]/g, '');
            }
            const numericMatch = msgId.match(/\d+$/);
            if (numericMatch) msgId = numericMatch[0];
            if (!msgId) msgId = Math.random().toString(36).substr(2, 9);
            if (seenIds.has(msgId)) return;
            seenIds.add(msgId);

            const ts = timeEl.getAttribute('datetime') || '';
            const textEl = container.querySelector(
                '[class*="messageContent"], [id^="message-content-"]'
            );
            const text = textEl ? (textEl.innerText || '').slice(0, 2000) : '';
            const attachments = extractUrls(container);
            container.querySelectorAll(
                '[class*="embed"], [class*="attachment"], [class*="imageContainer"], [class*="visualMediaItem"]'
            ).forEach(embed => {
                extractUrls(embed).forEach(u => {
                    if (!attachments.includes(u)) attachments.push(u);
                });
            });
            messages.push({ id: msgId, timestamp: ts, text, attachments });
        });
    } else {
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
            const textEl = el.querySelector(
                '[class*="messageContent"], [id^="message-content-"]'
            );
            if (textEl) text = (textEl.innerText || '').slice(0, 2000);
            const attachments = extractUrls(el);
            el.querySelectorAll(
                '[class*="embed"], [class*="attachment"], [class*="imageContainer"]'
            ).forEach(embed => {
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
        transformer,
        on_message_callback: Callable[[Any, SourceInfo], Coroutine[Any, Any, bool]],
        data_dir: Path,
        headless: bool = False,
        start_date: str | None = None,
        store=None,
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
                self.start_date = datetime.fromisoformat(start_date).replace(
                    tzinfo=timezone.utc
                )
                logger.info(f"Start date set: {self.start_date}")
            except Exception as e:
                logger.warning(
                    f"Invalid DISCORD_START_DATE: {start_date} – ignoring ({e})"
                )

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
        self._last_processed: dict[str, int] = {}

    # ------------------------------------------------------------------
    # Browser args / context
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
    # STEP 1 – Boot browser and verify / perform login
    # ------------------------------------------------------------------
    async def _ensure_browser_and_login(self):
        if self._browser_ready and self.context is not None:
            return

        logger.info("Launching Discord browser...")

        # Remove stale SingletonLock so Chromium doesn't refuse to start
        lock_file = self.user_data_dir / "SingletonLock"
        if lock_file.exists():
            logger.warning("Removing stale SingletonLock from chrome_user_data")
            try:
                lock_file.unlink()
            except Exception as e:
                logger.warning(f"Could not remove SingletonLock: {e}")

        self._playwright = await async_playwright().start()

        # Create browser context – wipe profile on failure
        try:
            self.context = await self._create_browser_context(self._playwright)
        except Exception as e:
            logger.warning(
                f"Browser context creation failed ({e}) – "
                "wiping chrome_user_data and retrying"
            )
            shutil.rmtree(self.user_data_dir, ignore_errors=True)
            self.user_data_dir.mkdir(parents=True, exist_ok=True)
            self.context = await self._create_browser_context(self._playwright)

        self._page = await self.context.new_page()

        # Navigate to the target channel to test session validity
        test_channel = self.channels[0] if self.channels else None
        guild_id = (
            self._channel_guilds.get(test_channel, self.GUILD_ID)
            if test_channel
            else self.GUILD_ID
        )
        test_url = (
            f"https://discord.com/channels/{guild_id}/{test_channel}"
            if test_channel
            else "https://discord.com/channels/@me"
        )
        logger.info(f"Navigating to test URL: {test_url}")

        try:
            await self._page.goto(
                test_url, wait_until="domcontentloaded", timeout=30000
            )
        except Exception as e:
            logger.warning(f"Initial navigation error (non-fatal): {e}")

        await asyncio.sleep(3)

        # DOM-based session check
        if await self._chat_is_visible(self._page):
            logger.info("✓ Session valid – message list found immediately")
            self._browser_ready = True
            return

        # No message list → must log in
        logger.info("Session invalid or not logged in – starting login flow")
        await self._perform_login(self._page)

        # After login, navigate to the actual channel
        if test_channel:
            target = f"https://discord.com/channels/{guild_id}/{test_channel}"
            logger.info(f"Post-login: navigating to {target}")
            try:
                await self._page.goto(
                    target, wait_until="domcontentloaded", timeout=30000
                )
            except Exception as e:
                logger.warning(f"Post-login navigation error (non-fatal): {e}")
            await asyncio.sleep(4)

        if not await self._chat_is_visible(self._page):
            await self._save_debug_snapshot(self._page, "post_login_no_chat")
            raise RuntimeError(
                "Login succeeded but message list still not visible. "
                f"URL: {self._page.url}"
            )

        logger.info("✓ Login complete – ready to poll")
        self._browser_ready = True

    # ------------------------------------------------------------------
    # STEP 2 – Login flow (NO about:blank, direct goto login)
    # ------------------------------------------------------------------
    async def _perform_login(self, page: Page) -> None:
        """
        Navigate directly to https://discord.com/login and fill credentials.
        No intermediate navigations that cause race conditions.
        """
        logger.info("→ Navigating to https://discord.com/login ...")

        # Direct navigation – no about:blank, no intermediate stops
        for attempt in range(1, 4):
            try:
                await page.goto(
                    "https://discord.com/login",
                    wait_until="domcontentloaded",
                    timeout=30000,
                )
                logger.info(f"Login page loaded (attempt {attempt})")
                break
            except Exception as e:
                logger.warning(f"Login page navigation attempt {attempt} failed: {e}")
                if attempt == 3:
                    raise RuntimeError(
                        "Cannot navigate to Discord login page after 3 attempts"
                    )
                await asyncio.sleep(3)

        # Wait for the React app to mount the email input (up to 40 s)
        logger.info("Waiting for login form to render...")
        email_selector = None
        for tick in range(20):  # 20 × 2 s = 40 s
            await asyncio.sleep(2)

            # Already logged in? (Discord may redirect to /channels/)
            if await self._chat_is_visible(page):
                logger.info("✓ Already logged in – skipping form fill")
                return
            if "/channels/" in page.url and await self._sidebar_is_visible(page):
                logger.info("✓ Sidebar visible – already logged in")
                return

            # Try all known email input selectors
            for sel in [
                'input[name="email"]',
                'input[type="email"]',
                'input[autocomplete="email"]',
                'input[autocomplete="username"]',
            ]:
                el = await page.query_selector(sel)
                if el:
                    email_selector = sel
                    logger.info(
                        f"  Email input found with '{sel}' after {(tick+1)*2}s"
                    )
                    break

            if email_selector:
                break

            logger.debug(
                f"  Tick {tick+1}/20 – form not yet visible | URL: {page.url}"
            )

        if not email_selector:
            await self._save_debug_snapshot(page, "login_form_missing")
            raise RuntimeError(
                f"Login form never appeared after 40 s. URL: {page.url}. "
                "See debug snapshot."
            )

        # ------------------------------------------------------------------
        # Fill email
        # ------------------------------------------------------------------
        logger.info("Filling email...")
        await page.click(email_selector)
        await asyncio.sleep(0.2)
        # Triple-click to select all existing text, then type
        await page.click(email_selector, click_count=3)
        await page.keyboard.type(self.email, delay=40)
        await asyncio.sleep(0.3)

        # ------------------------------------------------------------------
        # Fill password
        # ------------------------------------------------------------------
        pwd_selector = None
        for sel in ['input[name="password"]', 'input[type="password"]']:
            el = await page.query_selector(sel)
            if el:
                pwd_selector = sel
                break

        if not pwd_selector:
            await self._save_debug_snapshot(page, "password_field_missing")
            raise RuntimeError("Password field not found after filling email")

        logger.info("Filling password...")
        await page.click(pwd_selector)
        await asyncio.sleep(0.2)
        await page.click(pwd_selector, click_count=3)
        await page.keyboard.type(self.password, delay=40)
        await asyncio.sleep(0.4)

        # ------------------------------------------------------------------
        # Submit
        # ------------------------------------------------------------------
        submit = await page.query_selector('button[type="submit"]')
        if submit:
            logger.info("Clicking submit button...")
            await submit.click()
        else:
            logger.warning("Submit button not found – pressing Enter")
            await page.keyboard.press("Enter")

        logger.info("Form submitted – waiting for Discord to respond...")

        # ------------------------------------------------------------------
        # Wait for login result (up to 80 s)
        # ------------------------------------------------------------------
        for tick in range(40):  # 40 × 2 s = 80 s
            await asyncio.sleep(2)

            # Success indicators
            if await self._chat_is_visible(page):
                logger.info(f"✓ Logged in – chat visible after {(tick+1)*2}s")
                return
            if await self._sidebar_is_visible(page):
                logger.info(f"✓ Logged in – sidebar visible after {(tick+1)*2}s")
                return

            # 2FA / MFA prompt
            for twofa_sel in [
                'input[name="code"]',
                'input[placeholder*="6-digit"]',
                'input[placeholder*="authentication"]',
                'input[placeholder*="2FA"]',
            ]:
                twofa = await page.query_selector(twofa_sel)
                if twofa:
                    # Try to auto-fill TOTP if secret is configured
                    filled = await self._handle_2fa(page, twofa_sel)
                    if filled:
                        # Give Discord time to process
                        for _ in range(20):
                            await asyncio.sleep(2)
                            if await self._chat_is_visible(page):
                                logger.info("✓ 2FA auto-completed")
                                return
                            if await self._sidebar_is_visible(page):
                                logger.info("✓ 2FA auto-completed – sidebar")
                                return
                        raise RuntimeError(
                            "2FA code submitted but login not confirmed"
                        )
                    else:
                        raise RuntimeError(
                            "2FA required but no TOTP secret configured. "
                            "Set DISCORD_TOTP_SECRET env var or disable 2FA."
                        )

            # Error messages from Discord
            for err_sel in [
                '[class*="errorMessage"]',
                '[class*="error-message"]',
                'div[class*="toast-"][class*="error"]',
            ]:
                err_el = await page.query_selector(err_sel)
                if err_el:
                    err_text = (await err_el.text_content() or "").strip()
                    if err_text:
                        raise RuntimeError(f"Discord login rejected: {err_text}")

            logger.debug(
                f"  Awaiting login confirmation tick {tick+1}/40 | URL: {page.url}"
            )

        await self._save_debug_snapshot(page, "login_timeout")
        raise RuntimeError(
            f"Login timed out after 80 s. Final URL: {page.url}. "
            "Check credentials."
        )

    # ------------------------------------------------------------------
    # 2FA handler – auto-fill TOTP if secret is available
    # ------------------------------------------------------------------
    async def _handle_2fa(self, page: Page, input_selector: str) -> bool:
        """
        Attempt to auto-fill a TOTP code.
        Returns True if a code was submitted, False if no secret is available.
        """
        import os
        totp_secret = os.environ.get("DISCORD_TOTP_SECRET", "").strip()
        if not totp_secret:
            logger.warning(
                "2FA input detected but DISCORD_TOTP_SECRET is not set. "
                "Cannot auto-fill."
            )
            return False

        try:
            import pyotp
            totp = pyotp.TOTP(totp_secret)
            code = totp.now()
            logger.info(f"Auto-filling 2FA code: {code}")
            await page.click(input_selector, click_count=3)
            await page.keyboard.type(code, delay=30)
            await asyncio.sleep(0.3)

            # Submit the 2FA form
            submit = await page.query_selector('button[type="submit"]')
            if submit:
                await submit.click()
            else:
                await page.keyboard.press("Enter")
            return True
        except ImportError:
            logger.error(
                "pyotp is not installed – cannot auto-fill 2FA. "
                "Run: pip install pyotp"
            )
            return False
        except Exception as e:
            logger.error(f"2FA auto-fill failed: {e}")
            return False

    # ------------------------------------------------------------------
    # DOM presence helpers (the ONLY reliable login check)
    # ------------------------------------------------------------------
    async def _chat_is_visible(self, page: Page) -> bool:
        """Returns True if the Discord message list is in the DOM."""
        try:
            el = await page.query_selector('[data-list-id="chat-messages"]')
            return el is not None
        except Exception:
            return False

    async def _sidebar_is_visible(self, page: Page) -> bool:
        """Returns True if the Discord server sidebar is in the DOM."""
        try:
            for sel in [
                'nav[aria-label="Servers sidebar"]',
                'nav[aria-label="Servers"]',
                'div[class*="guilds-"]',
                'ul[aria-label="Servers"]',
            ]:
                el = await page.query_selector(sel)
                if el:
                    return True
            return False
        except Exception:
            return False

    # Kept for backward compatibility with _navigate_to_channel
    async def _is_logged_in(self, page: Page) -> bool:
        if "/login" in page.url:
            return False
        return await self._chat_is_visible(page) or await self._sidebar_is_visible(page)

    # ------------------------------------------------------------------
    # Debug snapshot
    # ------------------------------------------------------------------
    async def _save_debug_snapshot(self, page: Page, label: str) -> None:
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
                f"Debug snapshot → {base}.png / .html  (URL: {page.url})"
            )
        except Exception as e:
            logger.warning(f"Could not save debug snapshot '{label}': {e}")

    # ------------------------------------------------------------------
    # Browser close
    # ------------------------------------------------------------------
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

        # Already on correct channel with messages visible
        if channel_id in page.url and await self._chat_is_visible(page):
            logger.debug(f"Already on channel {channel_id}")
            return page

        guild_id = self._channel_guilds.get(channel_id, self.GUILD_ID)
        if not guild_id:
            raise ValueError(f"No guild ID for channel {channel_id}")

        target = f"https://discord.com/channels/{guild_id}/{channel_id}"
        logger.info(f"Navigating to: {target}")

        try:
            await page.goto(target, wait_until="domcontentloaded", timeout=30000)
        except Exception as e:
            logger.warning(f"Navigation error (non-fatal): {e}")

        await asyncio.sleep(2)

        # Session check after navigation
        if not await self._chat_is_visible(page):
            logger.warning(
                f"No chat after navigation to {channel_id} "
                f"(URL: {page.url}) – re-logging in"
            )
            await self._perform_login(page)
            try:
                await page.goto(target, wait_until="domcontentloaded", timeout=30000)
            except Exception as e:
                logger.warning(f"Post-relogin navigation error: {e}")
            await asyncio.sleep(2)

        await self._wait_for_chat(page)

        m = re.search(r"/channels/(\d+)/(\d+)", page.url)
        if m:
            self._channel_guilds[channel_id] = m.group(1)

        logger.info(f"✓ On channel {channel_id}")
        return page

    async def _wait_for_chat(self, page: Page) -> None:
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

    async def _dismiss_modals(self, page: Page) -> None:
        for btn in [
            'button:has-text("Accept")',
            'button:has-text("Continue")',
            'button:has-text("I understand")',
            'button:has-text("Got it")',
            'button:has-text("Okay")',
            'button[class*="confirmButton"]',
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
                        logger.info(f"Scroller: {sel}")
                        return el
                    parent = await el.evaluate_handle("e => e.parentElement")
                    if parent:
                        if await parent.evaluate(
                            "e => e.scrollHeight > e.clientHeight + 5"
                        ):
                            logger.info(f"Scroller (parent of): {sel}")
                            return parent
            except Exception:
                continue

        el = await page.evaluate_handle("""
            () => {
                let best = null, bestH = 0;
                for (const el of document.querySelectorAll('div')) {
                    const s = getComputedStyle(el);
                    const ok = s.overflowY === 'auto' || s.overflowY === 'scroll'
                             || s.overflow  === 'auto' || s.overflow  === 'scroll';
                    if (ok && el.scrollHeight > el.clientHeight + 10
                           && el.scrollHeight > bestH) {
                        best = el; bestH = el.scrollHeight;
                    }
                }
                return best;
            }
        """)
        try:
            if not await el.evaluate("e => e === null"):
                logger.info("Scroller: fallback JS")
                return el
        except Exception:
            pass

        logger.warning("No scroller found")
        return None

    async def _load_messages(self, page: Page, max_scrolls: int = 10) -> list[dict]:
        if not await self._page_alive(page):
            logger.warning("Page closed – skipping _load_messages")
            return []

        await self._dismiss_modals(page)
        scroller = await self._find_scroller(page)

        seen_ids: set[str] = set()
        collected: list[dict] = []
        no_new_streak = 0
        top_stuck_streak = 0
        scroll_step = 3000
        prev_top: float = -1

        for i in range(max_scrolls):
            try:
                if scroller:
                    await scroller.evaluate(f"e => e.scrollBy(0, -{scroll_step})")
                else:
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
                (self.debug_dir / "debug.html").write_text(html, encoding="utf-8")
                await page.screenshot(path=str(self.debug_dir / "debug.png"))
                logger.warning(f"No messages – saved debug to {self.debug_dir}")

            new_count = 0
            for data in message_data:
                msg_id = data.get("id", "")
                if not msg_id or msg_id in seen_ids:
                    continue
                seen_ids.add(msg_id)
                new_count += 1

                ts = data.get("timestamp", "")
                try:
                    parsed_ts = (
                        datetime.fromisoformat(ts.replace("Z", "+00:00")).isoformat()
                        if ts
                        else datetime.now(timezone.utc).isoformat()
                    )
                except Exception:
                    parsed_ts = datetime.now(timezone.utc).isoformat()

                raw_urls: list[str] = data.get("attachments", [])
                clean_urls = []
                for u in raw_urls:
                    u = self._normalize_url(u)
                    if self._validate_attachment_url(u) and u not in clean_urls:
                        clean_urls.append(u)

                collected.append(
                    {
                        "id": msg_id,
                        "timestamp": parsed_ts,
                        "text": data.get("text", ""),
                        "attachments": clean_urls,
                    }
                )

            if i % 100 == 0 and i > 0:
                logger.info(f"Scroll {i}/{max_scrolls} | unique: {len(seen_ids)}")

            no_new_streak = 0 if new_count else no_new_streak + 1

            try:
                cur_top = (
                    await scroller.evaluate("e => e.scrollTop")
                    if scroller
                    else await page.evaluate("window.scrollY")
                )
            except Exception:
                cur_top = -1

            top_stuck_streak = (
                top_stuck_streak + 1 if cur_top == prev_top else 0
            )
            prev_top = cur_top

            if cur_top == 0:
                await asyncio.sleep(1.0)
                try:
                    confirm = (
                        await scroller.evaluate("e => e.scrollTop")
                        if scroller
                        else await page.evaluate("window.scrollY")
                    )
                except Exception:
                    confirm = 0
                if confirm == 0:
                    top_stuck_streak += 1

            if top_stuck_streak >= 5:
                logger.info(f"Reached top after {i} scrolls")
                break
            if no_new_streak >= 300:
                logger.info(f"No new msgs after 300 scrolls – stopping")
                break

        logger.info(f"_load_messages: {len(collected)} unique messages")
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

        new_msgs = [
            m
            for m in all_msgs
            if (int(m["id"]) if m["id"].isdigit() else 0) > last_id
        ]
        new_msgs.sort(key=lambda m: int(m["id"]) if m["id"].isdigit() else 0)

        self._initial_load_done[channel_id] = True
        self._known_message_ids.setdefault(channel_id, set()).update(
            m["id"] for m in new_msgs
        )

        if new_msgs:
            self._last_processed[channel_id] = max(
                int(m["id"]) for m in new_msgs
            )

        logger.info(
            f"Channel {channel_id}: {len(new_msgs)} new messages (last_id={last_id})"
        )
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
                        logger.info(
                            f"[OK] {dest.name} "
                            f"({len(body)/1024/1024:.2f} MB)"
                        )
                        return dest
                elif response.status in (403, 404, 410):
                    logger.error(f"Permanent HTTP {response.status}: {url}")
                    self._download_stats["failed"] += 1
                    return None
                else:
                    logger.warning(f"HTTP {response.status} attempt {attempt}")
            except asyncio.TimeoutError:
                logger.warning(f"Timeout (attempt {attempt}): {url}")
            except Exception as e:
                logger.warning(f"Download error (attempt {attempt}): {e}")

            if attempt < retries:
                await asyncio.sleep(min(2**attempt, 30))

        self._download_stats["failed"] += 1
        logger.error(f"[FAIL] {url}")
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
        if not url or "/stickers/" in url:
            return False
        return any(d in url for d in self.DISCORD_CDN_DOMAINS)

    def _track(self, channel_id: str, key: str, delta: int = 1) -> None:
        self._ch_stats.setdefault(
            channel_id,
            {"collected": 0, "with_media": 0, "forwarded": 0, "failed": 0},
        )[key] += delta

    def _print_channel_summary(self, channel_id: str) -> None:
        s = self._ch_stats.get(channel_id, {})
        logger.info(
            f"[STATS] {channel_id}: collected={s.get('collected',0)} "
            f"with_media={s.get('with_media',0)} "
            f"forwarded={s.get('forwarded',0)} "
            f"failed={s.get('failed',0)}"
        )

    def reset_seen(self, channel_id: str) -> None:
        self._known_message_ids[channel_id] = set()
        self._initial_load_done[channel_id] = False

    # ------------------------------------------------------------------
    # Process message
    # ------------------------------------------------------------------
    async def _process_message(self, msg: dict, source_info: SourceInfo) -> None:
        class _W:
            def __init__(self, d):
                self.id = d["id"]
                self.content = d["text"]
                self.attachments = d["attachments"]
                self.author = "Scraped User"
                self.timestamp = d.get("timestamp", "")

        channel_id = source_info.channel_id
        has_media = bool(msg["attachments"])
        self._track(channel_id, "collected")
        if has_media:
            self._track(channel_id, "with_media")

        try:
            success = await self.on_message(_W(msg), source_info)
            if has_media:
                if success:
                    self._track(channel_id, "forwarded")
                    if self._ch_stats[channel_id]["forwarded"] % 50 == 0:
                        logger.info(
                            f"[STATS] {channel_id}: "
                            f"{self._ch_stats[channel_id]['forwarded']} forwarded"
                        )
                else:
                    self._track(channel_id, "failed")
        except Exception as e:
            logger.error(f"Callback error for {msg['id']}: {e}", exc_info=True)
            if has_media:
                self._track(channel_id, "failed")

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------
    async def start(self) -> None:
        self._running = True
        logger.info("Discord scraper ready (browser launches on first poll)")

    async def poll_channels(self) -> None:
        if not self._running:
            raise RuntimeError("Call start() first")

        logger.info(f"[POLL] Polling {len(self.channels)} channel(s)")
        poll_count = 0

        while self._running:
            async with self.run_lock:
                poll_count += 1
                logger.info(f"=== Poll cycle #{poll_count} ===")

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
                                logger.warning(f"Page not alive – skipping {channel_id}")
                                self._page = await self.context.new_page()
                                continue

                            try:
                                await page.evaluate(
                                    "window.scrollTo(0, document.body.scrollHeight)"
                                )
                            except Exception:
                                pass
                            await asyncio.sleep(random.uniform(0.5, 1.5))

                            messages = await self._get_new_messages(channel_id, page)
                            if messages:
                                logger.info(
                                    f"[MSG] {len(messages)} new from {channel_id}"
                                )
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
                            logger.exception(f"Error polling {channel_id}")
                            try:
                                await self._page.close()
                            except Exception:
                                pass
                            self._page = await self.context.new_page()
                            await asyncio.sleep(5)

                        await asyncio.sleep(random.uniform(1, 3))

                except Exception as e:
                    logger.exception(f"Poll cycle error: {e}")

                finally:
                    await self._close_browser()

            await asyncio.sleep(random.uniform(60, 120))

    async def stop(self) -> None:
        logger.info("[STOP] Stopping...")
        self._running = False
        await self._close_browser()
        logger.info("[OK] Stopped")