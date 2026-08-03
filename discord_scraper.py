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

logger = logging.getLogger(__name__)

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
        return CDN_HOSTS.some(h => url.includes(h)) || url.includes('/attachments/');
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
            const textEl = el.querySelector(
                '[class*="messageContent"], [id^="message-content-"]'
            );
            const text = textEl ? (textEl.innerText || '').slice(0, 2000) : '';
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

# JavaScript to inject a Discord auth token directly into localStorage
# This bypasses the login form entirely
_INJECT_TOKEN_JS = """
(token) => {
    // Store token in localStorage the same way Discord's app does
    window.localStorage.setItem('token', JSON.stringify(token));
    
    // Also try the Redux store injection approach
    try {
        const iframe = document.createElement('iframe');
        document.body.appendChild(iframe);
        iframe.contentWindow.localStorage.setItem('token', JSON.stringify(token));
        document.body.removeChild(iframe);
    } catch(e) {}
    
    return true;
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
                logger.warning(f"Invalid DISCORD_START_DATE: {start_date} – {e}")

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

        # Token-based auth (preferred over email/password)
        import os
        self._discord_token: str | None = os.environ.get("DISCORD_TOKEN", "").strip() or None
        if self._discord_token:
            logger.info("✓ DISCORD_TOKEN found – will use token injection (no browser login needed)")
        else:
            logger.info("No DISCORD_TOKEN – will use email/password browser login")

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
            # Memory saving flags for 512MB servers
            "--js-flags=--max-old-space-size=256",
            "--renderer-process-limit=1",
            "--disable-extensions",
            "--disable-background-networking",
            "--disable-sync",
            "--disable-translate",
            "--disable-plugins",
            "--disable-hang-monitor",
            "--disable-prompt-on-repost",
            "--disable-client-side-phishing-detection",
            "--disable-component-update",
            "--disable-default-apps",
            "--disable-domain-reliability",
            "--disable-features=AudioServiceOutOfProcess",
            "--no-first-run",
            "--safebrowsing-disable-auto-update",
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
    # Token injection login (PRIMARY method – no CAPTCHA, no OOM)
    # ------------------------------------------------------------------
    async def _login_with_token(self, page: Page) -> bool:
        """
        Inject the Discord auth token directly into localStorage.
        This is the most reliable method on headless servers.
        Returns True if successful.
        """
        if not self._discord_token:
            return False

        logger.info("Injecting Discord auth token into browser...")

        try:
            # Navigate to Discord first (need a page context to set localStorage)
            await page.goto(
                "https://discord.com/login",
                wait_until="domcontentloaded",
                timeout=20000,
            )
            await asyncio.sleep(2)

            # Inject token into localStorage
            await page.evaluate(_INJECT_TOKEN_JS, self._discord_token)
            logger.info("Token injected into localStorage")

            # Navigate to the app – Discord will pick up the token
            await page.goto(
                "https://discord.com/channels/@me",
                wait_until="domcontentloaded",
                timeout=20000,
            )
            await asyncio.sleep(3)

            # Verify login worked
            if await self._chat_is_visible(page) or await self._sidebar_is_visible(page):
                logger.info("✓ Token injection successful – logged in")
                return True

            # Try one more time with a direct channel URL
            await asyncio.sleep(2)
            if await self._chat_is_visible(page) or await self._sidebar_is_visible(page):
                logger.info("✓ Token injection confirmed on retry")
                return True

            logger.warning("Token injection did not result in login – token may be expired")
            await self._save_debug_snapshot(page, "token_injection_failed")
            return False

        except Exception as e:
            logger.error(f"Token injection failed: {e}")
            return False

    # ------------------------------------------------------------------
    # Email/password login (FALLBACK – may hit CAPTCHA on fresh browsers)
    # ------------------------------------------------------------------
    async def _login_with_email(self, page: Page) -> bool:
        """
        Fill the Discord login form with email/password.
        Returns True if login succeeded.
        """
        if not self.email or not self.password:
            logger.error("No email/password configured for login")
            return False

        logger.info("→ Attempting email/password login...")

        # Navigate to login page
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
                    return False
                await asyncio.sleep(3)

        # Wait for email input (up to 40 s)
        email_selector = None
        for tick in range(20):
            await asyncio.sleep(2)

            if await self._chat_is_visible(page) or await self._sidebar_is_visible(page):
                logger.info("✓ Already logged in during email login attempt")
                return True

            for sel in [
                'input[name="email"]',
                'input[type="email"]',
                'input[autocomplete="email"]',
                'input[autocomplete="username"]',
            ]:
                el = await page.query_selector(sel)
                if el:
                    email_selector = sel
                    logger.info(f"Email input found: '{sel}' after {(tick+1)*2}s")
                    break

            if email_selector:
                break
            logger.debug(f"Waiting for login form tick {tick+1}/20 | URL: {page.url}")

        if not email_selector:
            await self._save_debug_snapshot(page, "email_form_not_found")
            logger.error("Login form never appeared")
            return False

        # Fill email
        await page.click(email_selector)
        await asyncio.sleep(0.2)
        await page.click(email_selector, click_count=3)
        await page.keyboard.type(self.email, delay=40)
        await asyncio.sleep(0.3)

        # Fill password
        pwd_selector = None
        for sel in ['input[name="password"]', 'input[type="password"]']:
            el = await page.query_selector(sel)
            if el:
                pwd_selector = sel
                break

        if not pwd_selector:
            await self._save_debug_snapshot(page, "password_field_missing")
            logger.error("Password field not found")
            return False

        await page.click(pwd_selector)
        await asyncio.sleep(0.2)
        await page.click(pwd_selector, click_count=3)
        await page.keyboard.type(self.password, delay=40)
        await asyncio.sleep(0.4)

        # Submit
        submit = await page.query_selector('button[type="submit"]')
        if submit:
            logger.info("Clicking submit...")
            await submit.click()
        else:
            logger.warning("No submit button – pressing Enter")
            await page.keyboard.press("Enter")

        logger.info("Form submitted – waiting for response...")

        # Wait for login result (up to 60 s)
        for tick in range(30):
            await asyncio.sleep(2)

            if await self._chat_is_visible(page):
                logger.info(f"✓ Logged in via email – chat visible after {(tick+1)*2}s")
                return True

            if await self._sidebar_is_visible(page):
                logger.info(f"✓ Logged in via email – sidebar visible after {(tick+1)*2}s")
                return True

            # 2FA
            for twofa_sel in [
                'input[name="code"]',
                'input[placeholder*="6-digit"]',
                'input[placeholder*="authentication"]',
            ]:
                twofa = await page.query_selector(twofa_sel)
                if twofa:
                    logger.info("2FA prompt detected – attempting auto-fill")
                    filled = await self._handle_2fa(page, twofa_sel)
                    if not filled:
                        logger.error(
                            "2FA required but DISCORD_TOTP_SECRET not set. "
                            "Set env var or disable 2FA on the account."
                        )
                        return False
                    # Wait for 2FA to complete
                    for _ in range(20):
                        await asyncio.sleep(2)
                        if await self._chat_is_visible(page) or await self._sidebar_is_visible(page):
                            logger.info("✓ 2FA completed")
                            return True

            # Error messages
            for err_sel in ['[class*="errorMessage"]', '[class*="error-message"]']:
                err_el = await page.query_selector(err_sel)
                if err_el:
                    err_text = (await err_el.text_content() or "").strip()
                    if err_text:
                        logger.error(f"Discord login error: {err_text}")
                        return False

            logger.debug(f"Awaiting login tick {tick+1}/30 | URL: {page.url}")

        await self._save_debug_snapshot(page, "email_login_timeout")
        logger.error("Email login timed out after 60s")
        return False

    # ------------------------------------------------------------------
    # Master login orchestrator
    # ------------------------------------------------------------------
    async def _perform_login(self, page: Page) -> None:
        """
        Try token injection first, fall back to email/password.
        Raises RuntimeError if all methods fail.
        """
        # Method 1: Token injection (fast, reliable, no CAPTCHA)
        if self._discord_token:
            success = await self._login_with_token(page)
            if success:
                return
            logger.warning("Token login failed – falling back to email/password")

        # Method 2: Email/password form fill
        success = await self._login_with_email(page)
        if success:
            # If login succeeded via email, try to extract and cache the token
            await self._extract_and_cache_token(page)
            return

        raise RuntimeError(
            "All login methods failed. "
            "Set DISCORD_TOKEN env var with a valid token, "
            "or check email/password credentials."
        )

    async def _extract_and_cache_token(self, page: Page) -> None:
        """
        After email login, extract the token from localStorage and log it
        so the operator can set DISCORD_TOKEN for future deploys.
        """
        try:
            token = await page.evaluate(
                "() => window.localStorage.getItem('token')"
            )
            if token:
                # Strip surrounding quotes if present
                token = token.strip('"').strip("'")
                self._discord_token = token
                logger.info(
                    f"✓ Token extracted after login. "
                    f"Set DISCORD_TOKEN={token} in your environment "
                    f"to skip login next time."
                )
        except Exception as e:
            logger.debug(f"Could not extract token: {e}")

    # ------------------------------------------------------------------
    # 2FA handler
    # ------------------------------------------------------------------
    async def _handle_2fa(self, page: Page, input_selector: str) -> bool:
        import os
        totp_secret = os.environ.get("DISCORD_TOTP_SECRET", "").strip()
        if not totp_secret:
            return False
        try:
            import pyotp
            code = pyotp.TOTP(totp_secret).now()
            logger.info(f"Auto-filling TOTP: {code}")
            await page.click(input_selector, click_count=3)
            await page.keyboard.type(code, delay=30)
            await asyncio.sleep(0.3)
            submit = await page.query_selector('button[type="submit"]')
            if submit:
                await submit.click()
            else:
                await page.keyboard.press("Enter")
            return True
        except ImportError:
            logger.error("pip install pyotp to enable auto-2FA")
            return False
        except Exception as e:
            logger.error(f"2FA error: {e}")
            return False

    # ------------------------------------------------------------------
    # DOM presence helpers
    # ------------------------------------------------------------------
    async def _chat_is_visible(self, page: Page) -> bool:
        try:
            return await page.query_selector('[data-list-id="chat-messages"]') is not None
        except Exception:
            return False

    async def _sidebar_is_visible(self, page: Page) -> bool:
        try:
            for sel in [
                'nav[aria-label="Servers sidebar"]',
                'nav[aria-label="Servers"]',
                'div[class*="guilds-"]',
                'ul[aria-label="Servers"]',
            ]:
                if await page.query_selector(sel):
                    return True
            return False
        except Exception:
            return False

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
            logger.error(f"Debug snapshot → {base}.png | URL: {page.url}")
        except Exception as e:
            logger.warning(f"Could not save snapshot '{label}': {e}")

    # ------------------------------------------------------------------
    # Ensure browser and login
    # ------------------------------------------------------------------
    async def _ensure_browser_and_login(self):
        if self._browser_ready and self.context is not None:
            return

        logger.info("Launching browser...")

        # Remove stale lock
        lock_file = self.user_data_dir / "SingletonLock"
        if lock_file.exists():
            logger.warning("Removing stale SingletonLock")
            try:
                lock_file.unlink()
            except Exception as e:
                logger.warning(f"Could not remove lock: {e}")

        self._playwright = await async_playwright().start()

        try:
            self.context = await self._create_browser_context(self._playwright)
        except Exception as e:
            logger.warning(f"Context creation failed ({e}) – wiping profile")
            shutil.rmtree(self.user_data_dir, ignore_errors=True)
            self.user_data_dir.mkdir(parents=True, exist_ok=True)
            self.context = await self._create_browser_context(self._playwright)

        self._page = await self.context.new_page()

        # Check if already logged in via persistent session
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
        logger.info(f"Checking session: {test_url}")

        try:
            await self._page.goto(test_url, wait_until="domcontentloaded", timeout=25000)
        except Exception as e:
            logger.warning(f"Initial nav error (non-fatal): {e}")

        await asyncio.sleep(3)

        if await self._chat_is_visible(self._page):
            logger.info("✓ Existing session valid")
            self._browser_ready = True
            return

        # Must login
        logger.info("No valid session – logging in")
        await self._perform_login(self._page)

        # Navigate to channel after login
        if test_channel:
            try:
                await self._page.goto(
                    f"https://discord.com/channels/{guild_id}/{test_channel}",
                    wait_until="domcontentloaded",
                    timeout=25000,
                )
            except Exception as e:
                logger.warning(f"Post-login nav error (non-fatal): {e}")
            await asyncio.sleep(4)

        if not (await self._chat_is_visible(self._page) or await self._sidebar_is_visible(self._page)):
            await self._save_debug_snapshot(self._page, "post_login_failed")
            raise RuntimeError(
                f"Login failed – nothing visible after login. URL: {self._page.url}"
            )

        logger.info("✓ Login complete")
        self._browser_ready = True

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
                logger.warning(f"Browser close error: {e}")
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
            logger.info("Browser closed")

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
            logger.warning("Page dead – recreating")
            self._page = await self.context.new_page()

        page = self._page

        if channel_id in page.url and await self._chat_is_visible(page):
            return page

        guild_id = self._channel_guilds.get(channel_id, self.GUILD_ID)
        target = f"https://discord.com/channels/{guild_id}/{channel_id}"
        logger.info(f"Navigating → {target}")

        try:
            await page.goto(target, wait_until="domcontentloaded", timeout=25000)
        except Exception as e:
            logger.warning(f"Nav error (non-fatal): {e}")

        await asyncio.sleep(2)

        if not await self._chat_is_visible(page):
            logger.warning(f"No chat after nav – re-logging in")
            await self._perform_login(page)
            try:
                await page.goto(target, wait_until="domcontentloaded", timeout=25000)
            except Exception as e:
                logger.warning(f"Post-relogin nav error: {e}")
            await asyncio.sleep(2)

        await self._wait_for_chat(page)

        m = re.search(r"/channels/(\d+)/(\d+)", page.url)
        if m:
            self._channel_guilds[channel_id] = m.group(1)

        return page

    async def _wait_for_chat(self, page: Page) -> None:
        for sel in [
            '[data-list-id="chat-messages"]',
            'div[class*="scroller-"][class*="messages"]',
            'div[class*="messagesWrapper"]',
            'main[class*="chatContent"]',
        ]:
            try:
                await page.wait_for_selector(sel, timeout=6000, state="visible")
                return
            except Exception:
                continue
        logger.warning("Chat container not confirmed")

    async def _dismiss_modals(self, page: Page) -> None:
        for btn in [
            'button:has-text("Accept")',
            'button:has-text("Continue")',
            'button:has-text("I understand")',
            'button:has-text("Got it")',
            'button:has-text("Okay")',
        ]:
            try:
                if await page.locator(btn).count() > 0:
                    await page.click(btn, timeout=2000)
                    await asyncio.sleep(0.5)
                    return
            except Exception:
                continue

    # ------------------------------------------------------------------
    # Message loading  (reduced max_scrolls to save memory)
    # ------------------------------------------------------------------
    async def _find_scroller(self, page: Page):
        for sel in [
            'div[data-list-id="chat-messages"]',
            'div[class*="scroller-"][class*="messages"]',
            'div[class*="scroller-"][role="list"]',
            'div[class*="scroller-"]',
            'div[role="list"]',
        ]:
            try:
                el = await page.query_selector(sel)
                if el and await el.evaluate("e => e.scrollHeight > e.clientHeight + 5"):
                    return el
            except Exception:
                continue
        return None

    async def _load_messages(self, page: Page, max_scrolls: int = 10) -> list[dict]:
        if not await self._page_alive(page):
            return []

        await self._dismiss_modals(page)
        scroller = await self._find_scroller(page)

        seen_ids: set[str] = set()
        collected: list[dict] = []
        no_new_streak = 0
        top_stuck_streak = 0
        prev_top: float = -1
        scroll_step = 3000

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

            try:
                message_data: list[dict] = await page.evaluate(_EXTRACT_JS)
            except Exception as e:
                logger.warning(f"JS error at scroll {i}: {e}")
                message_data = []

            if not message_data and i == 0 and self.debug_dir:
                self.debug_dir.mkdir(parents=True, exist_ok=True)
                await page.screenshot(path=str(self.debug_dir / "debug.png"))
                logger.warning("No messages on first scroll – saved screenshot")

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
                        if ts else datetime.now(timezone.utc).isoformat()
                    )
                except Exception:
                    parsed_ts = datetime.now(timezone.utc).isoformat()

                clean_urls = []
                for u in data.get("attachments", []):
                    u = self._normalize_url(u)
                    if self._validate_attachment_url(u) and u not in clean_urls:
                        clean_urls.append(u)

                collected.append({
                    "id": msg_id,
                    "timestamp": parsed_ts,
                    "text": data.get("text", ""),
                    "attachments": clean_urls,
                })

            if i > 0 and i % 50 == 0:
                logger.info(f"Scroll {i}/{max_scrolls} | {len(seen_ids)} msgs")

            no_new_streak = 0 if new_count else no_new_streak + 1

            try:
                cur_top = (
                    await scroller.evaluate("e => e.scrollTop")
                    if scroller else await page.evaluate("window.scrollY")
                )
            except Exception:
                cur_top = -1

            top_stuck_streak = top_stuck_streak + 1 if cur_top == prev_top else 0
            prev_top = cur_top

            if top_stuck_streak >= 5 or no_new_streak >= 50:
                logger.info(f"Stopping scroll at {i} (stuck={top_stuck_streak} no_new={no_new_streak})")
                break

        logger.info(f"Loaded {len(collected)} messages")
        return collected

    async def _get_new_messages(self, channel_id: str, page: Page) -> list[dict]:
        initial_load = not self._initial_load_done.get(channel_id, False)
        last_id = self._last_processed.get(channel_id, 0)

        # CRITICAL: limit scrolls to prevent OOM
        # Initial load: 100 scrolls max (not 500!)
        # Subsequent: 20 scrolls
        max_scrolls = 100 if initial_load else 20

        all_msgs = await self._load_messages(page, max_scrolls=max_scrolls)

        if not all_msgs:
            self._initial_load_done[channel_id] = True
            return []

        new_msgs = [
            m for m in all_msgs
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

        logger.info(f"Channel {channel_id}: {len(new_msgs)} new (last_id={last_id})")
        return new_msgs

    # ------------------------------------------------------------------
    # Download
    # ------------------------------------------------------------------
    async def _download_attachment(self, url: str, dest: Path, retries: int = 3) -> Path | None:
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
                        return dest
                elif response.status in (403, 404, 410):
                    self._download_stats["failed"] += 1
                    return None
            except Exception as e:
                logger.warning(f"Download attempt {attempt} failed: {e}")
            if attempt < retries:
                await asyncio.sleep(min(2**attempt, 15))

        self._download_stats["failed"] += 1
        return None

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------
    def _normalize_url(self, url: str) -> str:
        if not url:
            return ""
        url = url.split("#")[0].replace("media.discordapp.net", "cdn.discordapp.com")
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
            f"forwarded={s.get('forwarded',0)} failed={s.get('failed',0)}"
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
                self._track(channel_id, "forwarded" if success else "failed")
        except Exception as e:
            logger.error(f"Callback error for {msg['id']}: {e}", exc_info=True)
            if has_media:
                self._track(channel_id, "failed")

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------
    async def start(self) -> None:
        self._running = True
        logger.info("Discord scraper ready")

    async def poll_channels(self) -> None:
        if not self._running:
            raise RuntimeError("Call start() first")

        logger.info(f"[POLL] Starting for {len(self.channels)} channel(s)")
        poll_count = 0

        while self._running:
            async with self.run_lock:
                poll_count += 1
                logger.info(f"=== Poll #{poll_count} ===")

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
                                self._page = await self.context.new_page()
                                continue

                            await asyncio.sleep(random.uniform(0.5, 1.5))
                            messages = await self._get_new_messages(channel_id, page)

                            if messages:
                                logger.info(f"[MSG] {len(messages)} new from {channel_id}")
                                for msg in messages:
                                    await self._process_message(
                                        msg,
                                        SourceInfo(
                                            platform="discord",
                                            channel_id=channel_id,
                                            channel_name=f"Channel-{channel_id}",
                                            author="Discord Scraper",
                                        ),
                                    )
                                self._print_channel_summary(channel_id)

                        except Exception:
                            logger.exception(f"Error on channel {channel_id}")
                            try:
                                await self._page.close()
                            except Exception:
                                pass
                            try:
                                self._page = await self.context.new_page()
                            except Exception:
                                pass
                            await asyncio.sleep(5)

                        await asyncio.sleep(random.uniform(1, 3))

                except Exception as e:
                    logger.exception(f"Poll cycle error: {e}")
                finally:
                    await self._close_browser()

            # Wait between cycles – longer to reduce memory pressure
            wait = random.uniform(90, 150)
            logger.info(f"Next poll in {wait:.0f}s")
            await asyncio.sleep(wait)

    async def stop(self) -> None:
        self._running = False
        await self._close_browser()
        logger.info("Scraper stopped")