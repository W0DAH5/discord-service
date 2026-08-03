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
from transformer import MediaTransformer
from utils import sanitize_filename, unlink_quiet

# ---------- Unicode safe logging ----------
logger = logging.getLogger(__name__)

# ---------- JavaScript extraction (unchanged) ----------
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

    function extractFromElement(el) {
        const urls = new Set();
        el.querySelectorAll('a[href]').forEach(a => {
            const href = a.getAttribute('href');
            if (href && isMediaUrl(href)) urls.add(cleanUrl(href));
        });
        el.querySelectorAll('img').forEach(img => {
            for (const attr of ['src', 'data-safe-src', 'data-original-src',
                                'data-src', 'data-url']) {
                const v = img.getAttribute(attr);
                if (v && isMediaUrl(v)) { urls.add(cleanUrl(v)); break; }
            }
        });
        el.querySelectorAll('video, video source').forEach(v => {
            for (const attr of ['src', 'data-src', 'data-url']) {
                const s = v.getAttribute(attr);
                if (s && isMediaUrl(s)) { urls.add(cleanUrl(s)); break; }
            }
        });
        el.querySelectorAll('[data-attachment-url], [data-media-url], ' +
                            '[data-original-filename]').forEach(d => {
            for (const attr of ['data-attachment-url', 'data-media-url',
                                'data-url', 'data-src']) {
                const v = d.getAttribute(attr);
                if (v && isMediaUrl(v)) { urls.add(cleanUrl(v)); break; }
            }
        });
        el.querySelectorAll('[style*="discordapp"]').forEach(d => {
            const style = d.getAttribute('style') || '';
            const matches = style.match(/url\(['"]?([^'")\s]+)['"]?\)/g) || [];
            matches.forEach(m => {
                const inner = m.replace(/^url\(['"]?/, '').replace(/['"]?\)$/, '');
                if (isMediaUrl(inner)) urls.add(cleanUrl(inner));
            });
        });
        el.querySelectorAll('a[class*="originalLink"], a[class*="imageWrapper"],' +
                            'a[class*="anchor"]').forEach(a => {
            const href = a.getAttribute('href');
            if (href && isMediaUrl(href)) urls.add(cleanUrl(href));
        });
        return [...urls].filter(Boolean);
    }

    const messages = [];
    const seenIds = new Set();

    document.querySelectorAll('[data-list-item-id]').forEach(el => {
        let rawId = el.getAttribute('data-list-item-id') || '';
        let msgId = rawId;
        if (msgId.includes('___')) {
            msgId = msgId.split('___').pop();
        }
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
            'div[class*="messageContent"], div[id^="message-content"],' +
            'div[class*="markup-"], span[class*="text-"]'
        );
        if (textEl) text = (textEl.innerText || '').slice(0, 2000);

        const attachments = extractFromElement(el);

        el.querySelectorAll(
            'div[class*="embed"], div[class*="attachment"],' +
            'div[class*="imageContainer"], div[class*="videoWrapper"],' +
            'div[class*="mediaContainer"]'
        ).forEach(embed => {
            extractFromElement(embed).forEach(u => {
                if (!attachments.includes(u)) attachments.push(u);
            });
        });

        messages.push({ id: msgId, timestamp: ts, text, attachments });
    });

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

    IMAGE_EXTENSIONS = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp", ".svg", ".avif"}
    VIDEO_EXTENSIONS = {".mp4", ".mov", ".mkv", ".webm", ".mpg", ".mpeg", ".avi", ".flv"}
    DOCUMENT_EXTENSIONS = {".pdf", ".txt", ".doc", ".docx", ".zip", ".rar", ".7z"}

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
        self._channel_guilds: dict[str, str] = {}
        self._last_poll: dict[str, float] = {}
        self._initial_load_done: dict[str, bool] = {}

        self._ch_stats: dict[str, dict[str, int]] = {}
        self._download_stats = {"success": 0, "failed": 0, "total_bytes": 0}
        self.user_data_dir = data_dir / "chrome_user_data"
        self.user_data_dir.mkdir(exist_ok=True)

        # Internal flag to track if browser is launched
        self._browser_ready = False
        self._playwright = None

    # ------------------------------------------------------------------
    # Browser lifecycle (deferred)
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

    async def _ensure_browser_and_login(self):
        """Launch browser and ensure login – called only when we hold the lock."""
        if self._browser_ready and self.context is not None:
            return

        logger.info("Launching Discord browser...")
        self._playwright = await async_playwright().start()
        self.context = await self._create_browser_context(self._playwright)
        self._page = await self.context.new_page()

        # Navigate to test channel to check login
        test_channel = self.channels[0] if self.channels else None
        test_url = (
            f"https://discord.com/channels/{self.GUILD_ID}/{test_channel}"
            if test_channel else "https://discord.com/channels/@me"
        )
        await self._page.goto(test_url, wait_until="networkidle")
        await asyncio.sleep(2)

        if await self._is_logged_in(self._page):
            logger.info("✓ Using existing Discord session")
            self._browser_ready = True
            return

        logger.warning("Session invalid – re-logging in")
        await self._page.close()
        await self.context.close()
        shutil.rmtree(self.user_data_dir, ignore_errors=True)
        self.user_data_dir.mkdir(exist_ok=True)

        self.context = await self._create_browser_context(self._playwright)
        self._page = await self.context.new_page()
        await self._perform_login(self._page)

        if test_channel:
            await self._page.goto(test_url, wait_until="networkidle")
            await asyncio.sleep(2)
            if not await self._is_logged_in(self._page):
                raise RuntimeError("Login seemed successful but cannot access channels")

        logger.info("✓ Login confirmed – ready to poll")
        self._browser_ready = True

    async def _close_browser(self):
        """Close the browser to free memory – called after releasing the lock."""
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
    # Login helpers (unchanged)
    # ------------------------------------------------------------------
    async def _is_logged_in(self, page: Page) -> bool:
        try:
            url = page.url
            if "/login" in url or "/register" in url or "/download" in url:
                return False
            if await page.locator('input[name="email"]').count() > 0:
                return False
            for sel in [
                'div[class*="sidebar"]', 'nav[aria-label="Servers"]',
                'div[class*="guilds"]', 'div[class*="app-"]',
            ]:
                try:
                    if await page.locator(sel).count() > 0:
                        return True
                except Exception:
                    continue
            return "/channels/" in url
        except Exception:
            return False

    async def _perform_login(self, page: Page):
        await page.goto("https://discord.com/login", wait_until="networkidle")
        await asyncio.sleep(1)
        await page.fill('input[name="email"]', self.email, timeout=10000)
        await asyncio.sleep(0.5)
        await page.fill('input[name="password"]', self.password, timeout=10000)
        await asyncio.sleep(0.5)
        await page.click('button[type="submit"]')
        logger.info("Login form submitted")
        for _ in range(24):
            await asyncio.sleep(5)
            if await self._is_logged_in(page):
                logger.info("✓ Login successful")
                return
            if await page.locator('input[name="code"]').count() > 0:
                logger.warning("⚠ 2FA required – enter code in browser")
        raise RuntimeError("Login failed after 2 minutes")

    # ------------------------------------------------------------------
    # Navigation (relies on self._page, which is set after browser launch)
    # ------------------------------------------------------------------
    async def _page_alive(self, page: Page) -> bool:
        try:
            await page.evaluate("1")
            return True
        except Exception:
            return False

    async def _navigate_to_channel(self, channel_id: str) -> Page:
        """Navigate the shared page to the given channel."""
        if self._page is None or not await self._page_alive(self._page):
            logger.warning("Page is dead – recreating")
            self._page = await self.context.new_page()

        page = self._page
        url = page.url
        if channel_id in url:
            return page

        if "/login" in url or "/download" in url:
            logger.warning("Session expired – re-logging in")
            await self._perform_login(page)

        guild = self._channel_guilds.get(channel_id, self.GUILD_ID)
        target = f"https://discord.com/channels/{guild}/{channel_id}"
        await page.goto(target, wait_until="networkidle", timeout=30000)

        if "/login" in page.url or "/download" in page.url:
            logger.warning("Session expired during navigation – re-logging in")
            await self._perform_login(page)
            await page.goto(target, wait_until="networkidle", timeout=30000)

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
    # Message loading (unchanged)
    # ------------------------------------------------------------------
    async def _find_scroller(self, page: Page):
        selectors = [
            'div[class*="scroller-"][class*="messages"]',
            'div[class*="scroller-"][role="list"]',
            'ol[class*="scrollerInner"]',
            'div[class*="messagesWrapper"] div[class*="scroller"]',
            'div[class*="chatContent"] div[class*="scroller"]',
            '[data-list-id="chat-messages"]',
            'div[role="list"]',
        ]
        for sel in selectors:
            try:
                el = await page.query_selector(sel)
                if el:
                    scrollable = await el.evaluate(
                        "e => e.scrollHeight > e.clientHeight + 5"
                    )
                    if scrollable:
                        return el
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
                return el
        except Exception:
            pass
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
        last_id = self.store.get_last_processed(channel_id) or 0 if self.store else 0

        max_scrolls = 500 if initial_load else 15
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
            if msg_id_int <= int(last_id):
                continue
            new_msgs.append(msg)

        new_msgs.sort(key=lambda m: int(m["id"]) if m["id"].isdigit() else 0)

        if initial_load:
            self._initial_load_done[channel_id] = True

        if channel_id not in self._known_message_ids:
            self._known_message_ids[channel_id] = set()
        for msg in new_msgs:
            self._known_message_ids[channel_id].add(msg["id"])

        logger.info(f"Channel {channel_id}: {len(new_msgs)} new messages (last_id={last_id})")
        return new_msgs

    # ------------------------------------------------------------------
    # Download (uses self.context – available after browser launch)
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
    # Helper: normalize URL (unchanged)
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
    # Process message (unchanged)
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
    # Public methods: start, poll_channels, stop
    # ------------------------------------------------------------------
    async def start(self):
        """Initialize scraper – does NOT launch browser."""
        self._running = True
        logger.info("Discord scraper initialized (browser will launch on first poll)")

    async def poll_channels(self):
        """Main polling loop – acquires lock, launches browser, processes, then closes browser."""
        if not self._running:
            raise RuntimeError("Scraper not started – call start() first")

        logger.info(f"[POLL] Starting poll loop for {len(self.channels)} channels")
        poll_count = 0

        while self._running:
            # Acquire lock – only one scraper at a time
            async with self.run_lock:
                poll_count += 1
                logger.info(f"=== Discord Poll cycle #{poll_count} ===")

                try:
                    # Ensure browser is launched and logged in
                    await self._ensure_browser_and_login()

                    # Process each channel
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

                            # Scroll to bottom
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
                    # Close browser to free memory – critical!
                    await self._close_browser()

            # Sleep outside the lock so other scrapers can run
            await asyncio.sleep(random.uniform(60, 120))

    async def stop(self):
        logger.info("[STOP] Stopping scraper …")
        self._running = False
        await self._close_browser()
        logger.info("[OK] Scraper stopped")