import asyncio
import os
import sys
import logging
from pathlib import Path
import aiohttp
from dotenv import load_dotenv
from aiohttp import web

from discord_scraper import DiscordScraper
from models import SourceInfo

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

load_dotenv()

# --- Environment variables ---
RENDER_URL = os.environ.get("RENDER_BACKEND_URL")
TOKEN = os.environ.get("WEB_UI_TOKEN")
DISCORD_EMAIL = os.environ.get("DISCORD_EMAIL")
DISCORD_PASSWORD = os.environ.get("DISCORD_PASSWORD")

if not RENDER_URL or not TOKEN or not DISCORD_EMAIL:
    logger.error("RENDER_BACKEND_URL, WEB_UI_TOKEN, DISCORD_EMAIL are required")
    sys.exit(1)

# Ensure data directory exists
DATA_DIR = Path("/tmp/discord_data")
DATA_DIR.mkdir(parents=True, exist_ok=True)

# --- Fetch Discord sources from main backend with retries ---
async def fetch_discord_sources(retries=5, delay=5):
    url = f"{RENDER_URL}/api/sources"
    headers = {"X-Forwarder-Token": TOKEN}
    for attempt in range(1, retries + 1):
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(url, headers=headers, timeout=10) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        sources = data.get("sources", [])
                        discord_sources = [s for s in sources if s["platform"] == "discord" and s["enabled"]]
                        channel_ids = []
                        channel_guilds = {}
                        for s in discord_sources:
                            channel_id = s["channel_id"]
                            guild_id = s.get("filters", {}).get("guild_id")
                            if guild_id:
                                channel_guilds[channel_id] = guild_id
                            channel_ids.append(channel_id)
                        logger.info(f"Fetched {len(channel_ids)} Discord sources (guilds for {len(channel_guilds)})")
                        return channel_ids, channel_guilds
                    elif resp.status in (429, 502, 503):
                        logger.warning(f"Received HTTP {resp.status}, retrying in {delay}s...")
                        await asyncio.sleep(delay * attempt)
                    else:
                        logger.error(f"Failed to fetch sources: {resp.status}")
                        return [], {}
        except Exception as e:
            logger.error(f"Error fetching sources (attempt {attempt}): {e}")
            await asyncio.sleep(delay * attempt)
    logger.error("Max retries exceeded for fetching sources")
    return [], {}

# --- Forwarding function ---
async def forward_to_backend(channel_id, message_id, attachments, timestamp):
    url = f"{RENDER_URL}/api/forward_discord_message"
    headers = {"X-Forwarder-Token": TOKEN}
    payload = {
        "channel_id": channel_id,
        "message_id": str(message_id),
        "attachments": attachments,
        "timestamp": timestamp
    }
    async with aiohttp.ClientSession() as session:
        try:
            async with session.post(url, json=payload, headers=headers) as resp:
                if resp.status == 200:
                    return True
                else:
                    text = await resp.text()
                    logger.error(f"Backend returned {resp.status}: {text}")
                    return False
        except Exception as e:
            logger.error(f"Failed to forward: {e}")
            return False

# --- Callback for scraper ---
async def on_scraped_message(msg, source_info):
    logger.info(f"Scraped message {msg.id} from {source_info.channel_id}")
    return await forward_to_backend(
        source_info.channel_id,
        msg.id,
        msg.attachments,
        getattr(msg, "timestamp", None)
    )

# --- Dummy transformer ---
class DummyTransformer:
    async def transform_image(self, path):
        return path
    async def transform_video(self, path):
        return {"video": path, "thumbnail": None}

# --- Health check endpoint ---
async def health_check(request):
    return web.Response(text="OK")

async def start_http_server():
    app = web.Application()
    app.router.add_get('/health', health_check)
    port = int(os.environ.get('PORT', 8080))
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, '0.0.0.0', port)
    await site.start()
    logger.info(f"Health check server running on port {port}")

# --- Main loop with dynamic refresh ---
async def main():
    # Initial fetch
    channels, channel_guilds = await fetch_discord_sources()
    if not channels:
        logger.warning("No Discord sources found. Will retry every 60 seconds.")

    # Create scraper
    scraper = DiscordScraper(
        email=DISCORD_EMAIL,
        password=DISCORD_PASSWORD,
        channels=channels,
        transformer=DummyTransformer(),
        on_message_callback=on_scraped_message,
        data_dir=DATA_DIR,
        headless=True,
        store=None,
        run_lock=None,
        channel_guilds=channel_guilds,          # pass guild mapping
    )

    await scraper.start()

    # Start health check HTTP server (keeps Render alive)
    await start_http_server()

    poll_task = asyncio.create_task(scraper.poll_channels())

    # Background task: refresh sources every 60 seconds
    async def refresh_loop():
        nonlocal channels, channel_guilds, scraper, poll_task
        while True:
            await asyncio.sleep(60)
            new_channels, new_guilds = await fetch_discord_sources()
            if new_channels is not None and (
                set(new_channels) != set(channels) or
                new_guilds != channel_guilds
            ):
                logger.info(f"Channel list or guild mapping changed. Channels: {new_channels}")
                poll_task.cancel()
                try:
                    await poll_task
                except asyncio.CancelledError:
                    pass
                scraper.channels = new_channels
                scraper._channel_guilds = new_guilds
                scraper._known_message_ids.clear()
                scraper._initial_load_done.clear()
                channels = new_channels
                channel_guilds = new_guilds
                poll_task = asyncio.create_task(scraper.poll_channels())

    refresh_task = asyncio.create_task(refresh_loop())

    # Keep running until cancelled
    try:
        await poll_task
    except asyncio.CancelledError:
        pass

if __name__ == "__main__":
    asyncio.run(main())