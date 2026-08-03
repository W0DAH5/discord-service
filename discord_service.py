import asyncio
import os
import sys
import logging
from pathlib import Path
import aiohttp
from dotenv import load_dotenv

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

# --- Fetch Discord sources from main backend ---
async def fetch_discord_sources():
    url = f"{RENDER_URL}/api/sources"
    headers = {"X-Forwarder-Token": TOKEN}
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, headers=headers) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    sources = data.get("sources", [])
                    discord_sources = [s for s in sources if s["platform"] == "discord" and s["enabled"]]
                    channel_ids = [s["channel_id"] for s in discord_sources]
                    logger.info(f"Fetched {len(channel_ids)} Discord sources")
                    return channel_ids
                else:
                    logger.error(f"Failed to fetch sources: {resp.status}")
                    return []
    except Exception as e:
        logger.error(f"Error fetching sources: {e}")
        return []

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

# --- Main loop with dynamic refresh ---
async def main():
    # Initial fetch
    channels = await fetch_discord_sources()
    if not channels:
        logger.warning("No Discord sources found. Will retry every 60 seconds.")

    # Create scraper
    scraper = DiscordScraper(
        email=DISCORD_EMAIL,
        password=DISCORD_PASSWORD,
        channels=channels,
        transformer=DummyTransformer(),
        on_message_callback=on_scraped_message,
        data_dir=Path("/tmp/discord_data"),
        headless=True,
        store=None,
        run_lock=None
    )

    await scraper.start()
    poll_task = asyncio.create_task(scraper.poll_channels())

    # Background task: refresh sources every 60 seconds
    async def refresh_loop():
        nonlocal channels, scraper, poll_task
        while True:
            await asyncio.sleep(60)
            new_channels = await fetch_discord_sources()
            if set(new_channels) != set(channels):
                logger.info(f"Channel list changed: {new_channels}")
                # Stop current poll loop
                poll_task.cancel()
                try:
                    await poll_task
                except asyncio.CancelledError:
                    pass
                # Update scraper's channels
                scraper.channels = new_channels
                scraper._known_message_ids.clear()
                scraper._initial_load_done.clear()
                # Restart poll
                channels = new_channels
                poll_task = asyncio.create_task(scraper.poll_channels())

    refresh_task = asyncio.create_task(refresh_loop())

    # Wait for poll task (will run until cancelled)
    try:
        await poll_task
    except asyncio.CancelledError:
        pass

if __name__ == "__main__":
    asyncio.run(main())