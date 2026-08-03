import asyncio
import os
import sys
import logging
from pathlib import Path
import aiohttp
from dotenv import load_dotenv

# The following imports expect that discord_scraper.py and models.py are in the same directory
from discord_scraper import DiscordScraper
from models import SourceInfo

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

load_dotenv()  # optional, if you want to test locally with .env

# --- Environment variables ---
RENDER_URL = os.environ.get("RENDER_BACKEND_URL")
TOKEN = os.environ.get("WEB_UI_TOKEN")
DISCORD_EMAIL = os.environ.get("DISCORD_EMAIL")
DISCORD_PASSWORD = os.environ.get("DISCORD_PASSWORD")
DISCORD_CHANNELS = os.environ.get("DISCORD_CHANNELS", "")
DISCORD_CHANNELS = [c.strip() for c in DISCORD_CHANNELS.split(",") if c.strip()]

if not RENDER_URL or not TOKEN or not DISCORD_EMAIL or not DISCORD_CHANNELS:
    logger.error("Missing required environment variables")
    logger.error("RENDER_BACKEND_URL, WEB_UI_TOKEN, DISCORD_EMAIL, DISCORD_CHANNELS are required")
    sys.exit(1)

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

# --- Callback for the scraper ---
async def on_scraped_message(msg, source_info):
    logger.info(f"Scraped message {msg.id} from {source_info.channel_id}")
    success = await forward_to_backend(
        source_info.channel_id,
        msg.id,
        msg.attachments,
        getattr(msg, "timestamp", None)
    )
    return success

# --- Dummy transformer (no media processing needed) ---
class DummyTransformer:
    async def transform_image(self, path):
        return path
    async def transform_video(self, path):
        return {"video": path, "thumbnail": None}

# --- Main ---
async def main():
    scraper = DiscordScraper(
        email=DISCORD_EMAIL,
        password=DISCORD_PASSWORD,
        channels=DISCORD_CHANNELS,
        transformer=DummyTransformer(),
        on_message_callback=on_scraped_message,
        data_dir=Path("/tmp/discord_data"),
        headless=True,   # headless mode to save memory
        store=None,
        run_lock=None
    )

    await scraper.start()
    await scraper.poll_channels()

if __name__ == "__main__":
    asyncio.run(main())