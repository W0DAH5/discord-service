from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime
from typing import Any


@dataclass
class SourceChannel:
    id: int
    platform: str
    channel_id: str
    enabled: bool = True
    forwarding_method: str = "auto"   # NEW: 'auto', 'api', or 'scrape'
    filters: dict[str, Any] = field(default_factory=dict)
    start_date: str | None = None
    created_at: str | None = None
    scrape_required: bool = False
    last_scraped_id: str | None = None


@dataclass
class ContentFilter:
    allowed_media_types: list[str] | None = None
    max_file_size_mb: int | None = None
    min_file_size_mb: int | None = None
    keyword_blacklist: list[str] | None = None
    keyword_whitelist: list[str] | None = None
    regex_pattern: str | None = None
    check_duplicates: bool = True
    duplicate_window_hours: int = 24


@dataclass
class SourceInfo:
    platform: str
    channel_id: str
    channel_name: str
    author: str = "Unknown"
    guild_id: str | None = None


@dataclass
class QueueItem:
    id: int
    platform: str
    channel_id: str
    message_id: str
    attempts: int
    status: str
    error: str | None
    created_at: str
    updated_at: str


def utcnow_iso() -> str:
    return datetime.utcnow().replace(microsecond=0).isoformat() + "Z"