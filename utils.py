from __future__ import annotations

import hashlib
import os
import re
from pathlib import Path
from typing import Any
from urllib.parse import urlparse


def sanitize_filename(name: str) -> str:
    name = re.sub(r"[^A-Za-z0-9._-]+", "_", name).strip("._")
    return name[:160] or "file"


def message_text(message: Any) -> str:
    for attr in ("message", "text", "content", "caption"):
        value = getattr(message, attr, None)
        if value:
            return str(value)
    return ""


def get_file_size(message: Any) -> int:
    if hasattr(message, "attachments") and getattr(message, "attachments"):
        total = 0
        for a in message.attachments:
            if isinstance(a, dict):
                total += int(a.get("size", 0) or 0)
            elif isinstance(a, str):
                # No size info for string URLs – assume 0
                continue
            else:
                total += int(getattr(a, "size", 0) or 0)
        return total
    media = getattr(message, "media", None)
    doc = getattr(media, "document", None)
    if doc is not None:
        return int(getattr(doc, "size", 0) or 0)
    if getattr(message, "document", None):
        return int(getattr(message.document, "size", 0) or 0)
    return 0


def get_media_type(message: Any) -> str:
    if hasattr(message, "attachments") and getattr(message, "attachments"):
        first = message.attachments[0]
        if isinstance(first, dict):
            ct = first.get("content_type", "").lower()
            fn = first.get("filename", "").lower()
        elif isinstance(first, str):
            # string URL – guess from extension
            parsed = urlparse(first)
            fn = Path(parsed.path).name.lower()
            ct = ""
        else:
            ct = (getattr(first, "content_type", "") or "").lower()
            fn = (getattr(first, "filename", "") or "").lower()
        if ct.startswith("image/") or fn.endswith((".jpg", ".jpeg", ".png", ".webp", ".gif")):
            return "photo"
        if ct.startswith("video/") or fn.endswith((".mp4", ".mov", ".mkv", ".webm", ".avi")):
            return "video"
        if ct.startswith("audio/") or fn.endswith((".mp3", ".wav", ".ogg", ".flac")):
            return "audio"
        return "document"

    if getattr(message, "photo", None):
        return "photo"
    if getattr(message, "video", None):
        return "video"
    if getattr(message, "audio", None) or getattr(message, "voice", None):
        return "audio"
    if getattr(message, "document", None):
        mime = (getattr(message.document, "mime_type", "") or "").lower()
        if mime.startswith("image/"):
            return "photo"
        if mime.startswith("video/"):
            return "video"
        if mime.startswith("audio/"):
            return "audio"
        return "document"
    if getattr(message, "media", None):
        return "media"
    return "text"


def content_hash_for_message(message: Any) -> tuple[str, int]:
    text = message_text(message)
    size = get_file_size(message)

    if hasattr(message, "attachments") and getattr(message, "attachments"):
        parts = []
        for a in message.attachments:
            if isinstance(a, dict):
                # Old format (discord.py bot) or custom dict
                parts.append(f"{a.get('filename','')}:{a.get('size',0)}:{a.get('url','')}")
            elif isinstance(a, str):
                # New format – just a URL string from the scraper
                parsed = urlparse(a)
                filename = Path(parsed.path).name or "file"
                # Use the full URL as the unique identifier
                parts.append(f"{filename}:0:{a}")
            else:
                # Fallback for unknown types
                parts.append(f"{getattr(a, 'filename', '')}:{getattr(a, 'size', 0)}:{getattr(a, 'url', '')}")
        raw = "discord|" + "|".join(parts) + "|" + text
    elif getattr(message, "document", None):
        doc = message.document
        raw = f"tgdoc|{getattr(doc, 'id', '')}|{getattr(doc, 'access_hash', '')}|{size}|{text}"
    elif getattr(message, "photo", None):
        photo = message.photo
        raw = f"tgphoto|{getattr(photo, 'id', '')}|{getattr(photo, 'access_hash', '')}|{text}"
    else:
        raw = "text|" + text
    return hashlib.sha256(raw.encode("utf-8", errors="ignore")).hexdigest(), size


def ensure_within_tmp(tmp_dir: Path, path: str | Path) -> Path:
    p = Path(path).resolve()
    tmp = tmp_dir.resolve()
    if not str(p).startswith(str(tmp)):
        raise RuntimeError(f"Refusing to handle file outside tmp dir: {p}")
    return p


def unlink_quiet(path: str | Path | None) -> None:
    if not path:
        return
    try:
        Path(path).unlink(missing_ok=True)
    except Exception:
        pass