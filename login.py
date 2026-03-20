import os
import re
import calendar
import time
import random

import asyncio
from datetime import datetime, timezone, timedelta
from typing import Dict, List, Tuple, Set, Any, Optional
from dotenv import load_dotenv
from supabase import create_client, Client
from telethon import TelegramClient, events, errors, Button
from telethon import types as tl_types  # for User/Chat/Channel/UpdateBotChatInviteRequester, InputUserEmpty
from telethon.tl.types import (
    UpdateChannelParticipant,
    ChannelParticipantBanned,
    ChannelParticipantLeft,
)
from telethon.tl import functions, types
from telethon.utils import get_peer_id
import logging
from error_handler import safe_event_handler, log_info, log_error, log_warning
import matplotlib.pyplot as plt
import matplotlib
matplotlib.use('Agg')  # use non-interactive backend
from openpyxl import Workbook
# ---------------- ENV & GLOBALS ----------------

load_dotenv()

API_ID = int(os.getenv("API_ID", "0"))
API_HASH = os.getenv("API_HASH", "")
BOT_TOKEN = os.getenv("BOT_TOKEN", "")

SUPABASE_URL = os.getenv("SUPABASE_URL", "")
# allow either SUPABASE_KEY or SUPABASE_SERVICE_ROLE_KEY
SUPABASE_KEY = os.getenv("SUPABASE_SERVICE_ROLE_KEY", "")

SESSION_DIR = os.getenv("SESSION_DIR", "sessions")
TOP_N = 14  # how many pinned chats to show in selection



assert API_ID and API_HASH and BOT_TOKEN, "Set API_ID, API_HASH, BOT_TOKEN in .env"
assert SUPABASE_URL and SUPABASE_KEY, "Set SUPABASE_URL and SUPABASE_KEY / SUPABASE_SERVICE_ROLE_KEY in .env"

os.makedirs(SESSION_DIR, exist_ok=True)

supabase: Client = create_client(SUPABASE_URL, SUPABASE_KEY)


# ---------------- SUPABASE + SUBSCRIPTION HELPERS ----------------

# Create the bot client but don't start it yet (lazy start inside async loop)
bot = TelegramClient("join_counter_bot", API_ID, API_HASH)

# ---- in-memory state ----
login_state: Dict[int, Dict[str, Any]] = {}
select_state: Dict[int, Dict[str, Any]] = {}   # selection flows (create/remove links/confirm)
# create link preference (approve vs normal)
create_link_pref: Dict[int, str] = {}  # uid -> "approval" | "normal"
USER_CLIENT_CACHE: Dict[int, TelegramClient] = {}
ACTIVE_LISTENERS: Set[int] = set()            # uids with active ChatAction listeners
stats_state: Dict[int, Dict[str, Any]] = {}    # stats link selection context
date_select_state: Dict[int, Dict[str, Any]] = {}  # uid -> {step, link_id, month, year, start_date, end_date, ...}

# ---------- Invite-link cache (avoid DB hit on every event) ----------
# Tuple: (rows, monotonic_timestamp)
_invite_link_cache: Dict[int, Tuple[List[dict], float]] = {}
CACHE_TTL: float = 60.0  # seconds

# ---------- Async sync queue (deferred importer sync) ----------
_sync_queue: asyncio.Queue = asyncio.Queue()
_pending_syncs: Set[Tuple[int, int]] = set()  # (uid, chat_id) dedup
_sync_worker_started: bool = False

# per-message stats pagination state
stats_pages: Dict[Tuple[int, int], Dict[str, Any]] = {}

PHONE_RE = re.compile(r"^\+\d{6,15}$", re.IGNORECASE)
OTP_RE = re.compile(r"^(?:HELLO\s*)?(\d{4,8})$", re.IGNORECASE)


# ---------------- TELEGRAM HELPERS ----------------

def session_path(uid: int, phone: str) -> str:
    digits = "".join([c for c in phone if c.isdigit()])
    return os.path.join(SESSION_DIR, f"{uid}_{digits}.session")


async def safe_connect(client: TelegramClient, retries: int = 3, delay: int = 2):
    """Safer connect with retries."""
    try:
        if client.is_connected():
            return
    except Exception:
        pass
    last_exc = None
    for attempt in range(1, retries + 1):
        try:
            await client.connect()
            if client.is_connected():
                return
        except Exception as exc:
            last_exc = exc
            if attempt < retries:
                await asyncio.sleep(delay * attempt)
    if isinstance(last_exc, BaseException):
        raise last_exc
    raise RuntimeError("safe_connect: failed to connect")


def title_of(ent) -> str:
    if getattr(ent, "title", None):
        return ent.title
    fn = getattr(ent, "first_name", "") or ""
    ln = getattr(ent, "last_name", "") or ""
    if fn or ln:
        return (fn + " " + ln).strip()
    if getattr(ent, "username", None):
        return "@" + ent.username
    return f"id:{getattr(ent, 'id', '')}"


async def top_dialog_pairs(client: TelegramClient, limit: int = TOP_N) -> List[Tuple[int, str]]:
    """
    Return only PRIVATE groups/channels (no 1-1 chats),
    AND only those where the logged-in user is admin/creator.
    Private ka matlab:
      - Normal groups (types.Chat) hamesha private
      - Channels jinka username None ho (no @publicname)
    """
    dialogs = await client.get_dialogs(limit=200)
    pairs: List[Tuple[int, str]] = []

    for d in dialogs:
        # 1-1 user chats skip
        if d.is_user:
            continue

        ent = d.entity

        # Sirf groups / channels hi allow
        if not isinstance(ent, (types.Channel, types.Chat)):
            continue

        # -------- PRIVATE FILTER --------
        # Channel / supergroup agar public @username hai toh skip
        if isinstance(ent, types.Channel):
            # Agar username hai -> public channel/supergroup
            if getattr(ent, "username", None):
                continue
        # types.Chat normal group hai – ye waise hi private hota hai, so ok

        # -------- ADMIN CHECK --------
        is_admin = False

        # creator ho ya admin_rights ho
        if getattr(ent, "creator", False):
            is_admin = True

        rights = getattr(ent, "admin_rights", None)
        if rights:
            is_admin = True

        if not is_admin:
            continue

        # Yaha tak aaya matlab:
        # - private group/channel
        # - jisme user admin/creator hai
        pairs.append((int(get_peer_id(ent)), title_of(ent)))

        if len(pairs) >= limit:
            break

    return pairs


def numbered_list_from_pairs(pairs: List[Tuple[int, str]]) -> str:
    return "\n".join([f"{i + 1}. {pairs[i][1]}" for i in range(len(pairs))])


def multi_kb(n: int, selected: Set[int]) -> List[List[Button]]:
    """Generic multi-select keyboard."""
    rows, row = [], []
    for i in range(1, n + 1):
        label = f"{'✅ ' if (i - 1) in selected else ''}{i}"
        row.append(Button.inline(label, data=f"msel:{i}".encode()))
        if len(row) == 7:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([Button.inline("✅ Done", data=b"msel_done"),
                 Button.inline("✖ Cancel", data=b"msel_cancel")])
    return rows


# ---------------- SUPABASE + SUBSCRIPTION HELPERS ----------------









def sp_get_session(uid: int) -> Optional[dict]:
    try:
        res = supabase.table("user_sessions").select("*").eq("user_id", uid).limit(1).execute()
        return res.data[0] if res.data else None
    except Exception as e:
        log_error(f"sp_get_session error for uid {uid}: {e}")
        return None


def sp_upsert_session(uid: int, phone: str, session_file: str):
    payload = {
        "user_id": uid,
        "phone": phone,
        "session_file": session_file,
        "is_active": True,
        "created_at": datetime.now(timezone.utc).isoformat(),
    }
    max_retries = 3
    for attempt in range(max_retries):
        try:
            supabase.table("user_sessions").upsert(payload, on_conflict="user_id").execute()
            return
        except Exception as e:
            if attempt < max_retries - 1:
                log_warning(f"sp_upsert_session retry {attempt + 1}/{max_retries}: {e}")
                continue
            log_error(f"sp_upsert_session failed after {max_retries} attempts: {e}")
            # Fallback: try update/insert separately
            try:
                existing = supabase.table("user_sessions").select("user_id").eq("user_id", uid).limit(1).execute()
                if existing and existing.data:
                    supabase.table("user_sessions").update(payload).eq("user_id", uid).execute()
                else:
                    supabase.table("user_sessions").insert(payload).execute()
            except Exception as fallback_error:
                log_error(f"sp_upsert_session fallback also failed: {fallback_error}")


def sp_delete_session(uid: int):
    try:
        supabase.table("user_sessions").delete().eq("user_id", uid).execute()
    except Exception as e:
        log_error(f"sp_delete_session error for uid {uid}: {e}")


def sp_save_invite_link(
    uid: int,
    chat_id: int,
    chat_title: str,
    link: str,
    link_type: str,   # 👈 NEW
):
    supabase.table("invite_links").upsert(
        {
            "user_id": uid,
            "chat_id": chat_id,
            "chat_title": chat_title,
            "invite_link": link,
            "link_type": link_type,   # ✅ SAVE TYPE
            "is_active": True,
            "created_at": datetime.now(timezone.utc).isoformat(),
        },
        on_conflict="user_id,chat_id,invite_link",
    ).execute()
    # Invalidate cache so next lookup fetches fresh data
    invalidate_invite_link_cache(uid)


def sp_list_invite_links(uid: int) -> List[dict]:
    res = (
        supabase.table("invite_links")
        .select("*")
        .eq("user_id", uid)
        .eq("is_active", True)
        .order("created_at", desc=True)
        .execute()
    )
    return res.data or []


def sp_soft_delete_links(uid: int, link_ids: List[int]):
    """
    Remove selected invite_links and all their join rows from the DB.
    """
    if not link_ids:
        return

    # 1) delete join rows
    supabase.table("joins") \
        .delete() \
        .eq("user_id", uid) \
        .in_("invite_link_id", link_ids) \
        .execute()

    # 2) delete invite_links rows
    supabase.table("invite_links") \
        .delete() \
        .eq("user_id", uid) \
        .in_("id", link_ids) \
        .execute()

    # Invalidate cache so removed links are no longer served
    invalidate_invite_link_cache(uid)


# ---------------------------------------------------------------------------
# INVITE LINK CACHE  — avoid DB hit on every real-time event
# ---------------------------------------------------------------------------

def invalidate_invite_link_cache(uid: int) -> None:
    """Drop the cached invite links for a user (call after create/remove)."""
    _invite_link_cache.pop(uid, None)


def get_cached_invite_links(uid: int) -> List[dict]:
    """
    Return the invite links for uid from cache (TTL = CACHE_TTL seconds).
    Falls back to Supabase on cache miss or expiry.
    """
    entry = _invite_link_cache.get(uid)
    if entry is not None:
        rows, ts = entry
        if time.monotonic() - ts < CACHE_TTL:
            return rows
    rows = sp_list_invite_links(uid)
    _invite_link_cache[uid] = (rows, time.monotonic())
    return rows


# ---------------------------------------------------------------------------
# REAL-TIME IMMEDIATE JOIN INSERT
# ---------------------------------------------------------------------------

def sp_realtime_join_insert(
    uid: int,
    chat_id: int,
    joined_user_id: int,
    invite_link_id: Optional[int] = None,
    joined_source: str = "realtime",
) -> None:
    """
    Insert/upsert a join row immediately on a real-time event.

    - invite_link_id may be NULL if we cannot determine the exact link yet;
      the background sync queue will later fill in the correct value.
    - Uses UNIQUE(user_id, chat_id, joined_user_id) conflict target so that
      if the row already exists (e.g. from a previous sync) we only update
      join metadata — we deliberately do NOT overwrite left_at.
    - joined_source is stored for debugging ("realtime" or "sync").
    """
    now_iso = datetime.now(timezone.utc).isoformat()
    payload = {
        "user_id": uid,
        "chat_id": chat_id,
        "joined_user_id": joined_user_id,
        "joined_at": now_iso,
        "left_at": None,
        "left_reason": None,
        "left_seen_at": None,
        "joined_source": joined_source,
    }
    if invite_link_id is not None:
        payload["invite_link_id"] = invite_link_id

    try:
        supabase.table("joins").upsert(
            payload,
            on_conflict="user_id,chat_id,joined_user_id",
        ).execute()
    except Exception as ex:
        log_error(f"sp_realtime_join_insert error uid={uid} joined_user={joined_user_id}: {ex}")


# ---------------------------------------------------------------------------
# ASYNC SYNC QUEUE WORKER
# ---------------------------------------------------------------------------

async def _sync_worker() -> None:
    """
    Background coroutine that drains the sync queue.

    Each item in the queue is (uid, chat_id).  Duplicate (uid, chat_id)
    pairs that arrive while one is already processing are discarded to
    avoid redundant Telegram API calls.
    A small random sleep (0.3 – 0.5 s) between API calls enforces the
    rate-limit budget.
    """
    while True:
        uid, chat_id = await _sync_queue.get()
        key = (uid, chat_id)
        try:
            links = get_cached_invite_links(uid)
            chat_links = [r for r in links if int(r.get("chat_id", 0)) == chat_id]
            for link_row in chat_links:
                try:
                    await sync_importers_to_db(uid, only_link_id=int(link_row["id"]))
                except Exception as ex:
                    log_error(f"_sync_worker sync error uid={uid} link={link_row['id']}: {ex}")
                await asyncio.sleep(random.uniform(0.3, 0.5))
        except Exception as ex:
            log_error(f"_sync_worker outer error uid={uid} chat={chat_id}: {ex}")
        finally:
            _pending_syncs.discard(key)
            _sync_queue.task_done()


def enqueue_sync(uid: int, chat_id: int) -> None:
    """Enqueue a deferred importer sync for (uid, chat_id) if not already pending."""
    key = (uid, chat_id)
    if key not in _pending_syncs:
        _pending_syncs.add(key)
        try:
            _sync_queue.put_nowait((uid, chat_id))
        except asyncio.QueueFull:
            _pending_syncs.discard(key)
            log_warning(f"enqueue_sync: queue full, dropping uid={uid} chat={chat_id}")



def sp_replace_joins_for_link(uid: int, invite_link_id: int, rows: List[dict]):
    """
    Upsert join rows WITHOUT usernames.
    Important:
      - Unique user per link (won't double count)
      - If user re-joins, we CLEAR left_at so "current joined" becomes correct.
    """
    if not rows:
        return

    clean_rows = []
    for r in rows:
        clean_rows.append({
            "user_id": r["user_id"],
            "chat_id": r["chat_id"],
            "invite_link_id": r["invite_link_id"],
            "joined_user_id": r["joined_user_id"],
            "joined_at": r.get("joined_at"),

            # ✅ Rejoin fix: mark as currently active by clearing left fields
            "left_at": None,
            "left_reason": None,
            "left_seen_at": None,
        })

    supabase.table("joins").upsert(
        clean_rows,
        on_conflict="user_id,chat_id,invite_link_id,joined_user_id"
    ).execute()


def _count_from_response(res) -> int:
    try:
        if hasattr(res, "count") and res.count is not None:
            return int(res.count)
    except Exception:
        pass
    try:
        return len(res.data or [])
    except Exception:
        return 0


def sp_count_joins_for_link(
    uid: int,
    invite_link_id: int,
    since: Optional[datetime] = None,
    until: Optional[datetime] = None,
) -> int:
    """Count joins for a specific invite_link."""
    q = (
        supabase.table("joins")
        .select("id", count="exact")
        .eq("user_id", uid)
        .eq("invite_link_id", invite_link_id)
    )
    if since:
        q = q.gte("joined_at", since.isoformat())
    if until:
        q = q.lte("joined_at", until.isoformat())
    res = q.execute()
    return _count_from_response(res)


def sp_count_left_for_link(
    uid: int,
    invite_link_id: int,
    since: Optional[datetime] = None,
    until: Optional[datetime] = None,
) -> int:
    q = (
        supabase.table("joins")
        .select("id", count="exact")
        .eq("user_id", uid)
        .eq("invite_link_id", invite_link_id)
        .not_.is_("left_at", "null")
    )
    if since:
        q = q.gte("joined_at", since.isoformat())
    if until:
        q = q.lte("joined_at", until.isoformat())
    res = q.execute()
    return _count_from_response(res)


def sp_fetch_joins_for_link(
    uid: int,
    invite_link_id: int,
    since: Optional[datetime] = None,
    until: Optional[datetime] = None,
    offset: int = 0,
    limit: int = 20,
) -> List[dict]:
    """
    Fetch a page of join rows for one invite_link, newest first.
    """
    q = (
        supabase.table("joins")
        .select("*")
        .eq("user_id", uid)
        .eq("invite_link_id", invite_link_id)
    )
    if since:
        q = q.gte("joined_at", since.isoformat())
    if until:
        q = q.lte("joined_at", until.isoformat())

    # newest first
    q = q.order("joined_at", desc=True).range(offset, offset + limit - 1)

    res = q.execute()
    return res.data or []


def _safe_ascii(s: str) -> str:
    s = (s or "").strip()
    s = re.sub(r"[^\x20-\x7E]+", " ", s)  # remove emojis/unicode
    s = re.sub(r"\s+", " ", s).strip()
    return s[:200]


# ---------------- STATS PAGE RENDER HELPER ----------------

# ---------------- STATS PAGE RENDER HELPER ----------------

from telethon.errors import UserNotParticipantError
from telethon.errors.rpcerrorlist import ChatAdminRequiredError


async def render_stats_page(event, uid: int, ctx: Dict[str, Any]):
    """
    FAST summary stats only:
    - Total joins (unique users ever joined via link)
    - Total left
    - Current joined = joins - left
    - No user IDs, no join list
    """
    link_id = ctx["link_id"]
    label = ctx["label"]
    since = ctx["since"]
    until = ctx["until"]
    total = ctx["total"]
    title = ctx["title"]
    link = ctx["link"]
    created_at = ctx.get("created_at")

    IST = timezone(timedelta(hours=5, minutes=30))

    # left count (same filter range)
    left_q = (
        supabase.table("joins")
        .select("id", count="exact")
        .eq("user_id", uid)
        .eq("invite_link_id", link_id)
        .not_.is_("left_at", "null")
    )
    if since:
        left_q = left_q.gte("joined_at", since.isoformat())
    if until:
        left_q = left_q.lte("joined_at", until.isoformat())
    left_count = _count_from_response(left_q.execute())

    active_count = total - left_count

    lines: List[str] = []
    lines.append(f"📊 **{label} stats**")
    lines.append(f"`{title}`")
    lines.append("")
    lines.append(f"🔗 `{link}`")

    lt = (ctx.get("link_type") or "normal").lower()
    lines.append("🛂 _required approval_" if lt == "approval" else "🔓 _normal link_")

    if created_at:
        try:
            clean = str(created_at).replace("Z", "")
            dt = datetime.fromisoformat(clean)
            dt_ist = dt.astimezone(IST)
            created_str = dt_ist.strftime("%d %b %Y, %H:%M IST")
        except Exception:
            created_str = str(created_at)
        lines.append(f"📅 Link created: `{created_str}`")

    lines.append("")
    lines.append(f"👥 Total joins: `{total}`")
    lines.append(f"🚪 Total left: `{left_count}`")
    lines.append(f"🟢 Current joined: `{active_count}`")

    buttons = [[Button.inline("✖ Close", data=b"stats_page:close")]]
    await event.edit("\n".join(lines), parse_mode="md", buttons=buttons)


# ---------------- USER CLIENT HANDLING ----------------

async def get_user_client(uid: int) -> TelegramClient:
    """Return cached TelegramClient for this user (login session)."""
    client = USER_CLIENT_CACHE.get(uid)
    if client:
        try:
            if client.is_connected():
                return client
        except Exception:
            pass

    sess = sp_get_session(uid)
    if not sess:
        raise RuntimeError("No saved session. Use /login first.")

    local = os.path.join(SESSION_DIR, sess["session_file"])
    client = TelegramClient(local, API_ID, API_HASH)
    await safe_connect(client)

    if not await client.is_user_authorized():
        await client.disconnect()
        # Mark as inactive to avoid redundant connection attempts
        sp_delete_session(uid)
        raise RuntimeError("Session exists but not authorized. /login again.")

    USER_CLIENT_CACHE[uid] = client
    return client


async def is_logged_in(uid: int) -> bool:
    try:
        _ = await get_user_client(uid)
        return True
    except Exception:
        return False


# ---------------- COMMANDS TEXT ----------------
def commands_text() -> str:
    lines = [
        "👋 Welcome to Join Counter Bot!",
        "",
        "ℹ️ This bot helps you **track how many users joined** via your private invite links.",
        "",
        "📌 If you log in and create invite links, the bot will:",
        "   • Save your private invite links in the database",
        "   • Track how many users joined via each link",
        "   • When you remove a link, all join data for that link will also be removed",
        "",
        "📖 Commands:",
        "",
        "▶️ /start — Show this help & all commands",
        "ℹ️ /help — Short usage guide",
        "🧷 /create_link — Create invite links for pinned private groups/channels",
        "📋 /links — List your active tracked invite links",
        "🗑️ /remove_link — Remove invite links (and their join data)",
        "",
        "📊 /select_date — Select date from the calendar",
        "📊 /stats — Select link & view all-time joins",
        "🗓️ /yesterday — Joins yesterday (IST)",
        "⏱️ /hour_status — Joins in last 1 hour",
        "📅 /today_status — Joins today",
        "📆 /week_status — Joins in last 7 days",
        "🗓️ /month_status — Joins in last 30 days",
        "",
        "🔐 /login — Login your Telegram account",
        "🛑 /stoplogin — Cancel login process",
        "✅ /status — Check login status",
        "🚪 /logout — Delete session & stop tracking",
        "",
    
        "",
        "_Flow: /login → /create_link → share invite link → /stats for join tracking._",
    ]
    return "\n".join(lines)


# ---------------- REPORT GENERATION HELPERS ----------------

def generate_today_text_report(data_rows: List[dict]) -> str:
    now_ist = datetime.now(timezone(timedelta(hours=5, minutes=30))).strftime("%d-%m-%Y at %I:%M %p")
    text = f"📌 **Daily Join Report for {now_ist}**\n\n"
    text += "Sl. No. — Link — Joins\n\n"

    for i, row in enumerate(data_rows, start=1):
        title = row["chat_title"]
        count = row["count"]
        text += f"{i}. `{title}` — `{count}`\n"

    if not data_rows:
        text += "_No joins recorded today._"

    return text


def generate_today_excel_report(data_rows: List[dict]) -> str:
    now_str = datetime.now().strftime("%d-%m-%Y")
    file_name = f"Daily_Report_{now_str}.xlsx"

    wb = Workbook()
    ws = wb.active
    ws.title = "Today's Joins"

    ws.append(["Sl No", "Link Title", "Invite Link", "Joins Today"])

    for i, row in enumerate(data_rows, start=1):
        ws.append([i, row["chat_title"], row["invite_link"], row["count"]])

    wb.save(file_name)
    return file_name


def generate_today_graph_report(data_rows: List[dict]) -> str:
    if not data_rows:
        return ""

    titles = [ (row["chat_title"][:10] + "...") if len(row["chat_title"]) > 10 else row["chat_title"] for row in data_rows]
    counts = [row["count"] for row in data_rows]

    # Use a nice color palette
    colors = ['#FF5733','#33C1FF','#28B463','#F39C12','#8E44AD','#1ABC9C']
    bar_colors = [colors[i % len(colors)] for i in range(len(titles))]

    plt.figure(figsize=(10, 6))
    bars = plt.bar(titles, counts, color=bar_colors)

    # Values on top
    for bar in bars:
        height = bar.get_height()
        plt.text(bar.get_x() + bar.get_width()/2., height + 0.1, str(int(height)), ha='center', va='bottom')

    plt.xlabel("Links")
    plt.ylabel("Joins Today")
    plt.title(f"Join Report for {datetime.now().strftime('%d-%m-%Y')}")
    plt.xticks(rotation=45, ha='right')
    plt.tight_layout()

    file_name = "today_graph.png"
    plt.savefig(file_name)
    plt.close()

    return file_name

# 👆 Button import already hoga, agar nahi hai to ye line ensure karo

# ... commands_text() function ke neeche yeh add karo:



# ---------------- /start /help /status /demo ----------------

@bot.on(events.NewMessage(pattern=r"^/start$"))
async def cmd_start(event):
    await event.respond(
        commands_text().replace("{BOT}", "Join Counter Bot"),
        parse_mode="html"
    )



@bot.on(events.NewMessage(pattern=r"^/help$"))
async def help_cmd(e):
    txt = (
        "ℹ️ **How to use this bot (simple flow)**\n\n"
        "1️⃣ Use /login and follow OTP / 2FA steps.\n"
        "2️⃣ In your Telegram app (same account), *pin* the private channel/group\n"
        "   where you want to generate an invite link.\n"
        "3️⃣ Come back here, type /create_link and select the chat using buttons.\n"
        "4️⃣ The invite link you get from the bot is the one you should share.\n"
        "   Everyone who joins using that invite link will be counted by the bot\n"
        "   (per link, not per channel only).\n"
        "5️⃣ Use /stats, /hour_status, /today_status, etc. — first you select which invite link,\n"
        "   then the bot will show join counts for that specific link.\n\n"
        "❗ When you use /remove_link and delete a link, **all join data for that link**\n"
        "   will also be permanently deleted from the database.\n"
    )
    await e.respond(txt, parse_mode="md")



@bot.on(events.NewMessage(pattern=r"^/status$"))
async def status_cmd(e):
    data = sp_get_session(e.sender_id)
    if not data:
        return await e.respond("🔴 Not logged in. Use **/login** first.", parse_mode="md")
    if not await is_logged_in(e.sender_id):
        return await e.respond(
            "🟠 Session found but not authorized locally. Please **/login** again.",
            parse_mode="md",
        )
    await e.respond(
        f"🟢 Logged In\n**Phone:** `{data['phone']}`\n`{data['session_file']}`",
        parse_mode="md",
    )


# ---------------- LOGIN / LOGOUT FLOW ----------------

@bot.on(events.NewMessage(pattern=r"^/login$"))
async def login_cmd(e):
    uid = e.sender_id
    if await is_logged_in(uid):
        return await e.respond(
            "✅ Already logged in.\nNow use /create_link to generate invite links.",
            parse_mode="md",
        )
    login_state[uid] = {"step": "phone", "phone": None}
    await e.respond(
        "📲 Send your phone number in this format:\n\n"
        "`+919876543210`\n\n"
        "You can cancel anytime with /stoplogin .",
        parse_mode="md",
    )


@bot.on(events.NewMessage(pattern=r"^/stoplogin$"))
async def stoplogin_cmd(e):
    uid = e.sender_id
    if uid in login_state:
        login_state.pop(uid, None)
        await e.respond("✖ Login cancelled. You can start again with /login .")
        return
    await e.respond("ℹ️ No login in progress.")


@bot.on(events.NewMessage)
async def login_flow(e):
    """Handles /login steps (phone → OTP → 2FA password)."""
    uid = e.sender_id
    msg = (e.raw_text or "").strip()
    if uid not in login_state:
        return
    st = login_state[uid]

    # STEP: phone number
    if st["step"] == "phone":
        if not PHONE_RE.match(msg):
            return await e.respond(
                "⚠️ Please send a valid number like `+919876543210`.",
                parse_mode="md",
            )
        phone = msg
        local = session_path(uid, phone)
        client = TelegramClient(local, API_ID, API_HASH)
        st["phone"] = phone
        try:
            await client.connect()
            if await client.is_user_authorized():
                me = await client.get_me()
                sp_upsert_session(uid, phone, os.path.basename(local))
                await e.respond(
                    f"✅ Already logged in as **{me.first_name}**.\n"
                    "Use /create_link to generate invite links.",
                    parse_mode="md",
                )
                login_state.pop(uid, None)
                asyncio.ensure_future(_start_listener_after_login(uid))
                return
            res = await client.send_code_request(phone)
            st["phone_code_hash"] = getattr(res, "phone_code_hash", None)
            await e.respond(
                "📩 Send OTP in this format: `123456` or `HELLO123456`.\n\n"
                "You can also tap *Resend OTP* if needed.",
                parse_mode="md",
                buttons=[[Button.inline("🔁 Resend OTP", data=b"resend_otp")]],
            )
            st["step"] = "otp"
        except Exception as ex:
            await e.respond(
                f"❌ OTP send error: `{ex}`\nStart again with /login.",
                parse_mode="md",
            )
        finally:
            try:
                await client.disconnect()
            except Exception:
                pass
        return

    # STEP: OTP
    if st["step"] == "otp":
        m = OTP_RE.match(msg)
        if not m:
            return await e.respond(
                "⚠️ Send OTP in `HELLO123456` format.",
                parse_mode="md",
            )
        otp = m.group(1)
        phone = st.get("phone")
        if not phone:
            login_state.pop(uid, None)
            return await e.respond(
                "⚠️ Phone missing. Start /login again.",
                parse_mode="md",
            )
        code_hash = st.get("phone_code_hash")
        if not code_hash:
            login_state.pop(uid, None)
            return await e.respond(
                "❌ Code session expired. /login again.",
                parse_mode="md",
            )

        local = session_path(uid, phone)
        client = TelegramClient(local, API_ID, API_HASH)
        try:
            await client.connect()
            try:
                await client.sign_in(phone, otp, phone_code_hash=code_hash)
                me = await client.get_me()
                sp_upsert_session(uid, phone, os.path.basename(local))
                await e.respond(
                    f"✅ Logged in as **{me.first_name}**.\n"
                    "Now use /create_link to generate invite links.",
                    parse_mode="md",
                )
                login_state.pop(uid, None)
                asyncio.ensure_future(_start_listener_after_login(uid))
                return
            except errors.SessionPasswordNeededError:
                try:
                    pwd = await client(functions.account.GetPasswordRequest())
                    hint = getattr(pwd, "hint", "") or ""
                except Exception:
                    hint = ""
                st["step"] = "2fa"
                st["twofa_session_path"] = local
                msg_hint = f" (hint: `{hint}`)" if hint else ""
                await e.respond(
                    f"🔐 2FA enabled. Please enter your **Telegram password**{msg_hint}.\n\n"
                    "We do not store your password; it is only used once to finish login.",
                    parse_mode="md",
                )
                return
        except errors.PhoneCodeInvalidError:
            await e.respond("❌ Wrong OTP. /login try again.", parse_mode="md")
        except Exception as ex:
            await e.respond(
                f"❌ Login failed: `{ex}`\nStart again with /login.",
                parse_mode="md",
            )
        finally:
            try:
                await client.disconnect()
            except Exception:
                pass
        return

    # STEP: 2FA password
    if st["step"] == "2fa":
        password = msg
        phone = st.get("phone")
        local = st.get("twofa_session_path") or session_path(uid, phone or "")
        if not phone or not local:
            login_state.pop(uid, None)
            return await e.respond(
                "⚠️ Session expired. Start `/login` again.",
                parse_mode="md",
            )
        client = TelegramClient(local, API_ID, API_HASH)
        try:
            await client.connect()
            await client.sign_in(password=password)
            me = await client.get_me()
            sp_upsert_session(uid, phone, os.path.basename(local))
            await e.respond(
                f"✅ 2FA verified. Logged in as **{me.first_name}**.\n"
                "Now use /create_link to generate invite links.",
                parse_mode="md",
            )
            asyncio.ensure_future(_start_listener_after_login(uid))
        except errors.PasswordHashInvalidError:
            return await e.respond(
                "❌ Wrong password, try again (or /login to restart).",
                parse_mode="md",
            )
        except Exception as ex:
            await e.respond(
                f"❌ 2FA login login failed: `{ex}`\nUse /login to reset.",
                parse_mode="md",
            )
        finally:
            login_state.pop(uid, None)
            try:
                await client.disconnect()
            except Exception:
                pass

def build_calendar_kb(year: int, month: int, selected_start: Optional[str], selected_end: Optional[str]) -> List[List[Button]]:
    """
    Inline calendar for a month.
    selected_start/end are 'YYYY-MM-DD' strings (for highlighting).
    """
    cal = calendar.monthcalendar(year, month)

    header = f"{calendar.month_name[month]} {year}"
    rows: List[List[Button]] = []

    # Month header row (non-clickable title) + nav
    rows.append([
        Button.inline("⬅️", data=f"cal_nav:prev:{year}:{month}".encode()),
        Button.inline(header, data=b"cal_noop"),
        Button.inline("➡️", data=f"cal_nav:next:{year}:{month}".encode()),
    ])

    # Weekday row
    rows.append([
        Button.inline("Mo", data=b"cal_noop"),
        Button.inline("Tu", data=b"cal_noop"),
        Button.inline("We", data=b"cal_noop"),
        Button.inline("Th", data=b"cal_noop"),
        Button.inline("Fr", data=b"cal_noop"),
        Button.inline("Sa", data=b"cal_noop"),
        Button.inline("Su", data=b"cal_noop"),
    ])

    # Days
    for week in cal:
        week_row: List[Button] = []
        for day in week:
            if day == 0:
                week_row.append(Button.inline(" ", data=b"cal_noop"))
                continue

            dstr = f"{year:04d}-{month:02d}-{day:02d}"

            # highlight selected range
            label = str(day)
            if selected_start == dstr:
                label = f"🟢{day}"
            if selected_end == dstr:
                label = f"🔴{day}"

            # simple range highlight (optional)
            if selected_start and selected_end:
                try:
                    s = datetime.fromisoformat(selected_start)
                    e = datetime.fromisoformat(selected_end)
                    cur = datetime.fromisoformat(dstr)
                    if s <= cur <= e and dstr not in (selected_start, selected_end):
                        label = f"•{day}"
                except Exception:
                    pass

            week_row.append(Button.inline(label, data=f"cal_day:{dstr}".encode()))
        rows.append(week_row)

    # action row
    rows.append([
        Button.inline("✖ Cancel", data=b"cal_cancel"),
        Button.inline("🔄 Reset", data=b"cal_reset"),
    ])
    return rows


# ---------- START MENU INLINE BUTTON HANDLERS ----------

@bot.on(events.CallbackQuery(pattern=b"menu_login"))
async def cb_menu_login(event):
    await event.answer()
    await event.respond("👤 Login ke liye command use karo:\n\n/login\n\nYahi se tum apna Telegram account connect karoge.", parse_mode="md")

@bot.on(events.CallbackQuery(pattern=b"menu_create_link"))
async def cb_menu_create_link(event):
    await event.answer()
    await event.respond("🧷 Naya invite link banane ke liye:\n\n/create_link\n\nYeh command sirf un groups/channels ke liye kaam karegi jahan tum admin ho.", parse_mode="md")

@bot.on(events.CallbackQuery(pattern=b"menu_links"))
async def cb_menu_links(event):
    await event.answer()
    await event.respond("📋 Apne sab active links dekhne ke liye:\n\n/links", parse_mode="md")

@bot.on(events.CallbackQuery(pattern=b"menu_stats"))
async def cb_menu_stats(event):
    await event.answer()
    await event.respond("📊 Joins ka stats dekhne ke liye:\n\n/stats\n\nYa jo bhi tumne stats wali command rakhi hai (agar naam alag hai to yahan update kar lena).", parse_mode="md")



@bot.on(events.CallbackQuery(pattern=b"resend_otp"))
async def cb_resend_otp(event):
    uid = event.sender_id
    st = login_state.get(uid)
    if not st or not st.get("phone"):
        return await event.answer("No login in progress. Use /login.", alert=True)
    phone = st["phone"]
    local = session_path(uid, phone)
    client = TelegramClient(local, API_ID, API_HASH)
    try:
        await safe_connect(client)
        res = await client.send_code_request(phone)
        st["phone_code_hash"] = getattr(res, "phone_code_hash", None)
        await event.edit(
            "📩 OTP resent. Send like `HELLO123456`.\n\n"
            "If you still do not receive it, try again after a minute.",
            buttons=[[Button.inline("🔁 Resend OTP", data=b"resend_otp")]],
        )
    except Exception as ex:
        await event.edit(f"❌ Resend failed: `{ex}`\nStart /login again.")
    finally:
        try:
            await client.disconnect()
        except Exception:
            pass


@bot.on(events.NewMessage(pattern=r"^/logout$"))
async def logout_cmd(e):
    if not await is_logged_in(e.sender_id):
        return await e.respond("ℹ️ Not logged in.", parse_mode="md")
    await e.respond(
        "⚠️ Are you sure you want to logout?\n\n"
        "Your session file and all tracked links will be removed.",
        parse_mode="md",
        buttons=[
            [
                Button.inline("✅ Yes, logout", data=b"logout_confirm"),
                Button.inline("✖ Cancel", data=b"logout_cancel"),
            ]
        ],
    )


@bot.on(events.CallbackQuery(pattern=b"logout_confirm"))
async def logout_confirm_cb(event):
    uid = event.sender_id
    data = sp_get_session(uid)
    if not data:
        return await event.edit("ℹ️ No session found.")
    # disconnect cached client
    client = USER_CLIENT_CACHE.pop(uid, None)
    if client:
        try:
            await client.disconnect()
        except Exception:
            pass
    # delete session file
    path = os.path.join(SESSION_DIR, data["session_file"])
    if os.path.exists(path):
        try:
            os.remove(path)
        except Exception as ex:
            print("remove session file err:", ex)
    sp_delete_session(uid)
    await event.edit("👋 Logged out. You can /login again anytime.", buttons=None)


@bot.on(events.CallbackQuery(pattern=b"logout_cancel"))
async def logout_cancel_cb(event):
    await event.edit("✖ Logout cancelled. You are still logged in.", buttons=None)


# ---------------- CREATE LINK FLOW (GROUPS/CHANNELS ONLY) ----------------

@bot.on(events.NewMessage(pattern=r"^/create_link$"))
async def create_link_cmd(e):
    if not await is_logged_in(e.sender_id):
        return await e.respond("🔒 Please /login first.", parse_mode="md")
    # premium check
    

    # default (reset preference)
    create_link_pref.pop(e.sender_id, None)

    await e.respond(
        "🔗 **Create Invite Link**\n\n"
        "Click on **Admin Approval Link** to create a link which requires admin to approve join requests.\n"
        "Or click on **Normal Link** to create a normal link without approval.\n\n"
        "👇 Choose one option:",
        parse_mode="md",
        buttons=[
            [
                Button.inline("✅ Admin Approval Link", data=b"cl_type:approval"),
                Button.inline("🔗 Normal Link", data=b"cl_type:normal"),
            ]
        ],
    )

@bot.on(events.NewMessage(pattern=r"^/select_date$"))
async def select_date_cmd(e):
    uid = e.sender_id
    if not await is_logged_in(uid):
        return await e.respond("🔒 Please /login first.", parse_mode="md")

    rows = sp_list_invite_links(uid)
    if not rows:
        return await e.respond("ℹ️ No active invite links. Use /create_link first.", parse_mode="md")

    # store state
    now = datetime.now(timezone.utc)
    date_select_state[uid] = {
        "step": "choose_link",
        "start_date": None,
        "end_date": None,
        "year": now.year,
        "month": now.month,
        "label": "Custom Range",
    }

    btn_rows: List[List[Button]] = []
    for r in rows[:10]:
        title = r.get("chat_title") or f"id:{r.get('chat_id')}"
        short = (title[:40] + "…") if len(title) > 40 else title
        btn_rows.append([Button.inline(short, data=f"dr_link:{r['id']}".encode())])
    btn_rows.append([Button.inline("✖ Cancel", data=b"dr_cancel")])

    await e.respond("📅 **Select link first:**", parse_mode="md", buttons=btn_rows)


@bot.on(events.CallbackQuery(pattern=b"^pin_create_links$"))
async def cb_pin_create_links(event):
    uid = event.sender_id
    try:
        uc = await get_user_client(uid)
    except Exception as ex:
        return await event.edit(f"❌ {ex}\nUse /login again.", buttons=None)

    pairs = await top_dialog_pairs(uc, TOP_N)
    if not pairs:
        return await event.edit(
            "ℹ️ No eligible group/channel dialogs found.\n"
            "Pin your private channel/group and try again.",
            buttons=None,
        )

    select_state[uid] = {
        "mode": "create_links",
        "pairs": pairs,
        "selected": set(),  # indexes
    }

    await event.edit(
        "🔗 Select chats for which you want new invite links (multi-select).\n"
        "Tap numbers to toggle, then **Done**.\n\n" + numbered_list_from_pairs(pairs),
        buttons=multi_kb(len(pairs), set()),
    )

@bot.on(events.CallbackQuery(pattern=b"^dr_link:"))
async def cb_dr_link(event):
    uid = event.sender_id
    st = date_select_state.get(uid)
    if not st:
        return await event.answer("Session expired. Run /select_date again.", alert=True)

    try:
        link_id = int(event.data.decode().split(":")[1])
    except Exception:
        return await event.answer("Invalid link.", alert=True)

    st["link_id"] = link_id
    st["step"] = "pick_start"

    year, month = st["year"], st["month"]
    kb = build_calendar_kb(year, month, st.get("start_date"), st.get("end_date"))

    await event.edit(
        "🟢 Select **START date** (calendar):",
        parse_mode="md",
        buttons=kb
    )

@bot.on(events.CallbackQuery(pattern=b"^cal_nav:"))
async def cb_cal_nav(event):
    uid = event.sender_id
    st = date_select_state.get(uid)
    if not st:
        return await event.answer("Session expired.", alert=True)

    parts = event.data.decode().split(":")
    direction = parts[1]
    year = int(parts[2]); month = int(parts[3])

    if direction == "prev":
        month -= 1
        if month == 0:
            month = 12
            year -= 1
    else:
        month += 1
        if month == 13:
            month = 1
            year += 1

    st["year"], st["month"] = year, month
    kb = build_calendar_kb(year, month, st.get("start_date"), st.get("end_date"))

    step = st.get("step", "pick_start")
    title = "🟢 Select **START date**" if step == "pick_start" else "🔴 Select **END date**"
    await event.edit(title, parse_mode="md", buttons=kb)


@bot.on(events.CallbackQuery(pattern=b"^cal_day:"))
async def cb_cal_day(event):
    uid = event.sender_id
    st = date_select_state.get(uid)
    if not st:
        return await event.answer("Session expired.", alert=True)

    dstr = event.data.decode().split(":", 1)[1]  # YYYY-MM-DD

    step = st.get("step")
    if step == "pick_start":
        st["start_date"] = dstr
        st["end_date"] = None
        st["step"] = "pick_end"

        kb = build_calendar_kb(st["year"], st["month"], st["start_date"], st.get("end_date"))
        return await event.edit(
            f"✅ Start date set: `{dstr}`\n\n🔴 Now select **END date**:",
            parse_mode="md",
            buttons=kb
        )

    if step == "pick_end":
        # ensure end >= start
        try:
            s = datetime.fromisoformat(st["start_date"])
            e = datetime.fromisoformat(dstr)
            if e < s:
                return await event.answer("End date must be >= start date.", alert=True)
        except Exception:
            return await event.answer("Invalid date.", alert=True)

        st["end_date"] = dstr

        # ✅ Now run stats
        start_str = st["start_date"]
        end_str = st["end_date"]
        link_id = st["link_id"]

        # Convert selected dates to UTC range based on IST day boundaries
        IST = timezone(timedelta(hours=5, minutes=30))

        start_ist = datetime.fromisoformat(start_str).replace(tzinfo=IST, hour=0, minute=0, second=0, microsecond=0)
        end_ist = datetime.fromisoformat(end_str).replace(tzinfo=IST, hour=23, minute=59, second=59, microsecond=999999)

        since_utc = start_ist.astimezone(timezone.utc)
        until_utc = end_ist.astimezone(timezone.utc)

        await event.edit(
            "⏳ Syncing join data from Telegram for this link...\nPlease wait 2–3 seconds.",
            buttons=None
        )

        # sync (same like /stats)
        await sync_importers_to_db(uid, only_link_id=link_id)


        # counts
        total = sp_count_joins_for_link(uid, link_id, since=since_utc, until=until_utc)
        left_total = sp_count_left_for_link(uid, link_id, since=since_utc, until=until_utc)
        active_total = total - left_total

        # link info
        rows = sp_list_invite_links(uid)
        chosen = next((r for r in rows if int(r["id"]) == link_id), None)

        title = chosen.get("chat_title") if chosen else "Unknown"
        link = chosen.get("invite_link") if chosen else "-"
        link_type = (chosen.get("link_type") if chosen else "normal")

        msg_lines = []
        msg_lines.append("📊 **Custom Range stats**")
        msg_lines.append(f"`{title}`")
        msg_lines.append("")
        msg_lines.append(f"🗓️ Range: `{start_str}` → `{end_str}` (IST)")
        msg_lines.append(f"🔗 `{link}`")
        msg_lines.append("🛂 _required approval_" if (link_type == "approval") else "🔓 _normal link_")
        msg_lines.append("")
        msg_lines.append(f"👥 Total joins: `{total}`")
        msg_lines.append(f"🚪 Total left: `{left_total}`")
        msg_lines.append(f"🟢 Current joined: `{active_total}`")

        date_select_state.pop(uid, None)
        return await event.edit("\n".join(msg_lines), parse_mode="md", buttons=[[Button.inline("✖ Close", data=b"stats_page:close")]])


@bot.on(events.CallbackQuery(pattern=b"^cal_reset$"))
async def cb_cal_reset(event):
    uid = event.sender_id
    st = date_select_state.get(uid)
    if not st:
        return await event.answer("Session expired.", alert=True)

    st["start_date"] = None
    st["end_date"] = None
    st["step"] = "pick_start"

    kb = build_calendar_kb(st["year"], st["month"], None, None)
    await event.edit("🟢 Select **START date** (calendar):", parse_mode="md", buttons=kb)


@bot.on(events.CallbackQuery(pattern=b"^cal_cancel$"))
async def cb_cal_cancel(event):
    date_select_state.pop(event.sender_id, None)
    await event.edit("✖ Date selection cancelled.", buttons=None)


@bot.on(events.CallbackQuery(pattern=b"^dr_cancel$"))
async def cb_dr_cancel(event):
    date_select_state.pop(event.sender_id, None)
    await event.edit("✖ Cancelled.", buttons=None)


@bot.on(events.CallbackQuery(pattern=b"^cal_noop$"))
async def cb_cal_noop(event):
    await event.answer()


@bot.on(events.CallbackQuery(pattern=b"^cl_type:"))
async def cb_choose_create_link_type(event):
    uid = event.sender_id
    choice = event.data.decode().split(":", 1)[1]  # approval | normal

    if choice not in ("approval", "normal"):
        return await event.answer("Invalid choice.", alert=True)

    create_link_pref[uid] = choice

    # Continue old flow (pinned instruction)
    await event.edit(
        "🔗 **Create Invite Links (Private Groups/Channels)**\n\n"
        "1️⃣ In your Telegram app, *pin* the private channels/groups where you want invite links.\n"
        "2️⃣ Come back here and tap the button below.\n\n"
        "_Only groups/channels are shown (no 1-1 user chats). Max top 14 pinned chats._",
        parse_mode="md",
        buttons=[[Button.inline("📌 I have pinned the chats", data=b"pin_create_links")]],
    )


@bot.on(events.CallbackQuery(pattern=b"^msel:"))
async def cb_toggle(event):
    uid = event.sender_id
    st = select_state.get(uid)
    if not st:
        return await event.answer(
            "Session expired. Use /create_link or /remove_link again.",
            alert=True,
        )
    try:
        idx = int(event.data.decode().split(":")[1]) - 1
    except Exception:
        return await event.answer("Invalid.", alert=True)
    if idx < 0 or idx >= len(st["pairs"]):
        return await event.answer("Out of range.", alert=True)

    sel: Set[int] = st["selected"]
    if idx in sel:
        sel.remove(idx)
    else:
        sel.add(idx)

    mode = st["mode"]
    if mode == "create_links":
        header = "🔗 Select chats to create invite links"
    elif mode == "remove_links":
        header = "🗑️ Select links to remove"
    else:
        header = "Select items"

    await event.edit(
        f"{header} (multi-select). Tap numbers, then **Done**.\n\n"
        + numbered_list_from_pairs(st["pairs"]),
        buttons=multi_kb(len(st["pairs"]), sel),
    )


@bot.on(events.CallbackQuery(pattern=b"^msel_done$"))
async def cb_msel_done(event):
    uid = event.sender_id
    st = select_state.get(uid)
    if not st:
        return await event.answer("Session expired. Start again.", alert=True)

    mode = st["mode"]

    # --- create_links mode ---
    if mode == "create_links":
        chosen = sorted(st["selected"])
        if not chosen:
            select_state.pop(uid, None)
            return await event.edit(
                "ℹ️ No chats selected. Use /create_link again.",
                buttons=None,
            )

        try:
            uc = await get_user_client(uid)
        except Exception as ex:
            select_state.pop(uid, None)
            return await event.edit(f"❌ {ex}", buttons=None)

        created_lines = []
        for idx in chosen:
            chat_id, title = st["pairs"][idx]
            try:
                # Export private invite link

                link_type = create_link_pref.get(uid, "normal")
                request_needed = True if link_type == "approval" else False
                res = await uc(
                    functions.messages.ExportChatInviteRequest(
                        peer=chat_id,
                        legacy_revoke_permanent=False,
                        request_needed=request_needed,   # ✅ admin approval toggle
                    )
                )
                link = res.link if hasattr(res, "link") else str(res)
                sp_save_invite_link(uid, int(chat_id), title, link, link_type)
                tag = " ✅ (Approval Required)" if request_needed else ""
                created_lines.append(f"• `{title}` → {link}")
            except Exception as ex:
                created_lines.append(f"• `{title}` → ❌ `{ex}`")

        select_state.pop(uid, None)
        create_link_pref.pop(uid, None)   # ✅ YAHAN add karna hai (important)
        txt = "✅ **Invite links created / saved:**\n\n" + "\n".join(created_lines)
        return await event.edit(txt, parse_mode="md", buttons=None)

    # --- remove_links mode → move to confirmation ---
    if mode == "remove_links":
        chosen = sorted(st["selected"])
        rows: List[dict] = st.get("rows", [])
        link_ids: List[int] = []
        selected_labels: List[str] = []

        for i in chosen:
            if 0 <= i < len(rows):
                rid = rows[i].get("id")
                if rid is not None:
                    link_ids.append(int(rid))
                    title = rows[i].get("chat_title") or f"id:{rows[i].get('chat_id')}"
                    link = rows[i].get("invite_link") or "-"
                    selected_labels.append(f"- `{title}` → {link}")

        if not link_ids:
            select_state.pop(uid, None)
            return await event.edit(
                "ℹ️ Nothing selected. Use /remove_link again.",
                buttons=None,
            )

        # save pending deletion state for confirmation
        select_state[uid] = {
            "mode": "remove_confirm",
            "link_ids": link_ids,
            "labels": selected_labels,
        }

        text = (
            "⚠️ **Delete confirmation**\n\n"
            "You are about to delete the following invite link(s):\n\n"
            + "\n".join(selected_labels)
            + "\n\n"
            "If you continue, **all join data associated with these invite links** "
            "will be permanently removed from the database.\n\n"
            "Are you sure you want to delete?"
        )

        return await event.edit(
            text,
            parse_mode="md",
            buttons=[
                [
                    Button.inline("✅ Yes, delete", data=b"rem_confirm"),
                    Button.inline("✖ Cancel", data=b"rem_cancel"),
                ]
            ],
        )

    # any other mode
    select_state.pop(uid, None)
    return await event.edit("ℹ️ Nothing to do.", buttons=None)


@bot.on(events.CallbackQuery(pattern=b"^rem_confirm$"))
async def cb_rem_confirm(event):
    uid = event.sender_id
    st = select_state.get(uid)
    if not st or st.get("mode") != "remove_confirm":
        return await event.answer("Nothing pending to delete.", alert=True)

    link_ids: List[int] = st.get("link_ids", [])
    count = len(link_ids)
    select_state.pop(uid, None)

    if not link_ids:
        return await event.edit("ℹ️ No links to delete.", buttons=None)

    sp_soft_delete_links(uid, link_ids)
    await event.edit(
        f"🗑️ Deleted **{count}** invite link(s) and all associated join data.",
        buttons=None,
    )


@bot.on(events.CallbackQuery(pattern=b"^rem_cancel$"))
async def cb_rem_cancel(event):
    uid = event.sender_id
    st = select_state.get(uid)
    if st and st.get("mode") == "remove_confirm":
        select_state.pop(uid, None)
    await event.edit("✖ Deletion cancelled. No links were removed.", buttons=None)


@bot.on(events.CallbackQuery(pattern=b"^msel_cancel$"))
async def cb_msel_cancel(event):
    select_state.pop(event.sender_id, None)
    await event.edit("✖ Selection cancelled.", buttons=None)


# ---------------- LIST / REMOVE LINKS ----------------

@bot.on(events.NewMessage(pattern=r"^/links$"))
async def links_cmd(e):
    uid = e.sender_id
    if not await is_logged_in(uid):
        return await e.respond("🔒 Please /login first.", parse_mode="md")
    rows = sp_list_invite_links(uid)
    if not rows:
        return await e.respond(
            "ℹ️ No active invite links yet. Use /create_link.",
            parse_mode="md",
        )
    lines = ["📋 **Your tracked invite links:**", ""]
    for r in rows:
        title = r.get("chat_title") or f"id:{r.get('chat_id')}"
        link = r.get("invite_link") or "-"
        created = str(r.get("created_at") or "")[:19]
        link_type = r.get("link_type", "normal")
        badge = "🛂 _required approval_" if link_type == "approval" else ""
        lines.append(
            f"- `{title}` {badge}\n"
            f"  {link}\n"
            f"  _created: {created}_\n"
        )
    await e.respond("\n".join(lines), parse_mode="md")


@bot.on(events.NewMessage(pattern=r"^/remove_link$"))
async def remove_link_cmd(e):
    uid = e.sender_id
    if not await is_logged_in(uid):
        return await e.respond("🔒 Please /login first.", parse_mode="md")
    rows = sp_list_invite_links(uid)
    if not rows:
        return await e.respond("ℹ️ No active links to remove.", parse_mode="md")
    pairs = []
    for i, r in enumerate(rows):
        title = r.get("chat_title") or f"id:{r.get('chat_id')}"
        link = r.get("invite_link") or "-"
        label = f"{title} — {link}"
        pairs.append((i, label))
    select_state[uid] = {
        "mode": "remove_links",
        "pairs": pairs,
        "selected": set(),
        "rows": rows,
    }
    await e.respond(
        "🗑️ **Remove Links** — select links to remove (multi-select) then **Done**.\n\n"
        "Note: Deleting a link will also permanently delete all join data stored for that link.\n\n"
        + numbered_list_from_pairs(pairs),
        buttons=multi_kb(len(pairs), set()),
    )


# ---------------- SYNC IMPORTERS → JOINS TABLE (FIXED) ----------------
from telethon.errors import FloodWaitError
import asyncio
from datetime import datetime, timezone
from typing import Optional, List, Dict

def extract_invite_hash(full_link: str) -> str:
    part = (full_link or "").rsplit("/", 1)[-1]
    part = part.replace("joinchat/", "")
    part = part.lstrip("+").strip()
    return part

async def fetch_all_importers(uc, peer, link_hash: str, requested: bool = False) -> list:
    """
    Fetch ALL importers via pagination.
    - FloodWait safe
    - If access_hash missing, continue date-based pagination (don't break)
    """
    all_imps = []
    offset_date = None
    offset_user = tl_types.InputUserEmpty()
    page_limit = 200  # safe

    while True:
        try:
            res = await uc(
                functions.messages.GetChatInviteImportersRequest(
                    peer=peer,
                    link=link_hash,
                    offset_date=offset_date,
                    offset_user=offset_user,
                    limit=page_limit,
                    requested=requested,
                )
            )
        except FloodWaitError as fw:
            await asyncio.sleep(fw.seconds + 5)
            continue
        except Exception as ex:
            # Silently skip - expired links are expected
            # Uncomment to debug: print("fetch_all_importers error:", ex)
            break

        imps = getattr(res, "importers", []) or []
        if not imps:
            break

        all_imps.extend(imps)

        if len(imps) < page_limit:
            break

        last = imps[-1]
        offset_date = getattr(last, "date", None)

        users = getattr(res, "users", []) or []
        user_map = {int(u.id): u for u in users if getattr(u, "id", None)}

        last_uid = int(getattr(last, "user_id", 0) or 0)

        # If access_hash exists, use it
        if last_uid and last_uid in user_map and getattr(user_map[last_uid], "access_hash", None):
            offset_user = types.InputUser(user_id=last_uid, access_hash=user_map[last_uid].access_hash)
        else:
            # IMPORTANT: continue with date-based pagination
            offset_user = tl_types.InputUserEmpty()

    return all_imps


# ✅ NEW RPC caller (upsert only, never delete)
def sp_upsert_joins_for_link(uid: int, invite_link_id: int, join_rows: List[dict]) -> int:
    """
    Returns inserted/updated count (best effort).
    Requires SQL RPC: upsert_joins_for_link
    """
    if not join_rows:
        return 0
    resp = supabase.rpc(
        "upsert_joins_for_link",
        {
            "p_user_id": int(uid),
            "p_invite_link_id": int(invite_link_id),
            "p_rows": join_rows,
        },
    ).execute()
    # resp.data may return count depending on your RPC implementation
    try:
        return int(resp.data or 0)
    except Exception:
        return 0


async def sync_importers_to_db(uid: int, only_link_id: Optional[int] = None) -> Dict[int, int]:
    """
    Sync from Telegram -> DB
    Returns dict: {invite_link_id: upserted_count}
    """
    rows = get_cached_invite_links(uid)
    if not rows:
        return {}

    if only_link_id is not None:
        rows = [r for r in rows if int(r.get("id", 0)) == int(only_link_id)]
        if not rows:
            return {}

    try:
        uc = await get_user_client(uid)
    except Exception as ex:
        print("sync_importers_to_db error (get_user_client):", ex)
        return {}

    results = {}

    for r in rows:
        invite_link_id = int(r["id"])
        chat_id = int(r["chat_id"])
        full_link = r.get("invite_link") or ""
        link_type = (r.get("link_type") or "normal").lower()  # normal / approval

        link_hash = extract_invite_hash(full_link)
        if not link_hash:
            print("sync_importers_to_db: invalid link hash:", full_link)
            results[invite_link_id] = 0
            continue

        try:
            peer = await uc.get_input_entity(chat_id)
        except Exception as ex:
            print(f"sync_importers_to_db get_input_entity error for {chat_id}:", ex)
            results[invite_link_id] = 0
            continue

        # ✅ approval links: fetch BOTH and merge
        try:
            importers_normal = await fetch_all_importers(uc, peer, link_hash, requested=False)

            importers_requested = []
            if link_type == "approval":
                importers_requested = await fetch_all_importers(uc, peer, link_hash, requested=True)

            merged: Dict[int, datetime] = {}
            for imp in (importers_normal + importers_requested):
                joined_user_id = int(getattr(imp, "user_id", 0) or 0)
                if not joined_user_id:
                    continue

                join_date = getattr(imp, "date", None)
                if isinstance(join_date, datetime):
                    joined_at = join_date.astimezone(timezone.utc)
                else:
                    joined_at = datetime.now(timezone.utc)

                prev = merged.get(joined_user_id)
                if (prev is None) or (joined_at < prev):
                    merged[joined_user_id] = joined_at

        except Exception as ex:
            print("GetChatInviteImporters error:", ex)
            results[invite_link_id] = 0
            continue

        join_rows: List[dict] = []
        for joined_user_id_int, joined_at in merged.items():
            join_rows.append(
                {
                    "user_id": int(uid),
                    "chat_id": int(chat_id),
                    "invite_link_id": int(invite_link_id),
                    "joined_user_id": int(joined_user_id_int),
                    "joined_at": joined_at.isoformat(),
                    "joined_source": "sync",  # ✅ debugging field
                }
            )

        # ✅ Skip users whose left_at is already set in DB (do not overwrite leave data)
        if join_rows:
            existing = supabase.table("joins") \
                .select("joined_user_id") \
                .eq("user_id", uid) \
                .eq("invite_link_id", invite_link_id) \
                .not_.is_("left_at", "null") \
                .execute()
            already_left_ids: Set[int] = {int(row["joined_user_id"]) for row in (existing.data or [])}
            join_rows = [r for r in join_rows if r["joined_user_id"] not in already_left_ids]

        # ✅ IMPORTANT FIX: UPSERT ONLY (never delete)
        upserted = sp_upsert_joins_for_link(uid, invite_link_id, join_rows)
        results[invite_link_id] = upserted

        # Rate-limit: random jitter delay between API calls
        await asyncio.sleep(random.uniform(0.3, 0.5))

    return results


# ---------------- REAL-TIME JOIN/LEAVE LISTENER ----------------

async def start_user_listeners(uid: int, client: TelegramClient):
    """
    Attach event listeners on the user client for real-time join/leave tracking.

    Two listeners:
    1. events.ChatAction  → groups/supergroups (user_joined / user_left)
    2. events.Raw(UpdateChannelParticipant) → channels (join / leave / kick)
    """
    if uid in ACTIVE_LISTENERS:
        return  # already attached
    ACTIVE_LISTENERS.add(uid)

      # ── LISTENER 1: Groups / Supergroups ─────────────────────────────────────────────
    @client.on(events.ChatAction)
    async def _on_chat_action(event):
        try:
            chat_id = int(event.chat_id)

            # Only handle chats this user is tracking (use cache)
            all_links = get_cached_invite_links(uid)
            chat_links = [r for r in all_links if int(r.get("chat_id", 0)) == chat_id]
            if not chat_links:
                return

            if event.user_joined or event.user_added:
                joined_user_id = int(getattr(event, "user_id", 0) or 0)
                if not joined_user_id:
                    return
                log_info(f"Real-time [group]: user {joined_user_id} joined chat {chat_id} (uid={uid})")

                # 1️⃣ Insert immediately into DB (invite_link_id=None for now)
                sp_realtime_join_insert(uid, chat_id, joined_user_id, joined_source="realtime_group")

                # 2️⃣ Enqueue deferred sync to resolve correct invite_link_id
                enqueue_sync(uid, chat_id)

            elif event.user_left or event.user_kicked:
                # User left/kicked → update left_at in DB immediately
                left_uid_val = int(getattr(event, "user_id", 0) or 0)
                if not left_uid_val:
                    return
                reason = "left" if event.user_left else "kicked"
                now_iso = datetime.now(timezone.utc).isoformat()
                try:
                    supabase.table("joins").update({
                        "left_at": now_iso,
                        "left_reason": reason,
                        "left_seen_at": now_iso,
                    }).eq("user_id", uid).eq("chat_id", chat_id).eq(
                        "joined_user_id", left_uid_val
                    ).is_("left_at", "null").execute()
                    log_info(f"Real-time [group]: user {left_uid_val} marked {reason} in chat {chat_id} (uid={uid})")
                except Exception as ex:
                    log_error(f"Real-time leave update error uid={uid}: {ex}")

        except Exception as ex:
            log_error(f"ChatAction handler error uid={uid}: {ex}")

    # ── LISTENER 2: Channels ────────────────────────────────────────────────
    # ChatAction does NOT fire for Telegram channels.
    # Channels generate UpdateChannelParticipant raw updates instead.
    @client.on(events.Raw(UpdateChannelParticipant))
    async def _on_channel_participant(event):
        try:
            # Convert bare channel_id → peer ID format used in DB (e.g. -1002922268649)
            bare_id = int(getattr(event, "channel_id", 0) or 0)
            if not bare_id:
                return
            chat_id = int(f"-100{bare_id}")

            # Only handle channels this user is tracking (use cache)
            all_links = get_cached_invite_links(uid)
            chat_links = [r for r in all_links if int(r.get("chat_id", 0)) == chat_id]
            if not chat_links:
                return

            new_p = getattr(event, "new_participant", None)
            prev_p = getattr(event, "prev_participant", None)
            joined_user_id = int(getattr(event, "user_id", 0) or 0)
            if not joined_user_id:
                return

            # ── JOIN: new participant is active (not banned/left) ──
            is_now_active = new_p is not None and not isinstance(
                new_p, (ChannelParticipantBanned, ChannelParticipantLeft)
            )
            was_inactive = prev_p is None or isinstance(
                prev_p, (ChannelParticipantBanned, ChannelParticipantLeft)
            )

            if is_now_active and was_inactive:
                log_info(f"Real-time [channel]: user {joined_user_id} joined chat {chat_id} (uid={uid})")

                # ✅ Improved: check if event carries the invite link used
                invite_obj = getattr(event, "invite", None)
                invite_link_str = getattr(invite_obj, "link", None) if invite_obj else None

                matched_link_id: Optional[int] = None
                if invite_link_str:
                    # Try to match directly against our stored links
                    for link_row in chat_links:
                        if link_row.get("invite_link") == invite_link_str:
                            matched_link_id = int(link_row["id"])
                            break

                # 1️⃣ Immediate DB insert (with or without invite_link_id)
                sp_realtime_join_insert(
                    uid, chat_id, joined_user_id,
                    invite_link_id=matched_link_id,
                    joined_source="realtime_channel",
                )

                # 2️⃣ Enqueue deferred sync to confirm and fill invite_link_id
                enqueue_sync(uid, chat_id)

            # ── LEAVE / KICK: new participant is banned or left ──
            elif isinstance(new_p, (ChannelParticipantBanned, ChannelParticipantLeft)):
                reason = "kicked" if isinstance(new_p, ChannelParticipantBanned) else "left"
                now_iso = datetime.now(timezone.utc).isoformat()
                try:
                    supabase.table("joins").update({
                        "left_at": now_iso,
                        "left_reason": reason,
                        "left_seen_at": now_iso,
                    }).eq("user_id", uid).eq("chat_id", chat_id).eq(
                        "joined_user_id", joined_user_id
                    ).is_("left_at", "null").execute()
                    log_info(f"Real-time [channel]: user {joined_user_id} marked {reason} in chat {chat_id} (uid={uid})")
                except Exception as ex:
                    log_error(f"Real-time channel leave update error uid={uid}: {ex}")

        except Exception as ex:
            log_error(f"UpdateChannelParticipant handler error uid={uid}: {ex}")

    log_info(f"✅ Real-time listeners attached (group + channel) for uid {uid}")

    # Start sync queue worker if not already running
    global _sync_worker_started
    if not _sync_worker_started:
        _sync_worker_started = True
        asyncio.ensure_future(_sync_worker())
        log_info("✅ Sync queue worker started")


async def _start_listener_after_login(uid: int):
    """Delayed start of listener after login (gives temp client time to disconnect)."""
    await asyncio.sleep(2)
    try:
        uc = await get_user_client(uid)
        await start_user_listeners(uid, uc)
    except Exception as ex:
        log_warning(f"Could not start listener after login uid={uid}: {ex}")


async def start_listeners_for_all_users():
    """On bot startup: reattach real-time listeners for ALL active user sessions."""
    try:
        res = supabase.table("user_sessions").select("user_id").eq("is_active", True).execute()
        for sess in (res.data or []):
            uid = int(sess["user_id"])
            try:
                client = await get_user_client(uid)
                await start_user_listeners(uid, client)
            except Exception as ex:
                log_warning(f"Could not attach listener for uid={uid}: {ex}")
            await asyncio.sleep(0.5)
    except Exception as ex:
        log_error(f"start_listeners_for_all_users error: {ex}")


async def auto_sync_loop():
    """
    Background loop: every 30 seconds, pull fresh join data from Telegram API.
    Safety net in case real-time events were missed (e.g. bot was down).
    """
    await asyncio.sleep(10)  # short initial wait so listeners attach first
    while True:
        log_info("🔄 Auto-sync started for all users...")
        try:
            res = supabase.table("user_sessions").select("user_id").eq("is_active", True).execute()
            for sess in (res.data or []):
                uid = int(sess["user_id"])
                try:
                    await sync_importers_to_db(uid)
                    log_info(f"✅ Auto-sync ok for uid={uid}")
                except Exception as ex:
                    log_error(f"Auto-sync failed for uid={uid}: {ex}")
                await asyncio.sleep(2)
        except Exception as ex:
            log_error(f"auto_sync_loop error: {ex}")
        log_info("✅ Auto-sync cycle complete.")
        await asyncio.sleep(20 * 3600)  # run again every 20 hours



async def _stats_template(
    e,
    label: str,
    since: Optional[datetime],
    until: Optional[datetime] = None,
):
    """Ask user which invite_link they want stats for."""
    uid = e.sender_id
    if not await is_logged_in(uid):
        return await e.respond("🔒 Please /login first.",parse_mode="md")
    

    rows = sp_list_invite_links(uid)
    if not rows:
        return await e.respond(
            "ℹ️ No active invite links yet. Use /create_link first.",
            parse_mode="md",
        )

    # save context for callback
    stats_state[uid] = {
        "label": label,
        "since": since,
        "until": until,
    }

    btn_rows: List[List[Button]] = []
    for r in rows[:10]:
        title = r.get("chat_title") or f"id:{r.get('chat_id')}"
        short = (title[:40] + "…") if len(title) > 40 else title
        data = f"stats:{r['id']}".encode()
        btn_rows.append([Button.inline(short, data=data)])

    btn_rows.append([Button.inline("✖ Cancel", data=b"stats_cancel")])

    await e.respond(
        "📊 **Select which invite link you want stats for:**",
        parse_mode="md",
        buttons=btn_rows,
    )

@bot.on(events.CallbackQuery(pattern=b"^close_msg$"))
async def cb_close_msg(event):
    # Option 1: delete the message
    await event.delete()

    # Option 2 (if you prefer edit):
    # await event.edit("✖ Closed.", buttons=None)


@bot.on(events.CallbackQuery(pattern=b"^stats:"))
async def cb_stats_link(event):
    """User selected a specific invite_link for stats (first page)."""
    uid = event.sender_id
    st = stats_state.get(uid)
    if not st:
        return await event.answer("Session expired. Run /stats again.", alert=True)

    try:
        link_id = int(event.data.decode().split(":")[1])
    except Exception:
        return await event.answer("Invalid selection.", alert=True)

    label = st["label"]
    since = st["since"]
    until = st["until"]
    stats_state.pop(uid, None)

    # Sync latest importers from Telegram to DB
    await event.edit(
        "⏳ Syncing join data from Telegram for this link...\n"
        "Please wait 2–3 seconds.",
        buttons=None,
    )
    await sync_importers_to_db(uid, only_link_id=link_id)

    # Total joins for this link
    total = sp_count_joins_for_link(uid, link_id, since=since, until=until)
    left_total = sp_count_left_for_link(uid, link_id, since=since, until=until)


    # Fetch link info once and store in context
    rows = sp_list_invite_links(uid)
    chosen = None
    for r in rows:
        if int(r["id"]) == link_id:
            chosen = r
            break

    if chosen:
        title = chosen.get("chat_title") or f"id:{chosen.get('chat_id')}"
        link = chosen.get("invite_link") or "-"
        created_at = chosen.get("created_at")
        link_type = chosen.get("link_type", "normal")  # ✅ NEW
    else:
        title = "(link not found / removed)"
        link = "-"
        created_at = None
        link_type = "normal"

    # Normal page size
    page_size = 15

    msg = await event.get_message()
    key = (uid, msg.id)
    stats_pages[key] = {
        "link_id": link_id,
        "label": label,
        "since": since,
        "until": until,
        "offset": 0,
        "page_size": page_size,
        "total": total,
        "title": title,
        "link": link,
        "created_at": created_at,
        "link_type": link_type,  # ✅ NEW
        "left_total": left_total,


    }

    # Render first page
    await render_stats_page(event, uid, stats_pages[key])


@bot.on(events.CallbackQuery(pattern=b"^stats_page:"))
async def cb_stats_page(event):
    """
    Handle pagination buttons for stats user list.
    """
    uid = event.sender_id
    try:
        action = event.data.decode().split(":")[1]
    except Exception:
        return await event.answer("Invalid action.", alert=True)

    msg = await event.get_message()
    key = (uid, msg.id)
    ctx = stats_pages.get(key)

    if not ctx:
        return await event.answer("Session expired. Run /stats again.", alert=True)

    if action == "close":
        stats_pages.pop(key, None)
        await event.edit("✖ Stats closed.", buttons=None)
        return

    if action == "next":
        ctx["offset"] += ctx["page_size"]
    elif action == "prev":
        ctx["offset"] -= ctx["page_size"]

    await render_stats_page(event, uid, ctx)


@bot.on(events.CallbackQuery(pattern=b"^stats_cancel$"))
async def cb_stats_cancel(event):
    stats_state.pop(event.sender_id, None)
    await event.edit("✖ Stats selection cancelled.", buttons=None)


@bot.on(events.NewMessage(pattern=r"^/stats$"))
async def stats_all_cmd(e):
    await _stats_template(e, "All time", since=None)

@bot.on(events.NewMessage(pattern=r"^/(?:yesterday|yestarday)$"))
async def yesterday_status_cmd(e):
    uid = e.sender_id
    if not await is_logged_in(uid):
        return await e.respond("🔒 Please /login first.", parse_mode="md")

    IST = timezone(timedelta(hours=5, minutes=30))
    now_ist = datetime.now(IST)

    # Yesterday range in IST
    y_start_ist = (now_ist - timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
    y_end_ist = y_start_ist + timedelta(days=1)

    # Convert to UTC for DB filters
    since_utc = y_start_ist.astimezone(timezone.utc)
    until_utc = y_end_ist.astimezone(timezone.utc)

    await _stats_template(e, label="Yesterday", since=since_utc, until=until_utc)



@bot.on(events.NewMessage(pattern=r"^/hour_status$"))
async def stats_hour_cmd(e):
    now = datetime.now(timezone.utc)
    start = now - timedelta(hours=1)
    await _stats_template(e, "Last 1 hour", since=start)


@bot.on(events.NewMessage(pattern=r"^/today_status$"))
async def stats_today_cmd(e):
    now = datetime.now(timezone.utc)
    start = now.replace(hour=0, minute=0, second=0, microsecond=0)
    await _stats_template(e, "Today", since=start)



@bot.on(events.NewMessage(pattern=r"^/week_status$"))
async def stats_week_cmd(e):
    now = datetime.now(timezone.utc)
    start = now - timedelta(days=7)
    await _stats_template(e, "Last 7 days", since=start)


async def send_daily_report_to_user(uid: int):
    """Generates and sends the daily join report to a specific user Telegram ID."""
    try:
        # 1. Sync latest data
        await sync_importers_to_db(uid)

        # 2. Get data for today
        links = sp_list_invite_links(uid)
        if not links:
            return

        IST = timezone(timedelta(hours=5, minutes=30))
        now_ist = datetime.now(IST)
        start_ist = now_ist.replace(hour=0, minute=0, second=0, microsecond=0)
        since_utc = start_ist.astimezone(timezone.utc)

        report_data = []
        for r in links:
            link_id = int(r["id"])
            count = sp_count_joins_for_link(uid, link_id, since=since_utc)
            if count > 0:
                report_data.append({
                    "chat_title": r.get("chat_title") or f"id:{r.get('chat_id')}",
                    "invite_link": r.get("invite_link", "-"),
                    "count": count
                })

        if not report_data:
            return False

        # 3. Generate Reports
        excel_file = generate_today_excel_report(report_data)
        graph_file = generate_today_graph_report(report_data)
        text_report = generate_today_text_report(report_data)

        try:
            # 4. Send Reports
            await bot.send_message(uid, text_report, parse_mode="md")

            if os.path.exists(excel_file):
                await bot.send_file(uid, excel_file, caption=f"📊 Daily Excel Report ({now_ist.strftime('%d-%m-%Y')})")

            if os.path.exists(graph_file):
                await bot.send_file(uid, graph_file, caption=f"📉 Daily Bar Graph ({now_ist.strftime('%d-%m-%Y')})")
        finally:
            # Cleanup
            for f in [excel_file, graph_file]:
                if os.path.exists(f):
                    try:
                        os.remove(f)
                    except Exception as e:
                        log_error(f"Failed to delete temporary report file {f}: {e}")
        return True
    except Exception as e:
        log_error(f"Error in send_daily_report_to_user for {uid}: {e}")
        return False


async def scheduled_report_loop():
    """Background task to send reports every day at 6 PM IST."""
    IST = timezone(timedelta(hours=5, minutes=30))
    log_info("⏰ Scheduled report loop started (Target: 06:00 PM IST daily)")
    
    while True:
        now_ist = datetime.now(IST)
        # Calculate next 6 PM IST
        target = now_ist.replace(hour=18, minute=0, second=0, microsecond=0)
        if now_ist >= target:
            target += timedelta(days=1)
        
        sleep_seconds = (target - now_ist).total_seconds()
        log_info(f"Next scheduled report in {sleep_seconds/3600:.2f} hours (at {target})")
        
        await asyncio.sleep(max(0.0, sleep_seconds))
        
        # Trigger report
        log_info("🔔 Triggering scheduled daily reports...")
        try:
            session_res = supabase.table("user_sessions").select("user_id").eq("is_active", True).execute()
            active_uids = [row["user_id"] for row in (session_res.data or [])]
            
            for uid in active_uids:
                await send_daily_report_to_user(uid)
                await asyncio.sleep(2) # small stagger
        except Exception as e:
            log_error(f"Error in scheduled_report_loop execution: {e}")


@bot.on(events.NewMessage(pattern=r"^/stats_today$"))
@safe_event_handler
async def cmd_stats_today(event):
    uid = event.sender_id
    if not await is_logged_in(uid):
        return await event.respond("🔒 Please /login first.", parse_mode="md")

    status_msg = await event.respond("⏳ Generating your daily report... Please wait.")
    found = await send_daily_report_to_user(uid)
    await status_msg.delete()
    
    if not found:
        await event.respond("ℹ️ **No users joined** on any of your links today.", parse_mode="md")


@bot.on(events.NewMessage(pattern=r"^/month_status$"))
async def stats_month_cmd(e):
    now = datetime.now(timezone.utc)
    start = now - timedelta(days=30)
    await _stats_template(e, "Last 30 days", since=start)



async def setup_bot_profile():
    """Sets the bot name and commands once on start."""
    try:
        # ✅ Ensure bot is started within the current async loop
        if not bot.is_connected():
            await bot.start(bot_token=BOT_TOKEN)
            
        me = await bot.get_me()
        await bot(
            functions.bots.SetBotInfoRequest(
                bot=me,
                lang_code="en",
                name="Join Counter Bot",
                about="Track private invite-link joins for your groups/channels.",
                description=(
                    "Log in with your own account, create unique private invite links for your "
                    "groups/channels, and track how many users joined via each link."
                ),
            )
        )
        cmds = [
            ("start", "Show help & all commands"),
            ("help", "Short usage guide"),
            ("start_demo", "Try limited demo mode"),
            ("login", "Login your Telegram account"),
            ("status", "Check login status"),
            ("logout", "Delete session & stop tracking"),
            ("create_link", "Create invite links for pinned chats"),
            ("links", "List your invite links"),
            ("remove_link", "Remove links & join data (with confirmation)"),
            ("stats", "Select link & show total joins"),
            ("hour_status", "Select link & joins last 1 hour"),
            ("today_status", "Select link & joins today"),
            ("week_status", "Select link & joins last 7 days"),
            ("month_status", "Select link & joins last 30 days"),
            
        ]
        await bot(
            functions.bots.SetBotCommandsRequest(
                scope=types.BotCommandScopeDefault(),
                lang_code="en",
                commands=[types.BotCommand(c, d) for c, d in cmds],
            )
        )
    except Exception as e:
        print("Profile/commands set error:", e)

# ---------------- RUN ----------------

async def main_async():
    """Single async entry point for the entire bot process."""
    global _sync_worker_started
    
    log_info("Initializing bot profile...")
    try:
        await setup_bot_profile()
        log_info("✅ Bot profile setup complete")
    except Exception as e:
        log_warning(f"Profile setup failed (non-critical): {e}")

    # Reattach real-time listeners for all active user sessions
    try:
        await start_listeners_for_all_users()
        log_info("✅ Real-time listeners attached for all active users")
    except Exception as e:
        log_warning(f"Listener attachment failed (non-critical): {e}")

    # Schedule background auto-sync task (runs every 20 hours)
    asyncio.create_task(auto_sync_loop())
    log_info("✅ Auto-sync loop scheduled (runs every 20 hours)")
    
    # Schedule daily 6 PM IST report
    asyncio.create_task(scheduled_report_loop())
    log_info("✅ Scheduled report loop active")

    # Ensure sync queue worker is running
    if not _sync_worker_started:
        _sync_worker_started = True
        asyncio.create_task(_sync_worker())
        log_info("✅ Sync queue worker started")

    log_info("🤖 Join Counter Bot ready! Starting main loop...")
    
    # Main bot loop will run forever until disconnected
    await bot.run_until_disconnected()


if __name__ == "__main__":
    import time
    
    # Auto-reconnect loop to prevent crashes
    retry_count = 0
    base_delay = 5  
    max_delay = 300 
    
    while True:
        try:
            # Single entry point: asyncio.run creates and manages its own loop
            asyncio.run(main_async())
            
            log_info("Bot disconnected. Reconnecting in 5 seconds...")
            time.sleep(5)
            continue
            
        except KeyboardInterrupt:
            log_info("🛑 Bot stopped by user (Ctrl+C)")
            break
            
        except Exception as e:
            retry_count += 1
            log_error(f"❌ Bot crashed: {type(e).__name__}: {e}", exc_info=True)
            
            delay = min(base_delay * (2 ** (retry_count - 1)), max_delay)
            log_info(f"🔄 Restarting bot in {delay} seconds... (attempt {retry_count})")
            time.sleep(delay)
    
    log_info("Bot shutdown complete.")

