import asyncio
import hashlib
import hmac
import json
import logging
import mimetypes
import os
import re
import shutil
import tempfile
import time
import traceback
import uuid
from pathlib import Path
from typing import Any, Optional
from urllib.parse import parse_qsl, quote

from dotenv import load_dotenv
from telethon import TelegramClient, events
from telethon.tl import functions, types
from telethon.errors import (
    AuthKeyUnregisteredError,
    FloodWaitError,
    SessionPasswordNeededError,
    PhoneNumberInvalidError,
    PhoneNumberBannedError,
    PhoneCodeInvalidError,
    PhoneCodeExpiredError,
    PasswordHashInvalidError,
    SendCodeUnavailableError,
)
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputFile, Update, WebAppInfo
from telegram.error import BadRequest, RetryAfter
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, TypeHandler, filters

load_dotenv()


def _required_env(name: str) -> str:
    value = os.getenv(name, "").strip()
    if not value:
        raise RuntimeError(
            f"متغير البيئة {name} مفقود أو فارغ. أضفه في إعدادات الاستضافة أو ملف .env ثم أعد تشغيل التطبيق."
        )
    return value


def _required_int_env(name: str) -> int:
    raw = _required_env(name)
    try:
        value = int(raw)
    except ValueError as exc:
        raise RuntimeError(
            f"متغير البيئة {name} يجب أن يكون رقماً صحيحاً فقط، لكن القيمة الحالية غير صالحة."
        ) from exc
    if value <= 0:
        raise RuntimeError(f"متغير البيئة {name} يجب أن يكون أكبر من صفر.")
    return value


logging.basicConfig(
    format="%(asctime)s [%(name)s] %(levelname)s: %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger("telegram_archiver")

API_ID = _required_int_env("TELEGRAM_API_ID")
API_HASH = _required_env("TELEGRAM_API_HASH")
BOT_TOKEN = _required_env("BOT_TOKEN")
OWNER_ID = _required_int_env("OWNER_ID")
SECOND_RECIPIENT = os.getenv("SECOND_RECIPIENT", "").strip()
DELETE_AFTER_SECONDS = 0
# لا تحذف رسائل الوسائط التي أرسلها البوت تلقائياً.
# يمكن استخدام حذف الرسائل يدوياً من Telegram أو من أدوات الإدارة الموجودة في البوت.
DELETE_SENT_MESSAGES = False
MAX_FILE_SIZE_MB = int(os.getenv("MAX_FILE_SIZE_MB", "1024"))
MAX_FILE_SIZE_BYTES = MAX_FILE_SIZE_MB * 1024 * 1024
DAILY_QUOTA = 5
REFERRAL_BONUS = 5
TRANSFER_REFERRAL_REQUIREMENT = 5
FORCE_SUB_CHANNEL = os.getenv("FORCE_SUB_CHANNEL", "").strip()
FORCE_SUB_URL = os.getenv("FORCE_SUB_URL", "").strip()
DOWNLOAD_TIMEOUT_SECONDS = int(os.getenv("DOWNLOAD_TIMEOUT_SECONDS", "1800"))
# مهلة نقل ملفات القنوات، بالثواني؛ الافتراضي ساعتان للملفات الكبيرة.
TRANSFER_MEDIA_TIMEOUT_SECONDS = int(os.getenv("TRANSFER_MEDIA_TIMEOUT_SECONDS", "7200"))
MIN_FREE_DISK_PERCENT = 15.0

# حدود التزامن: تمنع انهيار الأداء عندما يصل عدد المستخدمين/المهام إلى عشرات أو مئات.
# يمكن تعديلها من متغيرات البيئة حسب موارد الخادم.
# Conservative defaults for small containers. High concurrency is a common
# cause of exit 137 when several media downloads are active at once.
MEDIA_CONCURRENCY = max(1, min(3, int(os.getenv("MEDIA_CONCURRENCY", "2"))))
TRANSFER_CONCURRENCY = max(1, min(2, int(os.getenv("TRANSFER_CONCURRENCY", "1"))))

SESSION_DIR = Path(os.getenv("SESSION_DIR", "sessions"))
SESSION_DIR.mkdir(parents=True, exist_ok=True)
ARCHIVE_DIR = SESSION_DIR / "timed_message_archive"
ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
owner_session_ids: set[int] = set()
TRANSFER_STATE_PATH = SESSION_DIR / "channel_transfers.json"
ADMIN_STATE_PATH = SESSION_DIR / "admin_state.json"

admins: set[int] = {OWNER_ID}
user_registry: dict[str, dict[str, Any]] = {}


LANGUAGE_LABELS = {"ar": "العربية", "en": "English"}


def user_language(user_id: int) -> str:
    language = str(user_registry.get(str(user_id), {}).get("language", "ar")).lower()
    return language if language in {"ar", "en"} else "ar"


def localized(user_id: int, arabic: str, english: str) -> str:
    return english if user_language(user_id) == "en" else arabic


def set_user_language(user_id: int, language: str) -> None:
    entry = user_registry.setdefault(str(user_id), {"id": int(user_id)})
    entry["language"] = language if language in {"ar", "en"} else "ar"
    save_admin_state()


def load_admin_state() -> None:
    global admins, user_registry, FORCE_SUB_CHANNEL, FORCE_SUB_URL
    if not ADMIN_STATE_PATH.exists():
        return
    try:
        data = json.loads(ADMIN_STATE_PATH.read_text(encoding="utf-8"))
        admins = {OWNER_ID, *(int(value) for value in data.get("admins", []))}
        user_registry = {str(key): value for key, value in data.get("users", {}).items()}
        FORCE_SUB_CHANNEL = str(data.get("force_sub_channel", FORCE_SUB_CHANNEL) or "").strip()
        FORCE_SUB_URL = str(data.get("force_sub_url", FORCE_SUB_URL) or "").strip()
    except Exception:
        logger.exception("تعذر تحميل حالة المشرفين والمستخدمين")


def save_admin_state() -> None:
    temp_path = ADMIN_STATE_PATH.with_suffix(".tmp")
    temp_path.write_text(
        json.dumps({
            "admins": sorted(admins),
            "users": user_registry,
            "force_sub_channel": FORCE_SUB_CHANNEL,
            "force_sub_url": FORCE_SUB_URL,
        }, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    temp_path.replace(ADMIN_STATE_PATH)


def today_key() -> str:
    return time.strftime("%Y-%m-%d", time.gmtime())


def referral_id_from_args(args: list[str] | None) -> int | None:
    if not args:
        return None
    raw = str(args[0]).strip()
    if raw.startswith("ref_"):
        raw = raw[4:]
    try:
        value = int(raw)
    except ValueError:
        return None
    return value if value > 0 else None


def register_user(user, referral_id: int | None = None) -> None:
    if not user:
        return
    user_id = str(user.id)
    is_new = user_id not in user_registry
    entry = user_registry.setdefault(user_id, {})
    entry.setdefault("daily_date", today_key())
    entry.setdefault("daily_used", 0)
    entry.setdefault("bonus_credits", 0)
    entry.setdefault("referral_count", 0)
    entry.setdefault("referred_by", None)
    entry.setdefault("referral_processed", False)
    entry.setdefault("mini_app_access", False)
    # صلاحية مستقلة يمكن للمالك منحها دون تحويل المستخدم إلى مشرف.
    entry.setdefault("channel_transfer_access", False)
    entry.setdefault("language", "ar")
    entry.setdefault("blocked_until", 0)
    entry.setdefault("downloads_count", 0)
    entry.setdefault("timed_archive_granted", False)
    entry.setdefault("timed_archive_enabled", False)
    entry.setdefault("timed_archive_consent_at", 0)
    entry.update({
        "id": int(user.id),
        "name": getattr(user, "full_name", "") or "",
        "username": getattr(user, "username", "") or "",
        "last_seen": int(time.time()),
    })
    # تعالج الإحالة الصالحة مرة واحدة فقط لكل مستخدم، حتى لو ضغط الرابط مراراً.
    if (referral_id and not entry.get("referral_processed")
            and referral_id != int(user.id) and str(referral_id) in user_registry):
        entry["referral_processed"] = True
        referrer = user_registry[str(referral_id)]
        entry["referred_by"] = int(referral_id)
        referrer["referral_count"] = int(referrer.get("referral_count", 0)) + 1
        referrer["bonus_credits"] = int(referrer.get("bonus_credits", 0)) + REFERRAL_BONUS
    save_admin_state()


def quota_snapshot(user_id: int) -> dict[str, int]:
    entry = user_registry.setdefault(str(user_id), {"id": int(user_id)})
    if entry.get("daily_date") != today_key():
        entry["daily_date"] = today_key()
        entry["daily_used"] = 0
        save_admin_state()
    used = int(entry.get("daily_used", 0))
    bonus = int(entry.get("bonus_credits", 0))
    return {
        "daily_remaining": max(0, DAILY_QUOTA - used),
        "bonus_credits": max(0, bonus),
        "total_remaining": max(0, DAILY_QUOTA - used) + max(0, bonus),
        "referral_count": int(entry.get("referral_count", 0)),
    }


def consume_quota(user_id: int) -> bool:
    entry = user_registry.setdefault(str(user_id), {"id": int(user_id)})
    quota_snapshot(user_id)
    if int(entry.get("daily_used", 0)) < DAILY_QUOTA:
        entry["daily_used"] = int(entry.get("daily_used", 0)) + 1
    elif int(entry.get("bonus_credits", 0)) > 0:
        entry["bonus_credits"] = int(entry.get("bonus_credits", 0)) - 1
    else:
        return False
    save_admin_state()
    return True


def timed_archive_enabled(user_id: int) -> bool:
    entry = user_registry.get(str(user_id), {})
    return bool(entry.get("timed_archive_granted") and entry.get("timed_archive_enabled"))


def is_timed_message(message) -> bool:
    media = getattr(message, "media", None)
    ttl = getattr(media, "ttl_seconds", None) if media else None
    # Telegram Bot API لا يرسل مدة الاختفاء في بعض صور الرسائل المؤقتة.
    # بعد موافقة المستخدم، تعامل الأرشفة مع كل وسيط وارد منه كرسالة موقوتة.
    return bool(ttl or getattr(message, "ttl_period", None) or getattr(message, "ttl_seconds", None) or getattr(message, "media", None))


def timed_archive_files(user_id: int) -> list[Path]:
    root = ARCHIVE_DIR / str(user_id)
    return sorted(root.glob("*")) if root.exists() else []


def timed_archive_keyboard(user_id: int) -> InlineKeyboardMarkup:
    enabled = timed_archive_enabled(user_id)
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("⏹️ إيقاف الأرشفة" if enabled else "▶️ تفعيل الأرشفة", callback_data="user:archive_toggle")],
        [InlineKeyboardButton("🗑️ حذف أرشيفي", callback_data="user:archive_delete")],
        [InlineKeyboardButton("⬅️ رجوع", callback_data="user:account")],
    ])


async def archive_timed_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    if not message or not user or not is_timed_message(message) or not timed_archive_enabled(user.id):
        return
    if not getattr(message, "media", None):
        return
    root = ARCHIVE_DIR / str(user.id)
    root.mkdir(parents=True, exist_ok=True)
    original = (
        getattr(getattr(message, "document", None), "file_name", None)
        or getattr(getattr(message, "video", None), "file_name", None)
        or ("timed_photo.jpg" if getattr(message, "photo", None) else None)
        or ("timed_animation.gif" if getattr(message, "animation", None) else None)
        or "timed_message.bin"
    )
    safe_name = re.sub(r"[^\w.\- ]+", "_", str(original)).strip() or "timed_message.bin"
    destination = root / f"{int(time.time())}_{message.message_id}_{safe_name}"
    try:
        await message.download_to_drive(custom_path=str(destination))
        meta = destination.with_suffix(destination.suffix + ".json")
        meta.write_text(json.dumps({
            "user_id": user.id, "message_id": message.message_id,
            "saved_at": int(time.time()), "caption": message.caption or "",
            "filename": destination.name,
        }, ensure_ascii=False), encoding="utf-8")
        await message.reply_text("✅ تمت أرشفة الرسالة الموقوتة بناءً على تفعيلك للميزة.")
    except Exception:
        logger.exception("تعذر أرشفة الرسالة الموقوتة للمستخدم %s", user.id)


def record_download_success(user_id: int) -> None:
    entry = user_registry.setdefault(str(user_id), {"id": int(user_id)})
    entry["downloads_count"] = int(entry.get("downloads_count", 0) or 0) + 1
    entry["last_download_at"] = int(time.time())
    save_admin_state()


def is_user_blocked(user_id: int) -> bool:
    return int(user_registry.get(str(user_id), {}).get("blocked_until", 0) or 0) > int(time.time())


def blocked_message(user_id: int) -> str:
    remaining = max(1, int(user_registry.get(str(user_id), {}).get("blocked_until", 0) or 0) - int(time.time()))
    return f"🚫 تم إيقاف حسابك مؤقتاً. حاول بعد {remaining // 3600} ساعة و{(remaining % 3600) // 60} دقيقة."


async def is_force_subscribed(context: ContextTypes.DEFAULT_TYPE, user_id: int) -> bool:
    subscribed, _ = await force_subscription_status(context, user_id)
    return subscribed


async def force_subscription_status(context: ContextTypes.DEFAULT_TYPE, user_id: int) -> tuple[bool, str]:
    if user_id == OWNER_ID or not FORCE_SUB_CHANNEL:
        return True, "disabled_or_owner"
    try:
        chat_ref = int(FORCE_SUB_CHANNEL) if re.fullmatch(r"-100\d+", FORCE_SUB_CHANNEL) else FORCE_SUB_CHANNEL
        member = await context.bot.get_chat_member(chat_ref, user_id)
        subscribed = member.status in {"creator", "administrator", "member"} or (
            member.status == "restricted" and bool(getattr(member, "is_member", False))
        )
        return subscribed, str(member.status)
    except Exception:
        logger.exception("تعذر فحص الاشتراك الإجباري للمستخدم %s", user_id)
        return False, "تعذر الوصول إلى القناة. تأكد أن البوت عضو أو مشرف فيها وأن معرف القناة صحيح."


def admin_only(update: Update) -> bool:
    return bool(update.effective_user and update.effective_user.id in admins)


load_admin_state()

LINK_PATTERN = re.compile(
    r"https?://t\.me/(?:(?P<private>c)/(?P<private_id>\d+)/|(?P<username>[A-Za-z0-9_]+)/)(?P<message_id>\d+)"
)

# حالة كل مستخدم داخل الذاكرة: الهاتف، رمز الجلسة، والعميل الخاص به.
clients: dict[int, TelegramClient] = {}
public_client: TelegramClient | None = None
public_client_lock = asyncio.Lock()
states: dict[int, dict[str, Any]] = {}
# رابط بانتظار اختيار المستخدم، بدلاً من وضع الرابط كاملاً داخل callback_data.
pending_downloads: dict[int, tuple[str, float, Any]] = {}

# =========================
# Telegram Mini App Web UI
# =========================
FASTAPI_WEB_ENABLED = True
WEB_HOST = "0.0.0.0"
# JustRunMy يحدد المنفذ عبر PORT؛ نستخدم 8080 كقيمة احتياطية.
WEB_PORT = int(os.getenv("PORT", "8080"))
# الرابط العام الذي يفتحه زر Telegram Mini App. يمكن تغييره من البيئة.
WEB_PUBLIC_BASE_URL = os.getenv("WEB_PUBLIC_BASE_URL", "https://telebot-qk9v.onrender.com").rstrip("/")

# Telegram يوصي برفض initData القديمة. نسمح بحد أقصى 24 ساعة.
TELEGRAM_WEBAPP_INIT_DATA_MAX_AGE = 86400

# Web dependencies must be installed by the hosting platform from requirements.txt.
# Never run pip during application startup: it can consume the container memory and
# cause the process to be killed before the bot starts.
try:
    from fastapi import FastAPI, HTTPException, Query
    from fastapi.responses import HTMLResponse, StreamingResponse, JSONResponse, FileResponse
    from pydantic import BaseModel
    import uvicorn
except ImportError:
    logger.exception(
        "FastAPI/Uvicorn غير مثبتين. ثبتهما أثناء Build من requirements.txt "
        "ثم أعد تشغيل التطبيق. لن يتم تثبيتهما أثناء التشغيل."
    )
    FastAPI = None

WEB_HTML = r"""<!doctype html>
<html lang="ar" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>Telegram Mini App</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
:root{--bg:#0e1621;--panel:#17212b;--panel2:#202b36;--line:#2a3948;--blue:#2aabee;--bubble:#182533;--out:#2b5275}
*{box-sizing:border-box}html,body{margin:0;width:100%;height:100%;overflow:hidden;font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;background:var(--bg);color:#f2f5f8}
.app{display:flex;width:100vw;height:100dvh;min-height:560px;background:var(--bg)}
.side{flex:0 0 380px;border-left:1px solid var(--line);background:var(--panel);display:flex;flex-direction:column;box-shadow:-5px 0 24px #0002;z-index:2}
.main{flex:1;display:flex;flex-direction:column;min-width:0;background:linear-gradient(#101a25,#0e1722)}
.top{height:72px;flex:0 0 72px;border-bottom:1px solid var(--line);display:flex;align-items:center;padding:0 24px;gap:14px;background:#17232e}
h2,h3{margin:0}.top h3{font-size:18px}.search{margin:14px 18px}.search input,.composer input{width:100%;background:#0e1823;border:1px solid #314456;color:#fff;border-radius:12px;padding:13px 15px;font-size:14px;outline:none}.search input:focus,.composer input:focus{border-color:var(--blue);box-shadow:0 0 0 2px #2aabee22}
.sessions{overflow:auto;flex:1}.dialogs{overflow-x:auto;overflow-y:hidden;flex:0 0 112px;display:flex;padding:0 16px 12px;gap:8px;border-bottom:1px solid var(--line);scrollbar-width:thin}
.item{padding:14px 16px;border-bottom:1px solid #253442;cursor:pointer;transition:.15s;background:transparent}.sessions .item{min-height:72px}.dialogs .item{flex:0 0 230px;min-height:82px;border:1px solid #2b3b4a;border-radius:12px;background:#182532}.item:hover,.item.active{background:#263849;border-color:#3d7599}.dialogs .item.active{background:#21425b;border-color:var(--blue)}
.badge{font-size:11px;padding:4px 8px;border-radius:10px;background:#2b4054}.green{color:#65e59b}.muted{color:#91a4b7;font-size:12px}.title{font-weight:700;font-size:15px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.small{font-size:13px}
.messages{flex:1;min-height:0;overflow:auto;padding:24px clamp(18px,4vw,70px);display:flex;flex-direction:column;gap:9px;background-image:radial-gradient(#203142 1px,transparent 1px);background-size:22px 22px}
.session-view .side{display:none}.session-view .main,.chat-view .main{width:100%}.session-view .dialogs{display:flex;flex:1;flex-direction:column;overflow:auto;padding:0}.session-view .dialogs .item{width:100%;flex:0 0 auto;min-height:78px;border:0;border-bottom:1px solid #253442;border-radius:0;background:transparent;padding:17px 28px}.session-view .dialogs .item:hover,.session-view .dialogs .item.active{background:#263849}.session-view #backBtn,.chat-view #backBtn{display:block!important}.chat-view .dialogs{display:none}.messages,.composer,#olderWrap{display:none}.chat-view .messages,.chat-view .composer{display:flex}.chat-view #olderWrap{display:block}
.msg{max-width:min(780px,78%);background:var(--bubble);border:1px solid #25394b;border-radius:15px 15px 15px 5px;padding:13px 16px;align-self:flex-start;box-shadow:0 2px 5px #0002;line-height:1.55;font-size:14px}.msg.out{align-self:flex-end;background:var(--out);border-radius:15px 15px 5px 15px}.meta{font-size:11px;color:#a4b7c8;margin-top:7px;opacity:.85}
.media{margin-top:10px}.media img,.media video{display:block;max-width:min(620px,100%);width:auto;border-radius:12px;max-height:440px;object-fit:cover}.file{display:inline-block;padding:10px;background:#111c27;border-radius:10px;color:#fff;text-decoration:none}
.composer{display:flex;gap:10px;padding:14px 22px;border-top:1px solid var(--line);background:#17232e}.composer input{flex:1}.btn{border:0;background:var(--blue);color:white;border-radius:10px;padding:11px 17px;cursor:pointer;font-weight:600}.btn.alt{background:#2a3948}.btn:hover{filter:brightness(1.12)}
.transfer-panel{display:none;position:fixed;z-index:5;left:50%;top:50%;transform:translate(-50%,-50%);width:min(420px,90vw);max-height:75vh;overflow:auto;flex-direction:column;gap:10px;padding:20px;border:1px solid #466277;border-radius:16px;background:#17232e;box-shadow:0 10px 50px #000b}.transfer-panel .btn{width:100%;text-align:right}
.empty{padding:34px;text-align:center;color:#93a5b7}.row{display:flex;gap:8px;align-items:center}.auth-error{padding:32px;text-align:center}.auth-error h3{margin-bottom:10px}
@media(max-width:900px){.side{flex-basis:310px}.msg{max-width:86%}.top{padding:0 18px}}
@media(max-width:650px){.app{display:block;min-height:0}.side{width:100%;height:100dvh;min-height:0;border-left:0;border-bottom:0}.main{height:100dvh}.top{height:58px;flex-basis:58px}.messages{padding:18px 12px}.msg{max-width:94%}.composer{padding:10px}.search{margin:9px 12px}}
</style>
</head>
<body>
<div class="app">
  <aside class="side">
    <div class="top"><h3>📱 حساب Telegram</h3></div>
    <div class="search"><input id="sessionSearch" placeholder="بحث في الجلسة..." oninput="filterSessions()"></div>
    <div id="sessions" class="sessions"><div class="empty">جاري التحقق من Telegram...</div></div>
  </aside>
  <main class="main">
    <div class="top">
      <button id="backBtn" class="btn alt" onclick="goBack()" style="display:none">‹ رجوع</button>
      <div style="flex:1"><div id="chatTitle" class="title">اختر جلسة</div><div id="chatSub" class="muted">اختر حساباً لعرض المحادثات</div></div>
      <button id="transferChatBtn" class="btn alt" onclick="showChatTransferPicker()" style="display:none">🔁 نقل المحادثة</button>
      <button id="pinChatBtn" class="btn alt" onclick="togglePinChat()" style="display:none">📌 تثبيت</button>
      <button id="muteChatBtn" class="btn alt" onclick="toggleMuteChat()" style="display:none">🔕 كتم</button>
      <button id="archiveChatBtn" class="btn alt" onclick="toggleArchiveChat()" style="display:none">🗃️ أرشفة</button>
      <button class="btn alt" onclick="showTimedArchive()">🕘 الأرشيف الموقوت</button>
      <button class="btn alt" onclick="loadDialogs()">🔄 تحديث المحادثات</button>
    </div>
    <div class="search"><input id="chatSearch" placeholder="🔎 بحث داخل المحادثات أو الرسائل..." onkeydown="if(event.key==='Enter') searchMessages()"></div>
    <div id="dialogs" class="dialogs"></div>
    <div id="messages" class="messages"><div class="empty">اختر محادثة لعرض الرسائل والصور والفيديو والملفات.</div></div>
    <div id="olderWrap" style="padding:6px 12px;text-align:center"><button id="olderBtn" class="btn alt" onclick="loadOlder()" style="display:none">⬇️ رسائل أقدم</button></div>
    <div id="composer" class="composer">
      <input id="message" placeholder="اكتب رسالة..." onkeydown="if(event.key==='Enter') sendMessage()">
      <button class="btn" onclick="sendMessage()">إرسال</button>
    </div>
  </main>
</div>
<div id="transferPanel" class="transfer-panel"></div>
<script>
const tg = window.Telegram && window.Telegram.WebApp ? window.Telegram.WebApp : null;
const initData = tg ? (tg.initData || "") : "";
let sessions=[], currentSession=null, currentChat=null, sessionFilter='', oldestMessageId=0, currentChatMeta={};
const $=id=>document.getElementById(id);

if(tg){
  tg.ready();
  tg.expand();
  if(tg.setHeaderColor) tg.setHeaderColor('#10151d');
  if(tg.setBackgroundColor) tg.setBackgroundColor('#10151d');
}

function authUrl(path){
  const join = path.includes('?') ? '&' : '?';
  return path + join + 'init_data=' + encodeURIComponent(initData);
}

async function api(path, opts={}) {
  if(!initData) throw new Error('يجب فتح هذه الصفحة من داخل Telegram Mini App.');
  const url = authUrl(path);
  const r=await fetch(url,opts);
  if(!r.ok) throw new Error(await r.text());
  return r.json();
}

async function init(){
  if(!tg || !initData){
    $('sessions').innerHTML='<div class="auth-error"><h3>⚠️ يجب فتح Mini App من Telegram</h3><div class="muted">افتح الواجهة من زر Telegram Mini App داخل البوت.</div></div>';
    return;
  }
  try{
    sessions=await api('/api/sessions');
    renderSessions();
    if(sessions.length){
      currentSession=sessions[0].id;
      renderSessions();
      try{ await loadDialogs(); }
      catch(e){ $('dialogs').innerHTML='<div class="auth-error"><div class="muted">تعذر تحميل محادثات هذه الجلسة: '+esc(e.message)+'</div></div>'; }
    } else {
      $('dialogs').innerHTML='<div class="empty">لا توجد جلسات Telegram مسجلة وصالحة.</div>';
    }
  }catch(e){
    $('sessions').innerHTML='<div class="auth-error"><h3>⚠️ تعذر المصادقة</h3><div class="muted">'+esc(e.message)+'</div></div>';
    $('dialogs').innerHTML=''; $('messages').innerHTML='';
  }
}
function renderSessions(){
  $('sessions').innerHTML='';
  sessions.filter(s=>(s.name+' '+s.username).toLowerCase().includes(sessionFilter.toLowerCase())).forEach(s=>{
    const d=document.createElement('div'); d.className='item '+(s.id===currentSession?'active':'');
    d.innerHTML=`<div class="row"><b>${esc(s.name||'حساب')}</b><span class="badge">${s.connected?'🟢 متصل':'🔴 غير متصل'}</span></div><div class="muted">@${esc(s.username||'')} · ${s.id}</div>`;
    d.onclick=()=>selectSession(s.id,d); $('sessions').appendChild(d);
  });
}
function filterSessions(){sessionFilter=$('sessionSearch').value;renderSessions()}
function showView(view){
  const side=document.querySelector('.side');
  side.style.display=view==='sessions'?'flex':'none';
  $('dialogs').style.display=view==='chat'?'none':'flex';
  $('messages').style.display=view==='chat'?'flex':'none';
  $('composer').style.display=view==='chat'?'flex':'none';
  $('olderWrap').style.display=view==='chat'?'block':'none';
  $('backBtn').style.display=view==='sessions'?'none':'block';
}
async function selectSession(id,el){
  currentSession=id;
  showView('dialogs');
  document.body.classList.add('session-view');document.body.classList.remove('chat-view');
  currentChat=null; document.querySelectorAll('.item').forEach(x=>x.classList.remove('active'));el.classList.add('active');
  $('chatTitle').textContent='محادثات الحساب'; $('chatSub').textContent='الجلسة #'+id; $('messages').innerHTML='<div class="empty">اختر محادثة.</div>';
  try{ await loadDialogs(); }
  catch(e){ $('dialogs').innerHTML='<div class="auth-error"><div class="muted">تعذر تحميل محادثات هذه الجلسة: '+esc(e.message)+'</div></div>'; }
}
async function loadDialogs(){
 if(!currentSession)return;
 const q=$('chatSearch').value||'';
 const ds=await api('/api/sessions/'+currentSession+'/dialogs?search='+encodeURIComponent(q));
 $('dialogs').innerHTML='';
 ds.forEach(d=>{
   const x=document.createElement('div');x.className='item';
   x.innerHTML=`<div class="title">💬 ${esc(d.title)}</div><div class="muted">${esc(d.type)} · ${d.unread||0} غير مقروء</div>`;
   x.onclick=()=>openChat(d.id,d.title);$('dialogs').appendChild(x);
 });
}
async function openChat(id,title){
 currentChat=id; showView('chat'); document.body.classList.remove('session-view');document.body.classList.add('chat-view'); $('transferChatBtn').style.display='inline-block'; oldestMessageId=0; $('olderBtn').style.display='none'; $('chatTitle').textContent=title;$('chatSub').textContent='تحميل الرسائل...'; updateChatControls();
 try{
   const ms=await api(`/api/sessions/${currentSession}/chats/${id}/messages?limit=30`); renderMessages(ms);
   if(ms.length>=30){oldestMessageId=ms[ms.length-1].id;$('olderBtn').style.display='inline-block';}
   $('chatSub').textContent=ms.length+' رسالة معروضة'; await loadChatMeta();
 }catch(e){
   $('messages').innerHTML='<div class="auth-error"><h3>⚠️ تعذر فتح هذه المحادثة</h3><div class="muted">'+esc(friendlyError(e))+'</div><br><button class="btn alt" onclick="openChat(currentChat, document.getElementById(\'chatTitle\').textContent)">إعادة المحاولة</button></div>';
   $('chatSub').textContent='تعذر التحميل — بقيت داخل المحادثة';
 }
}
function friendlyError(e){
 try{const x=JSON.parse(e.message);if(x.detail)return x.detail;}catch(_){ }
 return e.message||'حدث خطأ غير معروف أثناء تحميل المحادثة.';
}
function goBack(){
 if(document.body.classList.contains('chat-view')){
   $('transferChatBtn').style.display='none';['pinChatBtn','muteChatBtn','archiveChatBtn'].forEach(id=>$(id).style.display='none');showView('dialogs');document.body.classList.remove('chat-view');document.body.classList.add('session-view');currentChat=null;$('chatTitle').textContent='محادثات الحساب';$('chatSub').textContent='الجلسة #'+currentSession;
 }else if(document.body.classList.contains('session-view')){
   showView('sessions');document.body.classList.remove('session-view');currentSession=null;$('chatTitle').textContent='اختر جلسة';$('chatSub').textContent='اختر حساباً لعرض المحادثات';$('dialogs').innerHTML='';
 }
}
async function loadOlder(){
 if(!currentSession||!currentChat||!oldestMessageId)return;
 const btn=$('olderBtn');btn.disabled=true;btn.textContent='جاري التحميل...';
 try{const ms=await api(`/api/sessions/${currentSession}/chats/${currentChat}/messages?limit=30&offset_id=${oldestMessageId}`);
   if(ms.length){oldestMessageId=ms[ms.length-1].id;appendMessages(ms);} else btn.style.display='none';
   if(ms.length<30)btn.style.display='none';
 }finally{btn.disabled=false;btn.textContent='⬇️ رسائل أقدم';}
}
async function searchMessages(){
 if(!currentSession)return;
 if(currentChat){ const q=$('chatSearch').value||''; const ms=await api(`/api/sessions/${currentSession}/chats/${currentChat}/search?q=`+encodeURIComponent(q));renderMessages(ms); }
 else await loadDialogs();
}
function renderMessages(ms){
 $('messages').innerHTML='';
 ms.slice().reverse().forEach(m=>{
   const x=document.createElement('div');x.className='msg '+(m.out?'out':'');
   let media='';
     if(m.media){
     const preview=authUrl(m.media.preview_url), download=authUrl(m.media.download_url);
     if(m.media.kind==='image' || m.media.kind==='video') media=`<div class="media"><img src="${esc(preview)}" loading="lazy" alt="معاينة"><br><button class="btn" onclick="sendMediaToBot(${m.id})">📥 إرسال إلى شات البوت</button></div>`;
     else media=`<div class="media"><button class="btn" onclick="sendMediaToBot(${m.id})">📥 إرسال الملف إلى شات البوت</button></div>`;
   }
   const who=m.sender_username?('@'+m.sender_username):((m.sender||'')+' '+(m.sender_id?'· ID '+m.sender_id:''));    const actions=`<div class="row" style="margin-top:8px;flex-wrap:wrap"><button class="btn alt" onclick="replyToMessage(${m.id})">↩️ رد</button>${m.out?`<button class="btn alt" onclick="editMessage(${m.id},${JSON.stringify(m.text||'')})">✏️ تعديل</button><button class="btn alt" onclick="deleteMessage(${m.id})">🗑️ حذف</button>`:''}</div>`;
    x.innerHTML=`<div>${esc(m.text||'')}</div>${media}<div class="meta">${esc(m.date||'')} ${who? '· '+esc(who):''}</div>${actions}`;
   $('messages').appendChild(x);
 });
 $('messages').scrollTop=$('messages').scrollHeight;
}
function appendMessages(ms){
 const box=$('messages'); const oldHeight=box.scrollHeight;
 ms.slice().reverse().forEach(m=>{
   const x=document.createElement('div');x.className='msg '+(m.out?'out':'');
   let media=''; if(m.media){const p=authUrl(m.media.preview_url),d=authUrl(m.media.download_url);media=(m.media.kind==='image'||m.media.kind==='video')?`<div class="media"><img src="${esc(p)}" loading="lazy"><br><button class="btn" onclick="sendMediaToBot(${m.id})">📥 إرسال إلى شات البوت</button></div>`:`<div class="media"><button class="btn" onclick="sendMediaToBot(${m.id})">📥 إرسال الملف إلى شات البوت</button></div>`;}
   const who=m.sender_username?('@'+m.sender_username):((m.sender||'')+' '+(m.sender_id?'· ID '+m.sender_id:''));
   const actions=`<div class="row" style="margin-top:8px;flex-wrap:wrap"><button class="btn alt" onclick="replyToMessage(${m.id})">↩️ رد</button>${m.out?`<button class="btn alt" onclick="editMessage(${m.id},${JSON.stringify(m.text||'')})">✏️ تعديل</button><button class="btn alt" onclick="deleteMessage(${m.id})">🗑️ حذف</button>`:''}</div>`;
   x.insertAdjacentHTML('beforeend',`<div>${esc(m.text||'')}</div>${media}<div class="meta">${esc(m.date||'')} ${who?'· '+esc(who):''}</div>${actions}`);box.insertBefore(x,box.firstChild);
 }); box.scrollTop=box.scrollHeight-oldHeight;
}
async function sendMessage(){
 if(!currentSession||!currentChat)return;
 const inp=$('message'), text=inp.value.trim();if(!text)return;
 await api(`/api/sessions/${currentSession}/chats/${currentChat}/send`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({text})});
 inp.value='';await openChat(currentChat,$('chatTitle').textContent);
}

function updateChatControls(){
  const show=!!currentChat;
  ['pinChatBtn','muteChatBtn','archiveChatBtn'].forEach(id=>$(id).style.display=show?'inline-block':'none');
  if(show){
    $('pinChatBtn').textContent=currentChatMeta.pinned?'📌 إلغاء التثبيت':'📌 تثبيت';
    $('muteChatBtn').textContent=currentChatMeta.muted?'🔔 إلغاء الكتم':'🔕 كتم';
    $('archiveChatBtn').textContent=currentChatMeta.archived?'📂 إلغاء الأرشفة':'🗃️ أرشفة';
  }
}
async function loadChatMeta(){
  if(!currentSession||!currentChat)return;
  try{
    currentChatMeta=await api(`/api/sessions/${currentSession}/chats/${currentChat}/meta`);
    updateChatControls();
  }catch(_){}
}
async function togglePinChat(){
  try{const r=await api(`/api/sessions/${currentSession}/chats/${currentChat}/pin`,{method:'POST'});currentChatMeta.pinned=r.pinned;updateChatControls();}
  catch(e){alert('تعذر تغيير التثبيت: '+friendlyError(e));}
}
async function toggleMuteChat(){
  try{const r=await api(`/api/sessions/${currentSession}/chats/${currentChat}/mute`,{method:'POST'});currentChatMeta.muted=r.muted;updateChatControls();}
  catch(e){alert('تعذر تغيير الكتم: '+friendlyError(e));}
}
async function toggleArchiveChat(){
  try{const r=await api(`/api/sessions/${currentSession}/chats/${currentChat}/archive`,{method:'POST'});currentChatMeta.archived=r.archived;updateChatControls();alert(r.archived?'✅ تمت أرشفة المحادثة':'✅ تمت إعادة المحادثة من الأرشيف');}
  catch(e){alert('تعذر تغيير الأرشفة: '+friendlyError(e));}
}
async function showChatTransferPicker(){
 try{
  const channels=await api('/api/owner/channels');
  if(!channels.length){alert('لا توجد قنوات مملوكة للمالك كقناة هدف.');return;}
  $('transferPanel').innerHTML='<b>اختر الجهة الهدف لنقل محتوى المحادثة</b>'+channels.map(c=>`<button class="btn alt" onclick="transferChat(${c.id},'${c.kind}')">${c.kind==='user'?'👤':'📣'} ${esc(c.title)}</button>`).join('')+'<button class="btn" onclick="$(\'transferPanel\').style.display=\'none\'">إلغاء</button>';
  $('transferPanel').style.display='flex';
 }catch(e){alert('تعذر تحميل قنوات الهدف: '+friendlyError(e));}
}
async function transferChat(targetId,targetKind){
 $('transferPanel').innerHTML='📤 يتم تنزيل المحتوى إلى السيرفر ثم رفعه إلى القناة الهدف...';
 try{const r=await api(`/api/sessions/${currentSession}/chats/${currentChat}/transfer-all`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({target_id:targetId,target_kind:targetKind})});pollTransfer(r.job_id);}
 catch(e){$('transferPanel').innerHTML='❌ فشل النقل: '+esc(friendlyError(e));}
}
async function pollTransfer(jobId){
 $('transferPanel').innerHTML='<b>نقل المحادثة جارٍ</b><div id="transferStatus">جاري البدء...</div><button class="btn alt" onclick="toggleTransfer(\''+jobId+'\')">⏸️ إيقاف مؤقت / متابعة</button><button class="btn" onclick="stopTransfer(\''+jobId+'\')">⏹️ إيقاف نهائي</button>';
 const tick=async()=>{try{const j=await api('/api/transfer-jobs/'+jobId);const s=$('transferStatus');if(s)s.textContent=`الحالة: ${j.status} | تم نقل: ${j.sent} | فشل: ${j.failed} | تمت معالجة: ${j.current}`;if(!['done','failed','stopped'].includes(j.status))setTimeout(tick,2000);else if(s)s.textContent+=j.error?' | '+j.error:' | اكتمل النقل';}catch(e){}}
 tick();
}
async function toggleTransfer(jobId){await api('/api/transfer-jobs/'+jobId+'/pause',{method:'POST'});}
async function stopTransfer(jobId){await api('/api/transfer-jobs/'+jobId+'/stop',{method:'POST'});$('transferPanel').style.display='none';}
async function showTimedArchive(){
  try{
    const items=await api('/api/owner/timed-archive');
    $('transferPanel').innerHTML='<b>🕘 أرشيف الرسائل ذاتية الاختفاء</b>'+
      (items.length?`<div style="margin:10px 0" class="muted">حدد العناصر التي تريد حذفها:</div>
      <div style="max-height:48vh;overflow:auto">${items.map(x=>`<label class="item" style="display:flex;gap:10px;align-items:center;border:1px solid #2b3b4a;border-radius:10px;margin:6px 0;padding:10px">
      <input type="checkbox" class="archive-check" value="${esc(x.session_id+'|'+x.name)}">
      <span style="flex:1">${esc(x.name)}<div class="muted">${Math.ceil(x.size/1024)} KB</div></span>
      <button class="btn alt" onclick="sendArchiveToBot(${x.session_id},${JSON.stringify(x.name)})">📤</button>
      </label>`).join('')}</div>
      <button class="btn" onclick="deleteSelectedArchive()">🗑️ حذف المحدد</button>
      <button class="btn alt" onclick="showTimedArchive()">🔄 تحديث</button>`
      :'<div class="empty">لا توجد رسائل موقوتة محفوظة بعد.</div>')+
      '<button class="btn alt" onclick="$(\'transferPanel\').style.display=\'none\'">إغلاق</button>';
    $('transferPanel').style.display='flex';
  }catch(e){alert('تعذر فتح الأرشيف: '+friendlyError(e));}
}
async function deleteSelectedArchive(){
  const selected=[...document.querySelectorAll('.archive-check:checked')].map(x=>x.value);
  if(!selected.length){alert('اختر ملفاً واحداً على الأقل.');return;}
  if(!confirm('هل تريد حذف العناصر المحددة نهائياً؟')) return;
  try{await api('/api/owner/timed-archive/delete',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({items:selected})});showTimedArchive();}
  catch(e){alert('تعذر حذف الأرشيف: '+friendlyError(e));}
}
async function sendArchiveToBot(sessionId,name){
  try{await api(`/api/owner/timed-archive/send-to-bot/${sessionId}/${encodeURIComponent(name)}`,{method:'POST'});alert('✅ تم إرسال الملف إلى شات البوت.');}
  catch(e){alert('تعذر إرسال الملف: '+friendlyError(e));}
}
async function sendMediaToBot(messageId){
  if(!currentSession||!currentChat)return;
  try{await api(`/api/sessions/${currentSession}/chats/${currentChat}/media/${messageId}/send-to-bot`,{method:'POST'});alert('✅ تم إرسال المحتوى إلى شات البوت.');}
  catch(e){alert('تعذر إرسال المحتوى: '+friendlyError(e));}
}
async function replyToMessage(messageId){
  const text=prompt('اكتب الرد:'); if(!text||!text.trim())return;
  await api(`/api/sessions/${currentSession}/chats/${currentChat}/reply`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({message_id:messageId,text:text.trim()})});
  await openChat(currentChat,$('chatTitle').textContent);
}
async function editMessage(messageId,currentText){
  const text=prompt('تعديل الرسالة:',currentText||''); if(text===null||!text.trim())return;
  await api(`/api/sessions/${currentSession}/chats/${currentChat}/edit`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({message_id:messageId,text:text.trim()})});
  await openChat(currentChat,$('chatTitle').textContent);
}
async function deleteMessage(messageId){
  if(!confirm('حذف هذه الرسالة؟'))return;
  await api(`/api/sessions/${currentSession}/chats/${currentChat}/delete`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({message_id:messageId})});
  await openChat(currentChat,$('chatTitle').textContent);
}
function esc(s){return String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
init();
</script>
</body></html>"""

if FastAPI:
    web_app = FastAPI(title="Telegram Mini App")

    @web_app.exception_handler(Exception)
    async def web_unhandled_exception(request, exc):
        await report_error_to_owner(
            "استثناء غير معالج في خادم Mini App",
            exc,
            f"{request.method} {request.url}",
        )
        return JSONResponse(
            status_code=500,
            content={"detail": f"Internal Server Error: {type(exc).__name__}: {str(exc)[:700]}"},
        )

    class SendBody(BaseModel):
        text: str

    class TransferBody(BaseModel):
        message_id: int
        target_id: int

    class TransferAllBody(BaseModel):
        target_id: int
        target_kind: str = "channel"

    class ArchiveDeleteBody(BaseModel):
        items: list[str]

    class MessageActionBody(BaseModel):
        message_id: int
        text: str = ""

    async def _authorized_user(init_data: str = Query("")) -> int:
        """تحقق رسمي من Telegram WebApp initData وتعيد Telegram user_id."""
        if not init_data or not init_data.strip():
            raise HTTPException(401, "initData مطلوب. افتح الواجهة من داخل Telegram Mini App.")

        try:
            pairs = dict(parse_qsl(init_data, keep_blank_values=True, strict_parsing=True))
        except ValueError as exc:
            raise HTTPException(401, "initData غير صالح") from exc

        received_hash = pairs.pop("hash", "")
        if not received_hash:
            raise HTTPException(401, "hash غير موجود في initData")

        try:
            auth_date = int(pairs.get("auth_date", "0"))
        except (TypeError, ValueError) as exc:
            raise HTTPException(401, "auth_date غير صالح") from exc

        now = int(time.time())
        if auth_date <= 0 or auth_date > now + 60:
            raise HTTPException(401, "auth_date غير صالح")
        if now - auth_date > TELEGRAM_WEBAPP_INIT_DATA_MAX_AGE:
            raise HTTPException(401, "انتهت صلاحية initData، أعد فتح Mini App من Telegram")

        data_check_string = "\n".join(
            f"{key}={value}" for key, value in sorted(pairs.items())
        )
        secret_key = hmac.new(
            key=b"WebAppData",
            msg=BOT_TOKEN.encode("utf-8"),
            digestmod=hashlib.sha256,
        ).digest()
        calculated_hash = hmac.new(
            key=secret_key,
            msg=data_check_string.encode("utf-8"),
            digestmod=hashlib.sha256,
        ).hexdigest()

        if not hmac.compare_digest(calculated_hash, received_hash):
            raise HTTPException(403, "فشل التحقق من هوية Telegram Mini App")

        user_raw = pairs.get("user", "")
        if not user_raw:
            raise HTTPException(401, "بيانات مستخدم Telegram غير موجودة")
        try:
            user_obj = json.loads(user_raw)
            user_id = int(user_obj["id"])
        except (json.JSONDecodeError, KeyError, TypeError, ValueError) as exc:
            raise HTTPException(401, "بيانات مستخدم Telegram غير صالحة") from exc

        if user_id <= 0:
            raise HTTPException(401, "معرّف مستخدم Telegram غير صالح")
        # المالك مخول دائماً، ويمكنه منح مستخدمين محددين صلاحية Mini App.
        entry = user_registry.get(str(user_id), {})
        if user_id != OWNER_ID and not bool(entry.get("mini_app_access", False)):
            raise HTTPException(403, "لا تملك صلاحية Mini App. اطلب من المالك منحك الصلاحية.")
        return user_id

    def _available_session_ids() -> list[int]:
        """Return every locally stored session id without exposing other users."""
        ids: set[int] = set(clients)
        for path in SESSION_DIR.glob("user_*.session"):
            try:
                ids.add(int(path.stem.removeprefix("user_")))
            except ValueError:
                continue
        return sorted(value for value in ids if value > 0)

    async def _web_client(sid: int, init_data: str = Query("")):
        """Authenticate the caller and open an allowed locally stored session."""
        authorized_user_id = await _authorized_user(init_data)
        if authorized_user_id != OWNER_ID and sid != authorized_user_id:
            raise HTTPException(403, "يمكنك الوصول إلى جلستك فقط")
        if sid not in _available_session_ids():
            raise HTTPException(404, "جلسة Telegram غير موجودة")

        try:
            c = await get_or_create_client(sid)
            if not c.is_connected():
                await c.connect()
            if not await c.is_user_authorized():
                raise HTTPException(403, "جلسة Telegram الخاصة بك غير مسجل الدخول فيها")
            me = await c.get_me()
        except HTTPException:
            raise
        except AuthKeyUnregisteredError as exc:
            raise HTTPException(403, "جلسة Telegram غير صالحة، أعد تسجيل الدخول من البوت") from exc
        except Exception as e:
            raise HTTPException(503, f"تعذر الاتصال بجلسة Telegram: {e}") from e
        return c

    @web_app.get("/", response_class=HTMLResponse)
    async def web_index():
        return HTMLResponse(WEB_HTML)

    @web_app.get("/healthz")
    async def web_healthz():
        return {"ok": True, "web": True, "mini_app": True, "host": WEB_HOST, "port": WEB_PORT,
                "sessions": len(clients)}

    @web_app.get("/api/sessions")
    async def web_sessions(init_data: str = Query("")):
        await _authorized_user(init_data)
        result = []
        for sid in _available_session_ids():
            try:
                c = await _web_client(sid, init_data)
                me = await c.get_me()
                name = f"{getattr(me,'first_name','') or ''} {getattr(me,'last_name','') or ''}".strip()
                result.append({"id": sid, "name": name or "حساب", "username": getattr(me,'username','') or "",
                               "account_id": int(getattr(me, 'id', 0) or 0), "connected": c.is_connected()})
            except Exception as e:
                logger.warning("تعذر فتح جلسة Mini App %s: %s", sid, e)
                # تجاهل الجلسة غير المسجلة أو التالفة حتى لا تختارها الواجهة
                # تلقائياً ثم تستبدل قائمة الجلسات برسالة مصادقة خاطئة.
                continue
        return result

    @web_app.get("/api/sessions/{sid}/dialogs")
    async def web_dialogs(sid:int, search:str="", init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        out=[]
        # لا نضع حداً منخفضاً؛ الواجهة يجب أن تعرض كل حوارات الجلسة.
        async for d in c.iter_dialogs(limit=None):
            title=d.name or str(d.id)
            if search and search.lower() not in title.lower(): continue
            ent=d.entity
            typ="مجموعة" if getattr(ent,"megagroup",False) else ("قناة" if getattr(ent,"broadcast",False) else "محادثة")
            out.append({"id":d.id,"title":title,"type":typ,"unread":d.unread_count})
        return out

    async def _message_json(c, chat_id, m):
        media=None
        if m.media:
            name=getattr(m.file,"name",None) or "ملف"
            mime=getattr(m.file,"mime_type",None) or ""
            kind="image" if mime.startswith("image/") else ("video" if mime.startswith("video/") else "file")
            base=f"/api/sessions/{getattr(c,'_web_sid',0)}/media/{chat_id}/{m.id}"
            media={"kind":kind,"name":name,"preview_url":base+"/preview","download_url":base}
        sender = getattr(m, "sender", None)
        sender_name = " ".join(filter(None, [getattr(sender, "first_name", None), getattr(sender, "last_name", None)]))
        return {"id":m.id,"text":m.text or "","out":bool(m.out),"date":m.date.isoformat() if m.date else "",
                "sender_id":getattr(m, "sender_id", None),
                "sender_username":getattr(sender, "username", None),
                "sender":sender_name or None,"media":media}

    @web_app.get("/api/sessions/{sid}/chats/{chat_id}/messages")
    async def web_messages(sid:int, chat_id:int, limit:int=30, offset_id:int=0, init_data:str=Query("")):
        c=await _web_client(sid, init_data); c._web_sid=sid
        try:
            msgs=[m async for m in c.iter_messages(chat_id,limit=min(max(limit,1),40),offset_id=max(offset_id,0))]
        except Exception as exc:
            logger.exception("تعذر فتح محادثة Mini App sid=%s chat=%s", sid, chat_id)
            raise HTTPException(
                403,
                "لا يمكن فتح هذه المحادثة بهذا الحساب. تأكد أن الحساب عضو فيها، وأنها ما زالت موجودة، ثم افتحها من تطبيق Telegram وأعد المحاولة."
            ) from exc
        return [await _message_json(c,chat_id,m) for m in msgs]

    @web_app.get("/api/sessions/{sid}/chats/{chat_id}/search")
    async def web_search_messages(sid:int, chat_id:int, q:str=Query(""), init_data:str=Query("")):
        c=await _web_client(sid, init_data); c._web_sid=sid
        try:
            msgs=[m async for m in c.iter_messages(chat_id,limit=40,search=q)]
        except Exception as exc:
            raise HTTPException(403, "لا يمكن البحث داخل هذه المحادثة بهذا الحساب. تأكد من عضوية الحساب في المحادثة.") from exc
        return [await _message_json(c,chat_id,m) for m in msgs]

    async def _media_stream(c, message, *, thumbnail: bool = False):
        """Download to disk, not RAM, then stream and remove the temporary file."""
        suffix = ".jpg" if thumbnail else ""
        fd, path = tempfile.mkstemp(prefix="miniapp_media_", suffix=suffix)
        os.close(fd)
        try:
            kwargs = {"file": path}
            if thumbnail:
                kwargs["thumb"] = -1
            saved = await c.download_media(message, **kwargs)
            if not saved or not os.path.exists(saved):
                raise HTTPException(404, "المعاينة غير متاحة")
            with open(saved, "rb") as stream:
                while True:
                    chunk = stream.read(256 * 1024)
                    if not chunk:
                        break
                    yield chunk
        finally:
            try:
                os.unlink(path)
            except FileNotFoundError:
                pass

    async def _get_media_response(sid:int, chat_id:int, msg_id:int, init_data:str, *, thumbnail: bool):
        c=await _web_client(sid, init_data)
        m=await c.get_messages(chat_id,ids=msg_id)
        if not m or not m.media: raise HTTPException(404,"الوسائط غير موجودة")
        mime="image/jpeg" if thumbnail else (getattr(getattr(m,"file",None),"mime_type",None) or "application/octet-stream")
        filename=getattr(getattr(m,"file",None),"name",None) or "media"
        disposition="inline" if thumbnail else "attachment"
        headers={"Content-Disposition": f"{disposition}; filename*=UTF-8''{quote(filename)}"}
        return StreamingResponse(_media_stream(c, m, thumbnail=thumbnail), media_type=mime, headers=headers)

    @web_app.get("/api/sessions/{sid}/media/{chat_id}/{msg_id}")
    async def web_media(sid:int, chat_id:int, msg_id:int, init_data:str=Query("")):
        return await _get_media_response(sid, chat_id, msg_id, init_data, thumbnail=False)

    @web_app.get("/api/sessions/{sid}/media/{chat_id}/{msg_id}/preview")
    async def web_media_preview(sid:int, chat_id:int, msg_id:int, init_data:str=Query("")):
        return await _get_media_response(sid, chat_id, msg_id, init_data, thumbnail=True)

    @web_app.get("/api/owner/timed-archive")
    async def web_timed_archive(init_data: str = Query("")):
        if await _authorized_user(init_data) != OWNER_ID:
            raise HTTPException(403, "أرشيف الرسائل الموقوتة مخصص للمالك فقط")
        result = []
        for session_id in sorted(owner_session_ids):
            for path in timed_archive_files(session_id):
                if path.suffix == ".json" or not path.is_file():
                    continue
                meta_path = path.with_suffix(path.suffix + ".json")
                try:
                    meta = json.loads(meta_path.read_text(encoding="utf-8")) if meta_path.exists() else {}
                except Exception:
                    meta = {}
                result.append({"name": path.name, "size": path.stat().st_size,
                               "saved_at": meta.get("saved_at", 0), "session_id": session_id,
                               "download_url": f"/api/owner/timed-archive/{session_id}/{quote(path.name)}"})
        return sorted(result, key=lambda x: x["saved_at"], reverse=True)

    @web_app.get("/api/owner/timed-archive/{session_id}/{filename}")
    async def web_timed_archive_file(session_id: int, filename: str, init_data: str = Query("")):
        if await _authorized_user(init_data) != OWNER_ID:
            raise HTTPException(403, "أرشيف الرسائل الموقوتة مخصص للمالك فقط")
        if session_id not in owner_session_ids:
            raise HTTPException(404, "جلسة الأرشيف غير موجودة")
        root = (ARCHIVE_DIR / str(session_id)).resolve()
        path = (root / Path(filename).name).resolve()
        if root not in path.parents or not path.is_file() or path.suffix == ".json":
            raise HTTPException(404, "الملف غير موجود")
        return FileResponse(path, filename=path.name)

    @web_app.get("/api/owner/channels")
    async def web_owner_channels(init_data: str = Query("")):
        authorized = await _authorized_user(init_data)
        if authorized != OWNER_ID:
            raise HTTPException(403, "عرض قنوات الهدف مخصص للمالك فقط")
        owner_client = await get_or_create_client(OWNER_ID)
        result = []
        async for dialog in owner_client.iter_dialogs(limit=None):
            entity = dialog.entity
            if getattr(entity, "creator", False) and getattr(entity, "broadcast", False):
                result.append({"id": int(entity.id), "title": dialog.name or "بدون اسم", "kind": "channel"})
            elif getattr(entity, "user_id", None) or entity.__class__.__name__ == "User":
                if int(getattr(entity, "id", 0) or 0) != OWNER_ID:
                    result.append({"id": int(entity.id), "title": dialog.name or "شخص", "kind": "user"})
        return result

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/transfer")
    async def web_transfer_media(sid:int, chat_id:int, body:TransferBody, init_data:str=Query("")):
        authorized = await _authorized_user(init_data)
        if authorized != OWNER_ID:
            raise HTTPException(403, "نقل المحتوى مخصص للمالك فقط")
        source_client = await _web_client(sid, init_data)
        target_client = await get_or_create_client(OWNER_ID)
        source = await source_client.get_messages(chat_id, ids=body.message_id)
        if not source or not source.media:
            raise HTTPException(404, "المنشور المطلوب لا يحتوي على وسائط قابلة للنقل")
        target_entity = await resolve_channel_entity(target_client, body.target_id)
        suffix = Path(getattr(getattr(source, "file", None), "name", None) or "media.bin").suffix or ".bin"
        fd, temp_path = tempfile.mkstemp(prefix="telegram_transfer_", suffix=suffix)
        os.close(fd)
        try:
            saved = await source_client.download_media(source, file=temp_path)
            if not saved or not os.path.exists(saved):
                raise HTTPException(500, "فشل تنزيل الوسيط إلى السيرفر")
            await target_client.send_file(target_entity, saved, caption=source.text or "")
            return {"ok": True, "message": "تم تنزيل الملف إلى السيرفر ثم رفعه إلى القناة الهدف"}
        finally:
            try:
                os.unlink(temp_path)
            except FileNotFoundError:
                pass

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/transfer-all")
    async def web_transfer_all(sid:int, chat_id:int, body:TransferAllBody, init_data:str=Query("")):
        authorized = await _authorized_user(init_data)
        if authorized != OWNER_ID:
            raise HTTPException(403, "نقل المحتوى مخصص للمالك فقط")
        source_client = await _web_client(sid, init_data)
        target_client = await get_or_create_client(OWNER_ID)
        target_entity = await (
            resolve_channel_entity(target_client, body.target_id)
            if body.target_kind == "channel"
            else target_client.get_entity(body.target_id)
        )
        job_id = uuid.uuid4().hex[:12]
        job = {"id": job_id, "status": "running", "sent": 0, "failed": 0, "current": 0, "pause": asyncio.Event(), "stop": False}
        job["pause"].set()
        web_transfer_jobs[job_id] = job

        async def worker() -> None:
            try:
                async for message in source_client.iter_messages(chat_id, limit=None, reverse=True):
                    if job["stop"]:
                        job["status"] = "stopped"
                        break
                    await job["pause"].wait()
                    job["current"] += 1
                    try:
                        if message.media:
                            original_name = getattr(getattr(message, "file", None), "name", None) or ""
                            suffix = Path(original_name).suffix or ".mp4"
                            fd, temp_path = tempfile.mkstemp(prefix="telegram_transfer_all_", suffix=suffix)
                            os.close(fd)
                            try:
                                saved = await source_client.download_media(message, file=temp_path)
                                if not saved or not os.path.exists(saved):
                                    job["failed"] += 1
                                    continue
                                await target_client.send_file(target_entity, saved, caption=message.text or "", file_name=original_name or f"media{suffix}")
                                job["sent"] += 1
                            finally:
                                try:
                                    os.unlink(temp_path)
                                except FileNotFoundError:
                                    pass
                        elif message.text:
                            await target_client.send_message(target_entity, message.text)
                            job["sent"] += 1
                    except Exception:
                        job["failed"] += 1
                        logger.exception("فشل نقل رسالة Mini App sid=%s chat=%s message=%s", sid, chat_id, getattr(message, "id", 0))
                if job["status"] == "running":
                    job["status"] = "done"
            except Exception as exc:
                job["status"] = "failed"
                job["error"] = f"{type(exc).__name__}: {exc}"
                logger.exception("فشل نقل المحادثة بالكامل")

        job["task"] = asyncio.create_task(worker())
        return {"ok": True, "job_id": job_id, "message": "بدأ نقل المحادثة عبر السيرفر"}

    @web_app.get("/api/transfer-jobs/{job_id}")
    async def web_transfer_status(job_id: str, init_data: str = Query("")):
        if await _authorized_user(init_data) != OWNER_ID or job_id not in web_transfer_jobs:
            raise HTTPException(404, "مهمة النقل غير موجودة")
        job = web_transfer_jobs[job_id]
        return {k: v for k, v in job.items() if k not in {"pause", "stop", "task"}}

    @web_app.post("/api/transfer-jobs/{job_id}/pause")
    async def web_transfer_pause(job_id: str, init_data: str = Query("")):
        if await _authorized_user(init_data) != OWNER_ID or job_id not in web_transfer_jobs:
            raise HTTPException(404, "مهمة النقل غير موجودة")
        job = web_transfer_jobs[job_id]
        if job["status"] == "running":
            job["pause"].clear(); job["status"] = "paused"
        elif job["status"] == "paused":
            job["pause"].set(); job["status"] = "running"
        return {"ok": True, "status": job["status"]}

    @web_app.post("/api/transfer-jobs/{job_id}/stop")
    async def web_transfer_stop(job_id: str, init_data: str = Query("")):
        if await _authorized_user(init_data) != OWNER_ID or job_id not in web_transfer_jobs:
            raise HTTPException(404, "مهمة النقل غير موجودة")
        job = web_transfer_jobs[job_id]
        job["stop"] = True; job["pause"].set(); job["status"] = "stopping"
        return {"ok": True, "status": "stopping"}


    async def _resolve_web_chat(c, chat_id: int):
        try:
            return await c.get_input_entity(chat_id)
        except Exception as exc:
            raise HTTPException(404, "المحادثة غير موجودة أو لا يمكن الوصول إليها") from exc

    @web_app.get("/api/sessions/{sid}/chats/{chat_id}/meta")
    async def web_chat_meta(sid:int, chat_id:int, init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        try:
            dialogs = [d async for d in c.iter_dialogs(limit=None) if int(d.id)==int(chat_id)]
            if not dialogs:
                raise HTTPException(404, "المحادثة غير موجودة")
            d=dialogs[0]
            return {"pinned":bool(getattr(d,"pinned",False)),
                    "muted":bool(getattr(d,"notify_settings",None) and getattr(d.notify_settings,"mute_until",None)),
                    "archived":int(getattr(d,"folder_id",0) or 0)==1}
        except HTTPException:
            raise
        except Exception as exc:
            raise HTTPException(500, f"تعذر قراءة حالة المحادثة: {exc}") from exc

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/pin")
    async def web_chat_pin(sid:int, chat_id:int, init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        peer=await _resolve_web_chat(c, chat_id)
        dialogs=[d async for d in c.iter_dialogs(limit=None) if int(d.id)==int(chat_id)]
        pinned=not bool(getattr(dialogs[0],"pinned",False)) if dialogs else True
        await c(functions.messages.UpdatePinnedDialogRequest(peer=peer, pinned=pinned, unpin=pinned is False))
        return {"ok":True,"pinned":pinned}

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/mute")
    async def web_chat_mute(sid:int, chat_id:int, init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        peer=await _resolve_web_chat(c, chat_id)
        dialogs=[d async for d in c.iter_dialogs(limit=None) if int(d.id)==int(chat_id)]
        muted=False
        if dialogs:
            ns=getattr(dialogs[0],"notify_settings",None)
            muted=bool(ns and getattr(ns,"mute_until",None))
        if muted:
            settings=types.InputPeerNotifySettings(mute_until=0)
            new_muted=False
        else:
            settings=types.InputPeerNotifySettings(mute_until=int(time.time())+365*24*3600)
            new_muted=True
        await c(functions.account.UpdateNotifySettingsRequest(peer=types.InputNotifyPeer(peer=peer), settings=settings))
        return {"ok":True,"muted":new_muted}

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/archive")
    async def web_chat_archive(sid:int, chat_id:int, init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        peer=await _resolve_web_chat(c, chat_id)
        dialogs=[d async for d in c.iter_dialogs(limit=None) if int(d.id)==int(chat_id)]
        archived=not (dialogs and int(getattr(dialogs[0],"folder_id",0) or 0)==1)
        await c(functions.folders.EditPeerFoldersRequest(
            folder_peers=[types.InputFolderPeer(peer=peer, folder_id=1 if archived else 0)]
        ))
        return {"ok":True,"archived":archived}


    async def _send_file_to_bot_from_path(
        path: Path,
        chat_id: int,
        caption: str = "",
        filename: str | None = None,
        media_kind: str = "document",
    ):
        """إرسال ملف Mini App إلى البوت مع اسم/امتداد صحيح وتقرير مفصل للأخطاء."""
        if not web_bot:
            exc = RuntimeError("web_bot غير جاهز")
            await report_error_to_owner(
                "البوت غير جاهز لإرسال ملف من Mini App",
                exc,
                f"path={path}\nfilename={filename}\nchat_id={chat_id}",
            )
            raise HTTPException(503, "البوت غير جاهز لإرسال الملف")

        if not path.is_file():
            exc = FileNotFoundError(str(path))
            await report_error_to_owner(
                "ملف Mini App غير موجود قبل الإرسال",
                exc,
                f"path={path}\nfilename={filename}\nchat_id={chat_id}",
            )
            raise HTTPException(404, "الملف غير موجود")

        size = path.stat().st_size
        if size > MAX_FILE_SIZE_BYTES:
            exc = ValueError(f"حجم الملف {size} bytes يتجاوز الحد {MAX_FILE_SIZE_BYTES} bytes")
            await report_error_to_owner(
                "حجم ملف Mini App أكبر من الحد المسموح",
                exc,
                f"path={path}\nfilename={filename}\nchat_id={chat_id}\nsize={size}",
            )
            raise HTTPException(413, f"الملف أكبر من الحد المسموح ({MAX_FILE_SIZE_MB} MB)")

        safe_name = Path(filename).name if filename else path.name
        if not safe_name or safe_name in {".", ".."}:
            safe_name = "media"

        # لا نسمح بأن يصبح اسم الملف .bin إذا كان لدينا امتداد حقيقي.
        if Path(safe_name).suffix.lower() == ".bin":
            real_suffix = path.suffix.lower()
            if real_suffix and real_suffix != ".bin":
                safe_name = Path(safe_name).stem + real_suffix

        # إذا لم يكن للملف امتداد، حاول أخذ الامتداد من الاسم الذي أعاده Telethon.
        if not Path(safe_name).suffix and path.suffix:
            safe_name += path.suffix

        context = (
            f"path={path}\nfilename={safe_name}\nchat_id={chat_id}\n"
            f"size={size} bytes\nmedia_kind={media_kind}"
        )

        try:
            # فتح الملف داخل with يضمن إغلاقه بعد اكتمال الرفع.
            with path.open("rb") as fh:
                upload = InputFile(fh, filename=safe_name)

                if media_kind == "photo":
                    await web_bot.send_photo(
                        chat_id=chat_id,
                        photo=upload,
                        caption=caption[:1024] if caption else None,
                    )
                elif media_kind == "video":
                    await web_bot.send_video(
                        chat_id=chat_id,
                        video=upload,
                        caption=caption[:1024] if caption else None,
                        supports_streaming=True,
                    )
                elif media_kind == "audio":
                    await web_bot.send_audio(
                        chat_id=chat_id,
                        audio=upload,
                        caption=caption[:1024] if caption else None,
                    )
                elif media_kind == "voice":
                    await web_bot.send_voice(
                        chat_id=chat_id,
                        voice=upload,
                        caption=caption[:1024] if caption else None,
                    )
                elif media_kind == "video_note":
                    await web_bot.send_video_note(
                        chat_id=chat_id,
                        video_note=upload,
                    )
                else:
                    await web_bot.send_document(
                        chat_id=chat_id,
                        document=upload,
                        caption=caption[:1024] if caption else None,
                    )
        except Exception as exc:
            logger.exception("فشل إرسال ملف Mini App إلى شات البوت")
            await report_error_to_owner(
                "فشل إرسال محتوى Mini App إلى شات البوت",
                exc,
                context,
            )
            # نرسل سبباً واضحاً للـMini App بدل 500 عام فقط.
            raise HTTPException(
                502,
                f"فشل إرسال المحتوى إلى البوت: {type(exc).__name__}: {str(exc)[:700]}",
            ) from exc


    @web_app.post("/api/owner/timed-archive/delete")
    async def web_timed_archive_delete(body:ArchiveDeleteBody, init_data:str=Query("")):
        if await _authorized_user(init_data) != OWNER_ID:
            raise HTTPException(403, "الأرشيف مخصص للمالك فقط")
        deleted=0
        for item in body.items[:100]:
            try:
                sid_raw, filename = item.split("|",1)
                sid=int(sid_raw)
                if sid not in owner_session_ids:
                    continue
                root=(ARCHIVE_DIR/str(sid)).resolve()
                path=(root/Path(filename).name).resolve()
                if root not in path.parents or not path.is_file() or path.suffix==".json":
                    continue
                path.unlink()
                meta=path.with_suffix(path.suffix+".json")
                if meta.exists(): meta.unlink()
                deleted+=1
            except Exception as exc:
                logger.exception("تعذر حذف عنصر أرشيف")
                await report_error_to_owner(
                    "فشل حذف عنصر من الأرشيف",
                    exc,
                    f"item={item}",
                )
        return {"ok":True,"deleted":deleted}

    @web_app.post("/api/owner/timed-archive/send-to-bot/{session_id}/{filename}")
    async def web_archive_send_to_bot(session_id:int, filename:str, init_data:str=Query("")):
        user_id=await _authorized_user(init_data)
        if user_id != OWNER_ID: raise HTTPException(403,"مخصص للمالك")
        root=(ARCHIVE_DIR/str(session_id)).resolve()
        path=(root/Path(filename).name).resolve()
        if root not in path.parents or not path.is_file() or path.suffix==".json":
            raise HTTPException(404,"الملف غير موجود")
        try:
            await _send_file_to_bot_from_path(path,user_id,caption=path.name,filename=path.name)
        except Exception as exc:
            if isinstance(exc, HTTPException):
                raise
            await report_error_to_owner(
                "خطأ غير متوقع أثناء إرسال ملف الأرشيف",
                exc,
                f"session_id={session_id}\nfilename={filename}\npath={path}",
            )
            raise
        return {"ok":True}

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/media/{msg_id}/send-to-bot")
    async def web_media_send_to_bot(sid:int, chat_id:int, msg_id:int, init_data:str=Query("")):
        user_id=await _authorized_user(init_data)
        context_info = f"user_id={user_id}\nsession_id={sid}\nchat_id={chat_id}\nmessage_id={msg_id}"
        try:
            c=await _web_client(sid, init_data)
            m=await c.get_messages(chat_id,ids=msg_id)
            if not m or not m.media:
                raise HTTPException(404,"الوسائط غير موجودة")

            file_obj = getattr(m, "file", None)
            original_name = getattr(file_obj, "name", None)
            mime_type = getattr(file_obj, "mime_type", None)

            if original_name:
                upload_name = Path(original_name).name
            else:
                guessed_ext = mimetypes.guess_extension(mime_type) if mime_type else None
                if not guessed_ext:
                    if getattr(m, "photo", None):
                        guessed_ext = ".jpg"
                    elif getattr(m, "video", None):
                        guessed_ext = ".mp4"
                    elif getattr(m, "audio", None):
                        guessed_ext = ".mp3"
                    elif getattr(m, "voice", None):
                        guessed_ext = ".ogg"
                    else:
                        guessed_ext = ""
                upload_name = f"media{guessed_ext}"

            suffix=Path(upload_name).suffix or ""
            fd,temp_path=tempfile.mkstemp(prefix="miniapp_send_",suffix=suffix)
            os.close(fd)

            try:
                saved=await c.download_media(m,file=temp_path)
                if not saved or not os.path.exists(saved):
                    raise RuntimeError("Telethon لم يُرجع ملفاً بعد download_media")

                # تحديد النوع الحقيقي لإرسال الصورة/الفيديو/الصوت كوسيط أصلي.
                if getattr(m, "photo", None):
                    media_kind = "photo"
                elif getattr(m, "video", None):
                    media_kind = "video"
                elif getattr(m, "audio", None):
                    media_kind = "audio"
                elif getattr(m, "voice", None):
                    media_kind = "voice"
                elif getattr(m, "video_note", None):
                    media_kind = "video_note"
                else:
                    media_kind = "document"

                await _send_file_to_bot_from_path(
                    Path(saved),
                    user_id,
                    caption=m.text or "",
                    filename=upload_name,
                    media_kind=media_kind,
                )
            finally:
                try:
                    os.unlink(temp_path)
                except FileNotFoundError:
                    pass

            return {"ok":True}

        except HTTPException as exc:
            # HTTPException already contains a useful user-facing reason.
            # Report it too when it represents an actual send/download failure.
            if exc.status_code >= 500:
                await report_error_to_owner(
                    "فشل طلب إرسال وسائط من Mini App",
                    exc,
                    context_info,
                )
            raise
        except Exception as exc:
            logger.exception("خطأ غير متوقع في إرسال وسائط Mini App")
            await report_error_to_owner(
                "خطأ غير متوقع في زر «إرسال إلى شات البوت»",
                exc,
                context_info,
            )
            raise HTTPException(
                500,
                f"خطأ داخلي أثناء إرسال المحتوى: {type(exc).__name__}: {str(exc)[:700]}",
            ) from exc

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/reply")
    async def web_reply(sid:int,chat_id:int,body:MessageActionBody,init_data:str=Query("")):
        c=await _web_client(sid,init_data)
        if not body.text.strip(): raise HTTPException(400,"الرد فارغ")
        m=await c.send_message(chat_id,body.text.strip(),reply_to=body.message_id)
        return {"ok":True,"id":m.id}

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/edit")
    async def web_edit(sid:int,chat_id:int,body:MessageActionBody,init_data:str=Query("")):
        c=await _web_client(sid,init_data)
        m=await c.get_messages(chat_id,ids=body.message_id)
        if not m or not m.out: raise HTTPException(403,"يمكن تعديل رسائلك الصادرة فقط")
        await c.edit_message(chat_id,body.message_id,body.text)
        return {"ok":True}

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/delete")
    async def web_delete(sid:int,chat_id:int,body:MessageActionBody,init_data:str=Query("")):
        c=await _web_client(sid,init_data)
        m=await c.get_messages(chat_id,ids=body.message_id)
        if not m or not m.out: raise HTTPException(403,"يمكن حذف رسائلك الصادرة فقط")
        await c.delete_messages(chat_id,[body.message_id],revoke=True)
        return {"ok":True}

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/send")
    async def web_send(sid:int, chat_id:int, body:SendBody, init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        text_msg=body.text.strip()
        if not text_msg: raise HTTPException(400,"الرسالة فارغة")
        m=await c.send_message(chat_id,text_msg)
        return {"ok":True,"id":m.id}


# Runtime dashboard counters
runtime_stats = {
    "started_at": time.time(),
    "downloads_started": 0,
    "downloads_done": 0,
    "downloads_failed": 0,
    "transfers_started": 0,
    "transfers_done": 0,
    "transfers_failed": 0,
    "messages_processed": 0,
    "bytes_downloaded": 0,
    "bytes_uploaded": 0,
}

locks: dict[int, asyncio.Lock] = {}
active_link_tasks: dict[int, asyncio.Task] = {}
channel_transfer_tasks: dict[int, asyncio.Task] = {}
web_transfer_jobs: dict[str, dict[str, Any]] = {}
channel_transfers: dict[str, dict[str, Any]] = {}

# Semaphores مستقلة حتى لا يؤدي ضغط المستخدمين إلى فتح عشرات عمليات نقل/رفع
# في نفس اللحظة وإسقاط الخدمة أو الوصول السريع إلى حدود Telegram.
media_semaphore = asyncio.Semaphore(MEDIA_CONCURRENCY)
transfer_semaphore = asyncio.Semaphore(TRANSFER_CONCURRENCY)


def load_channel_transfers() -> None:
    global channel_transfers
    if not TRANSFER_STATE_PATH.exists():
        return
    try:
        data = json.loads(TRANSFER_STATE_PATH.read_text(encoding="utf-8"))
        channel_transfers = {str(k): v for k, v in data.items()}
        changed = False
        for job in channel_transfers.values():
            if "session_user_id" not in job:
                job["session_user_id"] = OWNER_ID
                changed = True
            # المهام القديمة أنشأها المالك قبل إضافة صلاحية النقل للمستخدمين.
            if "created_by" not in job:
                job["created_by"] = OWNER_ID
                changed = True
        if changed:
            save_channel_transfers()
    except Exception:
        logger.exception("تعذر تحميل قائمة نقل القنوات")
        channel_transfers = {}


def save_channel_transfers() -> None:
    temp_path = TRANSFER_STATE_PATH.with_suffix(".tmp")
    temp_path.write_text(json.dumps(channel_transfers, ensure_ascii=False, indent=2), encoding="utf-8")
    temp_path.replace(TRANSFER_STATE_PATH)


def transfer_message_signature(message) -> str | None:
    """بصمة محافظة للبحث عن نسخة موجودة في الهدف دون تنزيل الوسائط."""
    text = (getattr(message, "message", None) or "").strip()
    media = getattr(message, "media", None)
    if not media:
        # النصوص العادية المتكررة قد تكون منشورات مختلفة؛ نقارن النص فقط إذا احتوى رابطاً.
        return f"text|{text}" if "http://" in text or "https://" in text else None
    document = getattr(message, "document", None)
    photo = getattr(message, "photo", None)
    if document is not None:
        size = int(getattr(document, "size", 0) or 0)
        mime = getattr(document, "mime_type", "") or ""
        name = ""
        width = height = duration = 0
        for attribute in getattr(document, "attributes", []) or []:
            filename = getattr(attribute, "file_name", None)
            if filename:
                name = filename
            width = int(getattr(attribute, "w", width) or width)
            height = int(getattr(attribute, "h", height) or height)
            duration = int(getattr(attribute, "duration", duration) or duration)
        # لا ندخل الوصف في بصمة الملف؛ قد يختلف الوصف عند إعادة النشر.
        return f"document|{mime}|{size}|{name}|{width}x{height}|{duration}"
    if photo is not None:
        photo_sizes = getattr(photo, "sizes", None) or []
        largest_photo_size = photo_sizes[-1] if photo_sizes else None
        photo_size = int(getattr(largest_photo_size, "size", 0) or 0)
        photo_width = int(getattr(photo, "w", 0) or 0)
        photo_height = int(getattr(photo, "h", 0) or 0)
        return f"photo|{photo_width}|{photo_height}|{photo_size}"
    return f"media|{type(media).__name__}|{text}"


async def build_target_signature_index(client: TelegramClient, target) -> set[str]:
    """يبني فهرساً خفيفاً من رسائل الهدف؛ لا ينزّل الملفات.
    TARGET_INDEX_LIMIT=0 يعني فهرسة كاملة؛ القيمة الافتراضية تحدّ من زمن البدء
    في القنوات الضخمة مع بقاء delivered_source_message_ids لمنع التكرار في المهام المستمرة.
    """
    signatures: set[str] = set()
    limit = max(0, int(os.getenv("TARGET_INDEX_LIMIT", "20000")))
    async for target_message in client.iter_messages(target, limit=limit or None):
        signature = transfer_message_signature(target_message)
        if signature:
            signatures.add(signature)
    return signatures


async def verify_target_message(client: TelegramClient, target, sent_message) -> bool:
    """يتأكد أن Telegram أنشأ الرسالة فعلاً في الهدف قبل اعتمادها."""
    if isinstance(sent_message, (list, tuple)):
        sent_message = sent_message[-1] if sent_message else None
    message_id = getattr(sent_message, "id", None)
    if not message_id:
        return False
    try:
        confirmed = await client.get_messages(target, ids=int(message_id))
        return confirmed is not None and getattr(confirmed, "id", None) == int(message_id)
    except Exception:
        logger.exception("تعذر التحقق من رسالة الهدف ذات المعرّف %s", message_id)
        return False


async def find_target_message_by_signature(client: TelegramClient, target, signature: str | None):
    """يبحث بعد فشل/مهلة الرفع عن نسخة قُبلت رغم عدم عودة الاستجابة."""
    if not signature:
        return None
    async for target_message in client.iter_messages(target):
        if transfer_message_signature(target_message) == signature:
            return target_message
    return None


load_channel_transfers()


def get_lock(user_id: int) -> asyncio.Lock:
    if user_id not in locks:
        locks[user_id] = asyncio.Lock()
    return locks[user_id]


def session_path(user_id: int) -> str:
    return str(SESSION_DIR / f"user_{user_id}")


def normalize_otp(value: str) -> str:
    arabic_digits = str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")
    return re.sub(r"\s+", "", value).translate(arabic_digits)


def format_size(size: int) -> str:
    size_gb = size / (1024 ** 3)
    if size_gb >= 1:
        return f"{size_gb:.2f} غيغابايت"
    return f"{size / (1024 ** 2):.0f} ميغابايت"


def normalize_channel_ref(value: str | int):
    """يقبل @username أو username أو معرّف القناة أو رابط Telegram."""
    raw = str(value).strip()
    public_match = re.fullmatch(r"https?://t\.me/(?P<username>[A-Za-z0-9_]+)(?:/\d+)?/?", raw)
    if public_match:
        return "@" + public_match.group("username")
    private_match = re.fullmatch(r"https?://t\.me/c/(?P<channel_id>\d+)(?:/\d+)?/?", raw)
    if private_match:
        return int("-100" + private_match.group("channel_id"))
    if re.fullmatch(r"-100\d+", raw):
        return int(raw)
    if re.fullmatch(r"\d+", raw):
        return int("-100" + raw)
    if raw.startswith("@") and re.fullmatch(r"@[A-Za-z0-9_]{3,}", raw):
        return raw
    if re.fullmatch(r"[A-Za-z0-9_]{3,}", raw):
        return "@" + raw
    raise ValueError(
        "صيغة القناة غير صحيحة. أرسل @username أو رابط https://t.me/... أو المعرّف الرقمي مثل -1001234567890."
    )


async def resolve_channel_entity(client: TelegramClient, reference):
    """حل قناة بالاسم أو الرابط أو المعرّف، مع البحث في حوارات الحساب عند الحاجة."""
    try:
        return await client.get_entity(reference)
    except (ValueError, TypeError) as first_error:
        if not isinstance(reference, int) and not str(reference).lstrip("-").isdigit():
            raise first_error
        numeric = int(reference)
        channel_id = int(str(abs(numeric))[3:]) if str(abs(numeric)).startswith("100") else abs(numeric)
        async for dialog in client.iter_dialogs():
            entity = dialog.entity
            if getattr(entity, "id", None) == channel_id:
                return entity
        raise ValueError(
            f"لم يجد الحساب القناة ذات المعرّف {reference} في حواراته. "
            "افتح القناة بالحساب أولاً، ثم أعد المحاولة."
        ) from first_error


async def find_owner_access_client(reference):
    """Find a logged-in user session that can access a private channel for the owner."""
    candidates = [OWNER_ID] + [int(raw_id) for raw_id in user_registry if str(raw_id).isdigit() and int(raw_id) != OWNER_ID]
    last_error = None
    for session_user_id in candidates:
        try:
            candidate = await get_or_create_client(session_user_id)
            if not await candidate.is_user_authorized():
                continue
            resolved = await resolve_channel_entity(candidate, reference)
            return candidate, resolved, session_user_id
        except Exception as exc:
            last_error = exc
            logger.info("الجلسة %s لا تملك وصولاً إلى القناة المطلوبة", session_user_id, exc_info=True)
    raise ValueError("لم يجد أي حساب مسجل في البوت هذه القناة. يجب أن يكون أحد المستخدمين عضواً فيها ويفتحها من Telegram أولاً.") from last_error


def parse_message_link(link: str):
    match = LINK_PATTERN.search(link.strip())
    if not match:
        return None
    if match.group("private"):
        entity = int(f"-100{match.group('private_id')}")
    else:
        # مرّر الاسم بصيغة @username حتى لا يُفسَّر كنص أو قيمة غير مكتملة.
        entity = "@" + match.group("username")
    return entity, int(match.group("message_id"))


def is_public_message_link(link: str) -> bool:
    parsed = parse_message_link(link)
    return bool(parsed and isinstance(parsed[0], str))


async def discard_client_session(user_id: int, remove_file: bool = True) -> None:
    """إسقاط عميل Telethon وملف الجلسة التالف بأمان."""
    client = clients.pop(user_id, None)
    if client is not None:
        try:
            if client.is_connected():
                await client.disconnect()
        except Exception:
            logger.exception("تعذر فصل عميل المستخدم %s", user_id)
    if not remove_file:
        return
    base = Path(session_path(user_id))
    candidates = [
        Path(str(base) + ".session"),
        Path(str(base) + "-journal"),
        Path(str(base) + ".session-journal"),
    ]
    for path in candidates:
        try:
            if path.exists():
                path.unlink()
                logger.warning("تم حذف ملف جلسة المستخدم %s: %s", user_id, path.name)
        except Exception:
            logger.exception("تعذر حذف ملف جلسة المستخدم %s: %s", user_id, path)


async def get_or_create_client(user_id: int) -> TelegramClient:
    """إرجاع عميل الجلسة دون حذف ملفها تلقائياً عند أخطاء التفويض.

    مهم جداً: user_id هنا هو آيدي مستخدم البوت الذي يملك ملف الجلسة،
    وليس بالضرورة آيدي حساب Telegram المسجّل داخل الجلسة. لذلك لا يجوز
    حذف ملف جلسة بناءً على AuthKeyUnregisteredError دون تأكيد صريح.
    """
    client = clients.get(user_id)
    if client is None:
        client = TelegramClient(session_path(user_id), API_ID, API_HASH)
        clients[user_id] = client
    if not client.is_connected():
        try:
            await client.connect()
        except AuthKeyUnregisteredError:
            # حماية من حذف جلسة أخرى بالخطأ. الملف يبقى كما هو حتى يقرر
            # المالك حذفه صراحة من زر تسجيل الخروج/الحذف.
            logger.warning(
                "مفتاح جلسة المستخدم %s غير مسجل؛ لن يتم حذف ملف الجلسة تلقائياً",
                user_id,
            )
            clients.pop(user_id, None)
            raise
        except ValueError as exc:
            if "cannot be reused after logging out" not in str(exc).lower():
                raise
            # لا نحذف ملف الجلسة هنا أيضاً؛ نترك قرار الحذف/إعادة التسجيل
            # لمسار تسجيل الدخول الصريح.
            logger.warning(
                "جلسة المستخدم %s لا يمكن إعادة استخدامها بعد تسجيل الخروج؛ "
                "يجب إعادة تسجيل الدخول صراحةً دون حذف جلسات أخرى",
                user_id,
            )
            clients.pop(user_id, None)
            raise
    if user_id in owner_session_ids and not getattr(client, "_timed_archive_watcher", False):
        async def _watch_timed(event) -> None:
            message = event.message
            media = getattr(message, "media", None)
            ttl = getattr(media, "ttl_seconds", None) if media else None
            if not media or not ttl:
                return
            root = ARCHIVE_DIR / str(user_id)
            root.mkdir(parents=True, exist_ok=True)
            file_name = getattr(getattr(message, "file", None), "name", None) or ("timed_photo.jpg" if getattr(message, "photo", None) else "timed_message.bin")
            safe_name = re.sub(r"[^\w.\- ]+", "_", str(file_name)).strip() or "timed_message.bin"
            destination = root / f"{int(time.time())}_{int(message.id)}_{safe_name}"
            try:
                saved = await client.download_media(message, file=str(destination))
                if saved and Path(saved).exists():
                    destination.with_suffix(destination.suffix + ".json").write_text(json.dumps({
                        "session_id": user_id, "chat_id": int(getattr(event, "chat_id", 0) or 0),
                        "message_id": int(message.id), "saved_at": int(time.time()), "filename": destination.name,
                    }, ensure_ascii=False), encoding="utf-8")
                    logger.info("تم حفظ رسالة موقوتة للمالك: session=%s message=%s", user_id, message.id)
            except Exception:
                logger.exception("تعذر حفظ رسالة موقوتة لجلسة المالك %s", user_id)
        client.add_event_handler(_watch_timed, events.NewMessage())
        client._timed_archive_watcher = True
    return client


async def inspect_session_identity(user_id: int, client: TelegramClient | None = None):
    """يتحقق من الحساب الحقيقي داخل ملف الجلسة دون حذف أي ملف.

    يعيد كائن الحساب إذا كانت الجلسة صالحة، ويرفع الخطأ الأصلي إذا كانت
    جلسة Telegram غير مسجلة. لا يوجد في هذه الدالة أي حذف تلقائي.
    """
    client = client or await get_or_create_client(user_id)
    if not await client.is_user_authorized():
        raise ValueError("الجلسة غير مسجلة الدخول")
    me = await client.get_me()
    if not me or not getattr(me, "id", None):
        raise ValueError("تعذر التحقق من هوية حساب Telegram داخل الجلسة")
    return me


async def resolve_second_recipient(client: TelegramClient):
    raw = SECOND_RECIPIENT.strip()
    if raw.startswith("@"):
        return await client.get_entity(raw)

    if raw.lstrip("-").isdigit():
        recipient_id = int(raw)
        try:
            return await client.get_entity(recipient_id)
        except ValueError:
            # أرقام المستخدمين لا يمكن حلها دائماً من الذاكرة المحلية.
            # نبحث في الحوارات التي حمّلها حساب المستخدم أولاً.
            async for dialog in client.iter_dialogs():
                entity = dialog.entity
                if getattr(entity, "id", None) == recipient_id:
                    return entity
            raise ValueError(
                f"لا يمكن لحساب المستخدم العثور على المستلم {raw}. "
                "اجعل الحساب يفتح محادثة معه أولاً، أو استخدم اسم المستخدم بصيغة @username."
            )

    raise ValueError(
        "قيمة SECOND_RECIPIENT غير صحيحة. استخدم @username أو المعرّف الرقمي مع وجود محادثة سابقة."
    )


async def reset_public_client() -> None:
    """إسقاط العميل العام التالف فقط، دون لمس جلسات المستخدمين."""
    global public_client
    async with public_client_lock:
        old_client = public_client
        public_client = None
        if old_client is not None:
            try:
                if old_client.is_connected():
                    await old_client.disconnect()
            except Exception:
                logger.exception("تعذر فصل العميل العام التالف")


async def get_public_client() -> TelegramClient:
    """إنشاء عميل غير مسجل جديد لكل عملية عامة مستقلة."""
    # لا نشارك عميلاً مؤقتاً بين المستخدمين؛ مشاركة العميل قد تؤدي إلى
    # AuthKeyUnregisteredError عند تزامن عمليات متعددة أو إبطال مفتاح مؤقت.
    client = TelegramClient(None, API_ID, API_HASH)
    await client.connect()
    return client


async def is_ready(user_id: int) -> bool:
    client = clients.get(user_id)
    if client is None:
        session_file = Path(f"{session_path(user_id)}.session")
        if not session_file.exists():
            return False
        try:
            client = await get_or_create_client(user_id)
        except AuthKeyUnregisteredError:
            logger.warning(
                "جلسة المستخدم %s غير صالحة أثناء فحص التفويض؛ تم الحفاظ على الملف",
                user_id,
            )
            return False
    try:
        return await client.is_user_authorized()
    except AuthKeyUnregisteredError:
        logger.warning(
            "جلسة المستخدم %s غير صالحة أثناء فحص التفويض؛ لن يتم حذفها تلقائياً",
            user_id,
        )
        clients.pop(user_id, None)
        return False


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    user_id = update.effective_user.id
    logger.info("استلام /start من المستخدم %s", user_id)
    if user_id != OWNER_ID:
        subscribed, reason = await force_subscription_status(context, user_id)
        if not subscribed:
            join_url = FORCE_SUB_URL or (f"https://t.me/{FORCE_SUB_CHANNEL.lstrip('@')}" if FORCE_SUB_CHANNEL.startswith("@") else "")
            buttons = [[InlineKeyboardButton("📢 اشترك في القناة", url=join_url)]] if join_url else []
            buttons.append([InlineKeyboardButton("✅ تحقّق من الاشتراك", callback_data="user:check_sub")])
            await update.message.reply_text(
                "🔒 يجب الاشتراك في القناة أولاً.\n\nاشترك ثم اضغط «تحقّق من الاشتراك» حتى تظهر لك مزايا البوت وتبدأ تسجيل الدخول.",
                reply_markup=InlineKeyboardMarkup(buttons),
            )
            return
    try:
        register_user(update.effective_user, referral_id_from_args(context.args))
    except Exception:
        logger.exception("تعذر حفظ بيانات المستخدم %s؛ يستمر /start دون الحفظ", user_id)
    if user_id in admins:
        await update.message.reply_text(
            "🛠️ *لوحة الإدارة*\n\nاختر القسم المطلوب من الأزرار أدناه.",
            parse_mode="Markdown",
            reply_markup=owner_keyboard() if user_id == OWNER_ID else admin_keyboard(),
        )
        return
    try:
        ready = await asyncio.wait_for(is_ready(user_id), timeout=20)
    except asyncio.TimeoutError:
        logger.warning("انتهت مهلة فحص جلسة المستخدم %s أثناء /start", user_id)
        ready = False
    except Exception:
        logger.exception("فشل فحص جلسة المستخدم %s أثناء /start", user_id)
        ready = False
    if ready:
        if user_id in admins:
            await update.message.reply_text(
                "🛠️ *لوحة الإدارة*\n\nاختر القسم المطلوب من الأزرار أدناه.",
                parse_mode="Markdown",
                reply_markup=admin_keyboard(),
            )
        else:
            await update.message.reply_text(
                "✅ *حسابك متصل*\n\nأرسل رابط منشور Telegram الذي تريد تنزيله.\n\n"
                "استخدم زر المساعدة لمعرفة طريقة الاستخدام.",
                parse_mode="Markdown",
                reply_markup=user_keyboard(user_id),
            )
        return
    await update.message.reply_text(
        "تنزيل المحتوى مقفول الحفظ من القنوات و القروبات فقط",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔑 ابدأ تسجيل الدخول", callback_data="user:login")]]),
    )


async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user:
        states.pop(update.effective_user.id, None)
    if update.message:
        await update.message.reply_text("تم إلغاء العملية الحالية.")


def download_choices_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"{n:+d}", callback_data=f"download:{n}") for n in range(-5, 0)],
        [InlineKeyboardButton("📌 الحالي", callback_data="download:0")],
        [InlineKeyboardButton(f"+{n}", callback_data=f"download:{n}") for n in range(1, 6)],
        [InlineKeyboardButton("❌ إلغاء", callback_data="download:cancel")],
    ])


def link_with_selected_message_id(link: str, offset: int) -> str:
    """Move the final Telegram message id backward/forward without changing the channel."""
    match = re.search(r"/(\d+)/?$", link.strip())
    if not match:
        raise ValueError("الرابط لا يحتوي على رقم رسالة في نهايته.")
    message_id = int(match.group(1)) + int(offset)
    if message_id <= 0:
        raise ValueError("رقم الرسالة الناتج غير صالح.")
    return link.strip()[:match.start(1)] + str(message_id) + link.strip()[match.end(1):]


def link_with_message_id(link: str, message_id: int) -> str:
    match = re.search(r"/(\d+)/?$", link.strip())
    if not match or int(message_id) <= 0:
        raise ValueError("الرابط أو رقم الرسالة غير صالح.")
    return link.strip()[:match.start(1)] + str(int(message_id)) + link.strip()[match.end(1):]


def links_for_download_count(link: str, choice: int) -> list[str]:
    """Return one link or a contiguous batch around the linked message."""
    count = abs(int(choice)) if choice else 1
    if count > 5:
        raise ValueError("يمكن تنزيل 5 مقاطع كحد أقصى في الطلب الواحد.")
    if choice > 0:
        offsets = range(0, count)
    elif choice < 0:
        offsets = range(-count + 1, 1)
    else:
        offsets = (0,)
    return [link_with_selected_message_id(link, offset) for offset in offsets]


async def media_links_for_batch(user_id: int, link: str, choice: int) -> list[str]:
    """Find the requested number of actual media messages around the linked post."""
    parsed = parse_message_link(link)
    if not parsed:
        raise ValueError("الرابط غير صالح.")
    entity, base_id = parsed
    needed = abs(int(choice)) if choice else 1
    direction = 1 if choice >= 0 else -1
    client = None
    temporary = False
    try:
        if await is_ready(user_id):
            client = await get_or_create_client(user_id)
        elif isinstance(entity, str):
            client = await get_public_client()
            temporary = True
        else:
            raise ValueError("لا توجد جلسة Telegram صالحة للوصول إلى هذه الرسائل.")
        scan_ids = [base_id + direction * step for step in range(0, max(needed * 20, 40))]
        if user_id == OWNER_ID and not isinstance(entity, str):
            client, resolved_entity, _ = await find_owner_access_client(entity)
        else:
            resolved_entity = entity if isinstance(entity, str) else await resolve_channel_entity(client, entity)
        messages = await client.get_messages(resolved_entity, ids=scan_ids)
        media_ids = [int(getattr(message, "id", 0)) for message in messages if message and message.media]
        media_ids = [value for value in media_ids if value > 0]
        if direction < 0:
            media_ids.sort(reverse=True)
        else:
            media_ids.sort()
        if len(media_ids) < needed:
            raise ValueError(f"وجدت {len(media_ids)} وسائط فقط حول الرسالة، ولم أجد {needed} مقاطع.")
        return [link_with_message_id(link, value) for value in media_ids[:needed]]
    finally:
        if temporary and client is not None and client.is_connected():
            await client.disconnect()


async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return

    user_id = update.effective_user.id
    text = (update.message.text or "").strip()
    state = states.get(user_id, {})

    if user_id != OWNER_ID:
        subscribed, reason = await force_subscription_status(context, user_id)
        if not subscribed:
            join_url = FORCE_SUB_URL or (f"https://t.me/{FORCE_SUB_CHANNEL.lstrip('@')}" if FORCE_SUB_CHANNEL.startswith("@") else "")
            buttons = [[InlineKeyboardButton("📢 اشترك في القناة", url=join_url)]] if join_url else []
            buttons.append([InlineKeyboardButton("✅ تحقّق من الاشتراك", callback_data="user:check_sub")])
            await update.message.reply_text("🔒 يجب الاشتراك في القناة أولاً لاستخدام البوت.", reply_markup=InlineKeyboardMarkup(buttons))
            return
    register_user(update.effective_user)

    if user_id != OWNER_ID and is_user_blocked(user_id):
        await update.message.reply_text(blocked_message(user_id))
        return
    async with get_lock(user_id):
        if state.get("step") == "phone":
            await begin_login(update, user_id, text)
            return
        if state.get("step") == "code":
            await finish_code(update, user_id, text)
            return
        if state.get("step") == "password":
            await finish_password(update, user_id, text)
            return
        if (user_id in admins or can_use_channel_transfer(user_id)) and state.get("step") in {
            "transfer_source", "transfer_target", "transfer_delete", "admin_add", "admin_broadcast", "transfer_access_grant", "transfer_access_revoke", "force_sub_channel"
        }:
            if state.get("step") == "admin_add" and user_id != OWNER_ID:
                states.pop(user_id, None)
                await update.message.reply_text("⛔ إضافة المشرفين مخصصة للمالك فقط.")
                return
            if state.get("step", "").startswith("transfer_"):
                await handle_transfer_input(update, text, state)
            else:
                await handle_admin_input(update, context, text, state)
            return

    try:
        ready = await asyncio.wait_for(is_ready(user_id), timeout=20)
    except Exception:
        logger.exception("فشل فحص الجلسة قبل معالجة رسالة المستخدم %s", user_id)
        ready = False
    if ready:
        if user_id not in admins:
            quota = quota_snapshot(user_id)
            if quota["total_remaining"] <= 0:
                await update.message.reply_text(
                    "🚫 انتهت حصتك الحالية.\n\n"
                    "الحصة اليومية: 5 مقاطع. ادعُ مستخدماً جديداً عبر رابطك لتحصل على 5 مقاطع إضافية لكل إحالة.\n\n"
                    f"👥 إحالاتك المقبولة: {quota['referral_count']}\n"
                    "🔗 رابط الدعوة موجود في زر حالة الحساب."
                )
                return
        pending_downloads[user_id] = (text, time.time(), update.message)
        await update.message.reply_text(
            "اختر الرسالة حول الرابط: السابقة أو الحالية أو التالية.",
            reply_markup=download_choices_keyboard(),
        )
    else:
        # القنوات العامة يمكن تجربتها دون تسجيل دخول؛ المحتوى الخاص أو المقيد
        # سيستمر في طلب جلسة Telegram مسجلة.
        if is_public_message_link(text):
            quota = quota_snapshot(user_id)
            if quota["total_remaining"] <= 0 and user_id not in admins:
                await update.message.reply_text(
                    localized(user_id,
                        "🚫 انتهت حصتك الحالية. ادعُ مستخدماً جديداً من حالة الحساب للحصول على رصيد إضافي.",
                        "🚫 Your quota is exhausted. Invite a new user from Account status to get bonus credits."
                    )
                )
                return
            pending_downloads[user_id] = (text, time.time(), update.message)
            await update.message.reply_text(
                "اختر الرسالة حول الرابط: السابقة أو الحالية أو التالية.",
                reply_markup=download_choices_keyboard(),
            )
        else:
            await update.message.reply_text(localized(user_id, "أرسل /start لتسجيل الدخول أو أرسل رابط قناة عامة.", "Send /start to log in, or send a public channel link."))


async def run_link_task(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    user_id: int,
    text: str,
) -> None:
    try:
        succeeded = await process_link(update, context, user_id, text)
        if succeeded:
            record_download_success(user_id)
            if user_id not in admins:
                consume_quota(user_id)
            quota = quota_snapshot(user_id)
            try:
                await update.message.reply_text(
                    f"📊 المتبقي: {quota['total_remaining']} مقطع "
                    f"(اليومي: {quota['daily_remaining']}، الإضافي: {quota['bonus_credits']})."
                )
            except Exception:
                logger.exception("تعذر إرسال رصيد المستخدم %s", user_id)
    except asyncio.CancelledError:
        logger.info("تم إلغاء مهمة الرابط للمستخدم %s", user_id)
        raise
    except Exception:
        logger.exception("خطأ غير معالج في مهمة الرابط للمستخدم %s", user_id)
    finally:
        current = asyncio.current_task()
        if active_link_tasks.get(user_id) is current:
            active_link_tasks.pop(user_id, None)


async def begin_login(update: Update, user_id: int, phone: str) -> None:
    if not re.fullmatch(r"\+[1-9]\d{7,14}", phone):
        await update.message.reply_text(
            "⚠️ رقم الهاتف غير صحيح.\n\nأرسله بالصيغة الدولية، مثل: `+249XXXXXXXXX`.",
            parse_mode="Markdown",
        )
        return

    try:
        client = await asyncio.wait_for(get_or_create_client(user_id), timeout=30)
        sent = await asyncio.wait_for(client.send_code_request(phone), timeout=60)
    except AuthKeyUnregisteredError:
        # المستخدم بدأ تسجيل دخول صريحاً؛ هنا فقط نزيل الجلسة القديمة
        # الخاصة بهذا المستخدم في البوت، ثم ننشئ جلسة نظيفة.
        clients.pop(user_id, None)
        await discard_client_session(user_id, remove_file=True)
        try:
            client = await asyncio.wait_for(get_or_create_client(user_id), timeout=30)
            sent = await asyncio.wait_for(client.send_code_request(phone), timeout=60)
        except Exception as exc:
            states.pop(user_id, None)
            logger.exception("فشل إنشاء جلسة جديدة للمستخدم %s بعد جلسة تالفة", user_id)
            await update.message.reply_text(
                f"❌ تعذر إنشاء جلسة Telegram جديدة ({type(exc).__name__}). أرسل /start وحاول مرة أخرى."
            )
            return
    except ValueError as exc:
        if "cannot be reused after logging out" not in str(exc).lower():
            states.pop(user_id, None)
            logger.exception("فشل تجهيز جلسة المستخدم %s", user_id)
            await update.message.reply_text(f"❌ تعذر تجهيز تسجيل الدخول ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
            return
        # تسجيل الدخول الصريح يسمح باستبدال جلسة هذا المستخدم فقط.
        clients.pop(user_id, None)
        await discard_client_session(user_id, remove_file=True)
        try:
            client = await asyncio.wait_for(get_or_create_client(user_id), timeout=30)
            sent = await asyncio.wait_for(client.send_code_request(phone), timeout=60)
        except Exception as retry_exc:
            states.pop(user_id, None)
            logger.exception("فشل إعادة إنشاء جلسة المستخدم %s", user_id)
            await update.message.reply_text(
                f"❌ تعذر إنشاء جلسة Telegram جديدة ({type(retry_exc).__name__}). أرسل /start وحاول مرة أخرى."
            )
            return
    except FloodWaitError as exc:
        states.pop(user_id, None)
        wait_seconds = int(exc.seconds)
        wait_minutes = (wait_seconds + 59) // 60
        await update.message.reply_text(
            f"Telegram فرض فترة انتظار بسبب كثرة طلبات الرموز. حاول مرة أخرى بعد نحو {wait_minutes} دقيقة."
        )
        logger.warning("FloodWait عند طلب رمز للمستخدم %s: %s ثانية", user_id, wait_seconds)
        return
    except (PhoneNumberInvalidError, PhoneNumberBannedError) as exc:
        states.pop(user_id, None)
        reason = "رقم الهاتف غير صحيح." if isinstance(exc, PhoneNumberInvalidError) else "هذا الرقم محظور من Telegram."
        await update.message.reply_text(f"❌ تعذر إرسال الرمز.\n\n{reason}\nتحقق من الرقم الدولي ثم أرسل /start وحاول مرة أخرى.")
        return
    except SendCodeUnavailableError:
        states.pop(user_id, None)
        await update.message.reply_text("❌ Telegram لا يسمح بإرسال رمز جديد لهذا الرقم حالياً. انتظر قليلاً ثم أرسل /start وحاول مرة أخرى.")
        return
    except asyncio.TimeoutError:
        states.pop(user_id, None)
        logger.warning("انتهت مهلة طلب رمز الدخول للمستخدم %s", user_id)
        await update.message.reply_text("⏱️ لم يصل رد Telegram في الوقت المحدد. لم تُحفظ محاولة ناقصة؛ أرسل /start وحاول مرة أخرى.")
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("فشل طلب رمز الدخول للمستخدم %s", user_id)
        await update.message.reply_text(
            "❌ تعذر إرسال رمز Telegram.\n\n"
            f"السبب التقني: `{type(exc).__name__}`\n\n"
            "لم يتم الانتقال إلى خطوة الرمز. تحقق من الرقم وأرسل /start وحاول مرة أخرى.",
            parse_mode="Markdown",
        )
        return

    states[user_id] = {
        "step": "code",
        "phone": phone,
        "phone_code_hash": sent.phone_code_hash,
    }
    await update.message.reply_text(
        "📩 تم إرسال رمز Telegram.\n\n"
        "الخطوة ٢ من ٣: أرسل الرمز *مفرقاً إجبارياً* بهذا الشكل:\n"
        "`1 2 3 4 5`\n\n"
        "لا ترسله هكذا: `12345`.\n"
        "للإلغاء استخدم /cancel.",
    )


async def finish_code(update: Update, user_id: int, code: str) -> None:
    state = states.get(user_id, {})
    spaced_code_pattern = r"^\s*[0-9٠-٩](?:\s+[0-9٠-٩]){3,7}\s*$"
    if not re.fullmatch(spaced_code_pattern, code):
        await update.message.reply_text(
            "⚠️ أرسل رمز التحقق مفرقاً بين كل رقم، مثل:\n\n"
            "`1 2 3 4 5`\n\n"
            "لا ترسله متجمعاً مثل `12345`.",
            parse_mode="Markdown",
        )
        return
    normalized_code = normalize_otp(code)

    try:
        client = await get_or_create_client(user_id)
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("تعذر تجهيز جلسة التحقق للمستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر تجهيز تسجيل الدخول ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return

    try:
        await client.sign_in(
            phone=state["phone"],
            code=normalized_code,
            phone_code_hash=state["phone_code_hash"],
        )
    except SessionPasswordNeededError:
        states[user_id] = {"step": "password", "phone": state.get("phone")}

        await update.message.reply_text(
            "الحساب محمي بالتحقق بخطوتين. أرسل كلمة المرور مرة واحدة لإكمال الدخول."
        )
        return
    except PhoneCodeInvalidError:
        await update.message.reply_text("⚠️ الرمز غير صحيح. أرسله مرة أخرى مفرقاً، مثل: 1 2 3 4 5.")
        return
    except PhoneCodeExpiredError:
        states.pop(user_id, None)
        await update.message.reply_text("⚠️ انتهت صلاحية الرمز. أرسل /start واطلب رمزاً جديداً.")
        return
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("فشل التحقق من رمز المستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر التحقق من الرمز ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return

    states.pop(user_id, None)
    await update.message.reply_text(
        "✅ تم تسجيل الدخول بنجاح.\n\nأرسل الآن رابط منشور الفيديو المصرح بأرشفته.",
    )


async def finish_password(update: Update, user_id: int, password: str) -> None:
    try:
        client = await get_or_create_client(user_id)
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("تعذر تجهيز جلسة كلمة المرور للمستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر تجهيز تسجيل الدخول ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return
    try:
        await client.sign_in(password=password)
    except PasswordHashInvalidError:
        await update.message.reply_text("⚠️ كلمة مرور التحقق بخطوتين غير صحيحة. حاول مرة أخرى أو استخدم /cancel.")
        return
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("فشل التحقق من كلمة مرور المستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر التحقق من كلمة المرور ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return

    states.pop(user_id, None)
    await update.message.reply_text(
        "✅ تم تسجيل الدخول بنجاح.\n\nأرسل الآن رابط منشور الفيديو المصرح بأرشفته.",
    )


def owner_only(update: Update) -> bool:
    return bool(update.effective_user and update.effective_user.id == OWNER_ID)


def message_kind_label(message) -> str:
    if getattr(message, "photo", None):
        return "🖼️ صورة"
    if getattr(message, "video", None):
        return "🎬 فيديو"
    if getattr(message, "voice", None):
        return "🎙️ رسالة صوتية"
    if getattr(message, "audio", None):
        return "🎵 ملف صوتي"
    if getattr(message, "document", None):
        return "📄 ملف"
    if getattr(message, "sticker", None):
        return "🏷️ ملصق"
    if getattr(message, "media", None):
        return "📎 وسائط"
    return "💬 نص"


def message_open_url(entity, message_id: int) -> str | None:
    username = getattr(entity, "username", None)
    if username:
        return f"https://t.me/{username}/{message_id}"
    entity_id = int(getattr(entity, "id", 0) or 0)
    if entity_id < 0:
        return f"https://t.me/c/{abs(entity_id)}/{message_id}"
    return None


def account_display_name(user_id: int, user_obj=None) -> str:
    """اسم الحساب مع اليوزر، مع استخدام الآيدي كمرجع عند غياب الاسم."""
    entry = user_registry.get(str(user_id), {})
    name = getattr(user_obj, "full_name", "") if user_obj is not None else ""
    username = getattr(user_obj, "username", "") if user_obj is not None else ""
    name = name or entry.get("name") or ""
    username = username or entry.get("username") or ""
    if name and username:
        return f"{name} (@{username})"
    if name:
        return str(name)
    if username:
        return f"@{username}"
    return f"حساب Telegram {user_id}"


def admin_only(update: Update) -> bool:
    return bool(update.effective_user and update.effective_user.id in admins)


def has_channel_transfer_access(user_id: int) -> bool:
    """صلاحية نقل القنوات: المالك/المشرف، أو منح يدوي، أو خمسة إحالات."""
    if user_id == OWNER_ID or user_id in admins:
        return True
    entry = user_registry.get(str(user_id), {})
    return bool(entry.get("channel_transfer_access", False)) or int(entry.get("referral_count", 0) or 0) >= TRANSFER_REFERRAL_REQUIREMENT


def can_use_channel_transfer(user_id: int) -> bool:
    return has_channel_transfer_access(user_id)


def transfer_job_visible_to(user_id: int, job: dict[str, Any]) -> bool:
    """المالك يرى كل المهام؛ بقية المستخدمين يرون مهامهم فقط."""
    if user_id == OWNER_ID:
        return True
    return int(job.get("created_by", 0) or 0) == int(user_id)


def transfer_session_for_user(user_id: int, selected_session_id: int | None = None) -> int:
    """تحديد جلسة النقل. المستخدم العادي يستخدم جلسته؛ المالك يستطيع اختيار جلسة أخرى."""
    if selected_session_id is None:
        return int(user_id)
    selected = int(selected_session_id)
    if user_id != OWNER_ID and selected != user_id:
        raise PermissionError("لا يمكن لهذا المستخدم استخدام جلسة حساب آخر.")
    return selected


async def prepare_transfer_session(requesting_user_id: int, selected_session_id: int | None = None):
    """فتح جلسة النقل والتحقق من الحساب الحقيقي داخل ملف الجلسة."""
    session_user_id = transfer_session_for_user(requesting_user_id, selected_session_id)
    session_file = Path(f"{session_path(session_user_id)}.session")
    if not session_file.exists():
        raise ValueError(
            f"لا يوجد ملف جلسة للحساب {session_user_id}. سجّل دخول هذا الحساب أولاً من البوت ثم أعد المحاولة."
        )
    try:
        client = await get_or_create_client(session_user_id)
        authorized = await client.is_user_authorized()
    except AuthKeyUnregisteredError as exc:
        clients.pop(session_user_id, None)
        raise AuthKeyUnregisteredError() from exc
    if not authorized:
        raise ValueError(
            "الجلسة موجودة، لكن الحساب غير مسجل الدخول فيها. API ID وAPI HASH لا يسجلان دخول حساب Telegram؛ "
            "يجب أن تحتوي الجلسة على تسجيل دخول فعلي للحساب."
        )
    me = await client.get_me()
    actual_id = int(getattr(me, "id", 0) or 0)
    if not actual_id:
        raise ValueError("تعذر قراءة هوية حساب Telegram من الجلسة.")
    if actual_id != session_user_id:
        raise ValueError(
            f"عدم تطابق خطير: ملف الجلسة user_{session_user_id}.session مرتبط بالحساب {actual_id}. "
            "لن أستخدم الجلسة ولن أحذف أي ملف."
        )
    return client, me, session_user_id


def transfer_back_callback(user_id: int) -> str:
    return "admin:transfers" if user_id in admins else "user:transfers"


def user_keyboard(user_id: int | None = None) -> InlineKeyboardMarkup:
    uid = int(user_id or 0)
    is_en = user_language(uid) == "en" if uid else False
    rows = [
        [InlineKeyboardButton("🔑 Log in" if is_en else "🔑 تسجيل الدخول", callback_data="user:login")],
        [InlineKeyboardButton("📖 Help" if is_en else "📖 طريقة الاستخدام", callback_data="user:help")],
        [InlineKeyboardButton("🔐 Account status" if is_en else "🔐 حالة الحساب", callback_data="user:account")],
        [InlineKeyboardButton("🔁 Channel transfer" if is_en else "🔁 نقل القنوات", callback_data="user:transfers")],
        [InlineKeyboardButton("🔌 Disconnect temporarily" if is_en else "🔌 فصل مؤقت", callback_data="user:disconnect")],
        [InlineKeyboardButton("🗑️ Log out and delete session" if is_en else "🗑️ حذف الجلسة وتسجيل الخروج", callback_data="user:logout")],
        [InlineKeyboardButton("🌐 العربية" if is_en else "🌐 English", callback_data="user:language")],
    ]
    return InlineKeyboardMarkup(rows)


def transfer_keyboard(back_callback: str = "admin:transfers") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ إضافة قناة مصدر وهدف", callback_data="transfer:add")],
        [InlineKeyboardButton("📋 قائمة القنوات", callback_data="transfer:list")],
        [InlineKeyboardButton("▶️ بدء الكل", callback_data="transfer:start_all"), InlineKeyboardButton("⏹️ إيقاف الكل", callback_data="transfer:stop_all")],
        [InlineKeyboardButton("🗑️ حذف مهمة", callback_data="transfer:delete")],
        [InlineKeyboardButton("⬅️ رجوع", callback_data=back_callback)],
    ])


def admin_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("👥 المستخدمون والجلسات", callback_data="admin:users")],
        [InlineKeyboardButton("🔁 نقل القنوات", callback_data="admin:transfers")],
        [InlineKeyboardButton("📢 إذاعة رسالة", callback_data="admin:broadcast")],
        [InlineKeyboardButton("🔄 تحديث اللوحة", callback_data="admin:home")],
    ])



def _fmt_bytes(n: int) -> str:
    n = max(0, int(n or 0))
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} TB"


def cleanup_old_temp_files(force: bool = False) -> None:
    """Remove abandoned bot temp files, especially when the disk is nearly full."""
    try:
        usage = shutil.disk_usage("/")
        free_percent = usage.free * 100.0 / max(1, usage.total)
        if not force and free_percent >= MIN_FREE_DISK_PERCENT:
            return
        candidates = []
        for root in (Path(tempfile.gettempdir()), Path("/tmp")):
            if not root.exists():
                continue
            for path in root.glob("telegram_*"):
                candidates.append(path)
            for path in root.glob("miniapp_media_*"):
                candidates.append(path)
            for path in root.glob("session_browser_*"):
                candidates.append(path)
        for path in sorted(set(candidates), key=lambda item: item.stat().st_mtime if item.exists() else 0):
            try:
                if path.exists() and time.time() - path.stat().st_mtime > 300:
                    shutil.rmtree(path, ignore_errors=True) if path.is_dir() else path.unlink(missing_ok=True)
            except OSError:
                logger.debug("تعذر حذف الملف المؤقت %s", path, exc_info=True)
    except OSError:
        logger.debug("تعذر فحص مساحة القرص", exc_info=True)

def owner_dashboard_text() -> str:
    active_tasks = sum(1 for t in asyncio.all_tasks() if not t.done())
    active_transfers = sum(1 for t in channel_transfer_tasks.values() if t and not t.done())
    sessions_total = len(clients)
    sessions_connected = sum(1 for c in clients.values() if c and c.is_connected())
    uptime = int(max(0, time.time() - runtime_stats["started_at"]))
    h, rem = divmod(uptime, 3600)
    m, s = divmod(rem, 60)
    return (
        "📊 لوحة تحكم المالك\n\n"
        f"👥 المستخدمون: {len(users)}\n"
        f"🔑 الجلسات: {sessions_total}\n"
        f"🟢 المتصلة: {sessions_connected}\n"
        f"🔄 عمليات النقل النشطة: {active_transfers}\n"
        f"⚙️ المهام النشطة: {active_tasks}\n\n"
        f"📥 التحميلات: {runtime_stats['downloads_started']} بدأ / "
        f"{runtime_stats['downloads_done']} مكتمل / {runtime_stats['downloads_failed']} فشل\n"
        f"🔄 النقل: {runtime_stats['transfers_started']} بدأ / "
        f"{runtime_stats['transfers_done']} مكتمل / {runtime_stats['transfers_failed']} فشل\n"
        f"💬 الرسائل المعالجة: {runtime_stats['messages_processed']}\n"
        f"⬇️ البيانات: {_fmt_bytes(runtime_stats['bytes_downloaded'])}\n"
        f"⬆️ البيانات: {_fmt_bytes(runtime_stats['bytes_uploaded'])}\n"
        f"⏱️ التشغيل: {h:02d}:{m:02d}:{s:02d}"
    )

def owner_dashboard_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔄 تحديث الإحصائيات", callback_data="owner:dashboard")],
        [InlineKeyboardButton("👥 الجلسات", callback_data="owner:sessions")],
        [InlineKeyboardButton("🔄 عمليات النقل", callback_data="transfer:list")],
    ])

def owner_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🌐 فتح Telegram Mini App", web_app=WebAppInfo(url=WEB_PUBLIC_BASE_URL))],
        [InlineKeyboardButton("🔑 تسجيل الدخول / تبديل الحساب", callback_data="user:login")],
        [InlineKeyboardButton("👥 المستخدمون والجلسات", callback_data="admin:users")],
        [InlineKeyboardButton("🔁 نقل القنوات", callback_data="admin:transfers")],
        [InlineKeyboardButton("💬 استعراض جلساتي", callback_data="owner:sessions")],
        [InlineKeyboardButton("📢 إذاعة رسالة", callback_data="admin:broadcast")],
        [InlineKeyboardButton("🔒 الاشتراك الإجباري", callback_data="admin:force_sub")],
        [InlineKeyboardButton("🔄 تحديث اللوحة", callback_data="admin:home")],
    ])


async def channels_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    if not channel_transfers:
        text = "📋 قائمة القنوات فارغة.\nأضف قناة بصيغة:\n/addchannel @source @target"
    else:
        rows = []
        for job_id, job in channel_transfers.items():
            rows.append(
                f"{job_id}. {job['source']} ➜ {job['target']} | "
                f"جلسة: {job.get('session_user_id', OWNER_ID)} | "
                f"{job.get('status', 'متوقف')} | آخر رسالة: {job.get('last_message_id', 0)}"
            )
        text = "📋 قائمة نقل القنوات:\n\n" + "\n".join(rows)
    await update.message.reply_text(text, reply_markup=admin_keyboard())


async def add_channel_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    if len(context.args) != 2:
        await update.message.reply_text("الاستخدام: /addchannel @قناة_المصدر @قناة_الهدف")
        return
    source, target = context.args
    try:
        source = normalize_channel_ref(source)
        target = normalize_channel_ref(target)
    except ValueError as exc:
        await update.message.reply_text(f"⚠️ {exc}")
        return
    try:
        client = await get_or_create_client(OWNER_ID)
    except AuthKeyUnregisteredError:
        clients.pop(OWNER_ID, None)
        await update.message.reply_text(
            "⚠️ جلسة المالك غير صالحة لدى Telegram. لم يتم حذف ملفها. أعد تسجيل الدخول ثم حاول مرة أخرى."
        )
        return
    try:
        me = await inspect_session_identity(OWNER_ID, client)
    except AuthKeyUnregisteredError:
        clients.pop(OWNER_ID, None)
        await update.message.reply_text("⚠️ جلسة المالك غير صالحة لدى Telegram. لم يتم حذف ملفها. أعد تسجيل الدخول ثم حاول مرة أخرى.")
        return
    except Exception:
        await update.message.reply_text("سجّل دخول حساب النقل أولاً عبر /start.")
        return
    try:
        await resolve_channel_entity(client, source)
        await resolve_channel_entity(client, target)
    except Exception as exc:
        logger.exception("تعذر التحقق من القنوات")
        await update.message.reply_text(
            "تعذر الوصول إلى إحدى القناتين. تأكد أن حساب النقل عضو في المصدر ومشرف في الهدف.\n"
            f"التفصيل: {exc}"
        )
        return
    job_id = str(max([int(k) for k in channel_transfers if str(k).isdigit()] or [0]) + 1)
    channel_transfers[job_id] = {
        "source": source,
        "target": target,
        "created_by": OWNER_ID,
        "session_user_id": OWNER_ID,
        "session_account_id": int(getattr(me, "id", 0) or 0),
        "session_account_username": getattr(me, "username", "") or "",
        "status": "متوقف",
        "last_message_id": 0,
        "sent_count": 0,
        "skipped_count": 0,
        "skipped_message_ids": [],
    }
    save_channel_transfers()
    await update.message.reply_text(f"✅ تمت إضافة النقل رقم {job_id}: {source} ➜ {target}")


async def handle_transfer_input(update: Update, text: str, state: dict[str, Any]) -> None:
    if not update.message:
        return
    user_id = update.effective_user.id
    step = state.get("step")
    if step == "transfer_source":
        if not text:
            await update.message.reply_text("أرسل قناة المصدر بصيغة @username أو رابط القناة أو المعرّف الرقمي.")
            return
        try:
            state["source"] = normalize_channel_ref(text)
        except ValueError as exc:
            await update.message.reply_text(f"⚠️ {exc}")
            return
        state["step"] = "transfer_target"
        await update.message.reply_text(
            "أرسل الآن قناة الهدف بصيغة @username أو رابط القناة أو المعرّف الرقمي."
        )
        return
    if step == "transfer_target":
        source = state.get("source")
        target = text
        try:
            source = normalize_channel_ref(source or "")
            target = normalize_channel_ref(target)
        except ValueError as exc:
            await update.message.reply_text(f"⚠️ {exc}\nأرسل قيمة القناة من جديد، أو اضغط /cancel.")
            state["step"] = "transfer_source"
            return
        if not source or not target:
            states.pop(user_id, None)
            await update.message.reply_text("تعذر حفظ القنوات. اضغط إضافة وحاول من جديد.", reply_markup=transfer_keyboard(transfer_back_callback(user_id)))
            return
        # الجلسة تُحفظ صراحة داخل الحالة. للمستخدم الممنوح له النقل تكون جلسته هو،
        # وللمالك يمكن أن تكون جلسة اختارها من «استعراض جلساتي».
        requested_session_id = state.get("transfer_session_id")
        try:
            client, session_me, transfer_session_id = await prepare_transfer_session(
                user_id, int(requested_session_id) if requested_session_id is not None else None
            )
        except AuthKeyUnregisteredError:
            await update.message.reply_text(
                "⚠️ مفتاح جلسة الحساب غير مسجل لدى Telegram. لم يتم حذف الملف.\n"
                "أعد تسجيل الدخول للحساب من البوت ثم حاول النقل مرة أخرى."
            )
            return
        except Exception as identity_error:
            await update.message.reply_text(
                f"⚠️ تعذر التحقق من جلسة النقل.\n\n{identity_error}\n\n"
                "ملاحظة: API ID وAPI HASH هما بيانات تطبيق وليسا تسجيل دخول للحساب."
            )
            return
        try:
            source_entity = await resolve_channel_entity(client, source)
            target_entity = await resolve_channel_entity(client, target)
            if getattr(source_entity, "id", None) == getattr(target_entity, "id", None):
                raise ValueError("قناة المصدر وقناة الهدف متطابقتان. اختر قناتين مختلفتين.")
        except Exception as exc:
            logger.exception("تعذر التحقق من القنوات من الواجهة")
            await update.message.reply_text(
                "تعذر الوصول إلى إحدى القناتين. تأكد من عضوية الحساب وصلاحية الإرسال في الهدف.\n"
                f"التفصيل: {exc}\n\nأرسل اسم المصدر من جديد، أو اضغط /cancel."
            )
            state["step"] = "transfer_source"
            return
        job_id = str(max([int(k) for k in channel_transfers if str(k).isdigit()] or [0]) + 1)
        channel_transfers[job_id] = {
            "source": source,
            "target": target,
            "created_by": int(user_id),
            "session_user_id": transfer_session_id,
            "session_account_id": int(getattr(session_me, "id", 0) or 0),
            "session_account_username": getattr(session_me, "username", "") or "",
            "status": "متوقف",
            "last_message_id": 0,
            "sent_count": 0,
            "skipped_count": 0,
        }
        save_channel_transfers()
        states.pop(user_id, None)
        await update.message.reply_text(
            f"✅ تمت الإضافة رقم {job_id}.\n{source} ➜ {target}",
            reply_markup=transfer_keyboard(transfer_back_callback(user_id)),
        )
        return
    if step == "transfer_delete":
        if text not in channel_transfers or not transfer_job_visible_to(user_id, channel_transfers[text]):
            await update.message.reply_text("رقم المهمة غير موجود أو لا تملك صلاحية حذفها.")
            return
        task = channel_transfer_tasks.get(int(text))
        if task and not task.done():
            task.cancel()
        channel_transfers.pop(text, None)
        save_channel_transfers()
        states.pop(user_id, None)
        await update.message.reply_text("🗑️ حُذفت مهمة النقل.", reply_markup=transfer_keyboard(transfer_back_callback(user_id)))


def format_transfer_status(job_id: str, job: dict[str, Any]) -> str:
    status = job.get("status", "متوقف")
    sent = int(job.get("sent_count", 0))
    skipped = int(job.get("skipped_count", 0))
    last_id = int(job.get("last_message_id", 0))
    total = int(job.get("total_messages", 0))
    processed = sent + skipped
    if total > 0:
        percent = min(100, int(processed * 100 / total))
        progress = f"📊 التقدم: {processed} من {total} ({percent}٪)"
    else:
        progress = f"📊 تمت معالجة: {processed} رسالة"
    return (
        f"🔄 مهمة نقل رقم {job_id}\n\n"
        f"📥 المصدر: {job.get('source')}\n"
        f"📤 الهدف: {job.get('target')}\n"
        f"👤 جلسة النقل: {job.get('session_user_id', OWNER_ID)}"
        + (f" (@{job.get('session_account_username')})" if job.get('session_account_username') else "")
        + "\n"
        f"📌 الحالة: {status}\n"
        + (f"🛑 الخطأ: {job.get('error')}\n" if job.get('error') else "")
        + f"✅ تم الإرسال: {sent}\n"
        f"⚠️ تم التخطي: {skipped}\n"
        f"🆔 آخر رسالة: {last_id}\n"
        f"{progress}"
    )


async def update_transfer_status_message(job_id: str, context: ContextTypes.DEFAULT_TYPE) -> None:
    job = channel_transfers.get(job_id)
    if not job:
        return
    last_text = format_transfer_status(job_id, job)
    status_recipient = int(job.get("created_by") or OWNER_ID)
    message = await context.bot.send_message(
        chat_id=status_recipient,
        text=last_text,
    )
    try:
        while True:
            # تحديث كل 30 ثانية لتجنب Flood control؛ تقدم الملف التفصيلي
            # يبقى محفوظاً في الحالة ويظهر عند كل تحديث ناجح.
            await asyncio.sleep(30)
            job = channel_transfers.get(job_id)
            if not job:
                return
            new_text = format_transfer_status(job_id, job)
            if new_text != last_text:
                try:
                    await message.edit_text(new_text)
                    last_text = new_text
                except RetryAfter as exc:
                    wait_seconds = int(getattr(exc, "retry_after", 60))
                    logger.warning(
                        "Flood control أثناء تحديث المهمة %s؛ إيقاف تحديث الواجهة لمدة %s ثانية مع استمرار النقل",
                        job_id,
                        wait_seconds,
                    )
                    # لا نكرر editMessageText أثناء الحظر؛ عامل النقل مستقل ويستمر
                    # في حفظ status و last_message_id داخل ملف الحالة.
                    return
                except BadRequest as exc:
                    if "Message is not modified" not in str(exc):
                        logger.exception("تعذر تحديث رسالة تقدم المهمة %s", job_id)
                except Exception:
                    logger.exception("تعذر تحديث رسالة تقدم المهمة %s", job_id)
            if job.get("status") in {"مكتمل", "متوقف", "فشل"}:
                return
    except asyncio.CancelledError:
        job = channel_transfers.get(job_id)
        if job:
            final_text = format_transfer_status(job_id, job)
            if final_text != last_text:
                try:
                    await message.edit_text(final_text)
                except BadRequest as exc:
                    if "Message is not modified" not in str(exc):
                        logger.exception("تعذر تحديث الحالة النهائية للمهمة %s", job_id)
                except Exception:
                    logger.exception("تعذر تحديث الحالة النهائية للمهمة %s", job_id)
        raise


async def start_transfer_job(job_id: str, context: ContextTypes.DEFAULT_TYPE) -> None:
    async with transfer_semaphore:
        return await _start_transfer_job_inner(job_id, context)


async def _start_transfer_job_inner(job_id: str, context: ContextTypes.DEFAULT_TYPE) -> None:
    job = channel_transfers[job_id]
    progress_task = None
    job["status"] = "جارٍ تشغيل المهمة"
    job.pop("error", None)
    save_channel_transfers()
    progress_task = asyncio.create_task(update_transfer_status_message(job_id, context))
    try:
        logger.info("بدأ عامل نقل القنوات للمهمة %s", job_id)
        created_by = int(job.get("created_by") or OWNER_ID)
        transfer_session_id = int(job.get("session_user_id") or created_by)
        job["session_user_id"] = transfer_session_id
        job["status"] = f"جارٍ الاتصال بجلسة النقل {transfer_session_id}"
        try:
            client, session_me, transfer_session_id = await prepare_transfer_session(
                created_by, transfer_session_id
            )
        except AuthKeyUnregisteredError:
            job["status"] = "فشل؛ جلسة النقل غير صالحة"
            job["error"] = (
                f"جلسة النقل المرتبطة بالمعرّف {transfer_session_id} غير مسجلة لدى Telegram. "
                "لم يتم حذف ملف الجلسة تلقائياً."
            )
            save_channel_transfers()
            return
        except Exception as exc:
            job["status"] = "فشل؛ تعذر التحقق من جلسة النقل"
            job["error"] = str(exc)
            save_channel_transfers()
            return
        job["session_account_id"] = int(getattr(session_me, "id", 0) or 0)
        job["session_account_username"] = getattr(session_me, "username", "") or ""
        job["session_account_name"] = getattr(session_me, "first_name", "") or ""
        job["status"] = "جارٍ التحقق من القنوات"
        job.pop("error", None)
        save_channel_transfers()
        source = await resolve_channel_entity(client, job["source"])
        target = await resolve_channel_entity(client, job["target"])
        source_id = getattr(source, "id", None)
        target_id = getattr(target, "id", None)
        logger.info(
            "تم حل القنوات للمهمة %s: source_id=%s target_id=%s",
            job_id,
            source_id,
            target_id,
        )
        job["status"] = "جارٍ فهرسة محتوى الهدف للمقارنة"
        save_channel_transfers()
        target_signatures = await build_target_signature_index(client, target)
        job["target_indexed_count"] = len(target_signatures)
        logger.info("تمت فهرسة %s بصمة في الهدف للمهمة %s", len(target_signatures), job_id)
        if source_id is not None and source_id == target_id:
            raise ValueError(
                "قناة المصدر والهدف متطابقتان فعلياً؛ احذف المهمة وأضف قناة هدف مختلفة."
            )
        job["status"] = "جارٍ قراءة عدد الرسائل"
        try:
            job["total_messages"] = await client.get_messages(source, limit=0)
            job["total_messages"] = int(getattr(job["total_messages"], "total", 0) or 0)
        except Exception:
            job["total_messages"] = 0
        job["status"] = "يعمل"
        job.pop("last_skip_reason", None)
        save_channel_transfers()
        found_messages = 0
        async for message in client.iter_messages(
            source,
            min_id=int(job.get("last_message_id", 0)),
            reverse=True,
        ):
            if message.id <= int(job.get("last_message_id", 0)):
                continue
            found_messages += 1
            job["current_message_id"] = int(message.id)
            job["status"] = f"يعمل؛ معالجة الرسالة {message.id}"
            logger.info("معالجة الرسالة %s في المهمة %s", message.id, job_id)
            signature = transfer_message_signature(message)
            if signature and signature in target_signatures:
                job["duplicate_count"] = int(job.get("duplicate_count", 0)) + 1
                job["last_duplicate_message_id"] = int(message.id)
                job["status"] = f"تم تجاوز الرسالة {message.id}؛ موجودة مسبقاً في الهدف"
                job["last_message_id"] = int(message.id)
                save_channel_transfers()
                continue
            delivered = False
            sent_this_message = False
            transfer_attempts = 0
            delivered_source_ids = job.setdefault("delivered_source_message_ids", {})
            if str(message.id) in delivered_source_ids:
                job["duplicate_count"] = int(job.get("duplicate_count", 0)) + 1
                job["last_duplicate_message_id"] = int(message.id)
                job["status"] = f"تم تجاوز الرسالة {message.id}؛ نجاحها محفوظ مسبقاً"
                job["last_message_id"] = int(message.id)
                save_channel_transfers()
                continue
            while not delivered:
                try:
                    # لا نستخدم التحويل المباشر هنا؛ فقد يقبل Telegram الطلب
                    # ثم يعرض الرسالة في الهدف كقناة غير قابلة للعرض.
                    # المسار الوحيد هو تنزيل المحتوى ثم إعادة رفعه كنسخة مستقلة.
                    direct_forwarded = False
                    if not direct_forwarded:
                        if message.media:
                            with tempfile.TemporaryDirectory(prefix=f"transfer_{job_id}_") as temp_dir:
                                progress_clock = {"last": 0.0}

                                def download_progress(current: int, total: int) -> None:
                                    now = time.monotonic()
                                    if total <= 0:
                                        return
                                    if (now - progress_clock["last"] >= 5.0) or current >= total:
                                        progress_clock["last"] = now
                                        percent = min(100, int(current * 100 / total))
                                        job["download_current"] = int(current)
                                        job["download_total"] = int(total)
                                        job["status"] = (
                                            f"يعمل؛ تنزيل الرسالة {message.id}: "
                                            f"{format_size(current)} من {format_size(total)} ({percent}٪)"
                                        )

                                job["status"] = f"يعمل؛ تنزيل الرسالة {message.id}: 0 من الحجم الكلي (0٪)"
                                job["download_current"] = 0
                                job["download_total"] = 0
                                save_channel_transfers()
                                downloaded = await asyncio.wait_for(
                                    client.download_media(
                                        message,
                                        file=temp_dir,
                                        progress_callback=download_progress,
                                    ),
                                    timeout=TRANSFER_MEDIA_TIMEOUT_SECONDS,
                                )
                                if downloaded:
                                    downloaded_size = os.path.getsize(downloaded) if os.path.exists(downloaded) else 0
                                    job["status"] = (
                                        f"يعمل؛ جارٍ رفع الرسالة {message.id}: "
                                        f"0 من {format_size(downloaded_size)} (0٪)"
                                    )
                                    upload_clock = {"last": 0.0}

                                    def upload_progress(current: int, total: int) -> None:
                                        now = time.monotonic()
                                        if total <= 0:
                                            return
                                        if (now - upload_clock["last"] >= 5.0) or current >= total:
                                            upload_clock["last"] = now
                                            percent = min(100, int(current * 100 / total))
                                            job["upload_current"] = int(current)
                                            job["upload_total"] = int(total)
                                            job["status"] = (
                                                f"يعمل؛ رفع الرسالة {message.id}: "
                                                f"{format_size(current)} من {format_size(total)} ({percent}٪)"
                                            )

                                    save_channel_transfers()
                                    sent_result = await asyncio.wait_for(
                                        client.send_file(
                                            target,
                                            downloaded,
                                            caption=message.message or "",
                                            force_document=False,
                                            progress_callback=upload_progress,
                                        ),
                                        timeout=TRANSFER_MEDIA_TIMEOUT_SECONDS,
                                    )
                                    if not await verify_target_message(client, target, sent_result):
                                        raise RuntimeError("تمت محاولة الرفع لكن لم يتم تأكيد ظهور الرسالة في الهدف")
                                    sent_target_id = getattr(sent_result, "id", None)
                                    if isinstance(sent_result, (list, tuple)) and sent_result:
                                        sent_target_id = getattr(sent_result[-1], "id", None)
                                    delivered_source_ids[str(message.id)] = int(sent_target_id or 0)
                                    sent_this_message = True
                                else:
                                    raise ValueError("تعذر تنزيل الوسائط")
                        elif message.message:
                            job["status"] = f"يعمل؛ جارٍ إرسال النص {message.id}"
                            save_channel_transfers()
                            sent_result = await asyncio.wait_for(
                                client.send_message(target, message.message),
                                timeout=120,
                            )
                            if not await verify_target_message(client, target, sent_result):
                                raise RuntimeError("تمت محاولة إرسال النص لكن لم يتم تأكيد ظهوره في الهدف")
                            delivered_source_ids[str(message.id)] = int(getattr(sent_result, "id", 0) or 0)
                            sent_this_message = True
                        else:
                            job["skipped_count"] = int(job.get("skipped_count", 0)) + 1
                            skipped_ids = job.setdefault("skipped_message_ids", [])
                            if int(message.id) not in skipped_ids:
                                skipped_ids.append(int(message.id))
                            job["last_skip_reason"] = "منشور بلا نص أو وسائط قابلة للنقل"
                    delivered = True
                    if sent_this_message:
                        job["sent_count"] = int(job.get("sent_count", 0)) + 1
                        if signature:
                            target_signatures.add(signature)
                        save_channel_transfers()
                except FloodWaitError as exc:
                    wait_seconds = int(exc.seconds)
                    job["status"] = f"انتظار Telegram {wait_seconds} ثانية"
                    save_channel_transfers()
                    await asyncio.sleep(wait_seconds + 2)
                    job["status"] = "يعمل"
                except asyncio.TimeoutError:
                    confirmed_after_timeout = await find_target_message_by_signature(client, target, signature)
                    if confirmed_after_timeout is not None:
                        delivered_source_ids[str(message.id)] = int(getattr(confirmed_after_timeout, "id", 0) or 0)
                        if signature:
                            target_signatures.add(signature)
                        sent_this_message = True
                        delivered = True
                        job["sent_count"] = int(job.get("sent_count", 0)) + 1
                        job["status"] = f"تم تأكيد الرسالة {message.id} بعد انتهاء المهلة؛ لن تتكرر"
                        save_channel_transfers()
                        continue
                    transfer_attempts += 1
                    logger.exception("انتهت مهلة نقل الرسالة %s في المهمة %s", message.id, job_id)
                    if transfer_attempts < 5:
                        job["status"] = (
                            f"إعادة محاولة الرسالة {message.id} "
                            f"({transfer_attempts} من 4) بعد انتهاء المهلة"
                        )
                        job["last_error"] = "انتهت مهلة التنزيل أو الرفع؛ لم تُحسب الرسالة كتخطي"
                        save_channel_transfers()
                        await asyncio.sleep(min(60, transfer_attempts * 10))
                    else:
                        job["status"] = f"فشل نقل الرسالة {message.id} بعد 4 محاولات"
                        job["error"] = "الملف الكبير لم يكتمل؛ أعد تشغيل المهمة للاستئناف من هذه الرسالة"
                        save_channel_transfers()
                        raise RuntimeError(job["error"])
                except Exception as exc:
                    confirmed_after_error = await find_target_message_by_signature(client, target, signature)
                    if confirmed_after_error is not None:
                        delivered_source_ids[str(message.id)] = int(getattr(confirmed_after_error, "id", 0) or 0)
                        if signature:
                            target_signatures.add(signature)
                        sent_this_message = True
                        delivered = True
                        job["sent_count"] = int(job.get("sent_count", 0)) + 1
                        job["status"] = f"تم تأكيد الرسالة {message.id} بعد خطأ مؤقت؛ لن تتكرر"
                        save_channel_transfers()
                        continue
                    transfer_attempts += 1
                    logger.exception("فشل نقل الرسالة %s في المهمة %s", message.id, job_id)
                    if transfer_attempts < 4:
                        job["status"] = (
                            f"إعادة محاولة الرسالة {message.id} "
                            f"({transfer_attempts} من 3): {type(exc).__name__}"
                        )
                        job["last_error"] = f"{type(exc).__name__}: {exc}"
                        save_channel_transfers()
                        await asyncio.sleep(min(60, transfer_attempts * 10))
                    else:
                        job["status"] = f"فشل نقل الرسالة {message.id} بعد 3 محاولات"
                        job["error"] = f"{type(exc).__name__}: {exc}؛ لم تُحسب الرسالة كتخطي"
                        save_channel_transfers()
                        raise
            job["last_message_id"] = int(message.id)
            job.pop("current_message_id", None)
            save_channel_transfers()
        if found_messages == 0:
            job["status"] = "مكتمل؛ لا توجد رسائل جديدة"
            logger.info(
                "اكتملت المهمة %s دون رسائل جديدة؛ last_message_id=%s total=%s",
                job_id,
                job.get("last_message_id", 0),
                job.get("total_messages", 0),
            )
        else:
            job["status"] = "مكتمل"
            logger.info(
                "اكتملت المهمة %s: عُولجت=%s أُرسلت=%s تم تخطيها=%s",
                job_id,
                found_messages,
                job.get("sent_count", 0),
                job.get("skipped_count", 0),
            )
    except asyncio.CancelledError:
        job["status"] = "متوقف"
        raise
    except Exception as exc:
        logger.exception("فشل عامل نقل القنوات للمهمة %s", job_id)
        job["status"] = "فشل"
        job["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        if progress_task and not progress_task.done():
            progress_task.cancel()
            try:
                await progress_task
            except asyncio.CancelledError:
                pass
        save_channel_transfers()
        channel_transfer_tasks.pop(int(job_id), None)


async def start_transfer_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    job_ids = context.args or list(channel_transfers.keys())
    started = []
    for job_id in job_ids:
        if job_id not in channel_transfers:
            continue
        if int(job_id) in channel_transfer_tasks and not channel_transfer_tasks[int(job_id)].done():
            continue
        channel_transfer_tasks[int(job_id)] = asyncio.create_task(start_transfer_job(job_id, context))
        started.append(job_id)
    await update.message.reply_text("▶️ بدأ النقل: " + (", ".join(started) if started else "لا توجد مهمة جديدة."))


async def stop_transfer_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    job_ids = context.args or list(channel_transfers.keys())
    stopped = []
    for job_id in job_ids:
        task = channel_transfer_tasks.get(int(job_id)) if str(job_id).isdigit() else None
        if task and not task.done():
            task.cancel()
            stopped.append(job_id)
    await update.message.reply_text("⏹️ تم طلب إيقاف: " + (", ".join(stopped) if stopped else "لا توجد مهمة تعمل."))


async def transfer_status_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await channels_command(update, context)


async def handle_admin_input(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str, state: dict[str, Any]) -> None:
    if not update.message:
        return
    step = state.get("step")
    if step == "force_sub_channel":
        global FORCE_SUB_CHANNEL, FORCE_SUB_URL
        value = text.strip()
        if value.lower() in {"off", "disable", "تعطيل", "إيقاف"}:
            FORCE_SUB_CHANNEL = ""
            FORCE_SUB_URL = ""
            result = "تم تعطيل الاشتراك الإجباري."
        else:
            try:
                channel_ref = normalize_channel_ref(value)
            except ValueError:
                await update.message.reply_text("⚠️ أرسل @username للقناة أو رابط https://t.me/channel، أو أرسل تعطيل.")
                return
            channel = str(channel_ref)
            url = value.rstrip("/") if value.startswith("https://t.me/") else (f"https://t.me/{channel[1:]}" if channel.startswith("@") else "")
            FORCE_SUB_CHANNEL, FORCE_SUB_URL = channel, url
            result = f"تم تفعيل الاشتراك الإجباري للقناة {channel}."
        save_admin_state()
        states.pop(update.effective_user.id, None)
        await update.message.reply_text(f"✅ {result}", reply_markup=owner_keyboard())
    elif step in {"transfer_access_grant", "transfer_access_revoke"}:
        try:
            target_id = int(text.strip())
            if target_id <= 0:
                raise ValueError
        except ValueError:
            await update.message.reply_text("⚠️ أرسل آيدي Telegram الرقمي فقط، مثل: 123456789")
            return
        target = user_registry.setdefault(str(target_id), {"id": target_id})
        granted = step == "transfer_access_grant"
        target["channel_transfer_access"] = granted
        save_admin_state()
        states.pop(update.effective_user.id, None)
        action = "منح" if granted else "سحب"
        await update.message.reply_text(
            f"✅ تم {action} صلاحية نقل القنوات للمستخدم {target_id}.\n"
            "هذه الصلاحية لا تضيفه كمشرف ولا تمنحه استعراض الجلسات.",
            reply_markup=owner_keyboard(),
        )
    elif step == "admin_add":
        try:
            new_admin = int(text.strip())
            if new_admin <= 0:
                raise ValueError
        except ValueError:
            await update.message.reply_text("⚠️ أرسل آيدي Telegram الرقمي فقط، مثل: 123456789")
            return
        admins.add(new_admin)
        save_admin_state()
        states.pop(update.effective_user.id, None)
        await update.message.reply_text(f"✅ تمت إضافة المشرف {new_admin} بنجاح.", reply_markup=admin_keyboard())
    elif step == "admin_broadcast":
        if not text:
            await update.message.reply_text("⚠️ لا يمكن إرسال إذاعة فارغة. أرسل النص أو /cancel.")
            return
        sent = failed = 0
        broadcast_sem = asyncio.Semaphore(max(1, int(os.getenv("BROADCAST_CONCURRENCY", "8"))))

        async def send_one(user_id: str) -> bool:
            async with broadcast_sem:
                try:
                    await context.bot.send_message(
                        chat_id=int(user_id),
                        text=f"📢 رسالة من الإدارة\n\n{text}",
                    )
                    return True
                except Exception:
                    logger.exception("فشلت الإذاعة إلى المستخدم %s", user_id)
                    return False

        results = await asyncio.gather(
            *(send_one(user_id) for user_id in list(user_registry)),
            return_exceptions=False,
        )
        sent = sum(results)
        failed = len(results) - sent
        states.pop(update.effective_user.id, None)
        await update.message.reply_text(f"✅ اكتملت الإذاعة.\nتم الإرسال: {sent}\nفشل الإرسال: {failed}", reply_markup=admin_keyboard())


def admin_users_text() -> str:
    active_sessions = sum(1 for uid in user_registry if Path(f"{session_path(int(uid))}.session").exists())
    active_clients = sum(1 for client in clients.values() if client.is_connected())
    lines = [
        "👥 *المستخدمون والجلسات*", "",
        f"👤 المستخدمون المسجلون: {len(user_registry)}",
        f"💾 ملفات الجلسات: {active_sessions}",
        f"🔌 الجلسات المتصلة الآن: {active_clients}",
        f"🛡️ عدد المشرفين: {len(admins)}", "",
    ]
    for entry in list(user_registry.values())[-20:]:
        name = entry.get("name") or "بدون اسم"
        username = f"@{entry['username']}" if entry.get("username") else "بدون معرف"
        referral_count = int(entry.get("referral_count", 0) or 0)
        transfer_status = "متاح ✅" if has_channel_transfer_access(int(entry.get("id", 0) or 0)) else "مغلق 🔒"
        if entry.get("channel_transfer_access"):
            transfer_status = "متاح بمنح المالك ✅"
        downloads_count = int(entry.get("downloads_count", 0) or 0)
        lines.append(f"• {name} — {username} — {entry.get('id')} | تنزيلات: {downloads_count} | إحالات: {referral_count} | نقل: {transfer_status}")
    return "\n".join(lines)


def owner_permissions_keyboard() -> InlineKeyboardMarkup:
    rows = []
    for raw_id, entry in list(user_registry.items())[-30:]:
        try:
            uid = int(raw_id)
        except ValueError:
            continue
        label = entry.get("name") or entry.get("username") or str(uid)
        mini = "سحب Mini App" if entry.get("mini_app_access") else "منح Mini App"
        rows.append([InlineKeyboardButton(f"{mini}: {str(label)[:22]}", callback_data=f"admin:mini:{uid}")])
    rows.append([InlineKeyboardButton("⬅️ رجوع", callback_data="admin:users")])
    return InlineKeyboardMarkup(rows)


def admin_users_keyboard() -> InlineKeyboardMarkup:
    rows = []
    for raw_id, entry in list(user_registry.items())[-30:]:
        try:
            uid = int(raw_id)
        except ValueError:
            continue
        label = str(entry.get("name") or entry.get("username") or uid)[:24]
        rows.append([InlineKeyboardButton(f"👤 {label} · {uid}", callback_data=f"admin:user:{uid}")])
    rows.extend([
        [InlineKeyboardButton("🛡️ قائمة المشرفين", callback_data="admin:admins")],
        [InlineKeyboardButton("⬅️ لوحة المالك", callback_data="admin:home")],
    ])
    return InlineKeyboardMarkup(rows)


def user_detail_keyboard(uid: int) -> InlineKeyboardMarkup:
    entry = user_registry.get(str(uid), {})
    mini = "سحب Mini App" if entry.get("mini_app_access") else "منح Mini App"
    transfer = "سحب نقل القنوات" if entry.get("channel_transfer_access") else "منح نقل القنوات"
    blocked = "إلغاء الحظر" if is_user_blocked(uid) else "حظر 24 ساعة"
    archive = "سحب أرشفة الرسائل الموقوتة" if user_registry.get(str(uid), {}).get("timed_archive_granted") else "منح أرشفة الرسائل الموقوتة"
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(archive, callback_data=f"admin:user:{uid}:timed")],
        [InlineKeyboardButton("📁 عرض أرشيف المستخدم", callback_data=f"admin:archive:{uid}")],
        [InlineKeyboardButton("📣 رؤية القنوات المملوكة والدخول إليها", callback_data=f"admin:user:{uid}:channels")],
        [InlineKeyboardButton(mini, callback_data=f"admin:user:{uid}:mini")],
        [InlineKeyboardButton(transfer, callback_data=f"admin:user:{uid}:transfer")],
        [InlineKeyboardButton("➕ زيادة الحد 5", callback_data=f"admin:user:{uid}:quota")],
        [InlineKeyboardButton(blocked, callback_data=f"admin:user:{uid}:block")],
        [InlineKeyboardButton("⬅️ قائمة المستخدمين", callback_data="admin:users")],
    ])


def admins_keyboard() -> InlineKeyboardMarkup:
    rows = []
    for uid in sorted(admins):
        if uid == OWNER_ID:
            rows.append([InlineKeyboardButton(f"👑 المالك: {uid}", callback_data="admin:noop")])
        else:
            rows.append([InlineKeyboardButton(f"🛡️ إزالة المشرف {uid}", callback_data=f"admin:remove:{uid}")])
    rows.append([InlineKeyboardButton("➕ إضافة مشرف", callback_data="admin:add")])
    rows.append([InlineKeyboardButton("⬅️ رجوع", callback_data="admin:home")])
    return InlineKeyboardMarkup(rows)


async def transfer_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query:
        return
    data = query.data or ""
    logger.info("معالجة زر callback: user_id=%s data=%r", update.effective_user.id if update.effective_user else None, data)
    if data.startswith("admin:"):
        if not admin_only(update):
            await query.answer("هذه اللوحة مخصصة للمشرفين فقط.", show_alert=True)
            return
    if data.startswith("transfer:"):
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
    await query.answer()
    if data.startswith("download:"):
        uid = update.effective_user.id
        pending = pending_downloads.pop(uid, None)
        choice = data.split(":", 1)[1]
        if choice == "cancel":
            await query.edit_message_text("تم إلغاء اختيار التنزيل.")
            return
        if not pending or time.time() - pending[1] > 300:
            await query.edit_message_text("انتهت صلاحية الرابط. أرسل الرابط مرة أخرى.")
            return
        if choice not in {str(n) for n in range(-5, 6)}:
            await query.edit_message_text("الاختيار غير صالح.")
            return
        try:
            selected_links = await media_links_for_batch(uid, pending[0], int(choice))
        except ValueError as exc:
            await query.edit_message_text(f"⚠️ {exc}")
            return
        except Exception:
            logger.exception("تعذر تجهيز دفعة التنزيل للمستخدم %s", uid)
            if uid == OWNER_ID:
                await query.edit_message_text("❌ تفاصيل الخطأ للمالك:\n\n" + traceback.format_exc()[-3800:])
            else:
                await query.edit_message_text("⚠️ تعذر العثور على الرسائل المطلوبة. تأكد من صلاحية الرابط وتسجيل الدخول ثم حاول مرة أخرى.")
            return
        requested = len(selected_links)
        if uid not in admins:
            available = quota_snapshot(uid)["total_remaining"]
            if requested > available:
                await query.edit_message_text(f"🚫 رصيدك المتبقي {available} فقط، ولا يكفي لتنزيل {requested} مقاطع.")
                return
        original_message = pending[2]
        await query.edit_message_text(f"✅ بدأ تنزيل {requested} مقطع، بحد أقصى مقطعين بالتوازي.")
        batch_sem = asyncio.Semaphore(2)

        async def run_batch_item(selected_link: str) -> None:
            async with batch_sem:
                task_update = Update(update_id=update.update_id or 0, message=original_message)
                await run_link_task(task_update, context, uid, selected_link)

        await asyncio.gather(*(run_batch_item(selected_link) for selected_link in selected_links))
    elif data == "admin:home":
        await query.edit_message_text("🛠️ *لوحة الإدارة*\n\nاختر القسم المطلوب:", parse_mode="Markdown", reply_markup=owner_keyboard() if owner_only(update) else admin_keyboard())
    elif data == "admin:users":
        if not owner_only(update):
            await query.answer("هذه القائمة مخصصة للمالك فقط.", show_alert=True)
            return
        await query.edit_message_text(
            admin_users_text(),
            reply_markup=admin_users_keyboard(),
        )
    elif data.startswith("admin:user:"):
        if not owner_only(update):
            await query.answer("هذه العملية للمالك فقط.", show_alert=True)
            return
        parts = data.split(":")
        target_id = int(parts[2])
        entry = user_registry.setdefault(str(target_id), {"id": target_id})
        action = parts[3] if len(parts) > 3 else "view"
        if action == "timed":
            enabled_before = bool(entry.get("timed_archive_granted"))
            entry["timed_archive_granted"] = not enabled_before
            if enabled_before:
                entry["timed_archive_enabled"] = False
            save_admin_state()
            if entry["timed_archive_granted"]:
                try:
                    await context.bot.send_message(
                        chat_id=target_id,
                        text="🕒 تم إعطاؤك ميزة حفظ الرسائل الموقوتة.\n\nلن يبدأ الحفظ إلا بعد موافقتك. عند التفعيل سيتم حفظ نسخة دائمة على الخادم، وسيتمكن المالك من عرضها أو تنزيلها أو حذفها.",
                        reply_markup=InlineKeyboardMarkup([
                            [InlineKeyboardButton("✅ تفعيل والموافقة", callback_data="user:archive_accept")],
                            [InlineKeyboardButton("❌ رفض", callback_data="user:archive_reject")],
                        ]),
                    )
                except Exception:
                    logger.exception("تعذر إرسال إشعار الأرشفة للمستخدم %s", target_id)
            await query.answer("تم إرسال إشعار الموافقة للمستخدم" if entry["timed_archive_granted"] else "تم سحب الميزة")
        elif action == "channels":
            try:
                client = await get_or_create_client(target_id)
                if not await client.is_user_authorized():
                    raise ValueError("جلسة هذا المستخدم غير مسجلة الدخول")
                rows = []
                count = 0
                async for dialog in client.iter_dialogs(limit=None):
                    entity = dialog.entity
                    # القنوات المملوكة تحديداً: الحساب هو المنشئ، وليس مجرد عضو أو مشرف.
                    if not bool(getattr(entity, "creator", False)):
                        continue
                    if not (getattr(entity, "broadcast", False) or getattr(entity, "megagroup", False)):
                        continue
                    chat_id = int(getattr(entity, "id", 0) or 0)
                    if not chat_id:
                        continue
                    title = (dialog.name or "بدون اسم")[:45]
                    kind = "📣 قناة" if getattr(entity, "broadcast", False) else "👥 مجموعة"
                    rows.append([InlineKeyboardButton(
                        f"{kind} {title}",
                        callback_data=f"owner:chat:{target_id}:{chat_id}:1",
                    )])
                    count += 1
                rows.append([InlineKeyboardButton("⬅️ رجوع إلى تفاصيل المستخدم", callback_data=f"admin:user:{target_id}")])
                if not count:
                    text = (
                        f"📣 القنوات المملوكة للمستخدم {target_id}\n\n"
                        "لم يتم العثور على قناة يملكها هذا الحساب.\n"
                        "تظهر هنا القنوات التي يكون فيها الحساب هو المنشئ، وليس القنوات التي يتابعها أو يديرها فقط."
                    )
                else:
                    text = f"📣 القنوات المملوكة للمستخدم {target_id}\n\nاختر قناة للدخول واستعراض رسائلها:\nعدد القنوات: {count}"
                await query.edit_message_text(text, reply_markup=InlineKeyboardMarkup(rows))
            except AuthKeyUnregisteredError:
                clients.pop(target_id, None)
                await query.edit_message_text(
                    "⚠️ جلسة هذا المستخدم غير صالحة لدى Telegram.\nلم يتم حذف ملف الجلسة.",
                    reply_markup=user_detail_keyboard(target_id),
                )
            except Exception as exc:
                logger.exception("تعذر عرض القنوات المملوكة للمستخدم %s", target_id)
                await query.edit_message_text(
                    f"⚠️ تعذر عرض القنوات المملوكة.\nالسبب: {type(exc).__name__}: {exc}",
                    reply_markup=user_detail_keyboard(target_id),
                )
            return
        if action == "mini":
            entry["mini_app_access"] = not bool(entry.get("mini_app_access", False))
        elif action == "transfer":
            entry["channel_transfer_access"] = not bool(entry.get("channel_transfer_access", False))
        elif action == "quota":
            entry["bonus_credits"] = int(entry.get("bonus_credits", 0) or 0) + 5
        elif action == "block":
            entry["blocked_until"] = 0 if is_user_blocked(target_id) else int(time.time()) + 86400
        save_admin_state()
        label = entry.get("name") or entry.get("username") or str(target_id)
        await query.edit_message_text(
            f"👤 المستخدم: {label}\n🆔 {target_id}\n📥 إجمالي التنزيلات: {int(entry.get('downloads_count', 0) or 0)}\n\nاختر الإجراء المطلوب:",
            reply_markup=user_detail_keyboard(target_id),
        )
    elif data == "admin:admins":
        if not owner_only(update):
            await query.answer("قائمة المشرفين للمالك فقط.", show_alert=True)
            return
        await query.edit_message_text("🛡️ *قائمة المشرفين*\n\nاختر إزالة مشرف أو إضافة مشرف جديد.", parse_mode="Markdown", reply_markup=admins_keyboard())
    elif data == "admin:force_sub":
        if not owner_only(update):
            await query.answer("هذا الإعداد للمالك فقط.", show_alert=True)
            return
        states[update.effective_user.id] = {"step": "force_sub_channel"}
        await query.edit_message_text(
            "🔒 *الاشتراك الإجباري*\n\n"
            f"القناة الحالية: `{FORCE_SUB_CHANNEL or 'غير مفعّل'}`\n\n"
            "أرسل @username للقناة أو رابطها.\n"
            "للتعطيل أرسل: تعطيل",
            parse_mode="Markdown",
        )
    elif data == "admin:mini":
        if not owner_only(update):
            await query.answer("صلاحيات Mini App للمالك فقط.", show_alert=True)
            return
        await query.edit_message_text("🌐 *صلاحيات Mini App*\n\nاضغط على المستخدم لمنحه أو سحب الصلاحية.", parse_mode="Markdown", reply_markup=owner_permissions_keyboard())
    elif data.startswith("admin:promote:"):
        if not owner_only(update):
            await query.answer("هذه العملية للمالك فقط.", show_alert=True)
            return
        target_id = int(data.rsplit(":", 1)[1])
        if target_id == OWNER_ID:
            await query.answer("المالك موجود دائماً.", show_alert=True)
            return
        if target_id in admins:
            admins.discard(target_id)
            result = "تمت إزالة المشرف"
        else:
            admins.add(target_id)
            result = "تمت إضافة المشرف"
        save_admin_state()
        await query.answer(result)
        await query.edit_message_text(admin_users_text(), reply_markup=admin_users_keyboard())
    elif data.startswith("admin:mini:"):
        if not owner_only(update):
            await query.answer("هذه العملية للمالك فقط.", show_alert=True)
            return
        target_id = int(data.rsplit(":", 1)[1])
        entry = user_registry.setdefault(str(target_id), {"id": target_id})
        entry["mini_app_access"] = not bool(entry.get("mini_app_access", False))
        save_admin_state()
        await query.answer("تم تحديث الصلاحية")
        await query.edit_message_text("🌐 *صلاحيات Mini App*\n\nتم تحديث الصلاحية.", parse_mode="Markdown", reply_markup=owner_permissions_keyboard())
    elif data.startswith("admin:remove:"):
        if not owner_only(update):
            await query.answer("هذه العملية للمالك فقط.", show_alert=True)
            return
        target_id = int(data.rsplit(":", 1)[1])
        if target_id == OWNER_ID:
            await query.answer("لا يمكن إزالة المالك.", show_alert=True)
            return
        admins.discard(target_id)
        save_admin_state()
        await query.answer("تمت إزالة المشرف")
        await query.edit_message_text("🛡️ *قائمة المشرفين*", parse_mode="Markdown", reply_markup=admins_keyboard())
    elif data == "admin:noop":
        await query.answer("هذا هو المالك")
    elif data in {"admin:grant_transfer", "admin:revoke_transfer"}:
        if not owner_only(update):
            await query.answer("هذه العملية مخصصة للمالك فقط.", show_alert=True)
            return
        granting = data == "admin:grant_transfer"
        states[update.effective_user.id] = {"step": "transfer_access_grant" if granting else "transfer_access_revoke"}
        action = "منح" if granting else "سحب"
        await query.edit_message_text(
            f"🛡️ {action} صلاحية نقل القنوات\n\n"
            "أرسل آيدي Telegram الرقمي للمستخدم.\n"
            "لن تتم إضافته كمشرف، ولن يحصل على استعراض جلساتك.\n\n"
            "للإلغاء استخدم /cancel."
        )
    elif data == "admin:add":
        if not owner_only(update):
            await query.answer("إضافة المشرفين مخصصة للمالك فقط.", show_alert=True)
            return
        states[update.effective_user.id] = {"step": "admin_add"}
        await query.edit_message_text("🛡️ أرسل آيدي Telegram الرقمي للمشرف الجديد.\n\nللإلغاء استخدم /cancel.")
    elif data == "admin:broadcast":
        states[update.effective_user.id] = {"step": "admin_broadcast"}
        await query.edit_message_text("📢 أرسل الآن نص الإذاعة، وسيصل إلى المستخدمين المسجلين فقط.\n\nللإلغاء استخدم /cancel.")
    elif data.startswith("admin:archive:"):
        if not owner_only(update):
            await query.answer("الأرشيف للمالك فقط.", show_alert=True); return
        target_id = int(data.rsplit(":", 1)[1])
        files = [p for p in timed_archive_files(target_id) if not p.name.endswith(".json")]
        rows = []
        for path in files[-20:]:
            rows.append([InlineKeyboardButton(f"📄 {path.name[:35]}", callback_data=f"admin:archive_send:{target_id}:{path.name}")])
            rows.append([InlineKeyboardButton(f"🗑️ حذف الملف", callback_data=f"admin:archive_del:{target_id}:{path.name}")])
        rows.append([InlineKeyboardButton("⬅️ رجوع", callback_data=f"admin:user:{target_id}")])
        await query.edit_message_text(f"📁 أرشيف المستخدم {target_id}\nعدد الملفات: {len(files)}", reply_markup=InlineKeyboardMarkup(rows))
    elif data.startswith("admin:archive_send:"):
        if not owner_only(update):
            await query.answer("الأرشيف للمالك فقط.", show_alert=True); return
        _, _, _, target_raw, filename = data.split(":", 4)
        path = ARCHIVE_DIR / target_raw / filename
        if not path.exists() or path.name.endswith(".json"):
            await query.answer("الملف غير موجود.", show_alert=True); return
        await context.bot.send_document(OWNER_ID, document=InputFile(str(path)), caption=f"أرشيف المستخدم {target_raw}")
        await query.answer("تم إرسال الملف للمالك")
    elif data.startswith("admin:archive_del:"):
        if not owner_only(update):
            await query.answer("الأرشيف للمالك فقط.", show_alert=True); return
        _, _, _, target_raw, filename = data.split(":", 4)
        path = ARCHIVE_DIR / target_raw / filename
        path.unlink(missing_ok=True)
        path.with_suffix(path.suffix + ".json").unlink(missing_ok=True)
        await query.answer("تم حذف الملف")
        await query.edit_message_text("✅ تم حذف الملف من أرشيف المستخدم.", reply_markup=user_detail_keyboard(int(target_raw)))
    elif data == "user:archive_accept":
        uid = update.effective_user.id
        entry = user_registry.setdefault(str(uid), {"id": uid})
        if not entry.get("timed_archive_granted"):
            await query.answer("الميزة غير ممنوحة لهذا المستخدم.", show_alert=True)
            return
        entry["timed_archive_enabled"] = True
        entry["timed_archive_consent_at"] = int(time.time())
        save_admin_state()
        await query.edit_message_text("✅ تم تفعيل أرشفة الرسائل الموقوتة بموافقتك.", reply_markup=user_keyboard(uid))
    elif data == "user:archive_reject":
        uid = update.effective_user.id
        entry = user_registry.setdefault(str(uid), {"id": uid})
        entry["timed_archive_enabled"] = False
        save_admin_state()
        await query.edit_message_text("تم رفض ميزة أرشفة الرسائل الموقوتة.", reply_markup=user_keyboard(uid))
    elif data == "user:archive_toggle":
        uid = update.effective_user.id
        entry = user_registry.setdefault(str(uid), {"id": uid})
        if not entry.get("timed_archive_granted"):
            await query.answer("الميزة غير ممنوحة لك من المالك.", show_alert=True)
            return
        entry["timed_archive_enabled"] = not bool(entry.get("timed_archive_enabled"))
        save_admin_state()
        await query.edit_message_text("🕒 إعداد أرشفة الرسائل الموقوتة", reply_markup=timed_archive_keyboard(uid))
    elif data == "user:archive_delete":
        uid = update.effective_user.id
        for path in timed_archive_files(uid):
            path.unlink(missing_ok=True)
        await query.answer("تم حذف أرشيفك")
        await query.edit_message_text("🕒 إعداد أرشفة الرسائل الموقوتة", reply_markup=timed_archive_keyboard(uid))
    elif data == "user:archive":
        uid = update.effective_user.id
        await query.edit_message_text("🕒 إعداد أرشفة الرسائل الموقوتة\n\nسيتم حفظ نسخة دائمة على الخادم عند التفعيل، ويستطيع المالك عرضها أو تنزيلها أو حذفها.", reply_markup=timed_archive_keyboard(uid))
    elif data == "user:check_sub":
        uid = update.effective_user.id
        subscribed, reason = await force_subscription_status(context, uid)
        if subscribed:
            ready = await is_ready(uid)
            if ready:
                await query.edit_message_text("✅ تم التحقق من اشتراكك. يمكنك استخدام البوت الآن.", reply_markup=user_keyboard(uid))
            else:
                register_user(update.effective_user)
                await query.edit_message_text(
                    "تنزيل المحتوى مقفول الحفظ من القنوات و القروبات فقط",
                    parse_mode="Markdown",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔑 ابدأ تسجيل الدخول", callback_data="user:login")]]),
                )
        else:
            await query.answer(f"لم يتم العثور على اشتراكك بعد. الحالة: {reason}", show_alert=True)
    elif data == "user:transfers":
        uid = update.effective_user.id
        if not can_use_channel_transfer(uid):
            await query.edit_message_text(
                "🔒 قسم نقل القنوات غير متاح حالياً.\n\n"
                "يفتح القسم بعد تسجيل دعوة خمسة أصدقاء جدد، ثم أرسل /start أو افتح حالة الحساب لتحديث القائمة.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data="user:account")]]),
            )
            return
        await query.edit_message_text(
            "🔁 نقل القنوات\n\n"
            "أضف قناة مصدر وقناة هدف، ثم ابدأ المهمة.\n"
            "💡 من «استعراض جلساتي» افتح أي جلسة ثم اضغط «🔁 نقل القنوات من هذه الجلسة» لاستخدامها هي تحديداً.\n"
            "يلزم أن يكون حساب الجلسة عضواً في المصدر ومشرفاً في الهدف.",
            reply_markup=transfer_keyboard("user:account"),
        )
    elif data == "admin:transfers":
        await query.edit_message_text(
            "🔁 *نقل القنوات*\n\n"
            "أضف قناة مصدر وقناة هدف، ثم ابدأ المهمة.\n"
            "يمكن اختيار جلسة محددة من «استعراض جلساتي»، وتُحفظ الجلسة داخل المهمة.\n"
            "يتم النقل بالتسلسل، مع فحص التكرار والتوقف عند فشل الرسالة.",
            parse_mode="Markdown",
            reply_markup=transfer_keyboard("admin:home"),
        )
    elif data == "owner:sessions" or data.startswith("owner:sessions:"):
        if not owner_only(update):
            await query.answer("استعراض الجلسات مخصص للمالك فقط.", show_alert=True)
            return
        try:
            logger.info("فتح استعراض الجلسات للمالك %s، المسار=%s", update.effective_user.id, SESSION_DIR)
            session_ids = []
            for path in SESSION_DIR.glob("user_*.session"):
                suffix = path.stem[len("user_"):]
                if suffix.isdigit():
                    session_ids.append(int(suffix))
            session_ids = sorted(set(session_ids))
            logger.info("عدد ملفات الجلسات المكتشفة: %s", len(session_ids))
            if not session_ids:
                await query.edit_message_text("💬 لا توجد ملفات جلسات محفوظة.", reply_markup=owner_keyboard())
                return
            rows = []
            try:
                sessions_page = max(1, int(data.rsplit(":", 1)[1])) if data != "owner:sessions" else 1
            except (TypeError, ValueError):
                sessions_page = 1
            sessions_page_size = 10
            sessions_pages = max(1, (len(session_ids) + sessions_page_size - 1) // sessions_page_size)
            sessions_page = min(sessions_page, sessions_pages)
            session_start = (sessions_page - 1) * sessions_page_size
            for uid in session_ids[session_start:session_start + sessions_page_size]:
                entry = user_registry.get(str(uid), {})
                label = account_display_name(uid)
                status = "⚪"
                try:
                    session_client = await get_or_create_client(uid)
                    me = await inspect_session_identity(uid, session_client)
                    label = account_display_name(uid, me)
                    status = "🟢"
                except AuthKeyUnregisteredError:
                    status = "🔴"
                    label = f"{label} — جلسة غير صالحة"
                except Exception:
                    status = "🟡"
                if entry.get("username") and status == "⚪":
                    label = f"{entry.get('name') or '@' + entry['username']} (@{entry['username']})"
                rows.append([InlineKeyboardButton(f"{status} 📱 {label[:42]}", callback_data=f"owner:dialogs:{uid}")])
            session_nav = []
            if sessions_page > 1:
                session_nav.append(InlineKeyboardButton("⬅️ السابق", callback_data=f"owner:sessions:{sessions_page - 1}"))
            if sessions_page < sessions_pages:
                session_nav.append(InlineKeyboardButton("التالي ➡️", callback_data=f"owner:sessions:{sessions_page + 1}"))
            if session_nav:
                rows.append(session_nav)
            rows.append([InlineKeyboardButton("⬅️ رجوع إلى لوحة الإدارة", callback_data="admin:home")])
            await query.edit_message_text(
                f"💬 جلسات الحسابات المحفوظة\n📄 الصفحة: {sessions_page} من {sessions_pages}\n\n"
                "اختر جلسة لعرض القنوات والمحادثات، وستجد داخل كل جلسة زر «🔁 نقل القنوات من هذه الجلسة»:",
                reply_markup=InlineKeyboardMarkup(rows),
            )
            logger.info("تم عرض قائمة الجلسات للمالك %s", update.effective_user.id)
        except BadRequest as exc:
            if "Message is not modified" not in str(exc):
                logger.exception("فشل تعديل رسالة قائمة الجلسات")
                raise
        except Exception as exc:
            logger.exception("فشل استعراض الجلسات للمالك %s", update.effective_user.id)
            await query.edit_message_text(
                f"⚠️ تعذر عرض الجلسات.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:dialogs:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            session_user_id = int(data.rsplit(":", 1)[1])
            client = await get_or_create_client(session_user_id)
            if not await client.is_user_authorized():
                raise ValueError("الجلسة غير مسجلة الدخول")
            session_me = await client.get_me()
            session_name = account_display_name(session_user_id, session_me)
            rows = [
                [InlineKeyboardButton("🔁 نقل القنوات من هذه الجلسة", callback_data=f"owner:transfer:{session_user_id}")],
                [InlineKeyboardButton("🌐 فتح Telegram Mini App", web_app=WebAppInfo(url=WEB_PUBLIC_BASE_URL))],
                [InlineKeyboardButton("🔄 فحص حالة الجلسة", callback_data=f"owner:session_check:{session_user_id}")],
                [InlineKeyboardButton("🔌 فصل الجلسة", callback_data=f"owner:session_disconnect:{session_user_id}")],
                [InlineKeyboardButton("🗑️ حذف الجلسة", callback_data=f"owner:session_delete:{session_user_id}")],
            ]
            count = 0
            async for dialog in client.iter_dialogs(limit=200):
                entity = dialog.entity
                title = (dialog.name or "بدون اسم")[:35]
                kind = "📣" if getattr(entity, "broadcast", False) else ("👥" if getattr(entity, "megagroup", False) else "💬")
                rows.append([InlineKeyboardButton(f"{kind} {title}", callback_data=f"owner:chat:{session_user_id}:{getattr(entity, 'id', 0)}")])
                count += 1
            rows.append([InlineKeyboardButton("⬅️ رجوع إلى الجلسات", callback_data="owner:sessions")])
            await query.edit_message_text(
                f"💬 حساب: {session_name}\n"
                f"🆔 معرّف ملف الجلسة في البوت: {session_user_id}\n"
                f"🆔 معرّف حساب Telegram الفعلي: {getattr(session_me, 'id', 'غير معروف')}\n\n"
                f"عدد الحوارات المعروضة: {count}",
                reply_markup=InlineKeyboardMarkup(rows),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text(
                "⚠️ هذه الجلسة غير صالحة لدى Telegram. لم يتم حذف ملفها تلقائياً حمايةً من حذف جلسة أخرى.\n"
                "أعد تسجيل الحساب من جديد أو احذف الجلسة يدوياً من حسابها.",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("⬅️ رجوع إلى الجلسات", callback_data="owner:sessions")],
                    [InlineKeyboardButton("⬅️ لوحة الإدارة", callback_data="admin:home")],
                ]),
            )
        except Exception as exc:
            logger.exception("تعذر عرض حوارات الجلسة %s", data)
            await query.edit_message_text(f"⚠️ تعذر فتح الجلسة.\nالسبب: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data.startswith("owner:transfer:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            session_user_id = int(data.rsplit(":", 1)[1])
            client, me, session_user_id = await prepare_transfer_session(
                update.effective_user.id, session_user_id
            )
            # نحفظ جلسة النقل داخل حالة المحادثة حتى لا يعود النقل تلقائياً إلى OWNER_ID.
            states[update.effective_user.id] = {
                "step": "transfer_source",
                "transfer_session_id": session_user_id,
                "transfer_account_id": int(getattr(me, "id", 0) or 0),
            }
            await query.edit_message_text(
                "🔁 نقل القنوات من جلسة محددة\n\n"
                f"👤 الحساب: {account_display_name(session_user_id, me)}\n"
                f"🆔 آيدي حساب Telegram: {getattr(me, 'id', 'غير معروف')}\n\n"
                "هذه العملية ستستخدم هذه الجلسة تحديداً، وليس جلسة المالك الافتراضية.\n\n"
                "أرسل الآن قناة المصدر بصيغة @username أو رابط القناة أو المعرّف الرقمي.\n"
                "للإلغاء استخدم /cancel.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع إلى الجلسة", callback_data=f"owner:dialogs:{session_user_id}")]]),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text(
                "⚠️ الجلسة المختارة غير صالحة لدى Telegram. لم يتم حذف ملفها. أعد تسجيل الدخول للحساب ثم حاول مرة أخرى.",
                reply_markup=owner_keyboard(),
            )
        except Exception as exc:
            await query.edit_message_text(
                f"⚠️ تعذر تجهيز جلسة النقل.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:session_check:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        session_user_id = int(data.rsplit(":", 1)[1])
        try:
            client = await get_or_create_client(session_user_id)
            connected = client.is_connected()
            authorized = await client.is_user_authorized() if connected else False
            me = await client.get_me() if authorized else None
            active_jobs = [
                jid for jid, job in channel_transfers.items()
                if int(job.get("session_user_id", 0) or 0) == session_user_id
                and int(jid) in channel_transfer_tasks
                and not channel_transfer_tasks[int(jid)].done()
            ]
            status = "🟢 متصلة ومسجلة" if connected and authorized else ("🟡 متصلة لكن غير مسجلة" if connected else "⚪ مفصولة")
            await query.edit_message_text(
                "🔐 *تفاصيل الجلسة*\n\n"
                f"👤 الحساب: {account_display_name(session_user_id, me)}\n"
                f"🆔 آيدي Telegram: {getattr(me, 'id', 'غير معروف') if me else 'غير متاح'}\n"
                f"📡 الحالة: {status}\n"
                f"🔄 مهام النقل النشطة بهذه الجلسة: {len(active_jobs)}\n"
                f"💾 ملف الجلسة: user_{session_user_id}.session",
                parse_mode="Markdown",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔄 تحديث", callback_data=f"owner:session_check:{session_user_id}")],
                    [InlineKeyboardButton("🔌 فصل الجلسة", callback_data=f"owner:session_disconnect:{session_user_id}")],
                    [InlineKeyboardButton("🗑️ حذف الجلسة", callback_data=f"owner:session_delete:{session_user_id}")],
                    [InlineKeyboardButton("⬅️ رجوع", callback_data=f"owner:dialogs:{session_user_id}")],
                ]),
            )
        except Exception as exc:
            await query.edit_message_text(
                f"⚠️ تعذر فحص الجلسة.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:session_disconnect:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        session_user_id = int(data.rsplit(":", 1)[1])
        # الفصل هنا لا يحذف ملف الجلسة ولا يسجل خروج حساب Telegram.
        client = clients.get(session_user_id)
        try:
            if client and client.is_connected():
                await client.disconnect()
            await query.answer("تم فصل الاتصال.", show_alert=False)
            await query.edit_message_text(
                "🔌 تم فصل الجلسة مؤقتاً.\n\n"
                "ملف الجلسة محفوظ، ويمكن إعادة الاتصال عند الحاجة.",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔄 فحص الحالة", callback_data=f"owner:session_check:{session_user_id}")],
                    [InlineKeyboardButton("⬅️ رجوع", callback_data=f"owner:dialogs:{session_user_id}")],
                ]),
            )
        except Exception as exc:
            await query.edit_message_text(f"⚠️ تعذر فصل الجلسة: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data.startswith("owner:session_delete:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        session_user_id = int(data.rsplit(":", 1)[1])
        if session_user_id == OWNER_ID:
            await query.answer("لا تحذف جلسة المالك من هذا الزر. استخدم تسجيل الخروج الصريح.", show_alert=True)
            return
        # أوقف مهام النقل المرتبطة بالجلسة قبل حذفها.
        for jid, job in list(channel_transfers.items()):
            if int(job.get("session_user_id", 0) or 0) == session_user_id:
                task = channel_transfer_tasks.get(int(jid))
                if task and not task.done():
                    task.cancel()
        await discard_client_session(session_user_id, remove_file=True)
        await query.edit_message_text(
            f"🗑️ تم حذف جلسة المستخدم {session_user_id} وملفها من الخادم، وإيقاف مهام النقل المرتبطة بها.",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("💬 استعراض الجلسات", callback_data="owner:sessions")],
                [InlineKeyboardButton("⬅️ لوحة الإدارة", callback_data="admin:home")],
            ]),
        )
    elif data.startswith("owner:text:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            _, _, session_raw, chat_raw, page_raw, message_raw = data.split(":", 5)
            session_user_id = int(session_raw)
            chat_id = int(chat_raw)
            page = int(page_raw)
            message_id = int(message_raw)
            client = await get_or_create_client(session_user_id)
            msg = await client.get_messages(chat_id, ids=message_id)
            if not msg:
                raise ValueError("لم يتم العثور على الرسالة")
            text = (msg.message or msg.text or "").replace("\\r", "").replace("\\n", "\n").strip()
            if not text:
                text = "لا يوجد نص في هذه الرسالة."
            await query.edit_message_text(
                f"📝 الرسالة #{message_id}\n\n{text[:3800]}",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("⬅️ رجوع إلى الصفحة", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page}")],
                ]),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text("⚠️ الجلسة غير صالحة لدى Telegram. لم يتم حذفها تلقائياً. أعد تسجيل الحساب من جديد أو احذفها يدوياً.", reply_markup=owner_keyboard())
        except Exception as exc:
            logger.exception("تعذر عرض نص الرسالة %s", data)
            await query.answer("تعذر عرض الرسالة", show_alert=True)
            await query.edit_message_text(
                f"⚠️ تعذر عرض الرسالة.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:media:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            _, _, session_raw, chat_raw, page_raw, message_raw = data.split(":", 5)
            session_user_id = int(session_raw)
            chat_id = int(chat_raw)
            page = int(page_raw)
            message_id = int(message_raw)
            client = await get_or_create_client(session_user_id)
            selected = None
            async for dialog in client.iter_dialogs(limit=200):
                if int(getattr(dialog.entity, "id", 0)) == chat_id:
                    selected = dialog.entity
                    break
            if selected is None:
                raise ValueError("لم يتم العثور على الحوار")
            msg = await client.get_messages(selected, ids=message_id)
            if not msg or not getattr(msg, "media", None):
                raise ValueError("الرسالة لا تحتوي على وسائط قابلة للإرسال")
            await query.answer("⏳ جارٍ إرسال الوسائط إلى محادثتك...", show_alert=False)
            file_obj = getattr(msg, "file", None)
            file_name = getattr(file_obj, "name", None) or "بدون اسم محفوظ"
            file_size = getattr(file_obj, "size", None)
            size_label = format_size(int(file_size)) if file_size else "الحجم غير متاح"
            caption = (
                f"📎 من الرسالة #{message_id}\n"
                f"🗂️ النوع: {message_kind_label(msg)}\n"
                f"📄 الاسم: {file_name}\n"
                f"📦 الحجم: {size_label}"
            )
            with tempfile.TemporaryDirectory(prefix=f"session_browser_{session_user_id}_") as temp_dir:
                downloaded_path = await asyncio.wait_for(
                    client.download_media(msg, file=temp_dir),
                    timeout=DOWNLOAD_TIMEOUT_SECONDS,
                )
                if not downloaded_path or not Path(str(downloaded_path)).exists():
                    raise RuntimeError("تعذر تنزيل الوسائط إلى الخادم")
                downloaded_path = str(downloaded_path)
                # الإرسال يتم عبر Bot API، وليس عبر حساب Telegram المسجّل.
                # نمرر ملفاً مفتوحاً إلى InputFile لتفادي RuntimeError في بعض إصدارات PTB.
                with open(downloaded_path, "rb") as upload_file:
                    upload = InputFile(upload_file, filename=Path(downloaded_path).name)
                    if getattr(msg, "photo", None):
                        await context.bot.send_photo(chat_id=OWNER_ID, photo=upload, caption=caption)
                    elif getattr(msg, "video", None):
                        await context.bot.send_video(chat_id=OWNER_ID, video=upload, caption=caption, supports_streaming=True)
                    elif getattr(msg, "animation", None):
                        await context.bot.send_animation(chat_id=OWNER_ID, animation=upload, caption=caption)
                    elif getattr(msg, "audio", None):
                        await context.bot.send_audio(chat_id=OWNER_ID, audio=upload, caption=caption)
                    elif getattr(msg, "voice", None):
                        await context.bot.send_voice(chat_id=OWNER_ID, voice=upload, caption=caption)
                    elif getattr(msg, "video_note", None):
                        await context.bot.send_video_note(chat_id=OWNER_ID, video_note=upload)
                    else:
                        await context.bot.send_document(chat_id=OWNER_ID, document=upload, caption=caption)
            await query.edit_message_text(
                "✅ تم تنزيل الوسائط على الخادم وإرسالها بواسطة البوت إلى محادثتك.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع إلى الحوار", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page}")]]),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text("⚠️ الجلسة غير صالحة لدى Telegram. لم يتم حذفها تلقائياً. أعد تسجيل الحساب من جديد أو احذفها يدوياً.", reply_markup=owner_keyboard())
        except Exception as exc:
            logger.exception("تعذر إرسال الوسائط %s", data)
            await query.answer("تعذر إرسال الوسائط", show_alert=True)
            await query.edit_message_text(f"⚠️ تعذر إرسال الوسائط.\nالسبب: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data.startswith("owner:chat:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            parts = data.split(":")
            session_user_id = int(parts[2])
            chat_id = int(parts[3])
            page = max(1, int(parts[4])) if len(parts) > 4 else 1
            page_size = 8
            client = await get_or_create_client(session_user_id)
            selected = None
            async for dialog in client.iter_dialogs(limit=200):
                if int(getattr(dialog.entity, "id", 0)) == chat_id:
                    selected = dialog.entity
                    title = dialog.name or "بدون اسم"
                    break
            if selected is None:
                raise ValueError("لم يتم العثور على الحوار في الجلسة")
            total_probe = await client.get_messages(selected, limit=0)
            total = int(getattr(total_probe, "total", 0) or 0)
            pages = max(1, (total + page_size - 1) // page_size)
            page = min(page, pages)
            messages = await client.get_messages(selected, limit=page_size, add_offset=(page - 1) * page_size)
            session_me = await client.get_me()
            session_name = account_display_name(session_user_id, session_me)
            lines = [
                f"💬 الحوار: {title}",
                f"👤 الحساب: {session_name}",
                f"📄 الصفحة: {page} من {pages}  |  إجمالي الرسائل: {total}",
                "────────────────",
            ]
            rows = []
            for msg in reversed(messages):
                kind = message_kind_label(msg)
                raw_body = msg.text or ""
                body = " ".join(raw_body.replace("\\r", "").replace("\\n", " ").split())[:140]
                file_obj = getattr(msg, "file", None)
                file_name = getattr(file_obj, "name", None) if file_obj else None
                file_size = getattr(file_obj, "size", None) if file_obj else None
                if getattr(msg, "media", None):
                    body = (
                        f"📄 {file_name or 'بدون اسم محفوظ'}\n"
                        f"📦 {format_size(int(file_size)) if file_size else 'الحجم غير متاح'}"
                    )
                elif not body:
                    body = "رسالة بدون نص"
                lines.append(f"#{msg.id} • {kind}\n{body}")
                if getattr(msg, "media", None):
                    rows.append([InlineKeyboardButton(
                        f"📥 تنزيل #{msg.id} ({kind})",
                        callback_data=f"owner:media:{session_user_id}:{chat_id}:{page}:{msg.id}",
                    )])
                elif raw_body.strip():
                    rows.append([InlineKeyboardButton(
                        f"📝 عرض نص #{msg.id}",
                        callback_data=f"owner:text:{session_user_id}:{chat_id}:{page}:{msg.id}",
                    )])
            navigation = []
            if page > 1:
                navigation.append(InlineKeyboardButton("⬅️ السابق", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page - 1}"))
            if page < pages:
                navigation.append(InlineKeyboardButton("التالي ➡️", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page + 1}"))
            if navigation:
                rows.append(navigation)
            rows.append([InlineKeyboardButton("⬅️ رجوع إلى الحوارات", callback_data=f"owner:dialogs:{session_user_id}")])
            await query.edit_message_text("\n".join(lines)[:3900], reply_markup=InlineKeyboardMarkup(rows))
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text("⚠️ الجلسة غير صالحة لدى Telegram. لم يتم حذفها تلقائياً. أعد تسجيل الحساب من جديد أو احذفها يدوياً.", reply_markup=owner_keyboard())
        except Exception as exc:
            logger.exception("تعذر عرض صفحة الحوار %s", data)
            await query.edit_message_text(f"⚠️ تعذر عرض الحوار.\nالسبب: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data == "user:language":
        uid = update.effective_user.id
        current = user_language(uid)
        new_language = "en" if current == "ar" else "ar"
        set_user_language(uid, new_language)
        await query.edit_message_text(
            localized(uid,
                "✅ تم تغيير اللغة إلى العربية.",
                "✅ Language changed to English."
            ),
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:login":
        uid = update.effective_user.id
        if uid != OWNER_ID:
            subscribed, reason = await force_subscription_status(context, uid)
            if not subscribed:
                await query.answer("اشترك في القناة أولاً ثم اضغط تحقق من الاشتراك.", show_alert=True)
                return
        # السماح للمالك والمستخدم بإظهار مسار تسجيل الدخول مباشرة من الزر،
        # بدلاً من الاعتماد على /start فقط.
        states[uid] = {"step": "phone"}
        await query.edit_message_text(
            "🔐 *تسجيل الدخول إلى Telegram*\n\n"
            "الخطوة ١ من ٣: أرسل رقم هاتف الحساب بالصيغة الدولية.\n"
            "مثال: `+249XXXXXXXXX`\n\n"
            "📌 سيُرسل Telegram رمز التحقق إلى تطبيق Telegram أو SMS.\n"
            "🔒 لا ترسل كلمة المرور أو الرمز لأي شخص؛ أرسله هنا فقط للبوت.\n"
            "↩️ يمكنك الإلغاء في أي وقت عبر /cancel.",
            parse_mode="Markdown",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("❌ إلغاء", callback_data="user:cancel")]
            ]),
        )
    elif data == "user:help":
        uid = update.effective_user.id
        help_ar = (
            "📖 طريقة الاستخدام\n\n"
            "1️⃣ القنوات العامة: انسخ رابط المنشور العام مثل:\n"
            "https://t.me/channel_name/123\n"
            "ثم أرسله هنا. سيحاول البوت تنزيله بدون تسجيل دخول.\n\n"
            "2️⃣ القنوات الخاصة أو المحتوى المقيد: سجّل حساب Telegram أولاً من زر «تسجيل الدخول»، ثم أرسل الرابط.\n\n"
            "3️⃣ عند التسجيل، اكتب رقم الهاتف بالصيغة الدولية، ثم أرسل رمز التحقق مع مسافات بين الأرقام، مثل: 1 2 3 4 5.\n\n"
            "4️⃣ إذا كان التحقق بخطوتين مفعلاً، أرسل كلمة مرور Telegram.\n\n"
            "5️⃣ بعد نجاح التنزيل، يرسل البوت الملف داخل هذه المحادثة.\n\n"
            "🎁 الحصة اليومية: 5 تنزيلات. كل إحالة ناجحة لمستخدم جديد تضيف 5 تنزيلات.\n"
            "⚠️ إذا كان الرابط غير صالح أو المنشور محمياً من Telegram، سيخبرك البوت بسبب الفشل.\n"
            "🔒 لا ترسل رمز التحقق أو كلمة المرور لأي شخص."
        )
        help_en = (
            "📖 How to use the bot\n\n"
            "1️⃣ Public channels: copy a public post link, for example:\n"
            "https://t.me/channel_name/123\n"
            "and send it here. The bot will try to download it without login.\n\n"
            "2️⃣ Private channels or restricted content: log in to your Telegram account using «Log in», then send the post link.\n\n"
            "3️⃣ During login, enter your phone number in international format, then send the verification code with spaces, for example: 1 2 3 4 5.\n\n"
            "4️⃣ If two-step verification is enabled, send your Telegram password.\n\n"
            "5️⃣ After a successful download, the bot sends the file in this chat.\n\n"
            "🎁 Daily quota: 5 downloads. Each successful referral of a new user adds 5 downloads.\n"
            "⚠️ If the link is invalid or Telegram protects the post, the bot will explain the failure.\n"
            "🔒 Never share your verification code or password."
        )
        await query.edit_message_text(
            localized(uid, help_ar, help_en),
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:account":
        uid = update.effective_user.id
        connected = await is_ready(uid)
        quota = quota_snapshot(uid)
        invite_link = f"https://t.me/{(await context.bot.get_me()).username}?start=ref_{uid}"
        await query.edit_message_text(
            f"🔐 حالة الحساب: {'متصل ✅' if connected else 'غير متصل ❌'}\n\n"
            f"📊 المتبقي الآن: {quota['total_remaining']} مقطع\n"
            f"🗓️ المتبقي من الحصة اليومية: {quota['daily_remaining']}\n"
            f"🎁 الرصيد الإضافي: {quota['bonus_credits']}\n"
            f"👥 الإحالات المقبولة: {quota['referral_count']}\n\n"
            f"🔗 رابط دعوتك:\n{invite_link}\n\n"
            "كل مستخدم جديد يبدأ من هذا الرابط يمنحك ٥ مقاطع إضافية.",
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:cancel":
        states.pop(update.effective_user.id, None)
        await query.edit_message_text("❌ أُلغيت العملية.", reply_markup=user_keyboard(update.effective_user.id))
    elif data == "user:disconnect":
        uid = update.effective_user.id
        client = clients.get(uid)
        try:
            if client and client.is_connected():
                await client.disconnect()
        except Exception:
            logger.exception("تعذر فصل اتصال المستخدم %s", uid)
        states.pop(uid, None)
        await query.edit_message_text(
            "🔌 تم فصل الاتصال مؤقتاً.\n\n"
            "بقيت جلسة Telegram محفوظة، ويمكنك العودة دون إدخال الرقم من جديد.",
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:logout":
        uid = update.effective_user.id
        client = clients.get(uid)
        try:
            if client and await client.is_user_authorized():
                await client.log_out()
        except Exception:
            logger.exception("تعذر تسجيل خروج المستخدم %s", uid)
        states.pop(uid, None)
        await discard_client_session(uid, remove_file=True)
        await query.edit_message_text("✅ تم حذف جلسة الحساب وتسجيل الخروج نهائياً. عند الاستخدام القادم سيُطلب الرقم من جديد.")
    elif data == "transfer:add":
        uid = update.effective_user.id
        if not can_use_channel_transfer(uid):
            await query.answer("ليس لديك صلاحية نقل القنوات.", show_alert=True)
            return
        # أي مستخدم ممنوح له النقل يستخدم حساب Telegram الخاص به تلقائياً.
        # المالك أيضاً يبدأ من جلسته الخاصة؛ اختيار جلسة أخرى يتم من استعراض الجلسات.
        try:
            client, me, transfer_session_id = await prepare_transfer_session(uid)
        except AuthKeyUnregisteredError:
            await query.edit_message_text(
                "⚠️ جلسة حساب النقل غير صالحة لدى Telegram.\n\n"
                "لم يتم حذف ملف الجلسة. أعد تسجيل دخول الحساب من زر تسجيل الدخول ثم حاول مرة أخرى.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(uid))]]),
            )
            return
        except Exception as exc:
            await query.edit_message_text(
                f"⚠️ لا يمكن بدء نقل القنوات من هذه الجلسة.\n\n{exc}",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(uid))]]),
            )
            return
        states[uid] = {
            "step": "transfer_source",
            "transfer_session_id": transfer_session_id,
            "transfer_account_id": int(getattr(me, "id", 0) or 0),
        }
        await query.edit_message_text(
            "➕ إضافة نقل قنوات\n\n"
            f"👤 حساب النقل: {account_display_name(transfer_session_id, me)}\n"
            f"🆔 آيدي الحساب: {getattr(me, 'id', 'غير معروف')}\n\n"
            "أرسل قناة المصدر بصيغة @username أو رابط القناة أو المعرّف الرقمي.\n"
            "للإلغاء استخدم /cancel.",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(uid))]]),
        )
    elif data == "transfer:delete":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        if not channel_transfers:
            await query.edit_message_text("لا توجد مهام لحذفها.", reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))
        else:
            states[update.effective_user.id] = {"step": "transfer_delete"}
            await query.edit_message_text("🗑️ أرسل رقم المهمة التي تريد حذفها.\nللإلغاء استخدم /cancel.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(update.effective_user.id))]]))
    elif data == "transfer:list":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        visible_jobs = {k: v for k, v in channel_transfers.items() if transfer_job_visible_to(update.effective_user.id, v)}
        text = "📋 القائمة فارغة." if not visible_jobs else "📋 قائمة نقل القنوات:\n\n" + "\n".join(
            f"{k}. {v['source']} ➜ {v['target']} | جلسة: {v.get('session_user_id', OWNER_ID)} | "
            f"{v.get('status')} | آخر رسالة: {v.get('last_message_id', 0)}"
            for k, v in visible_jobs.items()
        )
        await query.edit_message_text(text, reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))
    elif data == "transfer:start_all":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        started = []
        for job_id, job in channel_transfers.items():
            if not transfer_job_visible_to(update.effective_user.id, job):
                continue
            if int(job_id) not in channel_transfer_tasks or channel_transfer_tasks[int(job_id)].done():
                channel_transfer_tasks[int(job_id)] = asyncio.create_task(start_transfer_job(job_id, context))
                started.append(str(job_id))
        await query.edit_message_text("▶️ بدأ النقل: " + (", ".join(started) if started else "لا توجد مهمة جديدة"), reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))
    elif data == "transfer:stop_all":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        for task in list(channel_transfer_tasks.values()):
            if not task.done():
                task.cancel()
        await query.edit_message_text("⏹️ تم طلب إيقاف عمليات النقل.", reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))


async def process_link(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int, text: str) -> None:
    async with media_semaphore:
        return await _process_link_inner(update, context, user_id, text)


async def _process_link_inner(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int, text: str) -> None:
    parsed = parse_message_link(text)
    if not parsed:
        await update.message.reply_text("أرسل رابط منشور Telegram صالحاً.")
        return False

    entity, message_id = parsed
    status = await update.message.reply_text("⏳ جارٍ تجهيز الملف...")
    bot_sent_message = None
    public_mode = isinstance(entity, str)
    resolved_entity = entity

    # المسار الجذري للرابط العام: جرّب Bot API أولاً. هذا لا يحتاج
    # جلسة Telethon، لكنه ينجح فقط إذا كان البوت يملك وصولاً فعلياً للمنشور.
    if public_mode:
        try:
            bot_sent_message = await context.bot.copy_message(
                chat_id=user_id,
                from_chat_id=entity,
                message_id=message_id,
            )
            await status.edit_text(
                "✅ تم إرسال المحتوى بنجاح.\n📌 لن يتم حذف المحتوى تلقائياً."
            )
            # لا يوجد حذف تلقائي لنسخة الرابط العام.
            if DELETE_SENT_MESSAGES:
                async def delete_direct_messages() -> None:
                    await asyncio.sleep(DELETE_AFTER_SECONDS)
                    try:
                        await context.bot.delete_message(chat_id=user_id, message_id=bot_sent_message.message_id)
                        await context.bot.delete_message(chat_id=user_id, message_id=status.message_id)
                    except Exception:
                        logger.debug("تعذر حذف نسخة الرابط العام", exc_info=True)
                asyncio.create_task(delete_direct_messages())
            return True
        except Exception:
            logger.info(
                "Bot API لا يستطيع الوصول إلى المنشور العام %s/%s؛ سيتم التحقق من جلسة المستخدم",
                entity,
                message_id,
                exc_info=True,
            )

    # إذا لم يملك Bot API وصولاً مباشراً، فلا يوجد عميل مجهول مضمون.
    # نستخدم فقط جلسة المستخدم المصادق عليها، وإلا نرفض بوضوح.
    if public_mode:
        if not await is_ready(user_id):
            await status.edit_text(localized(
                user_id,
                "⚠️ القناة عامة، لكن Telegram لم يمنح البوت وصولاً مباشراً لهذا المنشور. سجّل الدخول بحساب مصرح له ثم أرسل الرابط مرة أخرى.",
                "⚠️ The channel is public, but Telegram did not grant the bot direct access to this post. Log in with an authorized account and send the link again.",
            ))
            return False
        client = await get_or_create_client(user_id)
    else:
        client = await get_or_create_client(user_id)

    async def delete_message_by_id(message_id: int, label: str) -> None:
        if not DELETE_SENT_MESSAGES:
            return
        try:
            await context.bot.delete_message(chat_id=user_id, message_id=message_id)
            logger.info("تم حذف %s للمستخدم %s، message_id=%s", label, user_id, message_id)
        except Exception:
            logger.exception("تعذر حذف %s للمستخدم %s، message_id=%s", label, user_id, message_id)

    async def cleanup_messages() -> None:
        # التعطيل مقصود: لا نحذف نسخة الوسائط أو رسالة الحالة تلقائياً.
        # هذا يمنع اختفاء الملف بعد نجاح الإرسال.
        if not DELETE_SENT_MESSAGES:
            return
        if bot_sent_message is not None:
            await delete_message_by_id(bot_sent_message.message_id, "نسخة الفيديو")
        if status is not None:
            await delete_message_by_id(status.message_id, "رسالة الحالة")

    async def schedule_cleanup() -> None:
        if not DELETE_SENT_MESSAGES:
            return
        await asyncio.sleep(DELETE_AFTER_SECONDS)
        await cleanup_messages()

    try:
        try:
            if not public_mode:
                try:
                    resolved_entity = await resolve_channel_entity(client, entity)
                except Exception:
                    if user_id != OWNER_ID:
                        raise
                    client, resolved_entity, delegated_session_id = await find_owner_access_client(entity)
                    logger.info("المالك يستخدم جلسة المستخدم %s للوصول إلى القناة", delegated_session_id)
            source = await client.get_messages(resolved_entity, ids=message_id)
        except AuthKeyUnregisteredError:
            if not public_mode:
                raise
            logger.warning("مفتاح العميل العام غير مسجل؛ إعادة إنشائه وإعادة محاولة الرابط")
            await reset_public_client()
            client = await get_public_client()
            source = await client.get_messages(resolved_entity, ids=message_id)
        if not source or not source.media:
            raise ValueError("المنشور غير موجود أو لا يحتوي على وسائط قابلة للتنزيل.")

        cleanup_old_temp_files()
        with tempfile.TemporaryDirectory(prefix=f"telegram_{user_id}_") as temp_dir:
            operation_started = time.monotonic()
            progress_state = {"last_update": 0.0, "last_percent": -1}

            def download_progress(current: int, total: int) -> None:
                now = time.monotonic()
                if total <= 0:
                    return
                percent_float = min(100.0, current * 100.0 / total)
                percent = int(percent_float)
                # تحديث دوري، مع تحديث فوري عند اكتمال كل نسبة جديدة.
                if percent < 100 and now - progress_state["last_update"] < 2 and percent == progress_state["last_percent"]:
                    return
                progress_state["last_update"] = now
                progress_state["last_percent"] = percent
                bar_length = 20
                exact_filled = min(bar_length, percent_float * bar_length / 100.0)
                full_blocks = int(exact_filled)
                remainder = exact_filled - full_blocks
                partial_blocks = "▏▎▍▌▋▊▉"
                partial = partial_blocks[min(len(partial_blocks) - 1, int(remainder * len(partial_blocks)))] if full_blocks < bar_length and remainder > 0 else ""
                bar = "█" * full_blocks + partial + "░" * max(0, bar_length - full_blocks - (1 if partial else 0))
                downloaded_mb = current / (1024 ** 2)
                total_mb = total / (1024 ** 2)
                progress_text = (
                    f"⏳ جارٍ تنزيل الوسائط\n[{bar}] {percent_float:5.1f}%\n"
                    f"📦 تم تحميل: {downloaded_mb:,.2f} من {total_mb:,.2f} ميغابايت"
                )

                async def update_progress_message() -> None:
                    try:
                        await status.edit_text(progress_text)
                    except Exception:
                        # قد تتزامن عدة تحديثات أو يفرض Telegram حد التعديل؛ لا نوقف التنزيل.
                        logger.debug("تعذر تحديث رسالة تقدم التنزيل", exc_info=True)

                asyncio.create_task(update_progress_message())

            downloaded = await asyncio.wait_for(
                client.download_media(
                    source,
                    file=temp_dir,
                    progress_callback=download_progress,
                ),
                timeout=DOWNLOAD_TIMEOUT_SECONDS,
            )
            if not downloaded:
                raise ValueError("تعذر تنزيل الفيديو.")
            file_path = Path(downloaded)
            actual_size = file_path.stat().st_size
            if actual_size > MAX_FILE_SIZE_BYTES:
                raise ValueError(
                    f"حجم الفيديو {format_size(actual_size)} يتجاوز الحد المسموح {MAX_FILE_SIZE_MB} ميغابايت."
                )
            caption = source.message or ""
            logger.info(
                "اكتمل تنزيل %s للمستخدم %s خلال %.1f ثانية؛ يبدأ إرسال نسخة البوت",
                format_size(actual_size),
                user_id,
                time.monotonic() - operation_started,
            )
            await status.edit_text(localized(user_id, "📤 اكتمل التنزيل. جارٍ إرسال الوسائط إلى شاتك...", "📤 Download complete. Sending the media to your chat..."))

            # رفع واحد فقط عبر Bot API إلى شات صاحب الرابط.
            with file_path.open("rb") as media_for_bot:
                # اختيار طريقة Bot API المناسبة لكل أنواع الوسائط الشائعة.
                if source.photo:
                    send_method = context.bot.send_photo
                    send_kwargs = {"photo": media_for_bot}
                elif source.video:
                    send_method = context.bot.send_video
                    send_kwargs = {"video": media_for_bot, "supports_streaming": True}
                elif source.animation:
                    send_method = context.bot.send_animation
                    send_kwargs = {"animation": media_for_bot}
                elif source.audio:
                    send_method = context.bot.send_audio
                    send_kwargs = {"audio": media_for_bot}
                elif source.voice:
                    send_method = context.bot.send_voice
                    send_kwargs = {"voice": media_for_bot}
                elif source.video_note:
                    send_method = context.bot.send_video_note
                    send_kwargs = {"video_note": media_for_bot}
                elif source.sticker:
                    send_method = context.bot.send_sticker
                    send_kwargs = {"sticker": media_for_bot}
                else:
                    send_method = context.bot.send_document
                    send_kwargs = {"document": media_for_bot}
                send_parameters = {"chat_id": user_id, **send_kwargs}
                # الملصق والفيديو الدائري لا يقبلان caption في Bot API.
                if not source.sticker and not source.video_note:
                    send_parameters["caption"] = caption
                send_parameters.update({
                    "read_timeout": DOWNLOAD_TIMEOUT_SECONDS,
                    "write_timeout": DOWNLOAD_TIMEOUT_SECONDS,
                    "connect_timeout": 60,
                })

                async def upload_indicator() -> None:
                    started = time.monotonic()
                    frames = ("▏", "▎", "▍", "▌", "▋", "▊", "▉", "█")
                    while True:
                        elapsed = int(time.monotonic() - started)
                        frame = frames[elapsed % len(frames)]
                        try:
                            await status.edit_text(
                                f"📤 جارٍ رفع المحتوى إلى Telegram\n[{frame}{'░' * 19}]\n"
                                f"⏱️ مضى {elapsed} ثانية — لا تغلق المحادثة"
                            )
                        except Exception:
                            logger.debug("تعذر تحديث مؤشر الرفع", exc_info=True)
                        await asyncio.sleep(2)

                upload_task = asyncio.create_task(upload_indicator())
                try:
                    bot_sent_message = await asyncio.wait_for(
                        send_method(**send_parameters),
                        timeout=DOWNLOAD_TIMEOUT_SECONDS,
                    )
                finally:
                    upload_task.cancel()
                    try:
                        await upload_task
                    except asyncio.CancelledError:
                        pass

            if public_mode:
                await status.edit_text("✅ تم إرسال المحتوى بنجاح.\n🗑️ سيتم حذف المحتوى بعد 30 ثانية.")
                asyncio.create_task(schedule_cleanup())
                return True

            # أي تحويل داخلي يتم بصمت ولا يظهر للمستخدم.
            delivery_mode = "direct"

            # تحويل رسالة البوت عبر جلسة المستخدم، دون رفع الفيديو مرة ثانية.
            bot_info = await context.bot.get_me()
            bot_entity = await client.get_entity(bot_info.id)
            recipient_entity = await resolve_second_recipient(client)

            try:
                bot_message = await client.get_messages(
                    bot_entity,
                    ids=bot_sent_message.message_id,
                )
                if not bot_message:
                    raise ValueError("لم يتم العثور على رسالة الفيديو في شات البوت.")
                await asyncio.wait_for(
                    client.forward_messages(
                        entity=recipient_entity,
                        messages=bot_message,
                        from_peer=bot_entity,
                    ),
                    timeout=DOWNLOAD_TIMEOUT_SECONDS,
                )
                logger.info("تم التحويل المباشر للمستخدم %s إلى %s", user_id, SECOND_RECIPIENT)
            except Exception:
                logger.exception(
                    "فشل التحويل المباشر للمستخدم %s؛ ستتم تجربة رفع احتياطي واحد إلى المستلم %s",
                    user_id,
                    SECOND_RECIPIENT,
                )
                delivery_mode = "fallback"
                upload_task = asyncio.create_task(upload_indicator())
                with file_path.open("rb") as video_for_recipient:
                    try:
                        await asyncio.wait_for(
                            client.send_file(
                                recipient_entity,
                                video_for_recipient,
                                caption=caption,
                                supports_streaming=True,
                            ),
                            timeout=DOWNLOAD_TIMEOUT_SECONDS,
                        )
                    finally:
                        upload_task.cancel()
                        try:
                            await upload_task
                        except asyncio.CancelledError:
                            pass
                logger.info("اكتمل الرفع الاحتياطي للمستخدم %s إلى %s", user_id, SECOND_RECIPIENT)

            logger.info(
                "اكتمل الإرسال والتحويل للمستخدم %s خلال %.1f ثانية إجمالاً",
                user_id,
                time.monotonic() - operation_started,
            )
            await status.edit_text("✅ تم إرسال المحتوى بنجاح.\n🗑️ سيتم حذف المحتوى بعد 30 ثانية.")
            asyncio.create_task(schedule_cleanup())

        # التنظيف يتم داخل cleanup_messages حتى لا تبقى رسالة الحالة أو الفيديو.
        return True

    except AuthKeyUnregisteredError:
        logger.exception("مفتاح العميل العام غير مسجل أثناء معالجة الرابط للمستخدم %s", user_id)
        if public_mode:
            await reset_public_client()
            # بديل Bot API مشروع: ينجح فقط إذا كان البوت قادراً فعلياً
            # على الوصول إلى القناة العامة. لا يتجاوز الخصوصية أو الحماية.
            try:
                bot_sent_message = await context.bot.copy_message(
                    chat_id=user_id,
                    from_chat_id=entity,
                    message_id=message_id,
                )
                await status.edit_text("✅ تم إرسال المحتوى بنجاح.\n🗑️ سيتم حذف المحتوى بعد 30 ثانية.")
                asyncio.create_task(schedule_cleanup())
                return True
            except Exception:
                logger.warning(
                    "تعذر استخدام Bot API للوصول إلى المنشور العام %s/%s",
                    entity,
                    message_id,
                    exc_info=True,
                )
        try:
            await status.edit_text(localized(
                user_id,
                "⚠️ لا يملك البوت وصولاً إلى هذا المنشور العام عبر Telegram. أضف البوت إلى القناة أو سجّل الدخول بحساب مصرح له ثم أرسل الرابط مرة أخرى.",
                "⚠️ Telegram did not grant the bot access to this public post. Add the bot to the channel or log in with an authorized account, then send the link again.",
            ))
        finally:
            await cleanup_messages()
        return False
    except asyncio.TimeoutError:
        logger.exception("انتهت مهلة معالجة الرابط للمستخدم %s", user_id)
        try:
            if user_id == OWNER_ID:
                await status.edit_text("❌ تفاصيل الخطأ للمالك:\n\n" + traceback.format_exc()[-3800:])
            else:
                await status.edit_text("⏱️ استغرقت العملية وقتاً أطول من المسموح وتم إيقافها.\nجرّب مقطعاً أصغر أو أعد المحاولة لاحقاً.")
        finally:
            await cleanup_messages()
        return False
    except ValueError as exc:
        try:
            if user_id == OWNER_ID:
                await status.edit_text("❌ تفاصيل الخطأ للمالك:\n\n" + traceback.format_exc()[-3800:])
            else:
                await status.edit_text(f"⚠️ {exc}")
        finally:
            await cleanup_messages()
        return False
    except Exception as exc:
        logger.exception("فشلت معالجة رابط للمستخدم %s", user_id)
        try:
            if bot_sent_message is not None:
                await status.edit_text("✅ تم إرسال المحتوى بنجاح.\n🗑️ سيتم حذف المحتوى بعد 30 ثانية.")
                asyncio.create_task(schedule_cleanup())
                return True
            if user_id == OWNER_ID:
                await status.edit_text("❌ تفاصيل الخطأ للمالك:\n\n" + traceback.format_exc()[-3800:])
            else:
                await status.edit_text("❌ لم يتم التنزيل.\nتحقق من أن الرابط صحيح، وأن المنشور متاح للحساب، وأن حجم الملف ضمن الحد المسموح.")
        finally:
            await cleanup_messages()
        return False
    finally:
        if public_mode and client is not None:
            try:
                if client.is_connected():
                    await client.disconnect()
            except Exception:
                logger.debug("تعذر فصل عميل الرابط العام بعد انتهاء العملية", exc_info=True)



# حالة خادم الويب على مستوى الملف حتى يمكن لـ post_init تشغيله فعلياً.
web_server = None
web_server_task = None
web_bot = None


async def report_error_to_owner(title: str, exc: BaseException | None = None, details: str = "") -> None:
    """إرسال تفاصيل الأخطاء المهمة للمالك مع traceback كامل قدر الإمكان."""
    try:
        parts = [
            "🚨 خطأ في البوت / Mini App",
            f"📌 {title}",
            f"🕒 {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime())}",
        ]
        if details:
            parts.append(f"📋 السياق:\n{details}")
        if exc is not None:
            parts.append(f"❌ النوع: {type(exc).__name__}")
            parts.append(f"💬 الرسالة: {exc}")
            tb = "".join(traceback.TracebackException.from_exception(exc).format())
            parts.append("🧩 Traceback:\n" + tb[-6000:])
        text = "\n\n".join(parts)
        # Telegram message limit is 4096 chars; keep a safe margin.
        text = text[:3900]
        if web_bot is not None:
            await web_bot.send_message(chat_id=OWNER_ID, text=text)
    except Exception:
        logger.exception("تعذر إرسال تقرير الخطأ إلى المالك")


async def post_init(application: Application) -> None:
    global web_bot
    web_bot = application.bot
    try:
        bot_info = await application.bot.get_me()
        logger.info("البوت المتصل فعلياً: @%s (id=%s)، المالك: %s", bot_info.username, bot_info.id, OWNER_ID)
    except Exception:
        logger.exception("تعذر قراءة هوية البوت عند بدء التشغيل")
    logger.info("البوت يعمل، المالك: %s", OWNER_ID)
    # جلسات المالك المتعددة: تفعيل مستمع الرسائل الموقوتة لكل ملف جلسة محفوظ.
    owner_session_ids.update({
        int(path.stem[len("user_"):])
        for path in SESSION_DIR.glob("user_*.session")
        if path.stem[len("user_"):].isdigit()
    })
    for session_id in sorted(owner_session_ids):
        try:
            session_client = await get_or_create_client(session_id)
            if await session_client.is_user_authorized():
                logger.info("تم تفعيل مراقبة الرسائل الموقوتة لجلسة المالك %s", session_id)
        except Exception:
            logger.warning("تعذر تفعيل مراقبة جلسة المالك %s", session_id, exc_info=True)
    # مهام asyncio لا تبقى بعد إعادة تشغيل الخدمة، لكن حالة المهمة محفوظة في JSON.
    # نزيل الحالات المؤقتة القديمة فقط، ونحافظ على last_message_id للاستئناف.
    changed = False
    for job_id, job in channel_transfers.items():
        status = str(job.get("status", ""))
        if status.startswith(("يعمل", "جارٍ", "انتظار Telegram", "إعادة محاولة")):
            job["status"] = (
                "متوقف بعد إعادة التشغيل؛ اضغط بدء النقل للاستئناف من الرسالة "
                f"{int(job.get('last_message_id', 0)) + 1}"
            )
            job.pop("current_message_id", None)
            changed = True
    if changed:
        save_channel_transfers()

    # تشغيل واجهة الويب فعلياً عند بدء البوت.
    # مهم: لا نعتمد على دالة متداخلة داخل كتلة FastAPI، بل نشغّل Uvicorn
    # من post_init مباشرة حتى لا يحدث NameError.
    global web_server, web_server_task
    try:
        if FastAPI is None:
            raise RuntimeError("FastAPI/uvicorn غير مثبتين في بيئة التشغيل")
        config = uvicorn.Config(
            web_app,
            host=WEB_HOST,
            port=WEB_PORT,
            log_level="info",
            access_log=True,
        )
        web_server = uvicorn.Server(config)
        web_server_task = asyncio.create_task(web_server.serve())

        for _ in range(50):
            if web_server.started:
                logger.info("WEB_READY: http://%s:%s", WEB_HOST, WEB_PORT)
                logger.info("WEB_PUBLIC_URL: %s", WEB_PUBLIC_BASE_URL)
                break
            if web_server_task.done():
                exc = web_server_task.exception()
                if exc:
                    raise exc
                raise RuntimeError("Uvicorn توقف قبل بدء الاستماع")
            await asyncio.sleep(0.1)
        else:
            logger.warning("WEB_START_TIMEOUT: لم يؤكد Uvicorn بدء الاستماع خلال 5 ثوانٍ")
    except Exception:
        logger.exception("تعذر تشغيل واجهة الويب على 0.0.0.0:8080")


async def post_shutdown(application: Application) -> None:
    global web_server, web_server_task
    if web_server is not None:
        try:
            web_server.should_exit = True
        except Exception:
            pass
    for client in clients.values():
        if client.is_connected():
            await client.disconnect()


async def trace_update(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = getattr(update, "message", None)
    if message:
        logger.info(
            "تحديث وارد: update_id=%s user_id=%s chat_id=%s text=%r",
            getattr(update, "update_id", None),
            getattr(getattr(message, "from_user", None), "id", None),
            getattr(getattr(message, "chat", None), "id", None),
            getattr(message, "text", None),
        )
    else:
        logger.info("تحديث وارد غير نصي: update_id=%s", getattr(update, "update_id", None))


async def application_error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.exception("خطأ غير معالج في تحديث Telegram", exc_info=context.error)
    try:
        update_info = repr(update)
        await report_error_to_owner(
            "خطأ غير معالج في تحديث Telegram",
            context.error,
            update_info[-2500:],
        )
    except Exception:
        logger.exception("تعذر إرسال تقرير خطأ Telegram إلى المالك")
    if isinstance(update, Update) and update.effective_chat:
        try:
            await context.bot.send_message(
                chat_id=update.effective_chat.id,
                text="⚠️ حدث خطأ مؤقت. تم تسجيل التفاصيل، حاول الضغط على الزر مرة أخرى.",
            )
        except Exception:
            logger.exception("تعذر إرسال رسالة الخطأ للمستخدم")


def main() -> None:
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .concurrent_updates(max(1, min(4, int(os.getenv("BOT_CONCURRENT_UPDATES", "2")))))
        .build()
    )
    # مجموعة تشخيصية قبل المعالجات العادية: لا تغيّر السلوك، وتؤكد وصول /start لهذه النسخة.
    app.add_handler(TypeHandler(Update, trace_update), group=-1)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("cancel", cancel))
    app.add_handler(CommandHandler("channels", channels_command))
    app.add_handler(CommandHandler("addchannel", add_channel_command))
    app.add_handler(CommandHandler("starttransfer", start_transfer_command))
    app.add_handler(CommandHandler("stoptransfer", stop_transfer_command))
    app.add_handler(CommandHandler("transferstatus", transfer_status_command))
    app.add_handler(CallbackQueryHandler(transfer_callback, pattern=r"^(?:transfer|admin|user|owner|download):"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))
    app.add_handler(MessageHandler(filters.ALL & ~filters.TEXT & ~filters.COMMAND, archive_timed_message))
    app.add_error_handler(application_error_handler)
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
async def owner_open_session_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_owner(uid):
        return
    try:
        sid = int(q.data.split(":")[-1])
    except Exception:
        return
    client = clients.get(sid)
    if not client:
        await q.edit_message_text("❌ الجلسة غير موجودة.")
        return
    try:
        me = await client.get_me()
        await q.edit_message_text(
            f"📱 جلسة الحساب\n\n"
            f"الاسم: {getattr(me, 'first_name', '') or ''} {getattr(me, 'last_name', '') or ''}\n"
            f"المعرف: @{getattr(me, 'username', '') or 'بدون'}\n"
            f"ID: {me.id}\n\n"
            "اختر ما تريد فتحه:",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("💬 المحادثات", callback_data=f"owner:chats:{sid}:0")],
                [InlineKeyboardButton("🔙 الجلسات", callback_data="owner:sessions")],
            ])
        )
    except Exception as e:
        await q.edit_message_text(f"❌ تعذر فتح الجلسة: {e}")

async def owner_chats_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_owner(uid):
        return
    parts = q.data.split(":")
    sid, page = int(parts[2]), int(parts[3])
    client = clients.get(sid)
    if not client:
        await q.edit_message_text("❌ الجلسة غير متاحة.")
        return
    try:
        dialogs = [d async for d in client.iter_dialogs(limit=12)]
        start = page * 6
        chunk = dialogs[start:start+6]
        if not chunk:
            await q.edit_message_text("لا توجد محادثات في هذه الصفحة.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 رجوع", callback_data=f"owner:open_session:{sid}")]]))
            return
        rows = []
        for d in chunk:
            title = (d.name or "بدون اسم")[:28]
            rows.append([InlineKeyboardButton(f"💬 {title}", callback_data=f"owner:chat:{sid}:{d.id}")])
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅️ السابق", callback_data=f"owner:chats:{sid}:{page-1}"))
        nav.append(InlineKeyboardButton("➡️ التالي", callback_data=f"owner:chats:{sid}:{page+1}"))
        rows.append(nav)
        rows.append([InlineKeyboardButton("🔙 الجلسة", callback_data=f"owner:open_session:{sid}")])
        await q.edit_message_text("💬 محادثات الحساب:", reply_markup=InlineKeyboardMarkup(rows))
    except Exception as e:
        await q.edit_message_text(f"❌ تعذر جلب المحادثات: {e}")

async def owner_chat_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_owner(uid):
        return
    parts = q.data.split(":")
    sid, chat_id = int(parts[2]), int(parts[3])
    client = clients.get(sid)
    if not client:
        await q.edit_message_text("❌ الجلسة غير متاحة.")
        return
    try:
        msgs = [m async for m in client.iter_messages(chat_id, limit=8)]
        lines = ["🗨️ آخر الرسائل:\n"]
        media_count = 0
        for msg in reversed(msgs):
            text_msg = (msg.text or "").replace("\n", " ")[:90]
            if msg.media:
                media_count += 1
                text_msg = ("🖼️/📎 " + text_msg).strip()
            if not text_msg:
                text_msg = "📎 وسائط"
            lines.append(f"• {text_msg}")
        lines.append(f"\n📎 وسائط في المعاينة: {media_count}")
        await q.edit_message_text(
            "\n".join(lines),
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔙 المحادثات", callback_data=f"owner:chats:{sid}:0")],
                [InlineKeyboardButton("📱 الجلسة", callback_data=f"owner:open_session:{sid}")],
            ])
        )
    except Exception as e:
        await q.edit_message_text(f"❌ تعذر فتح المحادثة: {e}")
