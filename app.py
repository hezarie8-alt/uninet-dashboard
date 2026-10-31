import os
import json
import re
import secrets
import socket as _socket_mod
import threading
import time as _time_mod
import urllib.request
import jdatetime
from datetime import datetime, timedelta, date
from email.utils import parsedate_to_datetime
from functools import wraps
from zoneinfo import ZoneInfo
from concurrent.futures import ThreadPoolExecutor

from flask import (Flask, render_template, request, redirect, url_for,
                   session, flash, jsonify, Response)
from werkzeug.exceptions import HTTPException
from flask_sqlalchemy import SQLAlchemy
from werkzeug.security import generate_password_hash, check_password_hash
from flask_migrate import Migrate
from sqlalchemy import or_, and_, func, case, Index
from flask_wtf import FlaskForm, CSRFProtect
from wtforms import StringField, PasswordField, SubmitField
from wtforms.validators import DataRequired, Length, EqualTo, ValidationError
from flask_socketio import SocketIO, emit, join_room
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address

# ==========================================
# Timezone  —  همه timestamp‌ها به وقت تهران
# ==========================================
TEHRAN_TZ = ZoneInfo('Asia/Tehran')

# نام‌های فارسی (تنها یک منبع، هم برای رندر سرور و هم برای /api/now)
WEEKDAYS_FA = ['شنبه', 'یکشنبه', 'دوشنبه', 'سه‌شنبه', 'چهارشنبه', 'پنجشنبه', 'جمعه']
JALALI_MONTHS_FA = ['فروردین', 'اردیبهشت', 'خرداد', 'تیر', 'مرداد', 'شهریور',
                    'مهر', 'آبان', 'آذر', 'دی', 'بهمن', 'اسفند']
_PERSIAN_DIGITS = str.maketrans('0123456789', '۰۱۲۳۴۵۶۷۸۹')


def fa_digits(value):
    """تبدیل ارقام لاتین به فارسی"""
    return str(value).translate(_PERSIAN_DIGITS)


def jalali_text(jd):
    """«۲۱ مهر ۱۴۰۵» — ارقام و نام ماه فارسی"""
    return '%s %s %s' % (fa_digits(jd.day), JALALI_MONTHS_FA[jd.month - 1],
                         fa_digits(jd.year))


def now_tehran():
    """زمان فعلی با timezone تهران (بدون tzinfo برای ذخیره در DB)

    منبع واحد زمان کل برنامه. اگر اختلاف ساعت سیستم با ساعت جهانی
    بیشتر از ۲ ثانیه اندازه‌گیری شده باشد (در thread پس‌زمینه)، اصلاحش اعمال می‌شود.
    """
    with _clock_lock:
        offset_ms = _clock_state['offset_ms']
    base = datetime.now(TEHRAN_TZ)
    if offset_ms:
        base = base + timedelta(milliseconds=offset_ms)
    return base.replace(tzinfo=None)


def now_tehran_aware():
    """همان now_tehran ولی با tzinfo (برای epoch/ISO در /api/now)"""
    return now_tehran().replace(tzinfo=TEHRAN_TZ)


# ==========================================
# Trusted time — همگام‌سازی با ساعت جهانی (Task 2)
#   اگر ساعت سیستم خراب باشد (مثلاً ۱۰٫۵ ساعت جلوتر — طبق Event Log ویندوز
#   در ۲۰۲۶/۱۰/۱۳)، این اصلاح خودکار آن را درست می‌کند. بدون بلاک کردن صفحات.
# ==========================================
_clock_lock = threading.Lock()
_clock_state = {
    'offset_ms': 0,    # اصلاح اعمال‌شده روی ساعت سیستم (جهانی − سیستم)
    'drift_ms': 0,     # آخرین اختلاف اندازه‌گیری‌شده
    'source': None,    # منبع معتبر آخرین همگام‌سازی موفق
    'last_sync': None,  # ISO زمان آخرین همگام‌سازی موفق
    'error': None,     # آخرین خطا (برای هشدار/گزارش)
}
_clock_thread_started = False
_SYNC_INTERVAL_S = 600          # هر ۱۰ دقیقه
_DRIFT_APPLY_THRESHOLD_MS = 2000
_DRIFT_MAX_PLAUSIBLE_MS = 7 * 24 * 3600 * 1000


def _fetch_json(url, timeout=4):
    req = urllib.request.Request(url, headers={'User-Agent': 'UniNet/1.0'})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode('utf-8', 'replace'))


def _external_ms_timeapi():
    """timeapi.io — زنده آزمایش شد: dateTime به وقت تهران (بدون offset)"""
    data = _fetch_json('https://timeapi.io/api/Time/current/zone?timeZone=Asia/Tehran')
    dt = datetime.fromisoformat(data['dateTime'])
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=TEHRAN_TZ)
    return int(dt.timestamp() * 1000), 'timeapi.io'


def _external_ms_worldtime():
    """worldtimeapi.org — در این شبکه معمولاً خطای SSL می‌دهد؛ به‌عنوان پشتیبان"""
    data = _fetch_json('https://worldtimeapi.org/api/timezone/Asia/Tehran')
    return int(data['unixtime']) * 1000, 'worldtimeapi.org'


def _external_ms_date_header():
    """هدر Date پاسخ HTTPS (دقت ۱ ثانیه) — پشتیبان نهایی؛ زنده آزمایش شد"""
    req = urllib.request.Request('https://www.cloudflare.com/', method='HEAD',
                                 headers={'User-Agent': 'UniNet/1.0'})
    with urllib.request.urlopen(req, timeout=4) as resp:
        date_hdr = resp.headers.get('Date')
    if not date_hdr:
        raise RuntimeError('no Date header')
    return int(parsedate_to_datetime(date_hdr).timestamp() * 1000), 'HTTPS Date header'


def _apply_drift(drift_ms, source):
    """اعتبارسنجی + اعمال اختلاف اندازه‌گیری‌شده.
    فقط اگر |drift| > ۲ ثانیه باشد اعمال می‌شود؛ خرابی محاسباتی رد می‌شود."""
    if abs(drift_ms) > _DRIFT_MAX_PLAUSIBLE_MS:
        with _clock_lock:
            _clock_state['error'] = 'implausible drift %s ms from %s' % (drift_ms, source)
        app.logger.warning('clock sync: ignoring implausible drift %s ms from %s',
                           drift_ms, source)
        return False
    applied = abs(drift_ms) > _DRIFT_APPLY_THRESHOLD_MS
    with _clock_lock:
        _clock_state['offset_ms'] = drift_ms if applied else 0
        _clock_state['drift_ms'] = drift_ms
        _clock_state['source'] = source
        _clock_state['last_sync'] = datetime.now(TEHRAN_TZ).isoformat()
        _clock_state['error'] = None
    if applied:
        app.logger.warning(
            'clock sync: machine clock off by %s ms — correction applied (source=%s)',
            drift_ms, source)
    return True


def sync_clock_offset():
    """اندازه‌گیری اختلاف ساعت سیستم با چند منبع معتبر و اعمال اگر > ۲ ثانیه باشد.
    زنجیره منابع: timeapi.io → worldtimeapi.org → هدر Date HTTPS.
    اگر همه شکست بخورند: به ساعت سیستم (با اصلاح آخرین اندازه‌گیری موفق)
    برمی‌گردیم و هشدار ثبت می‌کنیم. هیچ‌وقت درخواست صفحه را معطل نمی‌کند."""
    for fetcher in (_external_ms_timeapi, _external_ms_worldtime,
                    _external_ms_date_header):
        t0 = int(_time_mod.time() * 1000)
        try:
            external_ms, source = fetcher()
        except Exception as exc:
            with _clock_lock:
                _clock_state['error'] = '%s: %s' % (fetcher.__name__, exc)
            app.logger.warning('clock sync: source %s failed: %s',
                               fetcher.__name__, exc)
            continue
        t1 = int(_time_mod.time() * 1000)
        # زمان سیستم را در وسط بازهٔ درخواست می‌خوانیم تا تأخیر شبکه خنثی شود
        drift = external_ms - ((t0 + t1) // 2)
        if _apply_drift(drift, source):
            return source
    with _clock_lock:
        prev_offset = _clock_state['offset_ms']
        _clock_state['error'] = 'all external time sources failed'
    app.logger.warning(
        'clock sync: all external sources failed — using system clock '
        '(previous correction: %s ms)', prev_offset)
    return None


def _clock_sync_loop():
    while True:
        try:
            sync_clock_offset()
        except Exception:
            app.logger.exception('clock sync loop error')
        _time_mod.sleep(_SYNC_INTERVAL_S)


def start_clock_sync():
    """شروع همگام‌سازی دوره‌ای در thread پس‌زمینه (فقط یک بار، غیر bloک‌کننده)"""
    global _clock_thread_started
    with _clock_lock:
        if _clock_thread_started:
            return
        _clock_thread_started = True
    threading.Thread(target=_clock_sync_loop, daemon=True,
                     name='uninet-clock-sync').start()


def fmt_time(dt):
    if dt is None:
        return ''
    return dt.strftime('%H:%M')


def fmt_datetime(dt):
    if dt is None:
        return ''
    return dt.strftime('%Y-%m-%d %H:%M')


# ==========================================
# App Configuration
# ==========================================
app = Flask(__name__)
app.config['SECRET_KEY'] = os.environ.get('SECRET_KEY') or 'uninet-dashboard-dev-secret-change-me'

# Session security
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
app.config['SESSION_COOKIE_NAME'] = 'uninet_dashboard_session'


# ─── Database ───
database_url = os.getenv("DATABASE_URL")
if not database_url:
    basedir = os.path.abspath(os.path.dirname(__file__))
    database_url = 'sqlite:///' + os.path.join(basedir, 'app.db')
else:
    if database_url.startswith("postgres://"):
        database_url = database_url.replace("postgres://", "postgresql://", 1)

app.config['SQLALCHEMY_ENGINE_OPTIONS'] = {
    "pool_pre_ping": True,
    "pool_recycle": 300,
    "pool_size": 5,
    "max_overflow": 10
}
app.config['SQLALCHEMY_DATABASE_URI'] = database_url
app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False

db = SQLAlchemy(app)
migrate = Migrate(app, db)
limiter = Limiter(key_func=get_remote_address, app=app, storage_uri="memory://")

# ─── SocketIO: threading mode (سازگار با ویندوز / Python 3.12) ───
def _build_allowed_origins():
    """فهرست مجاز Originها برای اتصال Socket.IO (همیشه به‌صورت list).

    نکته‌ی مهم (ریشه باگ «is not an accepted origin»): python-engineio یک رشته
    را split نمی‌کند و آن را به‌صورت «یک» Origin واحد در نظر می‌گیرد؛ پس
    'http://127.0.0.1:5000,http://localhost:5000' عملاً هیچ Origin واقعی را
    نمی‌پذیرد. بنابراین اینجا همیشه لیست پاس می‌شود.

    پیکربندی: متغیر محیطی SOCKETIO_ALLOWED_ORIGINS (جداشده با کاما)، وگرنه
    CORS_ORIGINS (نام قدیمی)، وگرنه مقادیر پیش‌فرض محلی + Origin آدرس LAN در
    صورت اجرا با میزبان 0.0.0.0.
    """
    raw = os.environ.get('SOCKETIO_ALLOWED_ORIGINS') or os.environ.get('CORS_ORIGINS', '')
    if raw.strip():
        return [o.strip() for o in raw.split(',') if o.strip()]
    try:
        port = int(os.environ.get('PORT', 5001))
    except ValueError:
        port = 5000
    origins = [
        'http://127.0.0.1:%d' % port,
        'http://localhost:%d' % port,
    ]
    if port != 5001:
        origins += ['http://127.0.0.1:5001', 'http://localhost:5001']
    if os.environ.get('HOST', '127.0.0.1') in ('0.0.0.0', '::', '::0'):
        # اجرای Lan-only: Origin آدرس IP داخلی را هم اضافه کن
        try:
            _s = _socket_mod.socket(_socket_mod.AF_INET, _socket_mod.SOCK_DGRAM)
            _s.settimeout(0.3)
            _s.connect(('8.8.8.8', 53))  # UDP connect: بسته‌ای ارسال نمی‌شود
            lan_ip = _s.getsockname()[0]
            _s.close()
            if lan_ip and not lan_ip.startswith('127.'):
                origins.append('http://%s:%d' % (lan_ip, port))
        except Exception:
            app.logger.warning('LAN origin detection failed; using local origins only')
    return origins


socketio = SocketIO(
    app,
    cors_allowed_origins=_build_allowed_origins(),
    async_mode='threading'
)

csrf = CSRFProtect(app)

ONLINE_USERS_MEMORY = set()

CLASS_TIME_SLOTS = ['08:00-10:00', '10:00-12:00', '12:00-14:00',
                    '14:00-16:00', '16:00-18:00', '18:00-20:00']


# ==========================================
# State Manager
# ==========================================
class StateManager:
    @staticmethod
    def set_online(user_id):
        ONLINE_USERS_MEMORY.add(user_id)

    @staticmethod
    def set_offline(user_id):
        ONLINE_USERS_MEMORY.discard(user_id)

    @staticmethod
    def is_online(user_id):
        return user_id in ONLINE_USERS_MEMORY


# ==========================================
# Models
# ==========================================

class User(db.Model):
    __tablename__ = 'user'
    id = db.Column(db.Integer, primary_key=True)
    full_name = db.Column(db.String(100), nullable=False)
    student_id = db.Column(db.String(20), unique=True, nullable=False, index=True)
    password_hash = db.Column(db.String(256), nullable=False)
    major = db.Column(db.String(100))
    profile_pic = db.Column(db.String(255), default='default.jpg')
    is_admin = db.Column(db.Boolean, default=False)
    created_at = db.Column(db.DateTime, default=now_tehran)
    last_seen = db.Column(db.DateTime, default=now_tehran)
    last_seen_visibility = db.Column(db.String(20), default='all')
    profile_pic_visibility = db.Column(db.String(20), default='all')
    who_can_message = db.Column(db.String(20), default='all')
    chat_theme = db.Column(db.String(50), default='default')


class ClassSchedule(db.Model):
    __tablename__ = 'schedule'
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    day = db.Column(db.String(10), nullable=False)
    time_slot = db.Column(db.String(20), nullable=False)
    course_name = db.Column(db.String(100))
    class_location = db.Column(db.String(100))
    professor_name = db.Column(db.String(100), nullable=True)
    week_type = db.Column(db.String(10), default='all')
    # Part B — واحد اختیاری برای کلاس‌های شخصی (در مجموع واحدها لحاظ می‌شود)
    units = db.Column(db.Float)

    def to_dict(self):
        """بریکت ساده برای `tojson` در dashboard.html (کلیدهایی که جاوااسکریپت می‌خواند).

        اشیای SQLAlchemy با فیلتر tojson قابل تبدیل به JSON نیستند؛ همه فیلدها
        در این مدل رشته/عدد هستند و None بدون تغییر null می‌ماند.
        """
        return {
            'id': self.id,
            'day': self.day,
            'time_slot': self.time_slot,
            'course_name': self.course_name,
            'class_location': self.class_location,
            'professor_name': self.professor_name,
            'week_type': self.week_type or 'all',
            'units': self.units,
        }


class MasterSchedule(db.Model):
    __tablename__ = 'master_schedule'
    id = db.Column(db.Integer, primary_key=True)
    day = db.Column(db.String(10), nullable=False)
    time_slot = db.Column(db.String(20), nullable=False)
    rooms = db.Column(db.Text, nullable=False)


class Reservation(db.Model):
    __tablename__ = 'reservation'
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    master_slot_id = db.Column(db.Integer, db.ForeignKey('master_schedule.id'), nullable=False)
    room_name = db.Column(db.String(50), nullable=False)
    reason = db.Column(db.Text, nullable=False)
    status = db.Column(db.String(20), default='pending')
    created_at = db.Column(db.DateTime, default=now_tehran)
    user = db.relationship('User', foreign_keys=[user_id])
    master_slot = db.relationship('MasterSchedule', foreign_keys=[master_slot_id])


class CancelledClass(db.Model):
    __tablename__ = 'cancelled_class'
    id = db.Column(db.Integer, primary_key=True)
    professor_name = db.Column(db.String(100), nullable=True)
    course_name = db.Column(db.String(100), nullable=True)
    time_slot = db.Column(db.String(20), nullable=True)
    cancel_date = db.Column(db.Date, nullable=True)
    start_date = db.Column(db.Date, nullable=True)
    end_date = db.Column(db.Date, nullable=True)
    description = db.Column(db.Text, nullable=True)
    created_at = db.Column(db.DateTime, default=now_tehran)

    viewer_records = db.relationship('CancelledClassView', backref='cancelled_class',
                                     lazy='dynamic', cascade='all, delete-orphan')


class CancelledClassView(db.Model):
    __tablename__ = 'cancelled_class_view'
    id = db.Column(db.Integer, primary_key=True)
    cancelled_class_id = db.Column(db.Integer, db.ForeignKey('cancelled_class.id'), nullable=False)
    user_id = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    viewed_at = db.Column(db.DateTime, default=now_tehran)
    __table_args__ = (db.UniqueConstraint('cancelled_class_id', 'user_id'),)


class Notification(db.Model):
    __tablename__ = 'notification'
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('user.id'), nullable=False)
    message = db.Column(db.String(255), nullable=False)
    is_read = db.Column(db.Boolean, default=False)
    created_at = db.Column(db.DateTime, default=now_tehran)


class SystemSetting(db.Model):
    __tablename__ = 'system_setting'
    key = db.Column(db.String(50), primary_key=True)
    value = db.Column(db.String(100), nullable=True)


class HolidayOverride(db.Model):
    """افزوده/حذف‌های مدیر روی تقویم تعطیلات (additive — جدول جدید Task 3)"""
    __tablename__ = 'holiday_overrides'

    id = db.Column(db.Integer, primary_key=True)
    year = db.Column(db.Integer, nullable=False)      # سال شمسی
    month = db.Column(db.Integer, nullable=False)     # ۱..۱۲
    day = db.Column(db.Integer, nullable=False)       # ۱..۳۱
    kind = db.Column(db.String(8), nullable=False)    # 'add' | 'remove'
    occasion = db.Column(db.String(200))              # برای kind='add'
    created_at = db.Column(db.DateTime, default=lambda: now_tehran())


# ==========================================
# Models — کاتالوگ دروس (Part B)
# «درس/گروه/جلسه» فقط یک‌بار توسط ادمین ثبت می‌شود؛ برنامهٔ دانشجو «مرجع»
# است (ScheduleEnrollment) و همهٔ داده‌های نمایش‌داده‌شده زنده از کاتالوگ
# خوانده می‌شوند تا ویرایش ادمین بلافاصله برای همه اعمال شود.
# ==========================================

class CatalogCourse(db.Model):
    """درس در کاتالوگ — «کد درسی» یکتا و ایندکس‌شده؛ name_norm کلید جست‌جوست."""
    __tablename__ = 'catalog_course'

    id = db.Column(db.Integer, primary_key=True)
    code = db.Column(db.String(20), unique=True, nullable=False, index=True)
    name = db.Column(db.String(200), nullable=False)
    name_norm = db.Column(db.String(200), nullable=False, default='', index=True)
    units = db.Column(db.Numeric(4, 1, asdecimal=False), nullable=False)  # >۰، اعشار مجاز
    major = db.Column(db.String(100))
    created_at = db.Column(db.DateTime, default=lambda: now_tehran())
    updated_at = db.Column(db.DateTime, default=lambda: now_tehran(),
                            onupdate=lambda: now_tehran())

    sections = db.relationship(
        'CourseSection', backref='course', lazy='selectin',
        cascade='all, delete-orphan',
        order_by='CourseSection.term, CourseSection.group_number')


class CourseSection(db.Model):
    """گروه یک درس در یک ترم (یکتای (course, term, group_number))."""
    __tablename__ = 'course_section'
    __table_args__ = (
        db.UniqueConstraint('course_id', 'term', 'group_number',
                            name='uq_section_course_term_group'),
    )

    id = db.Column(db.Integer, primary_key=True)
    course_id = db.Column(db.Integer, db.ForeignKey('catalog_course.id'),
                          nullable=False, index=True)
    term = db.Column(db.String(10), nullable=False, index=True)
    group_number = db.Column(db.Integer, nullable=False)
    teacher = db.Column(db.String(100), default='')
    location = db.Column(db.String(100), default='')   # محل پیش‌فرض گروه
    is_active = db.Column(db.Boolean, nullable=False, default=True)  # حذف نرم
    updated_at = db.Column(db.DateTime, default=lambda: now_tehran(),
                            onupdate=lambda: now_tehran())

    meetings = db.relationship(
        'SectionMeeting', backref='section', lazy='selectin',
        cascade='all, delete-orphan',
        order_by='SectionMeeting.day, SectionMeeting.start_time')


class SectionMeeting(db.Model):
    """جلسهٔ هفتگی یک گروه — همان قرارداد روز/هفتهٔ ClassSchedule.

    day: 'saturday'..'friday' (همان کلیدهای schedule شخصی)
    start_time/end_time: 'HH:MM' با ارقام ASCII (۲۴ ساعته)
    week_type: 'all' | 'odd' | 'even'
    location_override: محل جایگزینِ این جلسه (خالی = محل گروه)
    is_active: حذف نرم جلسه وقتی دانشجویی ثبت‌نام کرده است
    """
    __tablename__ = 'section_meeting'

    id = db.Column(db.Integer, primary_key=True)
    section_id = db.Column(db.Integer, db.ForeignKey('course_section.id'),
                           nullable=False, index=True)
    day = db.Column(db.String(10), nullable=False)
    start_time = db.Column(db.String(5), nullable=False)
    end_time = db.Column(db.String(5), nullable=False)
    week_type = db.Column(db.String(10), nullable=False, default='all')
    location_override = db.Column(db.String(100))
    is_active = db.Column(db.Boolean, nullable=False, default=True)


class ScheduleEnrollment(db.Model):
    """ثبت‌نام دانشجو در یک گروه — فقط «مرجع»؛ هیچ دادهٔ زمان/استاد/مکان/نام
    در اینجا کپی نمی‌شود تا ویرایش ادمین خودبه‌خود به همه برسد."""
    __tablename__ = 'schedule_enrollment'
    __table_args__ = (
        db.UniqueConstraint('user_id', 'section_id',
                            name='uq_enrollment_user_section'),
    )

    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey('user.id'),
                        nullable=False, index=True)
    section_id = db.Column(db.Integer, db.ForeignKey('course_section.id'),
                           nullable=False, index=True)
    created_at = db.Column(db.DateTime, default=lambda: now_tehran())

    section = db.relationship('CourseSection', backref='enrollments', lazy='joined')


# --- نرمال‌سازی متن فارسی (Part B9) — یک تابع مشترک برای ذخیره و جست‌جو ---
# جداکنندهٔ اعشار فارسی «٫» هم → '.' تا واحد «۲٫۵» پذیرفته شود (ورودی فقط؛ ذخیره ASCII)
_FA_DIGITS = str.maketrans('۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩٫',
                           '01234567890123456789.')
_EN_TO_FA_DIGITS = str.maketrans('0123456789', '۰۱۲۳۴۵۶۷۸۹')


def fa_digits_to_en(text):
    """ارقام فارسی/عربی + جداکنندهٔ اعشار فارسی → ASCII."""
    return str(text or '').translate(_FA_DIGITS)


def en_digits_to_fa(text):
    """ارقام ASCII → فارسی (برای نمایش)."""
    return str(text or '').translate(_EN_TO_FA_DIGITS)


def canon_fa(text):
    """نگارش استاندارد برای ذخیره/نمایش: ي عربی→ی فارسی و ك عربی→ک فارسی.

    بقیهٔ متن (شامل ZWNJ و ارقام فارسی) دست‌نخورده می‌ماند.
    """
    if not text:
        return ''
    return str(text).replace('\u064a', '\u06cc').replace('\u0643', '\u06a9')


def normalize_fa(text):
    """کلید جست‌جو: ي→ی، ك→ک، حذف تطويل/اعراب، ZWNJ→فاصله، ارقام→ASCII،
    فشردن فاصله‌ها و lowercase. «سیستم‌های نهفته» و «سيستم های نهفته» هم‌کلید می‌شوند."""
    if not text:
        return ''
    s = canon_fa(text)
    s = s.translate(_FA_DIGITS)
    s = re.sub(r'[\u0640\u064b-\u0652\u0670]', '', s)   # تطويل + اعراب + الف فوقانی
    s = s.replace('\u200c', ' ')                        # ZWNJ → فاصله
    s = re.sub(r'\s+', ' ', s).strip().lower()
    return s


HOLIDAY_DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')
_HOLIDAY_REFRESH_S = 24 * 3600
_holiday_file_cache = {}          # year -> (mtime, holidays dict)
_holiday_refresh_started = False
_holiday_refresh_lock = threading.Lock()


def _holiday_file_path(year):
    return os.path.join(HOLIDAY_DATA_DIR, 'iran_holidays_%d.json' % year)


def _clean_holiday_name(name):
    name = re.sub(r'\s+', ' ', (name or '')).strip()
    return name.replace('عیدنوروز', 'عید نوروز')


def _read_holiday_seed(year):
    """خواندن + ممورایز کردن فایل seed (بر اساس mtime تا refresh پس‌زمینه دیده شود)"""
    path = _holiday_file_path(year)
    try:
        mtime = os.path.getmtime(path)
    except OSError:
        return None
    cached = _holiday_file_cache.get(year)
    if cached and cached[0] == mtime:
        return cached[1]
    try:
        with open(path, encoding='utf-8') as fh:
            data = json.load(fh)
        holidays = data.get('holidays') or {}
        _holiday_file_cache[year] = (mtime, holidays)
        return holidays
    except Exception:
        app.logger.exception('holiday seed unreadable: %s', path)
        return None


def get_year_holidays(year):
    """تعطیلات رسمی یک سال = seed + addهای مدیر − removeهای مدیر.
    خروجی: {'MM-DD': [نام رویدادها]}"""
    base = dict(_read_holiday_seed(year) or {})
    try:
        overrides = HolidayOverride.query.filter_by(year=year).all()
    except Exception:
        app.logger.exception('holiday overrides query failed')
        overrides = []
    for ov in overrides:
        key = '%02d-%02d' % (ov.month, ov.day)
        if ov.kind == 'add':
            names = list(base.get(key) or [])
            if ov.occasion and ov.occasion not in names:
                names.append(ov.occasion)
            base[key] = names
        elif ov.kind == 'remove':
            base.pop(key, None)
    return base


def jalali_month_days(jy, jm):
    """تعداد روزهای یک ماه شمسی (اسفند سال کبیسه ۳۰)"""
    if jm <= 6:
        return 31
    if jm <= 11:
        return 30
    try:
        jdatetime.date(jy, 12, 30)
        return 30
    except ValueError:
        return 29


def build_calendar_month(jy, jm):
    """ساخت روزهای یک ماه شمسی با تعطیلات — بدون هیچ محاسبه جلالی سمت کلاینت.
    جمعه: قرمز + label «تعطیل» + tooltip «جمعه» (مگر مناسبت رسمی داشته باشد)."""
    holidays = get_year_holidays(jy)
    days = []
    for d in range(1, jalali_month_days(jy, jm) + 1):
        jd = jdatetime.date(jy, jm, d)
        widx = jd.weekday()                      # شنبه=۰ … جمعه=۶
        is_friday = (widx == 6)
        events = list(holidays.get('%02d-%02d' % (jm, d), []))
        if is_friday and events:                 # جمعه با مناسبت رسمی
            label = tooltip = events[0]
        elif is_friday:                          # جمعهٔ معمولی هفتگی
            label, tooltip = 'تعطیل', 'جمعه'
        elif events:                             # تعطیل رسمی روز هفته
            label = tooltip = events[0]
        else:
            label = tooltip = None
        days.append({
            'day': d,
            'weekday_index': widx,
            'gregorian': jd.togregorian().isoformat(),
            'is_friday': is_friday,
            'is_holiday': bool(events) or is_friday,
            'events': events,
            'label': label,
            'tooltip': tooltip,
        })
    return days


def _fetch_holiday_day(args):
    """یک روز شمسی از holidayapi.ir (برای refresh پس‌زمینه)"""
    jy, jm, day = args
    url = 'https://holidayapi.ir/jalali/%d/%02d/%02d' % (jy, jm, day)
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'UniNet/1.0'})
        with urllib.request.urlopen(req, timeout=6) as resp:
            return (jm, day), json.loads(resp.read().decode('utf-8', 'replace'))
    except Exception:
        return (jm, day), None


def _live_holiday_map(jy, fetcher=None):
    """دریافت زندهٔ کل یک سال از holidayapi.ir. اگر حتی یک روز شکست بخورد
    None برمی‌گرداند (هرگز کش ناقص نمی‌نویسد). fetcher برای تست قابل تزریق است."""
    fetcher = fetcher or _fetch_holiday_day
    args_list = [(jy, jm, d) for jm in range(1, 13)
                 for d in range(1, jalali_month_days(jy, jm) + 1)]
    holidays = {}
    with ThreadPoolExecutor(max_workers=6) as executor:
        for (jm, day), data in executor.map(fetcher, args_list):
            if data is None:
                return None
            if not data.get('is_holiday'):
                continue
            is_friday = jdatetime.date(jy, jm, day).weekday() == 6
            names = []
            for e in data.get('events', []):
                if not e.get('is_holiday'):
                    continue
                name = _clean_holiday_name(e.get('description'))
                if not name or name in names:
                    continue
                if is_friday and name == 'جمعه':
                    continue          # جمعهٔ هفتگی را سرور خودش محاسبه می‌کند
                names.append(name)
            if names:
                holidays['%02d-%02d' % (jm, day)] = names
    return holidays


def refresh_holiday_year(jy, fetcher=None):
    """به‌روزرسانی کش آفلاین یک سال از منبع زنده (atomic write + invalidate)"""
    holidays = _live_holiday_map(jy, fetcher=fetcher)
    if holidays is None:
        app.logger.warning('holiday refresh: live fetch incomplete for %d — '
                           'keeping previous cache', jy)
        return False
    payload = {
        'year': jy,
        'generated_at': now_tehran().isoformat(),
        'primary_source': 'holidayapi.ir day-level is_holiday '
                          '(events filtered to is_holiday=true)',
        'notes': 'refreshed by background service; plain Fridays are computed '
                 'by the server and are not stored.',
        'holidays': holidays,
    }
    path = _holiday_file_path(jy)
    tmp = path + '.tmp'
    os.makedirs(HOLIDAY_DATA_DIR, exist_ok=True)
    with open(tmp, 'w', encoding='utf-8') as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1, sort_keys=True)
    os.replace(tmp, path)
    _holiday_file_cache.pop(jy, None)
    app.logger.info('holiday cache refreshed for %d (%d holidays)',
                    jy, len(holidays))
    return True


def _run_holiday_refresh_once():
    """سال جاری و بعدی را فقط اگر فایل نباشد یا >۲۴ ساعت قدیمی باشد refresh کند"""
    today_j = jdatetime.date.fromgregorian(date=now_tehran().date())
    for jy in (today_j.year, today_j.year + 1):
        path = _holiday_file_path(jy)
        try:
            if (_time_mod.time() - os.path.getmtime(path)) < _HOLIDAY_REFRESH_S:
                continue
        except OSError:
            pass
        refresh_holiday_year(jy)


def _holiday_refresh_loop():
    while True:
        try:
            _run_holiday_refresh_once()
        except Exception:
            app.logger.exception('holiday refresh loop error')
        _time_mod.sleep(_HOLIDAY_REFRESH_S)


def start_holiday_refresh():
    """شروع refresh دوره‌ای در thread پس‌زمینه (فقط یک بار، غیر bloک‌کننده)"""
    global _holiday_refresh_started
    with _holiday_refresh_lock:
        if _holiday_refresh_started:
            return
        _holiday_refresh_started = True
    threading.Thread(target=_holiday_refresh_loop, daemon=True,
                     name='uninet-holiday-refresh').start()


def create_initial_data():
    try:
        if not User.query.filter_by(student_id='admin').first():
            admin_password = secrets.token_urlsafe(12)
            admin = User(
                full_name='مدیر سیستم',
                student_id='admin',
                major='مدیریت',
                password_hash=generate_password_hash(admin_password, method='pbkdf2:sha256'),
                is_admin=True
            )
            db.session.add(admin)
            db.session.commit()
            print(f"✓ Admin user created: ID=admin | Password={admin_password}")
        else:
            print("✓ Admin user already exists, skipping.")
    except Exception as e:
        db.session.rollback()
        print(f"Warning: create_initial_data error: {e}")


# ==========================================
# Helpers
# ==========================================


# ==========================================
# Services
# ==========================================

class AuthService:
    @staticmethod
    def register_user(student_id, password):
        """
        ثبت‌نام با شماره دانشجویی و کد ملی.
        full_name و major از طریق ویرایش پروفایل تکمیل می‌شوند.
        full_name به صورت موقت برابر شماره دانشجویی قرار می‌گیرد.
        """
        try:
            hashed = generate_password_hash(password, method='pbkdf2:sha256')
            is_admin = (student_id == 'admin')
            new_user = User(
                full_name=student_id,   # placeholder — کاربر در پروفایل تکمیل می‌کند
                student_id=student_id,
                major=None,
                password_hash=hashed,
                is_admin=is_admin
            )
            db.session.add(new_user)
            db.session.commit()
            return new_user
        except Exception as e:
            db.session.rollback()
            raise e

    @staticmethod
    def authenticate_user(student_id, password):
        user = User.query.filter_by(student_id=student_id).first()
        if user and check_password_hash(user.password_hash, password):
            return user
        return None



# ==========================================
# Forms
# ==========================================

MAJOR_CHOICES = [
    ('', 'انتخاب کنید'),
    ('مهندسی کامپیوتر', 'مهندسی کامپیوتر'),
    ('علوم کامپیوتر', 'علوم کامپیوتر')
]


class RegistrationForm(FlaskForm):
    """
    فرم ثبت‌نام — فقط شماره دانشجویی و رمز عبور (کد ملی).
    نام و رشته تحصیلی در بخش ویرایش پروفایل تکمیل می‌شوند.
    """
    student_id = StringField('شماره دانشجویی', validators=[
        DataRequired(message='شماره دانشجویی الزامی است'),
        Length(min=10, max=10, message='شماره دانشجویی باید ۱۰ رقم باشد')
    ])
    password = PasswordField('کد ملی (رمز عبور)', validators=[
        DataRequired(message='رمز عبور الزامی است'),
        Length(min=10, max=10, message='رمز عبور باید ۱۰ رقم باشد')
    ])
    confirm_password = PasswordField('تکرار رمز عبور', validators=[
        DataRequired(),
        EqualTo('password', message='رمزهای عبور مطابقت ندارند')
    ])
    submit = SubmitField('ثبت‌نام')

    def validate_student_id(self, field):
        if User.query.filter_by(student_id=field.data).first():
            raise ValidationError('این شماره دانشجویی قبلاً ثبت شده است.')


class LoginForm(FlaskForm):
    student_id = StringField('شماره دانشجویی',
                             validators=[DataRequired(message='شماره دانشجویی الزامی است')])
    password = PasswordField('رمز عبور',
                             validators=[DataRequired(message='رمز عبور الزامی است')])
    submit = SubmitField('ورود')


# ==========================================
# Decorators
# ==========================================

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'current_user_id' not in session:
            flash('برای دسترسی به این صفحه ابتدا وارد شوید.', 'info')
            return redirect(url_for('show_auth_page'))
        return f(*args, **kwargs)
    return decorated_function


def admin_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('is_admin'):
            flash('دسترسی غیرمجاز. این صفحه فقط برای مدیران است.', 'error')
            return redirect(url_for('index'))
        return f(*args, **kwargs)
    return decorated_function


# ==========================================
# Context Processor
# ==========================================

@app.context_processor
def inject_user():
    user_id = session.get('current_user_id')
    user_name = session.get('current_user_name')
    user_pic = session.get('current_user_pic')
    is_admin = session.get('is_admin', False)
    if user_id and user_name:
        return dict(
            current_user={'id': user_id, 'name': user_name, 'pic': user_pic},
            current_user_id=user_id,
            is_admin=is_admin
        )
    return dict(current_user=None, current_user_id=None, is_admin=False)


@app.context_processor
def inject_schedule_slots():
    """تنها منبع حقیقتِ اسلات‌های شبکهٔ هفتگی برای همهٔ قالب‌ها (داشبورد + ادمین).

    ثابت‌ها در بخش کاتالوگ تعریف شده‌اند؛ اینجا فقط به قالب‌ها تزریق
    می‌شوند تا هیچ قالبی فهرست اسلات/روز را کپی نکند."""
    return {
        'schedule_slots': SCHEDULE_SLOTS,
        'schedule_slot_labels': [
            '%s - %s' % (en_digits_to_fa(s.split('-')[0]),
                         en_digits_to_fa(s.split('-')[1]))
            for s in SCHEDULE_SLOTS],
        'schedule_grid_days': SCHEDULE_GRID_DAYS,
        'schedule_day_names_fa': {d: DAY_FA[d] for d in SCHEDULE_GRID_DAYS},
        'schedule_all_day_names_fa': DAY_FA,
    }


# ==========================================
# Utilities
# ==========================================

def get_week_number():
    return now_tehran().isocalendar()[1]


def check_weekly_reset():
    try:
        setting = SystemSetting.query.get('last_reset_week')
        current_week = str(get_week_number())
        if not setting:
            setting = SystemSetting(key='last_reset_week', value=current_week)
            db.session.add(setting)
            db.session.commit()
            return
        if setting.value != current_week:
            Reservation.query.delete()
            setting.value = current_week
            db.session.commit()
    except Exception:
        db.session.rollback()


# ==========================================
# Error Handlers
# ==========================================

@app.errorhandler(404)
def not_found_error(e):
    if request.is_json or request.path.startswith('/api/'):
        return jsonify({'error': 'یافت نشد', 'code': 404}), 404
    return render_template('error.html', error_code=404,
                           error_msg='صفحه مورد نظر یافت نشد.'), 404


@app.errorhandler(500)
def internal_error(e):
    db.session.rollback()
    if request.is_json or request.path.startswith('/api/'):
        return jsonify({'error': 'خطای داخلی سرور', 'code': 500}), 500
    return render_template('error.html', error_code=500,
                           error_msg='خطای داخلی سرور. لطفاً دوباره تلاش کنید.'), 500


@app.errorhandler(403)
def forbidden_error(e):
    return render_template('error.html', error_code=403,
                           error_msg='دسترسی به این صفحه مجاز نیست.'), 403


# ==========================================
# Security Headers
# ==========================================

@app.after_request
def set_security_headers(response):
    response.headers['X-Content-Type-Options'] = 'nosniff'
    response.headers['X-Frame-Options'] = 'SAMEORIGIN'
    response.headers['X-XSS-Protection'] = '1; mode=block'
    response.headers['Referrer-Policy'] = 'strict-origin-when-cross-origin'
    response.headers['Content-Security-Policy'] = (
        "default-src 'self'; "
        "script-src 'self' 'unsafe-inline' https://cdn.socket.io https://fonts.googleapis.com; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
        "font-src 'self' https://fonts.gstatic.com; "
        "img-src 'self' https://sfile.chatglm.cn data: blob:; "
        "connect-src 'self' wss: ws:; "
        "frame-ancestors 'self'"
    )
    return response


# ==========================================
# Routes — General
# ==========================================

@app.route('/')
def index():
    check_weekly_reset()
    return render_template('index.html')


@app.route('/auth')
def show_auth_page():
    if session.get('current_user_id'):
        return redirect(url_for('dashboard'))
    return render_template('register.html', form=RegistrationForm(), login_form=LoginForm())


# ==========================================
# Routes — Auth
# ==========================================

@app.route('/register', methods=['POST'])
@limiter.limit("5 per minute")
def register():
    form = RegistrationForm()
    if form.validate_on_submit():
        try:
            user = AuthService.register_user(
                student_id=form.student_id.data,
                password=form.password.data
            )
            session['current_user_id'] = user.id
            session['current_user_name'] = user.full_name
            session['current_user_pic'] = user.profile_pic
            session['is_admin'] = user.is_admin
            flash('ثبت‌نام با موفقیت انجام شد. لطفاً نام و رشته تحصیلی خود را در پروفایل تکمیل کنید.', 'success')
            return redirect(url_for('dashboard'))
        except Exception as e:
            db.session.rollback()
            app.logger.error(f"register error: {e}")
            flash('خطا در ثبت‌نام. لطفاً دوباره تلاش کنید.', 'error')
    else:
        for field, errors in form.errors.items():
            for error in errors:
                flash(f'{error}', 'error')
    return render_template('register.html', form=form, login_form=LoginForm())


@app.route('/login', methods=['POST'])
@limiter.limit("10 per minute")
def login():
    login_form = LoginForm()
    if login_form.validate_on_submit():
        user = AuthService.authenticate_user(
            login_form.student_id.data, login_form.password.data
        )
        if user:
            session['current_user_id'] = user.id
            session['current_user_name'] = user.full_name
            session['current_user_pic'] = user.profile_pic
            session['is_admin'] = user.is_admin
            flash('با موفقیت وارد شدید. خوش آمدید!', 'success')
            return redirect(url_for('dashboard'))
        else:
            flash('شماره دانشجویی یا رمز عبور اشتباه است.', 'error')
    else:
        for field, errors in login_form.errors.items():
            for error in errors:
                flash(f'{error}', 'error')
    return render_template('register.html', form=RegistrationForm(), login_form=login_form)


@app.route('/logout')
@login_required
def logout():
    StateManager.set_offline(session.get('current_user_id'))
    session.clear()
    flash('با موفقیت از حساب کاربری خارج شدید.', 'info')
    return redirect(url_for('index'))


# ==========================================
# Routes — Dashboard
# ==========================================

@app.route('/api/now')
def api_now():
    """منبع واحد زمان برای کلاینت (Task 2).

    خروجی: epoch_ms، ISO با offset، تاریخ جلالی (سال/ماه/روز + نام ماه فارسی)،
    نام و ایندکس روز هفته، تاریخ میلادی، is_friday و وضعیت همگام‌سازی ساعت.
    """
    try:
        start_clock_sync()          # شروع (تک‌بار) همگام‌سازی پس‌زمینه — بدون انتظار
        now = now_tehran_aware()
        greg = now.date()
        jd = jdatetime.date.fromgregorian(date=greg)
        widx = jd.weekday()
        with _clock_lock:
            clock_info = dict(_clock_state)
        return jsonify({
            'epoch_ms': int(now.timestamp() * 1000),
            'iso': now.isoformat(timespec='milliseconds'),
            'gregorian': greg.isoformat(),
            'jalali': {'year': jd.year, 'month': jd.month, 'day': jd.day},
            'month_name': JALALI_MONTHS_FA[jd.month - 1],
            'date_text': jalali_text(jd),
            'weekday': WEEKDAYS_FA[widx],
            'weekday_index': widx,
            'is_friday': widx == 6,
            'clock': {
                'offset_ms': clock_info['offset_ms'],
                'drift_ms': clock_info['drift_ms'],
                'source': clock_info['source'],
                'last_sync': clock_info['last_sync'],
                'error': clock_info['error'],
            },
        })
    except Exception:
        app.logger.exception('/api/now failed')
        return jsonify({'error': 'خطا در دریافت زمان'}), 500


@app.route('/dashboard')
@login_required
def dashboard():
    check_weekly_reset()
    current_user_id = session['current_user_id']

    try:
        # لیست یکپارچهٔ JSON-safe: کلاس‌های شخصی + جلسات کاتالوگیِ ثبت‌نام‌شده
        # (خواندن زنده از کاتالوگ — بدون هیچ کشی تا ویرایش ادمین فوراً دیده شود)
        schedule_items = build_schedule_items(current_user_id)
        total_units = compute_total_units(current_user_id)
    except Exception:
        app.logger.exception('build_schedule_items failed (user=%s)',
                             current_user_id)
        schedule_items, total_units = [], 0.0

    try:
        _today_greg = now_tehran().date()
        today_j = jdatetime.date.fromgregorian(date=_today_greg)
        weekday_name = WEEKDAYS_FA[today_j.weekday()]
        today_gregorian = _today_greg
    except Exception:
        today_j = None
        weekday_name = ''
        today_gregorian = now_tehran().date()

    try:
        cancelled_today = CancelledClass.query.filter(
            or_(
                CancelledClass.cancel_date == today_gregorian,
                and_(
                    CancelledClass.start_date <= today_gregorian,
                    CancelledClass.end_date >= today_gregorian
                )
            )
        ).all()
    except Exception:
        cancelled_today = []

    try:
        all_cancelled = CancelledClass.query.order_by(CancelledClass.created_at.desc()).all()
    except Exception:
        all_cancelled = []

    try:
        all_cancelled_ids = [c.id for c in all_cancelled]
        if all_cancelled_ids:
            viewed_ids = [v.cancelled_class_id for v in
                          CancelledClassView.query.filter(
                              CancelledClassView.user_id == current_user_id,
                              CancelledClassView.cancelled_class_id.in_(all_cancelled_ids)
                          ).all()]
            unviewed_cancelled_count = len(set(all_cancelled_ids) - set(viewed_ids))
        else:
            unviewed_cancelled_count = 0
    except Exception:
        unviewed_cancelled_count = 0

    try:
        notifications = Notification.query.filter_by(
            user_id=current_user_id, is_read=False
        ).order_by(Notification.created_at.desc()).limit(5).all()
    except Exception:
        notifications = []

    return render_template(
        'dashboard.html',
        # باید dict باشد؛ خودِ شیء SQLAlchemy در فیلتر tojson با TypeError می‌شکند
        schedules=schedule_items,
        total_units=total_units,
        today_j=today_j,
        today_persian=(jalali_text(today_j) if today_j else ''),
        weekday_name=weekday_name,
        cancelled_classes=cancelled_today,
        all_cancelled_classes=all_cancelled,
        notifications=notifications,
        unviewed_cancelled_count=unviewed_cancelled_count
    )


VALID_DAYS = {'saturday', 'sunday', 'monday', 'tuesday', 'wednesday'}
VALID_WEEK_TYPES = {'all', 'odd', 'even'}
# گروه‌های دربرگیرنده لازم است تا ساعت شروع/پایان استخراج شود
_TIME_SLOT_RE = re.compile(r'^(\d{1,2})-(\d{1,2})$')


def _serialize_schedules(rows):
    """JSON-safe برای dashboard.html (شامل واحد درسی کلاس شخصی)."""
    return [
        {
            'id': s.id,
            'day': s.day,
            'time_slot': s.time_slot,
            'course_name': s.course_name,
            'class_location': s.class_location,
            'professor_name': s.professor_name,
            'week_type': s.week_type or 'all',
            'units': s.units,
        }
        for s in rows
    ]


@app.route('/update_schedule', methods=['POST'])
@login_required
def update_schedule():
    """افزودن/ویرایش/حذف یک کلاس برنامه هفتگی (نسخهٔ کامل از app/routes/dashboard.py).

    - اگر id ارسال شود، دقیقاً همان رکورد ویرایش (یا حذف) می‌شود.
    - در غیر این صورت، ورودی جدید بر اساس «روز + بازه + نوع هفته» جایگزین می‌شود:
      «هر هفته» با هر دو خانه فرد و زوج تداخل دارد، اما فرد و زوج مستقل‌اند.
    - واحد درسی اختیاری کلاس شخصی (units > 0 یا خالی/None).
    """
    data = request.get_json(silent=True) or {}
    user_id = session['current_user_id']

    day = data.get('day')
    time_slot = str(data.get('time_slot') or '').strip()
    week_type = data.get('week_type', 'all')
    course_name = str(data.get('course_name') or '').strip()
    record_id = data.get('id')

    if day not in VALID_DAYS:
        return jsonify({'status': 'error', 'message': 'روز انتخابی نامعتبر است.'}), 400
    if not _TIME_SLOT_RE.fullmatch(time_slot):
        return jsonify({'status': 'error', 'message': 'بازه ساعتی نامعتبر است.'}), 400
    if week_type not in VALID_WEEK_TYPES:
        return jsonify({'status': 'error', 'message': 'نوع هفته نامعتبر است.'}), 400

    # واحد اختیاری کلاس شخصی (Part B) — عدد >0 یا خالی/None
    units = data.get('units', None)
    if units is not None and str(units).strip() != '':
        try:
            units = float(str(units).translate(_FA_DIGITS))
        except (TypeError, ValueError):
            return jsonify({'status': 'error',
                            'message': 'واحد درسی باید عدد باشد'}), 400
        if units <= 0:
            return jsonify({'status': 'error',
                            'message': 'واحد درسی باید بزرگ‌تر از صفر باشد'}), 400
        units = round(units, 1)
    else:
        units = None

    try:
        # ── حالت ویرایش/حذف رکورد مشخص با شناسه ──
        if record_id is not None:
            try:
                row = db.session.get(ClassSchedule, int(record_id))
            except (TypeError, ValueError):
                row = None
            if not row or row.user_id != user_id:
                return jsonify({'status': 'error', 'message': 'کلاس مورد نظر یافت نشد.'}), 404

            if course_name == '':
                db.session.delete(row)
                db.session.commit()
                return jsonify({'status': 'success', 'id': None})

            if week_type != (row.week_type or 'all'):
                clash_types = ['all'] if week_type == 'all' else [week_type, 'all']
                clash = ClassSchedule.query.filter(
                    ClassSchedule.user_id == user_id,
                    ClassSchedule.day == day,
                    ClassSchedule.time_slot == time_slot,
                    ClassSchedule.id != row.id,
                    ClassSchedule.week_type.in_(clash_types)
                ).first()
                if clash:
                    return jsonify({
                        'status': 'error',
                        'message': 'این بازه برای این نوع هفته قبلاً پر شده است.'
                    }), 409

            row.day = day
            row.time_slot = time_slot
            row.week_type = week_type
            row.course_name = course_name
            row.class_location = str(data.get('class_location') or '').strip()
            row.professor_name = str(data.get('professor_name') or '').strip()
            row.units = units
            db.session.commit()
            return jsonify({'status': 'success', 'id': row.id})

        # ── حالت ایجاد/جایگزینی بر اساس نوع هفته ──
        if week_type == 'all':
            ClassSchedule.query.filter_by(
                user_id=user_id, day=day, time_slot=time_slot
            ).delete(synchronize_session=False)
        else:
            ClassSchedule.query.filter(
                ClassSchedule.user_id == user_id,
                ClassSchedule.day == day,
                ClassSchedule.time_slot == time_slot,
                ClassSchedule.week_type.in_([week_type, 'all'])
            ).delete(synchronize_session=False)

        new_id = None
        if course_name:
            row = ClassSchedule(
                user_id=user_id,
                day=day,
                time_slot=time_slot,
                course_name=course_name,
                class_location=str(data.get('class_location') or '').strip(),
                professor_name=str(data.get('professor_name') or '').strip(),
                week_type=week_type,
                units=units
            )
            db.session.add(row)
            db.session.flush()
            new_id = row.id
        db.session.commit()
        return jsonify({'status': 'success', 'id': new_id})

    except Exception as e:
        db.session.rollback()
        app.logger.exception("update_schedule failed")
        msg = str(e)
        if 'UNIQUE' in msg.upper():
            return jsonify({
                'status': 'error',
                'message': 'این بازه برای این نوع هفته قبلاً پر شده است.'
            }), 409
        return jsonify({'status': 'error', 'message': 'خطا در ذخیره‌سازی برنامه. لطفاً دوباره تلاش کنید.'}), 500

@app.route('/bulk_update_schedule', methods=['POST'])
@login_required
def bulk_update_schedule():
    """جایگزینی برنامه هفتگی از پِیست اکسل (نسخهٔ کامل از app/routes/dashboard.py).

    - هر ردیف جداگانه اعتبارسنجی می‌شود (روز، بازه ساعتی، نوع هفته، نام درس).
    - ارقام فارسی/عربی در بازه ساعتی پشتیبانی می‌شوند (۸-۱۰ → 8-10).
    - اگر هیچ ردیف معتبری نباشد، چیزی حذف نمی‌شود (برنامه فعلی دست‌نخورده می‌ماند).
    - خروجی: شمارش واردشده/ردشده + `skipped[]` (ردیف، دلیل) برای هر ردیف ردشده.
    """
    try:
        data = request.get_json(silent=True) or {}
        schedules = data.get('schedules')
        if not isinstance(schedules, list):
            return jsonify({'status': 'error', 'message': 'داده‌ای ارسال نشد.'}), 400
        user_id = session['current_user_id']

        cleaned = []
        skipped = []
        seen = set()
        for idx, item in enumerate(schedules, start=1):
            if not isinstance(item, dict):
                skipped.append({'row': idx, 'reason': 'ساختار ردیف نامعتبر است.'})
                continue
            day = str(item.get('day', '')).strip().lower()
            time_slot = fa_digits_to_en(item.get('time_slot', ''))
            course_name = str(item.get('course_name') or '').strip()
            week_type = str(item.get('week_type') or 'all').strip().lower()

            if not course_name:
                skipped.append({'row': idx, 'reason': 'نام درس خالی است.'})
                continue
            if day not in VALID_DAYS:
                skipped.append({'row': idx, 'reason': 'روز نامعتبر است (فقط شنبه تا چهارشنبه).'})
                continue
            m = _TIME_SLOT_RE.fullmatch(time_slot)
            if not m:
                skipped.append({'row': idx, 'reason': 'بازه ساعتی نامعتبر است (مثال: 8-10).'})
                continue
            start_h, end_h = int(m.group(1)), int(m.group(2))
            if not (0 <= start_h <= 23 and 1 <= end_h <= 24) or start_h >= end_h:
                skipped.append({'row': idx, 'reason': 'بازه ساعتی خارج از محدوده است.'})
                continue
            if week_type not in VALID_WEEK_TYPES:
                skipped.append({'row': idx, 'reason': 'نوع هفته نامعتبر است.'})
                continue
            key = (day, time_slot, week_type)
            if key in seen:
                skipped.append({'row': idx, 'reason': 'ردیف تکراری است.'})
                continue
            seen.add(key)
            units = item.get('units', None)
            if units is not None and str(units).strip() != '':
                try:
                    units = float(str(units).translate(_FA_DIGITS))
                except (TypeError, ValueError):
                    skipped.append({'row': idx, 'reason': 'واحد درسی باید عدد باشد.'})
                    continue
                if units <= 0:
                    skipped.append({'row': idx, 'reason': 'واحد درسی باید بزرگ‌تر از صفر باشد.'})
                    continue
                units = round(units, 1)
            else:
                units = None
            cleaned.append({
                'day': day,
                'time_slot': time_slot,
                'course_name': course_name,
                'class_location': str(item.get('class_location', '') or '').strip(),
                'professor_name': str(item.get('professor_name', '') or '').strip(),
                'week_type': week_type,
                'units': units,
            })

        if not cleaned:
            db.session.rollback()
            return jsonify({
                'status': 'error',
                'message': 'هیچ ردیف معتبری یافت نشد؛ برنامه فعلی شما تغییری نکرد.',
                'imported': 0,
                'skipped': skipped[:30],
                'skipped_count': len(skipped)
            }), 400

        ClassSchedule.query.filter_by(user_id=user_id).delete(synchronize_session=False)
        for row in cleaned:
            db.session.add(ClassSchedule(user_id=user_id, **row))
        db.session.commit()

        saved = ClassSchedule.query.filter_by(user_id=user_id).all()
        return jsonify({
            'status': 'success',
            'count': len(cleaned),
            'imported': len(cleaned),
            'skipped_count': len(skipped),
            'skipped': skipped[:30],
            'schedules': _serialize_schedules(saved)
        })
    except Exception:
        db.session.rollback()
        app.logger.exception("bulk_update_schedule failed")
        return jsonify({'status': 'error', 'message': 'خطا در ورود اطلاعات. لطفاً دوباره تلاش کنید.'}), 500


# ==========================================
# Routes — Schedule settings (Task 1)
# ==========================================

SEMESTER_START_KEY_PREFIX = 'semester_start_'


def _semester_payload(value):
    """مقدار متنی «اول ترم» (شمسی) → بار خوانایی برای کلاینت؛ نامعتبر → None."""
    if not value:
        return None
    try:
        parts = [int(x) for x in str(value).replace('-', '/').split('/')]
        if len(parts) != 3:
            raise ValueError(parts)
        js = jdatetime.date(parts[0], parts[1], parts[2])
        return {
            'jalali': '%04d/%02d/%02d' % (js.year, js.month, js.day),
            'gregorian': js.togregorian().isoformat(),
            'weekday_index': js.weekday(),
        }
    except Exception:
        return None


@app.route('/api/schedule_settings', methods=['GET', 'POST'])
@login_required
def schedule_settings():
    """
    تنظیم «اول ترم» (تاریخ شمسی) برای تشخیص هفتهٔ فرد/زوج در برنامهٔ هفتگی.
    GET  → {'semester_start': {jalali, gregorian, weekday_index} | None}
    POST → {'semester_start': '1405/07/01'} ذخیره؛ null یا رشتهٔ خالی = حذف.
    داده در system_setting (کلید per-user) — بدون تغییر اسکیما.
    """
    uid = session['current_user_id']
    key = SEMESTER_START_KEY_PREFIX + str(uid)

    if request.method == 'GET':
        row = db.session.get(SystemSetting, key)
        payload = {'semester_start': None, 'source': None}
        if row and row.value:
            payload['semester_start'] = _semester_payload(row.value)
            if payload['semester_start'] is None:
                app.logger.warning('bad semester_start for user %s: %r',
                                   uid, row.value)
        if payload['semester_start'] is None:
            # پیش‌فرض ترمِ تنظیم‌شده توسط ادمین (اختیاری — دانشجو می‌تواند override کند)
            drow = db.session.get(SystemSetting, CATALOG_TERM_START_KEY)
            if drow and drow.value:
                payload['semester_start'] = _semester_payload(drow.value)
                if payload['semester_start'] is not None:
                    payload['source'] = 'default'
        return jsonify(payload)

    data = request.get_json() or {}
    value = data.get('semester_start')
    if value in (None, ''):
        existing = db.session.get(SystemSetting, key)
        if existing is not None:
            try:
                db.session.delete(existing)
                db.session.commit()
            except Exception:
                db.session.rollback()
                return jsonify({'error': 'خطا در حذف تنظیم'}), 500
        return jsonify({'status': 'success', 'semester_start': None})

    value = str(value).strip().replace('-', '/')
    try:
        parts = [int(x) for x in value.split('/')]
        if len(parts) != 3:
            raise ValueError(parts)
        js = jdatetime.date(parts[0], parts[1], parts[2])
    except Exception:
        return jsonify({'error': 'تاریخ شمسی نامعتبر است (مثال: ۱۴۰۵/۰۷/۰۱)'}), 400
    if not (1300 <= js.year <= 1499):
        return jsonify({'error': 'سال شمسی باید بین ۱۳۰۰ تا ۱۴۹۹ باشد'}), 400

    try:
        row = db.session.get(SystemSetting, key)
        if row is None:
            row = SystemSetting(key=key, value='')
            db.session.add(row)
        row.value = '%04d/%02d/%02d' % (js.year, js.month, js.day)
        db.session.commit()
    except Exception:
        db.session.rollback()
        return jsonify({'error': 'خطا در ذخیره‌سازی'}), 500
    return jsonify({'status': 'success', 'semester_start': {
        'jalali': row.value,
        'gregorian': js.togregorian().isoformat(),
        'weekday_index': js.weekday(),
    }})


# ==========================================
# Routes — کاتالوگ دروس (Part B)
# «درس/گروه/جلسه» یک‌بار توسط ادمین ثبت می‌شود؛ برنامهٔ دانشجو فقط «مرجع»
# است. هر بار که داشبورد ساخته می‌شود، جلسات زنده از کاتالوگ خوانده
# می‌شوند ⇒ ویرایش ادمین بدون هیچ اقدام دانشجویی اعمال می‌شود (بی‌کش).
# ==========================================

# --- تنها منبع حقیقتِ اسلات‌های شبکهٔ هفتگی (قالب داشبورد + پنل ادمین + JS) ---
SCHEDULE_SLOTS = ['8-10', '10-12', '12-14', '14-16', '16-18', '18-20']
SCHEDULE_GRID_DAYS = ['saturday', 'sunday', 'monday', 'tuesday', 'wednesday']
DAY_KEYS_ALL = ['saturday', 'sunday', 'monday', 'tuesday', 'wednesday',
                'thursday', 'friday']
DAY_FA = {'saturday': 'شنبه', 'sunday': 'یکشنبه', 'monday': 'دوشنبه',
          'tuesday': 'سه‌شنبه', 'wednesday': 'چهارشنبه',
          'thursday': 'پنجشنبه', 'friday': 'جمعه'}
WEEK_TYPE_FA = {'all': 'هر هفته', 'odd': 'فرد', 'even': 'زوج'}

ACTIVE_TERM_KEY = 'catalog_active_term'
CATALOG_TERM_START_KEY = 'catalog_term_start'
CATALOG_IMPORT_HEADER = ['term', 'code', 'name', 'units', 'major', 'group',
                         'teacher', 'day', 'start', 'end', 'week', 'location']
CATALOG_IMPORT_MAX_ROWS = 5000
CATALOG_IMPORT_MAX_BYTES = 1024 * 1024


def _minutes(hhmm):
    h, m = str(hhmm).split(':')
    return int(h) * 60 + int(m)


def parse_day(raw):
    """نام روز (با/بدون ZWNJ، حروف عربی، ارقام فارسی) یا ایندکس ۰..۶ (شنبه=۰)."""
    s = normalize_fa(raw)
    if not s:
        return None
    if s in DAY_KEYS_ALL:
        return s
    if s.isdigit() and 0 <= int(s) < 7:
        return DAY_KEYS_ALL[int(s)]
    aliases = {normalize_fa(fa): key for key, fa in DAY_FA.items()}
    return aliases.get(s)


def parse_week_type(raw):
    """«هر هفته»/«فرد»/«زوج» (+ every/odd/even) → 'all'/'odd'/'even'؛ نامعتبر → None."""
    s = normalize_fa(raw)
    if s in ('', 'هر هفته', 'همه هفته', 'every', 'all', 'always'):
        return 'all'
    if s in ('فرد', 'odd'):
        return 'odd'
    if s in ('زوج', 'even'):
        return 'even'
    return None


def parse_hhmm(raw):
    """'HH:MM' ۲۴ ساعته (ارقام فارسی هم پذیرفته می‌شود) → 'HH:MM' صفر-پرشده."""
    s = fa_digits_to_en(raw).strip().replace('.', ':')
    m = re.match(r'^(\d{1,2}):(\d{2})$', s)
    if not m:
        return None
    h, mi = int(m.group(1)), int(m.group(2))
    if not (0 <= h <= 23 and 0 <= mi <= 59):
        return None
    return '%02d:%02d' % (h, mi)


def _slot_bounds(slot):
    """'8-10' → ('08:00','10:00')؛ اسلات سفارشیِ قابل‌تحلیل هم پذیرفته می‌شود."""
    m = re.match(r'^(\d{1,2})-(\d{1,2})$', str(slot or '').strip())
    if not m:
        return None, None
    return '%02d:00' % int(m.group(1)), '%02d:00' % int(m.group(2))


def slot_for_start(start_time):
    """اسلاتِ شبکه که «شروع» در آن می‌افتد (بدون row-span؛ ساعت دقیق روی کارت).

    جلسات بیرون از بازهٔ ۸..۲۰ در نزدیک‌ترین اسلاتِ لبه جا داده می‌شوند و
    out_of_grid=True برمی‌گردد تا در گزارش نهایی فهرست شوند.
    """
    t = _minutes(start_time)
    first_start, _ = _slot_bounds(SCHEDULE_SLOTS[0])
    if t < _minutes(first_start):
        return SCHEDULE_SLOTS[0], True
    for slot in SCHEDULE_SLOTS:
        a, b = slot.split('-')
        if _minutes('%s:00' % a) <= t < _minutes('%s:00' % b):
            return slot, False
    return SCHEDULE_SLOTS[-1], True


def meeting_exact_time(slot, start_time, end_time):
    """آیا ساعت جلسه با برچسب اسلاتِ شبکه یکسان نیست؟ (کارت باید ساعت دقیق نشان دهد)"""
    a, b = slot.split('-')
    return start_time != '%02d:00' % int(a) or end_time != '%02d:00' % int(b)


def _hm_fa(hhmm):
    """'10:00' → '۱۰'؛ '10:30' → '۱۰:۳۰' (برای پیام «درس در زمان ثبت‌شده...»)."""
    h, m = str(hhmm).split(':')
    return en_digits_to_fa(h) if m == '00' else en_digits_to_fa('%s:%s' % (h, m))


def _times_overlap(s1, e1, s2, e2):
    return _minutes(s1) < _minutes(e2) and _minutes(s2) < _minutes(e1)


def _weektypes_overlap(w1, w2):
    w1 = w1 or 'all'
    w2 = w2 or 'all'
    return w1 == 'all' or w2 == 'all' or w1 == w2


def get_active_term():
    row = db.session.get(SystemSetting, ACTIVE_TERM_KEY)
    return (row.value or '').strip() if row else ''


def _units_num(u):
    return None if u is None else float(u)


def _parse_units(raw, required=True):
    """(مقدار float گردشده، خطای فارسی)"""
    if raw is None or str(raw).strip() == '':
        return None, ('واحد درسی الزامی است' if required else None)
    try:
        val = float(fa_digits_to_en(raw))
    except (TypeError, ValueError):
        return None, 'واحد درسی باید عدد باشد'
    if val <= 0:
        return None, 'واحد درسی باید بزرگ‌تر از صفر باشد'
    if val > 30:
        return None, 'واحد درسی نامعتبر است (حداکثر ۳۰)'
    return round(val, 1), None


# --- سازندهٔ لیست یکپارچهٔ برنامهٔ دانشجو (JSON-safe — بدون ORM در tojson) ---

def build_schedule_items(user_id):
    """کلاس‌های شخصی + جلساتِ کاتالوگیِ ثبت‌نام‌شده — همه با کلیدهای یکسان.

    هر آیتم: kind ('custom'|'catalog'), id, enrollment_id, section_id, course_id,
    name, code, group, teacher, room, major, units, day, time_slot, start, end,
    exact_time, week_type, is_active + کلیدهای قدیمی برای سازگاری کلاینت
    (course_name, professor_name, class_location).
    """
    items = []
    for row in ClassSchedule.query.filter_by(user_id=user_id).all():
        start, end = _slot_bounds(row.time_slot)
        items.append({
            'kind': 'custom', 'id': row.id, 'enrollment_id': None,
            'section_id': None, 'course_id': None,
            'name': row.course_name or '', 'code': None, 'group': None,
            'teacher': row.professor_name or '', 'room': row.class_location or '',
            'major': None, 'units': row.units,
            'day': row.day, 'time_slot': row.time_slot,
            'start': start, 'end': end, 'exact_time': False,
            'week_type': row.week_type or 'all', 'is_active': True,
            # سازگاری با کد قدیمی کلاینت:
            'course_name': row.course_name or '',
            'professor_name': row.professor_name or '',
            'class_location': row.class_location or '',
        })
    active = get_active_term()
    if active:
        for enr in ScheduleEnrollment.query.filter_by(user_id=user_id).all():
            sec = enr.section
            if not sec or sec.term != active or not sec.course:
                continue
            course = sec.course
            for mtg in sec.meetings:
                if not mtg.is_active:
                    continue
                slot, _oog = slot_for_start(mtg.start_time)
                room = (mtg.location_override or sec.location or '')
                name = course.name
                items.append({
                    'kind': 'catalog', 'id': enr.id,
                    'enrollment_id': enr.id, 'section_id': sec.id,
                    'course_id': course.id,
                    'name': name, 'code': course.code,
                    'group': sec.group_number,
                    'teacher': sec.teacher or '', 'room': room,
                    'major': course.major,
                    'units': _units_num(course.units),
                    'day': mtg.day, 'time_slot': slot,
                    'start': mtg.start_time, 'end': mtg.end_time,
                    'exact_time': meeting_exact_time(slot, mtg.start_time, mtg.end_time),
                    'week_type': mtg.week_type or 'all',
                    'is_active': sec.is_active,
                    # سازگاری با کد قدیمی کلاینت:
                    'course_name': name,
                    'professor_name': sec.teacher or '',
                    'class_location': room,
                })
    return items


def compute_total_units(user_id):
    """مجموع واحدها: هر درسِ کاتالوگیِ فعال یک‌بار + کلاس‌های شخصیِ دارای واحد.
    گروه‌های حذف‌شدهٔ نرم (is_active=False) نادیده گرفته می‌شوند."""
    total = 0.0
    active = get_active_term()
    seen_courses = set()
    if active:
        for enr in ScheduleEnrollment.query.filter_by(user_id=user_id).all():
            sec = enr.section
            if not sec or sec.term != active or not sec.is_active or not sec.course:
                continue
            if sec.course_id in seen_courses:
                continue
            seen_courses.add(sec.course_id)
            total += float(sec.course.units or 0)
    for row in ClassSchedule.query.filter_by(user_id=user_id).all():
        if row.units:
            total += float(row.units)
    return round(total, 1)


# --- اطلاعیه + رویداد Socket.IO برای تغییرات کاتالوگ (Part B7) ---

def _queue_catalog_notifications(pairs):
    """pairs: [(user_id, متن)] — ردیف‌های Notification را به تراکنش فعلی می‌افزاید."""
    for uid, msg in set(pairs):
        db.session.add(Notification(user_id=uid, message=msg))


def _emit_catalog_updated(user_ids):
    """فقط پس از commit — به اتاق اختصاصی user_<id> (مکانیزم موجود در connect)."""
    for uid in set(user_ids):
        try:
            socketio.emit('catalog_updated', {'reason': 'catalog'},
                          room='user_%d' % uid)
        except Exception:
            app.logger.warning('catalog_updated emit failed (user=%s)', uid)


def _enrolled_user_ids(section_ids):
    if not section_ids:
        return []
    rows = ScheduleEnrollment.query.filter(
        ScheduleEnrollment.section_id.in_(section_ids)).all()
    return sorted({r.user_id for r in rows})


# --- هشدارهای غیربلوکهٔ ادمین (استاد/مکان هم‌پوشان در گروه دیگر) ---

def _section_save_warnings(section_id, day, start, end, week_type,
                           teacher, room, term):
    warnings = []
    teacher_n = normalize_fa(teacher)
    room_n = normalize_fa(room)
    if not teacher_n and not room_n:
        return warnings
    others = CourseSection.query.filter(
        CourseSection.term == term,
        CourseSection.is_active.is_(True))
    if section_id:
        others = others.filter(CourseSection.id != section_id)
    for sec in others.all():
        for mtg in sec.meetings:
            if not mtg.is_active or mtg.day != day:
                continue
            if not _weektypes_overlap(mtg.week_type, week_type):
                continue
            if not _times_overlap(mtg.start_time, mtg.end_time, start, end):
                continue
            when = '%s %s تا %s' % (DAY_FA.get(mtg.day, mtg.day),
                                    _hm_fa(mtg.start_time), _hm_fa(mtg.end_time))
            cname = sec.course.name if sec.course else '—'
            if teacher_n and normalize_fa(sec.teacher) == teacher_n:
                warnings.append('استاد «%s» در همان بازه گروه %d درس «%s» (%s) کلاس دارد.'
                                % (sec.teacher, sec.group_number, cname, when))
            eff_room = normalize_fa(mtg.location_override or sec.location)
            if room_n and eff_room == room_n:
                warnings.append('مکان «%s» در همان بازه گروه %d درس «%s» (%s) رزرو است.'
                                % (room, sec.group_number, cname, when))
    return warnings


# --- سریالایزرهای JSON ---

def _course_dict(c):
    return {'id': c.id, 'code': c.code, 'name': c.name,
            'units': _units_num(c.units), 'major': c.major or ''}


def _meeting_dict(mtg):
    slot, oog = slot_for_start(mtg.start_time)
    return {
        'id': mtg.id, 'day': mtg.day, 'day_fa': DAY_FA.get(mtg.day, mtg.day),
        'start_time': mtg.start_time, 'end_time': mtg.end_time,
        'week_type': mtg.week_type or 'all',
        'week_fa': WEEK_TYPE_FA.get(mtg.week_type or 'all', 'هر هفته'),
        'location_override': mtg.location_override or '',
        'is_active': mtg.is_active, 'slot': slot, 'out_of_grid': oog,
        'exact_time': meeting_exact_time(slot, mtg.start_time, mtg.end_time),
    }


def _section_dict(sec, enrolled_count=None):
    d = {
        'id': sec.id, 'course_id': sec.course_id, 'term': sec.term,
        'group_number': sec.group_number, 'teacher': sec.teacher or '',
        'location': sec.location or '', 'is_active': sec.is_active,
        'updated_at': sec.updated_at.strftime('%Y-%m-%d %H:%M') if sec.updated_at else '',
        'meetings': [_meeting_dict(m) for m in sec.meetings if m.is_active],
        'meetings_all': [_meeting_dict(m) for m in sec.meetings],
    }
    if enrolled_count is not None:
        d['enrolled_count'] = enrolled_count
    if sec.course:
        d['course'] = _course_dict(sec.course)
    return d


# ------------------------------------------
# B1 — پنل ادمین: مدیریت دروس و گروه‌ها
# همه POST/PUT/DELETE هستند؛ CSRF با هدر X-CSRFToken (csrfFetch) و
# admin_required روی هر مسیر (فلش+ریدایرکت برای غیرادمین).
# ------------------------------------------

@app.route('/api/admin/catalog/list')
@admin_required
def admin_catalog_list():
    """فهرست دروس + گروه‌ها + جلسات + تعداد ثبت‌نام هر گروه (اسکیم صفحه)."""
    q = normalize_fa(request.args.get('q', ''))
    term = (request.args.get('term', '') or '').strip()
    major = canon_fa((request.args.get('major', '') or '').strip())
    page = max(1, request.args.get('page', 1, type=int) or 1)
    per_page = min(50, max(5, request.args.get('per_page', 10, type=int) or 10))
    include_inactive = request.args.get('include_inactive') in ('1', 'true', 'yes')
    try:
        qry = CatalogCourse.query
        if term:
            qry = qry.join(CourseSection).filter(CourseSection.term == term)
        if q:
            like = '%' + q + '%'
            code_like = '%' + fa_digits_to_en(q) + '%'
            qry = qry.filter(or_(CatalogCourse.name_norm.like(like),
                                 CatalogCourse.code.like(code_like)))
        if major:
            qry = qry.filter(CatalogCourse.major == major)
        qry = qry.order_by(CatalogCourse.name)
        total = qry.distinct().count()
        courses = (qry.distinct()
                       .offset((page - 1) * per_page)
                       .limit(per_page).all())
        counts = dict(db.session.query(
            ScheduleEnrollment.section_id, func.count(ScheduleEnrollment.id)
        ).group_by(ScheduleEnrollment.section_id).all())
        majors = sorted({m for (m,) in db.session.query(CatalogCourse.major)
                         .distinct().all() if m})
        terms = sorted({t for (t,) in db.session.query(CourseSection.term)
                        .distinct().all() if t})
        out = []
        for c in courses:
            secs = []
            for s in c.sections:
                if term and s.term != term:
                    continue
                if not include_inactive and not s.is_active:
                    continue
                secs.append(_section_dict(s, enrolled_count=counts.get(s.id, 0)))
            out.append({
                'course': _course_dict(c), 'sections': secs,
                'enrolled_total': sum(counts.get(s.id, 0)
                                      for s in c.sections if s.is_active),
            })
        tsrow = db.session.get(SystemSetting, CATALOG_TERM_START_KEY)
        return jsonify({
            'courses': out, 'page': page, 'per_page': per_page, 'total': total,
            'majors': majors, 'terms': terms,
            'settings': {'active_term': get_active_term(),
                         'term_start': (tsrow.value if tsrow else None)},
        })
    except Exception:
        app.logger.exception('admin_catalog_list failed')
        return jsonify({'error': 'خطا در خواندن کاتالوگ دروس'}), 500


@app.route('/api/admin/catalog/courses', methods=['POST'])
@admin_required
def admin_catalog_create_course():
    data = request.get_json(silent=True) or {}
    code = str(data.get('code', '')).strip()
    name = canon_fa(str(data.get('name', '')).strip())
    major = canon_fa(str(data.get('major', '')).strip())
    if not code:
        return jsonify({'error': 'کد درسی الزامی است'}), 400
    if not re.match(r'^[0-9A-Za-z_\-]{1,20}$', code):
        return jsonify({'error': 'کد درسی نامعتبر است (فقط حروف/اعداد و - یا _)'}), 400
    if not name:
        return jsonify({'error': 'نام درس الزامی است'}), 400
    units, err = _parse_units(data.get('units'))
    if err:
        return jsonify({'error': err}), 400
    try:
        existing = CatalogCourse.query.filter_by(code=code).first()
        if existing:
            return jsonify({'error': 'درسی با این کد درسی قبلاً ثبت شده است؛ '
                                     'همان درس را باز کنید و گروه اضافه کنید',
                            'existing': _course_dict(existing)}), 409
        course = CatalogCourse(code=code, name=name, name_norm=normalize_fa(name),
                               units=units, major=major or None)
        db.session.add(course)
        db.session.commit()
        return jsonify({'status': 'success', 'course': _course_dict(course)}), 201
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_create_course failed')
        return jsonify({'error': 'خطا در ذخیرهٔ درس'}), 500


@app.route('/api/admin/catalog/courses/<int:course_id>', methods=['PUT'])
@admin_required
def admin_catalog_update_course(course_id):
    course = db.session.get(CatalogCourse, course_id)
    if not course:
        return jsonify({'error': 'درس یافت نشد'}), 404
    data = request.get_json(silent=True) or {}
    try:
        if 'code' in data:
            code = str(data['code']).strip()
            if not re.match(r'^[0-9A-Za-z_\-]{1,20}$', code):
                return jsonify({'error': 'کد درسی نامعتبر است'}), 400
            clash = CatalogCourse.query.filter(
                CatalogCourse.code == code,
                CatalogCourse.id != course_id).first()
            if clash:
                return jsonify({'error': 'درس دیگری با این کد درسی وجود دارد'}), 409
            course.code = code
        if 'name' in data:
            name = canon_fa(str(data['name']).strip())
            if not name:
                return jsonify({'error': 'نام درس نمی‌تواند خالی باشد'}), 400
            course.name = name
            course.name_norm = normalize_fa(name)
        if 'units' in data and data['units'] not in (None, ''):
            units, err = _parse_units(data['units'])
            if err:
                return jsonify({'error': err}), 400
            course.units = units
        if 'major' in data:
            course.major = canon_fa(str(data['major']).strip()) or None
        db.session.commit()
        return jsonify({'status': 'success', 'course': _course_dict(course)})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_update_course failed')
        return jsonify({'error': 'خطا در ویرایش درس'}), 500


@app.route('/api/admin/catalog/courses/<int:course_id>/delete', methods=['POST'])
@admin_required
def admin_catalog_delete_course(course_id):
    course = db.session.get(CatalogCourse, course_id)
    if not course:
        return jsonify({'error': 'درس یافت نشد'}), 404
    data = request.get_json(silent=True) or {}
    soft = bool(data.get('soft'))
    try:
        sec_ids = [s.id for s in CourseSection.query.filter_by(
            course_id=course_id).all()]
        affected = _enrolled_user_ids(sec_ids)
        if affected and not soft:
            return jsonify({'error': 'این درس برای %d دانشجو ثبت‌نام شده است؛ '
                                     'حذف نرم انجام می‌شود. تأیید کنید.'
                                     % len(affected),
                            'confirm_required': True,
                            'affected': len(affected)}), 409
        if affected:
            for s in CourseSection.query.filter_by(course_id=course_id).all():
                s.is_active = False
            _queue_catalog_notifications([
                (uid, 'درس «%s» (کد %s) توسط مدیریت از کاتالوگ حذف شد؛ لطفاً گروه جدید انتخاب کنید.'
                 % (course.name, course.code)) for uid in affected])
            db.session.commit()
            _emit_catalog_updated(affected)
            return jsonify({'status': 'success', 'soft': True,
                            'affected': len(affected)})
        db.session.delete(course)   # cascade: گروه‌ها و جلسات
        db.session.commit()
        return jsonify({'status': 'success', 'soft': False, 'affected': 0})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_delete_course failed')
        return jsonify({'error': 'خطا در حذف درس'}), 500


@app.route('/api/admin/catalog/sections', methods=['POST'])
@admin_required
def admin_catalog_create_section():
    data = request.get_json(silent=True) or {}
    try:
        course = db.session.get(CatalogCourse, int(data.get('course_id') or 0))
    except (TypeError, ValueError):
        course = None
    if not course:
        return jsonify({'error': 'درس یافت نشد'}), 404
    term = str(data.get('term', '') or '').strip()
    if not term:
        term = get_active_term()
    if not term or len(term) > 10:
        return jsonify({'error': 'ترم را وارد کنید (حداکثر ۱۰ نویسه)'}), 400
    try:
        group_number = int(fa_digits_to_en(data.get('group_number')))
    except (TypeError, ValueError):
        group_number = 0
    if group_number < 1:
        return jsonify({'error': 'شمارهٔ گروه باید عددی صحیح و بزرگ‌تر از صفر باشد'}), 400
    teacher = canon_fa(str(data.get('teacher', '') or '').strip())
    location = canon_fa(str(data.get('location', '') or '').strip())
    try:
        clash = CourseSection.query.filter_by(
            course_id=course.id, term=term, group_number=group_number).first()
        if clash:
            return jsonify({'error': 'گروه %d این درس در ترم %s قبلاً ثبت شده است'
                                     % (group_number, term)}), 409
        section = CourseSection(course_id=course.id, term=term,
                                group_number=group_number, teacher=teacher,
                                location=location)
        db.session.add(section)
        db.session.commit()
        return jsonify({'status': 'success',
                        'section': _section_dict(section, enrolled_count=0)}), 201
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_create_section failed')
        return jsonify({'error': 'خطا در ذخیرهٔ گروه'}), 500


@app.route('/api/admin/catalog/sections/<int:section_id>', methods=['PUT'])
@admin_required
def admin_catalog_update_section(section_id):
    section = db.session.get(CourseSection, section_id)
    if not section:
        return jsonify({'error': 'گروه یافت نشد'}), 404
    data = request.get_json(silent=True) or {}
    try:
        old_snapshot = (section.teacher, section.location, section.term,
                        section.group_number)
        if 'teacher' in data:
            section.teacher = canon_fa(str(data['teacher'] or '').strip())
        if 'location' in data:
            section.location = canon_fa(str(data['location'] or '').strip())
        if 'term' in data:
            term = str(data['term'] or '').strip()
            if not term or len(term) > 10:
                return jsonify({'error': 'ترم نامعتبر است'}), 400
            section.term = term
        if 'group_number' in data:
            try:
                gn = int(fa_digits_to_en(data['group_number']))
            except (TypeError, ValueError):
                gn = 0
            if gn < 1:
                return jsonify({'error': 'شمارهٔ گروه باید عددی صحیح و بزرگ‌تر از صفر باشد'}), 400
            section.group_number = gn
        if 'is_active' in data:
            section.is_active = bool(data['is_active'])
        clash = CourseSection.query.filter(
            CourseSection.course_id == section.course_id,
            CourseSection.term == section.term,
            CourseSection.group_number == section.group_number,
            CourseSection.id != section.id).first()
        if clash:
            db.session.rollback()   # ویرایش‌های انجام‌شده در جلسه باید برگردد
            return jsonify({'error': 'گروه %d این درس در ترم %s قبلاً ثبت شده است'
                                     % (section.group_number, section.term)}), 409
        db.session.commit()
        changed = (section.teacher, section.location, section.term,
                   section.group_number) != old_snapshot
        if changed:
            affected = _enrolled_user_ids([section.id])
            if affected:
                _queue_catalog_notifications([
                    (uid, 'گروه %d درس «%s» توسط مدیریت ویرایش شد؛ برنامهٔ خود را بررسی کنید.'
                     % (section.group_number,
                        section.course.name if section.course else '—'))
                    for uid in affected])
                db.session.commit()
                _emit_catalog_updated(affected)
        return jsonify({'status': 'success',
                        'section': _section_dict(section),
                        'enrolled': len(_enrolled_user_ids([section.id]))})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_update_section failed')
        return jsonify({'error': 'خطا در ویرایش گروه'}), 500


@app.route('/api/admin/catalog/sections/<int:section_id>/delete', methods=['POST'])
@admin_required
def admin_catalog_delete_section(section_id):
    section = db.session.get(CourseSection, section_id)
    if not section:
        return jsonify({'error': 'گروه یافت نشد'}), 404
    data = request.get_json(silent=True) or {}
    soft = bool(data.get('soft'))
    try:
        affected = _enrolled_user_ids([section.id])
        if affected and not soft:
            return jsonify({'error': 'این گروه برای %d دانشجو ثبت‌نام شده است؛ '
                                     'حذف نرم انجام می‌شود. تأیید کنید.'
                                     % len(affected),
                            'confirm_required': True,
                            'affected': len(affected)}), 409
        if affected:
            section.is_active = False
            _queue_catalog_notifications([
                (uid, 'گروه %d درس «%s» توسط مدیریت حذف شد؛ لطفاً گروه جدید انتخاب کنید.'
                 % (section.group_number,
                    section.course.name if section.course else '—'))
                for uid in affected])
            db.session.commit()
            _emit_catalog_updated(affected)
            return jsonify({'status': 'success', 'soft': True,
                            'affected': len(affected)})
        db.session.delete(section)   # cascade: جلسات
        db.session.commit()
        return jsonify({'status': 'success', 'soft': False, 'affected': 0})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_delete_section failed')
        return jsonify({'error': 'خطا در حذف گروه'}), 500


def _parse_meeting_payload(data):
    """(payload_stud, خطای فارسی یا None)"""
    day = parse_day(data.get('day'))
    if not day:
        return None, 'روز نامعتبر است (شنبه تا جمعه یا ایندکس ۰ تا ۶)'
    start = parse_hhmm(data.get('start_time', data.get('start')))
    end = parse_hhmm(data.get('end_time', data.get('end')))
    if not start or not end:
        return None, 'ساعت شروع و پایان باید به صورت HH:MM باشد'
    if _minutes(start) >= _minutes(end):
        return None, 'ساعت شروع باید قبل از ساعت پایان باشد'
    week = parse_week_type(data.get('week_type', 'all'))
    if week is None:
        return None, 'نوع هفته نامعتبر است (هر هفته / فرد / زوج)'
    location = canon_fa(str(data.get('location_override',
                                     data.get('location', '')) or '').strip())
    return {'day': day, 'start_time': start, 'end_time': end,
            'week_type': week, 'location': location}, None


def _notify_section_students(section, verb):
    """اطلاعیه به همهٔ ثبت‌نام‌شدگانِ این گروه (داخل تراکنش جاری)."""
    affected = _enrolled_user_ids([section.id])
    if affected:
        _queue_catalog_notifications([
            (uid, ('برنامهٔ گروه %d درس «%s» %s؛ لطفاً برنامهٔ خود را بررسی کنید.'
                   % (section.group_number,
                      section.course.name if section.course else '—', verb)))
            for uid in affected])
    return affected


@app.route('/api/admin/catalog/warnings', methods=['POST'])
@admin_required
def admin_catalog_warnings():
    """پیش‌نمایش هشدارهای هم‌پوشانی استاد/مکان (بدون ذخیره — تأیید اختیاری ادمین)."""
    data = request.get_json(silent=True) or {}
    try:
        section = db.session.get(CourseSection, int(data.get('section_id') or 0))
    except (TypeError, ValueError):
        section = None
    if not section:
        return jsonify({'error': 'گروه یافت نشد'}), 404
    parsed, err = _parse_meeting_payload(data)
    if err:
        return jsonify({'error': err}), 400
    return jsonify({'warnings': _section_save_warnings(
        section.id, parsed['day'], parsed['start_time'], parsed['end_time'],
        parsed['week_type'], section.teacher,
        parsed['location'] or section.location, section.term)})


@app.route('/api/admin/catalog/meetings', methods=['POST'])
@admin_required
def admin_catalog_create_meeting():
    data = request.get_json(silent=True) or {}
    try:
        section = db.session.get(CourseSection, int(data.get('section_id') or 0))
    except (TypeError, ValueError):
        section = None
    if not section:
        return jsonify({'error': 'گروه یافت نشد'}), 404
    parsed, err = _parse_meeting_payload(data)
    if err:
        return jsonify({'error': err}), 400
    try:
        warnings = _section_save_warnings(
            section.id, parsed['day'], parsed['start_time'], parsed['end_time'],
            parsed['week_type'], section.teacher,
            parsed['location'] or section.location, section.term)
        if warnings and not data.get('acknowledge_warnings'):
            return jsonify({'error': 'هشدار تداخل؛ برای ادامه تأیید کنید',
                            'warning_required': True,
                            'warnings': warnings}), 409
        mtg = SectionMeeting(section_id=section.id, day=parsed['day'],
                             start_time=parsed['start_time'],
                             end_time=parsed['end_time'],
                             week_type=parsed['week_type'],
                             location_override=parsed['location'] or None)
        db.session.add(mtg)
        affected = _notify_section_students(section, 'جلسهٔ جدید گرفت')
        db.session.commit()
        _emit_catalog_updated(affected)
        return jsonify({'status': 'success', 'meeting': _meeting_dict(mtg)}), 201
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_create_meeting failed')
        return jsonify({'error': 'خطا در ذخیرهٔ جلسه'}), 500


@app.route('/api/admin/catalog/meetings/<int:meeting_id>', methods=['PUT'])
@admin_required
def admin_catalog_update_meeting(meeting_id):
    mtg = db.session.get(SectionMeeting, meeting_id)
    if not mtg:
        return jsonify({'error': 'جلسه یافت نشد'}), 404
    section = mtg.section
    data = request.get_json(silent=True) or {}
    parsed, err = _parse_meeting_payload(data)
    if err:
        return jsonify({'error': err}), 400
    try:
        warnings = _section_save_warnings(
            section.id, parsed['day'], parsed['start_time'], parsed['end_time'],
            parsed['week_type'], section.teacher,
            parsed['location'] or section.location, section.term)
        if warnings and not data.get('acknowledge_warnings'):
            return jsonify({'error': 'هشدار تداخل؛ برای ادامه تأیید کنید',
                            'warning_required': True,
                            'warnings': warnings}), 409
        changed = (mtg.day != parsed['day'] or
                   mtg.start_time != parsed['start_time'] or
                   mtg.end_time != parsed['end_time'] or
                   (mtg.week_type or 'all') != parsed['week_type'] or
                   (mtg.location_override or '') != parsed['location'])
        if 'is_active' in data:
            mtg.is_active = bool(data['is_active'])
        mtg.day = parsed['day']
        mtg.start_time = parsed['start_time']
        mtg.end_time = parsed['end_time']
        mtg.week_type = parsed['week_type']
        mtg.location_override = parsed['location'] or None
        affected = _notify_section_students(section, 'تغییر ساعت/روز پیدا کرد') if changed else []
        db.session.commit()
        _emit_catalog_updated(affected)
        return jsonify({'status': 'success', 'meeting': _meeting_dict(mtg)})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_update_meeting failed')
        return jsonify({'error': 'خطا در ویرایش جلسه'}), 500


@app.route('/api/admin/catalog/meetings/<int:meeting_id>/delete', methods=['POST'])
@admin_required
def admin_catalog_delete_meeting(meeting_id):
    mtg = db.session.get(SectionMeeting, meeting_id)
    if not mtg:
        return jsonify({'error': 'جلسه یافت نشد'}), 404
    section = mtg.section
    data = request.get_json(silent=True) or {}
    soft = bool(data.get('soft'))
    try:
        affected = _enrolled_user_ids([section.id])
        if affected and not soft:
            return jsonify({'error': 'این جلسه برای %d دانشجو ثبت‌نام شده است؛ '
                                     'حذف نرم انجام می‌شود. تأیید کنید.'
                                     % len(affected),
                            'confirm_required': True,
                            'affected': len(affected)}), 409
        if affected:
            mtg.is_active = False
            _notify_section_students(section, 'یک جلسه حذف شد')
        else:
            db.session.delete(mtg)
        db.session.commit()
        _emit_catalog_updated(affected)
        return jsonify({'status': 'success', 'soft': bool(affected),
                        'affected': len(affected)})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_delete_meeting failed')
        return jsonify({'error': 'خطا در حذف جلسه'}), 500


@app.route('/api/admin/catalog/active-term', methods=['POST'])
@admin_required
def admin_catalog_active_term():
    data = request.get_json(silent=True) or {}
    term = str(data.get('term', '') or '').strip()
    if term and not re.match(r'^[0-9A-Za-z_\-]{1,10}$', term):
        return jsonify({'error': 'کد ترم نامعتبر است (حداکثر ۱۰ نویسه)'}), 400
    try:
        row = db.session.get(SystemSetting, ACTIVE_TERM_KEY)
        if row is None:
            row = SystemSetting(key=ACTIVE_TERM_KEY, value='')
            db.session.add(row)
        row.value = term
        db.session.commit()
        return jsonify({'status': 'success', 'active_term': term})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_active_term failed')
        return jsonify({'error': 'خطا در ذخیرهٔ ترم فعال'}), 500


@app.route('/api/admin/catalog/term-start', methods=['POST'])
@admin_required
def admin_catalog_term_start():
    """تاریخ شروع ترم به‌عنوان پیش‌فرض «اول ترم» دانشجویان (Override شخصی مقدم است)."""
    data = request.get_json(silent=True) or {}
    value = str(data.get('jalali', '') or '').strip().replace('-', '/')
    if value:
        parsed = _semester_payload(value)
        if parsed is None:
            return jsonify({'error': 'تاریخ شمسی نامعتبر است (مثال: ۱۴۰۵/۰۷/۰۱)'}), 400
        value = parsed['jalali']
    try:
        row = db.session.get(SystemSetting, CATALOG_TERM_START_KEY)
        if row is None:
            row = SystemSetting(key=CATALOG_TERM_START_KEY, value='')
            db.session.add(row)
        row.value = value
        db.session.commit()
        return jsonify({'status': 'success', 'term_start': value or None})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_term_start failed')
        return jsonify({'error': 'خطا در ذخیرهٔ تاریخ شروع ترم'}), 500


# ------------------------------------------
# B2 — درون‌ریزی/برون‌بری متن استاندارد (لول به لول = یک جلسه)
# ------------------------------------------

def _decode_import_bytes(raw):
    """utf-8 (با/بدون BOM)؛ در صورت شکست cp1256 — کدگذاریِ استفاده‌شده گزارش می‌شود."""
    if raw.startswith(b'\xef\xbb\xbf'):
        try:
            return raw.decode('utf-8-sig'), 'utf-8-sig'
        except UnicodeDecodeError:
            pass
    try:
        return raw.decode('utf-8'), 'utf-8'
    except UnicodeDecodeError:
        pass
    try:
        return raw.decode('cp1256'), 'cp1256'
    except UnicodeDecodeError:
        return raw.decode('utf-8', errors='replace'), 'utf-8 (replace)'


def _detect_delimiter(header_line):
    """'|' پیش‌فرض؛ فقط وقتی هدر با TAB یا کاما منطبق باشد عوض می‌شود."""
    stripped = header_line.strip().lstrip('#').strip()
    if '\t' in stripped:
        if [c.strip().lower() for c in stripped.split('\t')] == CATALOG_IMPORT_HEADER:
            return '\t'
    if ',' in stripped:
        if [c.strip().lower() for c in stripped.split(',')] == CATALOG_IMPORT_HEADER:
            return ','
    return '|'


def _parse_catalog_text(text, active_term):
    """(rows | None, errors, delimiter, header_ok) — شمارهٔ خطا = خط فیزیکی فایل."""
    errors = []
    rows = []
    delimiter = '|'
    header_seen = False
    lines = text.replace('\r\n', '\n').replace('\r', '\n').split('\n')
    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith('#'):
            continue
        if not header_seen:
            delimiter = _detect_delimiter(stripped)
            cells = [c.strip().lower() for c in stripped.split(delimiter)]
            if cells != CATALOG_IMPORT_HEADER:
                return None, [{'line': idx,
                               'reason': 'ردیف هدر نامعتبر است؛ انتظار دقیقاً: '
                                         + '|'.join(CATALOG_IMPORT_HEADER)}], delimiter, False
            header_seen = True
            continue
        cells = [c.strip() for c in stripped.split(delimiter)]
        if len(cells) != len(CATALOG_IMPORT_HEADER):
            errors.append({'line': idx, 'reason': 'تعداد ستون‌ها نادرست است (%d به‌جای %d)'
                                                  % (len(cells), len(CATALOG_IMPORT_HEADER))})
            continue
        row = dict(zip(CATALOG_IMPORT_HEADER, cells))
        term = row['term'].strip() or active_term
        code = row['code'].strip()
        name = canon_fa(row['name'].strip())
        major = canon_fa(row['major'].strip())
        bad = None
        if not term:
            bad = 'ترم خالی است و ترم فعالی هم تعیین نشده است'
        elif len(term) > 10:
            bad = 'ترم بیش از ۱۰ نویسه دارد'
        elif not code:
            bad = 'کد درسی خالی است'
        elif not re.match(r'^[0-9A-Za-z_\-]{1,20}$', code):
            bad = 'کد درسی نامعتبر است'
        elif not name:
            bad = 'نام درس خالی است'
        units = None
        if bad is None:
            units, uerr = _parse_units(row['units'])
            if uerr:
                bad = uerr
        try:
            group = int(fa_digits_to_en(row['group']))
        except ValueError:
            group = 0
        if bad is None and group < 1:
            bad = 'شمارهٔ گروه باید عددی صحیح و بزرگ‌تر از صفر باشد'
        teacher = canon_fa(row['teacher'].strip())
        day = parse_day(row['day'])
        if bad is None and not day:
            bad = 'روز نامعتبر است (شنبه تا جمعه یا ایندکس ۰ تا ۶)'
        start = parse_hhmm(row['start'])
        end = parse_hhmm(row['end'])
        if bad is None and (not start or not end):
            bad = 'ساعت شروع/پایان باید HH:MM باشد'
        if bad is None and _minutes(start) >= _minutes(end):
            bad = 'ساعت شروع باید قبل از پایان باشد'
        week = parse_week_type(row['week'])
        if bad is None and week is None:
            bad = 'نوع هفته نامعتبر است (هر هفته / فرد / زوج)'
        if bad:
            errors.append({'line': idx, 'reason': bad})
            continue
        rows.append({'line': idx, 'term': term, 'code': code, 'name': name,
                     'units': units, 'major': major, 'group': group,
                     'teacher': teacher, 'day': day, 'start': start, 'end': end,
                     'week': week,
                     'location': canon_fa(row['location'].strip())})
    if not header_seen:
        return None, [{'line': 1, 'reason': 'هدر یافت نشد؛ فایل باید ردیف هدر '
                                            + '|'.join(CATALOG_IMPORT_HEADER)
                                            + ' را داشته باشد'}], delimiter, False
    # سازگاری فیلدهای سطح درس/گروه بین خطوط یک گروه — اختلاف = خطا
    groups = {}
    for r in rows:
        key = (r['term'], r['code'], r['group'])
        g = groups.setdefault(key, {'meta': None, 'teacher': None})
        meta = (normalize_fa(r['name']), r['units'], normalize_fa(r['major']))
        tnorm = normalize_fa(r['teacher'])
        if g['meta'] is None:
            g['meta'] = meta
        elif g['meta'] != meta:
            errors.append({'line': r['line'],
                           'reason': 'نام/واحد/رشتهٔ این گروه با خطوط قبلیِ همان گروه '
                                     'مغایرت دارد'})
            r['invalid'] = True
            continue
        if g['teacher'] is None:
            g['teacher'] = tnorm
        elif g['teacher'] != tnorm:
            errors.append({'line': r['line'],
                           'reason': 'نام استاد این گروه با خطوط قبلیِ همان گروه مغایرت دارد'})
            r['invalid'] = True
    rows = [r for r in rows if not r.get('invalid')]
    return rows, errors, delimiter, True


def _group_rows_by_key(rows):
    grouped = {}
    order = []
    for r in rows:
        key = (r['term'], r['code'], r['group'])
        if key not in grouped:
            grouped[key] = []
            order.append(key)
        grouped[key].append(r)
    return grouped, order


def _plan_catalog_import(rows, import_mode):
    """نقشهٔ create/update/skip برای هر (term, code, group) — بدون نوشتن."""
    grouped, order = _group_rows_by_key(rows)
    by_code = {c.code: c for c in CatalogCourse.query.all()}
    plan = []
    for key in order:
        term, code, group = key
        group_rows = grouped[key]
        course = by_code.get(code)
        section = None
        if course:
            section = CourseSection.query.filter_by(
                course_id=course.id, term=term, group_number=group).first()
        if section and import_mode == 'add_only':
            action, reason = 'skip', 'این گروه قبلاً ثبت شده است (حالت افزودن فقط)'
        elif section:
            action, reason = 'update', 'گروه موجود به‌روزرسانی می‌شود (جلسات جایگزین می‌شوند)'
        else:
            action, reason = 'create', 'جدید'
        plan.append({'term': term, 'code': code, 'group': group,
                     'name': group_rows[0]['name'], 'teacher': group_rows[0]['teacher'],
                     'action': action, 'reason': reason,
                     'course_exists': bool(course),
                     'section_id': section.id if section else None,
                     'meetings': len(group_rows)})
    return grouped, plan


def _catalog_import_counts(plan):
    c = {'courses_create': 0, 'courses_update': 0, 'sections_create': 0,
         'sections_update': 0, 'sections_skip': 0, 'meetings_create': 0}
    courses_seen = set()
    for p in plan:
        if p['action'] == 'skip':
            c['sections_skip'] += 1
            continue
        if not p['course_exists'] and p['code'] not in courses_seen:
            courses_seen.add(p['code'])
        if p['action'] == 'create':
            c['sections_create'] += 1
        else:
            c['sections_update'] += 1
        c['meetings_create'] += p['meetings']
    c['courses_create'] = len(courses_seen)
    return c


@app.route('/api/admin/catalog/template')
@admin_required
def admin_catalog_template():
    body = ('# قالب استاندارد کاتالوگ دروس یونی‌نت — هر خط = یک جلسهٔ هفتگی یک گروه\n'
            '# کدگذاری UTF-8 — جداکننده «|» — خطوط خالی و خطوطی که با # شروع می‌شوند نادیده‌اند\n'
            '# روز: شنبه..جمعه (یا ایندکس ۰..۶) — نوع هفته: هر هفته | فرد | زوج\n'
            + '|'.join(CATALOG_IMPORT_HEADER) + '\n'
            '14051|3110234|سیستم‌های نهفته و بی‌درنگ|3|مهندسی کامپیوتر|1|دکتر رمضانی|شنبه|08:00|10:00|هر هفته|کلاس 107\n'
            '14051|3110234|سیستم‌های نهفته و بی‌درنگ|3|مهندسی کامپیوتر|2|دکتر احمدی|دوشنبه|14:00|16:00|فرد|کلاس 210\n')
    return Response(body.encode('utf-8'), mimetype='text/plain; charset=utf-8',
                    headers={'Content-Disposition':
                             'attachment; filename="uninet_catalog_template.txt"'})


@app.route('/api/admin/catalog/export')
@admin_required
def admin_catalog_export():
    """خروجی دقیقاً در همان فرمت استاندارد (درون‌ریزی مجدد آن بی‌اثر است)."""
    term = (request.args.get('term', '') or '').strip()
    try:
        lines = ['|'.join(CATALOG_IMPORT_HEADER)]
        qry = CourseSection.query.order_by(CourseSection.term,
                                           CourseSection.group_number)
        if term:
            qry = qry.filter(CourseSection.term == term)
        for sec in qry.all():
            if not sec.is_active or not sec.course:
                continue
            for mtg in sec.meetings:
                if not mtg.is_active:
                    continue
                c = sec.course
                lines.append('|'.join([
                    sec.term, c.code, c.name,
                    ('%g' % float(c.units)) if c.units is not None else '',
                    c.major or '', str(sec.group_number), sec.teacher or '',
                    DAY_FA.get(mtg.day, mtg.day), mtg.start_time, mtg.end_time,
                    WEEK_TYPE_FA.get(mtg.week_type or 'all', 'هر هفته'),
                    mtg.location_override or sec.location or '']))
        fname = 'uninet_catalog_%s.txt' % (term or 'all')
        return Response(('\n'.join(lines) + '\n').encode('utf-8'),
                        mimetype='text/plain; charset=utf-8',
                        headers={'Content-Disposition':
                                 'attachment; filename="%s"' % fname})
    except Exception:
        app.logger.exception('admin_catalog_export failed')
        return jsonify({'error': 'خطا در خروجی گرفتن از کاتالوگ'}), 500


@app.route('/api/admin/catalog/import', methods=['POST'])
@admin_required
def admin_catalog_import():
    """پیش‌نمایش (خشک، بدون نوشتن) یا ثبت؛ پیش‌فرض اتمیک (همه یا هیچ)."""
    data = request.get_json(silent=True) or {}
    if request.form:   # آپلود multipart: mode/import_mode/skip_invalid در request.form هستند
        merged = request.form.to_dict()
        merged.update(data)
        data = merged
    mode = str(data.get('mode', 'preview')).lower()            # preview | commit
    import_mode = str(data.get('import_mode', 'update')).lower()  # update | add_only
    skip_invalid = str(data.get('skip_invalid', '')).lower() in ('1', 'true', 'yes', 'on')
    if import_mode not in ('update', 'add_only'):
        return jsonify({'error': 'حالت درون‌ریزی نامعتبر است'}), 400

    used_encoding = 'utf-8'
    text = data.get('text')
    if text is None and request.files.get('file'):
        f = request.files['file']
        raw = f.read()
        if len(raw) > CATALOG_IMPORT_MAX_BYTES:
            return jsonify({'error': 'حجم فایل بیش از حد مجاز است (حداکثر ۱ مگابایت)'}), 400
        text, used_encoding = _decode_import_bytes(raw)
    elif text is None:
        return jsonify({'error': 'متن یا فایلی ارسال نشد'}), 400
    if len(text.encode('utf-8', errors='replace')) > CATALOG_IMPORT_MAX_BYTES:
        return jsonify({'error': 'حجم متن بیش از حد مجاز است (حداکثر ۱ مگابایت)'}), 400

    active = get_active_term()
    rows, errors, delimiter, header_ok = _parse_catalog_text(text, active)
    if not header_ok:
        return jsonify({'committed': False, 'errors': errors,
                        'encoding': used_encoding, 'delimiter': delimiter}), 400
    if rows is not None and len(rows) > CATALOG_IMPORT_MAX_ROWS:
        return jsonify({'error': 'تعداد ردیف‌ها بیش از حد مجاز است (حداکثر %d)'
                                 % CATALOG_IMPORT_MAX_ROWS}), 400
    rows = rows or []
    if mode == 'preview':
        grouped, plan = _plan_catalog_import(rows, import_mode)
        return jsonify({'committed': False, 'encoding': used_encoding,
                        'delimiter': delimiter, 'errors': errors,
                        'rows_valid': len(rows), 'plan': plan,
                        'counts': _catalog_import_counts(plan)})

    # ---- ثبت ----
    if errors and not skip_invalid:
        grouped, plan = _plan_catalog_import(rows, import_mode)
        return jsonify({'committed': False,
                        'message': 'با وجود خطاها ثبت انجام نشد (همه یا هیچ)؛ '
                                   'یا خطاها را برطرف کنید یا «ردِ خطوط نامعتبر» را انتخاب کنید',
                        'errors': errors, 'encoding': used_encoding,
                        'rows_valid': len(rows), 'plan': plan,
                        'counts': _catalog_import_counts(plan)})
    if skip_invalid:
        # خطوط نامعتبر قبلاً در errors فهرست شده‌اند؛ rows فقط سالم‌هاست
        pass
    try:
        grouped, plan = _plan_catalog_import(rows, import_mode)
        by_code = {c.code: c for c in CatalogCourse.query.all()}
        summary = {'courses_created': 0, 'courses_updated': 0,
                   'sections_created': 0, 'sections_updated': 0,
                   'sections_skipped': 0, 'meetings_created': 0}
        skipped = []
        affected_uids = set()
        for p in plan:
            key = (p['term'], p['code'], p['group'])
            group_rows = grouped[key]
            first = group_rows[0]
            if p['action'] == 'skip':
                summary['sections_skipped'] += 1
                skipped.append({'term': p['term'], 'code': p['code'],
                                'group': p['group'], 'reason': p['reason']})
                continue
            course = by_code.get(p['code'])
            if course is None:
                course = CatalogCourse(code=p['code'], name=first['name'],
                                       name_norm=normalize_fa(first['name']),
                                       units=first['units'],
                                       major=first['major'] or None)
                db.session.add(course)
                db.session.flush()
                by_code[course.code] = course
                summary['courses_created'] += 1
            elif import_mode == 'update':
                touched = (course.name != first['name'] or
                           float(course.units or 0) != float(first['units'] or 0) or
                           (course.major or '') != (first['major'] or ''))
                course.name = first['name']
                course.name_norm = normalize_fa(first['name'])
                course.units = first['units']
                course.major = first['major'] or None
                if touched:
                    summary['courses_updated'] += 1
            section = CourseSection.query.filter_by(
                course_id=course.id, term=p['term'],
                group_number=p['group']).first()
            if section is None:
                section = CourseSection(course_id=course.id, term=p['term'],
                                        group_number=p['group'],
                                        teacher=first['teacher'],
                                        location=first['location'])
                db.session.add(section)
                db.session.flush()
                summary['sections_created'] += 1
            else:
                # is_active دست نمی‌خورد (حذف نرمِ ادمین باقی می‌ماند)
                if section.teacher != first['teacher'] or \
                        (section.location or '') != first['location']:
                    summary['sections_updated'] += 1
                section.teacher = first['teacher']
                section.location = first['location']
                # جایگزینی کامل فهرست جلسات با ردیف‌های فایل
                for old in list(section.meetings):
                    db.session.delete(old)
            for r in group_rows:
                db.session.add(SectionMeeting(
                    section_id=section.id, day=r['day'],
                    start_time=r['start'], end_time=r['end'],
                    week_type=r['week'], location_override=r['location'] or None))
                summary['meetings_created'] += 1
            sec_uids = _enrolled_user_ids([section.id])
            if sec_uids:
                affected_uids.update(sec_uids)
        if affected_uids:
            _queue_catalog_notifications([
                (uid, 'برنامهٔ دروس توسط مدیریت به‌روزرسانی شد؛ برنامهٔ هفتگی خود را '
                      'در داشبورد بررسی کنید.') for uid in affected_uids])
        db.session.commit()
        _emit_catalog_updated(affected_uids)
        return jsonify({'committed': True, 'encoding': used_encoding,
                        'delimiter': delimiter, 'errors': errors,
                        'rows_valid': len(rows), 'summary': summary,
                        'skipped': skipped})
    except Exception:
        db.session.rollback()
        app.logger.exception('admin_catalog_import failed')
        return jsonify({'committed': False,
                        'error': 'خطا در درون‌ریزی؛ هیچ تغییری اعمال نشد'}), 500


# ------------------------------------------
# B3/B5 — سمت دانشجو: جست‌وجو، افزودن، تغییر گروه/درس، حذف
# ------------------------------------------

def _enrollment_conflicts(uid, section, exclude_enrollment_id=None):
    """جلسات گروه با کدام کلاس‌های موجودِ همین دانشجو تداخل دارد؟"""
    conflicts = []
    items = build_schedule_items(uid)
    for mtg in section.meetings:
        if not mtg.is_active:
            continue
        for item in items:
            if exclude_enrollment_id and \
                    item.get('enrollment_id') == exclude_enrollment_id:
                continue
            if item['day'] != mtg.day:
                continue
            if not _weektypes_overlap(item['week_type'], mtg.week_type or 'all'):
                continue
            if not item.get('start') or not item.get('end'):
                continue
            if not _times_overlap(item['start'], item['end'],
                                  mtg.start_time, mtg.end_time):
                continue
            conflicts.append({
                'day': mtg.day, 'day_fa': DAY_FA.get(mtg.day, mtg.day),
                'start': mtg.start_time, 'end': mtg.end_time,
                'conflicts_with': item['name'], 'kind': item['kind']})
    return conflicts


def _placement_info(section):
    """محلِ قرارگیری واقعی (نخستین جلسهٔ فعال) — برای پیام «درس در زمان ثبت‌شده...»."""
    for mtg in section.meetings:
        if not mtg.is_active:
            continue
        slot, _ = slot_for_start(mtg.start_time)
        return {'day': mtg.day, 'day_fa': DAY_FA.get(mtg.day, mtg.day),
                'start': mtg.start_time, 'end': mtg.end_time,
                'start_fa': _hm_fa(mtg.start_time), 'end_fa': _hm_fa(mtg.end_time),
                'slot': slot,
                'label': '%s %s تا %s' % (DAY_FA.get(mtg.day, mtg.day),
                                          _hm_fa(mtg.start_time),
                                          _hm_fa(mtg.end_time))}
    return None


@app.route('/api/catalog/search')
@login_required
def catalog_search():
    """پیشنهادهای زندهٔ کاتالوگ — فقط ترم فعال و گروه‌های فعال.

    رتبه‌بندی: (1) نام درس با متنِ تایپ‌شده شروع می‌شود (2) هر واژهٔ نام (3) کد
    درسی (4) حاوی متن؛ سپس گروه‌ها به‌ترتیبِ نام و شمارهٔ گروه.
    """
    uid = session['current_user_id']
    q = normalize_fa(fa_digits_to_en(request.args.get('q', '')))
    group_raw = (request.args.get('group', '') or '').strip()
    group_num = None
    if group_raw:
        try:
            group_num = int(fa_digits_to_en(group_raw))
        except ValueError:
            group_num = 0
        if group_num < 1:
            return jsonify({'error': 'شمارهٔ گروه نامعتبر است'}), 400
    limit = min(50, max(1, request.args.get('limit', 20, type=int) or 20))
    active = get_active_term()
    if not active:
        return jsonify({'results': [], 'active_term': None})
    if not q and group_num is None:
        return jsonify({'results': [], 'active_term': active})
    try:
        sections = CourseSection.query.filter_by(term=active,
                                                 is_active=True).all()
        enrolled_section_ids = set()
        enr_by_course = {}
        for e in ScheduleEnrollment.query.filter_by(user_id=uid).all():
            enrolled_section_ids.add(e.section_id)
            sec = db.session.get(CourseSection, e.section_id)
            if sec:
                enr_by_course[sec.course_id] = e.id
        scored = []
        for sec in sections:
            if group_num is not None and sec.group_number != group_num:
                continue
            c = sec.course
            if not c:
                continue
            if q:
                if c.name_norm.startswith(q):
                    rank = 1
                elif any(w.startswith(q) for w in c.name_norm.split()):
                    rank = 2
                elif c.code.startswith(fa_digits_to_en(q)):
                    rank = 3
                elif q in c.name_norm or fa_digits_to_en(q) in c.code:
                    rank = 4
                else:
                    continue
            else:
                rank = 5
            scored.append((rank, c.name_norm, sec))
        scored.sort(key=lambda t: (t[0], t[1], t[2].group_number))
        results = []
        for _rank, _name, sec in scored[:limit]:
            c = sec.course
            results.append({
                'section_id': sec.id, 'course_id': c.id, 'code': c.code,
                'name': c.name, 'units': _units_num(c.units),
                'major': c.major or '', 'group': sec.group_number,
                'teacher': sec.teacher or '', 'location': sec.location or '',
                'already': sec.id in enrolled_section_ids,
                'other_group_enrollment_id': (
                    None if sec.id in enrolled_section_ids
                    else enr_by_course.get(c.id)),
                'meetings': [_meeting_dict(m) for m in sec.meetings if m.is_active],
            })
        return jsonify({'results': results, 'active_term': active})
    except Exception:
        app.logger.exception('catalog_search failed (user=%s)', uid)
        return jsonify({'error': 'خطا در جست‌وجوی کاتالوگ'}), 500


def _validate_enroll_target(section, active):
    """اعتبارسنجی مشترک enroll/replace؛ (خطا، کد) یا (None, None)."""
    if not section:
        return 'گروه موردنظر یافت نشد', 404
    if not section.is_active or section.term != active:
        return 'این گروه در فهرست دروس فعال نیست', 404
    return None, None


@app.route('/api/catalog/enroll', methods=['POST'])
@login_required
def catalog_enroll():
    """افزودن یک گروه به برنامه — جایگیری از کاتالوگ است، نه خانهٔ کلیک‌شده."""
    uid = session['current_user_id']
    data = request.get_json(silent=True) or {}
    try:
        section_id = int(data.get('section_id') or 0)
    except (TypeError, ValueError):
        section_id = 0
    section = db.session.get(CourseSection, section_id)
    active = get_active_term()
    err, code = _validate_enroll_target(section, active)
    if err:
        return jsonify({'error': err}), code
    confirm = bool(data.get('confirm'))
    replace = bool(data.get('replace'))
    try:
        already = ScheduleEnrollment.query.filter_by(
            user_id=uid, section_id=section.id).first()
        if already:
            return jsonify({'error': 'این گروه قبلاً به برنامه اضافه شده است'}), 400
        other = ScheduleEnrollment.query.join(
            CourseSection, CourseSection.id == ScheduleEnrollment.section_id).filter(
            ScheduleEnrollment.user_id == uid,
            CourseSection.course_id == section.course_id,
            CourseSection.id != section.id).first()
        if other and not replace:
            return jsonify({'error': 'گروه %d همین درس در برنامهٔ شماست؛ '
                                     'برای جایگزینی تأیید کنید'
                                     % (other.section.group_number if other.section else 0),
                            'requires_replace': True,
                            'existing_enrollment_id': other.id,
                            'existing_group': (other.section.group_number
                                               if other.section else None)}), 409
        conflicts = _enrollment_conflicts(
            uid, section,
            exclude_enrollment_id=(other.id if other else None))
        if conflicts and not confirm:
            return jsonify({'error': 'این گروه با برنامهٔ فعلی شما تداخل دارد؛ '
                                     'برای ادامه تأیید کنید',
                            'requires_confirm': True,
                            'conflicts': conflicts}), 409
        if other:
            db.session.delete(other)   # جایگزینی اتمیک در همان تراکنش
        enrollment = ScheduleEnrollment(user_id=uid, section_id=section.id)
        db.session.add(enrollment)
        db.session.flush()
        items = build_schedule_items(uid)
        total = compute_total_units(uid)
        placed = _placement_info(section)
        db.session.commit()
        return jsonify({'status': 'success', 'enrollment_id': enrollment.id,
                        'placed': placed, 'items': items, 'total_units': total})
    except Exception:
        db.session.rollback()
        app.logger.exception('catalog_enroll failed (user=%s section=%s)',
                             uid, section_id)
        return jsonify({'error': 'خطا در افزودن درس به برنامه'}), 500


@app.route('/api/catalog/enrollments/<int:enrollment_id>/replace', methods=['POST'])
@login_required
def catalog_replace_enrollment(enrollment_id):
    """«تغییر گروه» و «تغییر درس» — جایگزینی اتمیکِ همان ثبت‌نام."""
    uid = session['current_user_id']
    data = request.get_json(silent=True) or {}
    try:
        target_id = int(data.get('section_id') or 0)
    except (TypeError, ValueError):
        target_id = 0
    enrollment = db.session.get(ScheduleEnrollment, enrollment_id)
    if not enrollment or enrollment.user_id != uid:
        return jsonify({'error': 'ثبت‌نام یافت نشد'}), 404
    target = db.session.get(CourseSection, target_id)
    active = get_active_term()
    err, code = _validate_enroll_target(target, active)
    if err:
        return jsonify({'error': err}), code
    if target.id == enrollment.section_id:
        return jsonify({'error': 'همین گروه انتخاب شده است'}), 400
    confirm = bool(data.get('confirm'))
    try:
        conflicts = _enrollment_conflicts(uid, target,
                                          exclude_enrollment_id=enrollment.id)
        if conflicts and not confirm:
            return jsonify({'error': 'گروه جدید با برنامهٔ فعلی شما تداخل دارد؛ '
                                     'برای ادامه تأیید کنید',
                            'requires_confirm': True,
                            'conflicts': conflicts}), 409
        other = ScheduleEnrollment.query.join(
            CourseSection, CourseSection.id == ScheduleEnrollment.section_id).filter(
            ScheduleEnrollment.user_id == uid,
            CourseSection.course_id == target.course_id,
            CourseSection.id != target.id,
            ScheduleEnrollment.id != enrollment.id).first()
        if other:
            db.session.delete(other)
        db.session.delete(enrollment)
        new_enr = ScheduleEnrollment(user_id=uid, section_id=target.id)
        db.session.add(new_enr)
        db.session.flush()
        items = build_schedule_items(uid)
        total = compute_total_units(uid)
        placed = _placement_info(target)
        db.session.commit()
        return jsonify({'status': 'success', 'enrollment_id': new_enr.id,
                        'placed': placed, 'items': items, 'total_units': total})
    except Exception:
        db.session.rollback()
        app.logger.exception('catalog_replace_enrollment failed (user=%s)',
                             uid)
        return jsonify({'error': 'خطا در تغییر گروه'}), 500


@app.route('/api/catalog/enrollments/<int:enrollment_id>/delete', methods=['POST'])
@login_required
def catalog_delete_enrollment(enrollment_id):
    uid = session['current_user_id']
    enrollment = db.session.get(ScheduleEnrollment, enrollment_id)
    if not enrollment or enrollment.user_id != uid:
        return jsonify({'error': 'ثبت‌نام یافت نشد'}), 404
    try:
        db.session.delete(enrollment)
        items = build_schedule_items(uid)
        total = compute_total_units(uid)
        db.session.commit()
        return jsonify({'status': 'success', 'items': items,
                        'total_units': total})
    except Exception:
        db.session.rollback()
        app.logger.exception('catalog_delete_enrollment failed (user=%s)',
                             uid)
        return jsonify({'error': 'خطا در حذف درس از برنامه'}), 500


@app.route('/api/schedule/items')
@login_required
def api_schedule_items():
    """لیست تازهٔ برنامهٔ یکپارچه (برای بروزرسانی بدون reload پس از رویداد/تغییر تب)."""
    uid = session['current_user_id']
    try:
        items = build_schedule_items(uid)
        total = compute_total_units(uid)
        return jsonify({'items': items, 'total_units': total})
    except Exception:
        app.logger.exception('api_schedule_items failed (user=%s)', uid)
        return jsonify({'error': 'خطا در خواندن برنامه'}), 500


@app.route('/api/master_schedule')
@login_required
def get_master_schedule():
    try:
        slots = MasterSchedule.query.all()
        reservations = Reservation.query.filter_by(status='approved').all()
        reserved_map = {f"{r.master_slot_id}_{r.room_name}": True for r in reservations}
        output = []
        for s in slots:
            rooms_list = [r.strip() for r in s.rooms.split(',') if r.strip()]
            available_rooms = [r for r in rooms_list if f"{s.id}_{r}" not in reserved_map]
            output.append({
                'id': s.id,
                'day': s.day,
                'time_slot': s.time_slot,
                'available_rooms': available_rooms,
                'all_rooms': rooms_list
            })
        return jsonify(output)
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/submit_reservation/<int:slot_id>/<room_name>', methods=['POST'])
@login_required
def submit_reservation(slot_id, room_name):
    try:
        reason = request.form.get('reason', '').strip()
        if not reason:
            flash('لطفاً دلیل رزرو را وارد کنید.', 'error')
            return redirect(url_for('dashboard'))
        exists = Reservation.query.filter_by(
            master_slot_id=slot_id, room_name=room_name, status='approved'
        ).first()
        if exists:
            flash('این کلاس قبلاً رزرو شده است.', 'error')
            return redirect(url_for('dashboard'))
        db.session.add(Reservation(
            user_id=session['current_user_id'],
            master_slot_id=slot_id,
            room_name=room_name,
            reason=reason
        ))
        db.session.commit()
        flash('درخواست رزرو با موفقیت ثبت شد و در انتظار تأیید است.', 'success')
    except Exception as e:
        db.session.rollback()
        flash('خطا در ثبت درخواست. لطفاً دوباره تلاش کنید.', 'error')
    return redirect(url_for('dashboard'))


# ==========================================
# Routes — Admin
# ==========================================

@app.route('/admin')
@admin_required
def admin_dashboard():
    try:
        cancelled = CancelledClass.query.order_by(CancelledClass.created_at.desc()).limit(20).all()
        pending_requests = Reservation.query.filter_by(status='pending').all()
        master_slots = MasterSchedule.query.all()
        return render_template(
            'admin_dashboard.html',
            slots=master_slots,
            requests=pending_requests,
            cancelled_classes=cancelled,
            class_time_slots=CLASS_TIME_SLOTS
        )
    except Exception as e:
        app.logger.error(f"admin_dashboard error: {e}")
        flash('خطا در بارگذاری پنل مدیریت.', 'error')
        return redirect(url_for('index'))


@app.route('/admin/save_master_schedule', methods=['POST'])
@admin_required
def save_master_schedule():
    """ذخیره برنامه استاد (جدول اصلی) بدون آسیب به رزروهای موجود
    (نسخهٔ کاملِ همگام‌سازی ردیفی از app/routes/admin.py)."""
    try:
        data = request.get_json()
        if not isinstance(data, list):
            return jsonify({'status': 'error', 'message': 'داده ارسال‌شده معتبر نیست.'}), 400

        valid_days = set(DAY_FA.keys())
        # قالب تأییدشدهٔ جدول مرجع در ادمین/دیتابیس «8-10» است (SCHEDULE_SLOTS)؛
        # نسخهٔ «08:00-10:00» هم برای سازگاری با داده‌های قدیمی پذیرفته می‌شود.
        valid_slots = set(SCHEDULE_SLOTS) | set(CLASS_TIME_SLOTS)
        cleaned = []
        errors = []
        seen = set()
        for idx, item in enumerate(data, start=1):
            day = str(item.get('day', '')).strip().lower()
            time_slot = fa_digits_to_en(item.get('time_slot', '')).strip()
            rooms = str(item.get('rooms', '')).strip()
            if not day and not time_slot and not rooms:
                continue  # ردیف کاملاً خالی
            if day not in valid_days:
                errors.append('ردیف %d: روز نامعتبر است.' % idx)
                continue
            if time_slot not in valid_slots:
                errors.append('ردیف %d: بازه زمانی نامعتبر است.' % idx)
                continue
            if (day, time_slot) in seen:
                errors.append('ردیف %d: تکراری است.' % idx)
                continue
            seen.add((day, time_slot))
            cleaned.append((day, time_slot, rooms))

        if errors:
            return jsonify({
                'status': 'error',
                'message': 'برخی ردیف‌ها معتبر نیستند؛ تغییری اعمال نشد.',
                'errors': errors
            }), 400

        existing = {(s.day, s.time_slot): s for s in MasterSchedule.query.all()}
        referenced_ids = {r.master_slot_id for r in Reservation.query.all()
                          if r.master_slot_id is not None}
        wanted_keys = {(d, t) for d, t, _ in cleaned}

        created = updated = kept = removed = 0
        for day, time_slot, rooms in cleaned:
            slot = existing.get((day, time_slot))
            if slot is None:
                if not rooms:
                    continue  # slot خالیِ جدید نیازی به ذخیره ندارد
                db.session.add(MasterSchedule(day=day, time_slot=time_slot, rooms=rooms))
                created += 1
            else:
                if slot.rooms != rooms:
                    slot.rooms = rooms
                    updated += 1
                else:
                    kept += 1

        # حذف فقط slotهایی که در داده جدید نیستند و به هیچ رزروی اشاره نمی‌شوند
        preserved = 0
        for (day, time_slot), slot in existing.items():
            if (day, time_slot) not in wanted_keys:
                if slot.id in referenced_ids:
                    preserved += 1  # حفظ می‌شود چون درخواست رزرو به آن اشاره دارد
                else:
                    db.session.delete(slot)
                    removed += 1

        db.session.commit()
        return jsonify({
            'status': 'success',
            'created': created,
            'updated': updated,
            'kept': kept,
            'removed': removed,
            'preserved_referenced': preserved
        })
    except Exception:
        db.session.rollback()
        app.logger.exception("save_master_schedule failed")
        return jsonify({'status': 'error', 'message': 'خطا در ذخیره برنامه استاد. لطفاً دوباره تلاش کنید.'}), 500


@app.route('/admin/handle_reservation/<int:req_id>/<string:action>', methods=['POST'])
@admin_required
def handle_reservation(req_id, action):
    """تأیید/رد درخواست رزرو — فقط POST (نسخهٔ سالم از app/routes/admin.py).

    قبلاً GET بود (هر لینک/پیش‌بارگذاری صفحه درخواست را پردازش می‌کرد)؛
    اکنون POST است (قالب ادمین با form method=POST ارسال می‌کند) و
    فقط روی درخواست‌های pending اثر می‌گذارد.
    """
    try:
        if action not in ('approve', 'reject'):
            flash('عملیات نامعتبر است.', 'error')
            return redirect(url_for('admin_dashboard'))
        req = Reservation.query.get_or_404(req_id)
        if req.status != 'pending':
            flash('این درخواست قبلاً بررسی شده است.', 'info')
            return redirect(url_for('admin_dashboard'))

        slot = db.session.get(MasterSchedule, req.master_slot_id) if req.master_slot_id else None
        slot_info = (
            f"{DAY_FA.get(slot.day, 'روز نامشخص')} - {slot.time_slot}"
            if slot else "نامشخص"
        )
        if action == 'approve':
            conflict = Reservation.query.filter(
                Reservation.master_slot_id == req.master_slot_id,
                Reservation.room_name == req.room_name,
                Reservation.id != req.id,
                Reservation.status == 'approved'
            ).first()
            if conflict:
                flash('اتاق این بازه قبلاً به درخواست دیگری اختصاص یافته است.', 'error')
                return redirect(url_for('admin_dashboard'))
            req.status = 'approved'
            db.session.add(Notification(
                user_id=req.user_id,
                message=f"درخواست رزرو شما برای کلاس {req.room_name} در {slot_info} تأیید شد."
            ))
            Reservation.query.filter(
                Reservation.master_slot_id == req.master_slot_id,
                Reservation.room_name == req.room_name,
                Reservation.id != req.id,
                Reservation.status == 'pending'
            ).update({Reservation.status: 'rejected'}, synchronize_session=False)
            flash('درخواست رزرو تأیید شد.', 'success')
        else:  # reject
            req.status = 'rejected'
            db.session.add(Notification(
                user_id=req.user_id,
                message=f"متأسفانه درخواست رزرو شما برای کلاس {req.room_name} رد شد."
            ))
            flash('درخواست رزرو رد شد.', 'info')
        db.session.commit()
    except HTTPException:
        raise
    except Exception:
        db.session.rollback()
        app.logger.exception("handle_reservation failed")
        flash('خطا در پردازش درخواست.', 'error')
    return redirect(url_for('admin_dashboard'))


@app.route('/admin/add_cancelled_class', methods=['POST'])
@admin_required
def add_cancelled_class():
    try:
        prof = request.form.get('professor', '').strip()
        course = request.form.get('course', '').strip()
        time_slot = request.form.get('time_slot', '').strip()
        desc = request.form.get('desc', '').strip()

        def jalali_to_gregorian(j_str):
            if not j_str:
                return None
            try:
                parts = j_str.replace('-', '/').split('/')
                jd = jdatetime.date(int(parts[0]), int(parts[1]), int(parts[2]))
                return jd.togregorian()
            except Exception:
                return None

        cancel_date = jalali_to_gregorian(request.form.get('cancel_date_j', ''))
        start_date = jalali_to_gregorian(request.form.get('start_date_j', ''))
        end_date = jalali_to_gregorian(request.form.get('end_date_j', ''))

        new_cancel = CancelledClass(
            professor_name=prof or None,
            course_name=course or None,
            time_slot=time_slot or None,
            description=desc or None,
            cancel_date=cancel_date,
            start_date=start_date,
            end_date=end_date
        )
        db.session.add(new_cancel)
        db.session.commit()
        flash('لغو کلاس با موفقیت ثبت شد.', 'success')
    except Exception as e:
        db.session.rollback()
        app.logger.error(f"add_cancelled_class error: {e}")
        flash('خطا در ثبت لغو کلاس.', 'error')
    return redirect(url_for('admin_dashboard'))


@app.route('/admin/delete_cancelled_class/<int:class_id>', methods=['POST'])
@admin_required
def delete_cancelled_class(class_id):
    try:
        c = CancelledClass.query.get_or_404(class_id)
        db.session.delete(c)
        db.session.commit()
        return jsonify({'status': 'success'})
    except Exception as e:
        db.session.rollback()
        return jsonify({'status': 'error', 'message': str(e)}), 500


@app.route('/api/cancelled_classes/mark_viewed', methods=['POST'])
@login_required
def mark_cancelled_classes_viewed():
    try:
        data = request.get_json() or {}
        class_ids = data.get('ids', [])
        user_id = session['current_user_id']
        for cid in class_ids:
            existing = CancelledClassView.query.filter_by(
                cancelled_class_id=cid, user_id=user_id
            ).first()
            if not existing:
                db.session.add(CancelledClassView(
                    cancelled_class_id=cid, user_id=user_id
                ))
        db.session.commit()
        return jsonify({'status': 'success'})
    except Exception as e:
        db.session.rollback()
        return jsonify({'status': 'error', 'message': str(e)}), 500


@app.route('/api/cancelled_classes/unviewed_count')
@login_required
def unviewed_cancelled_count():
    try:
        user_id = session['current_user_id']
        all_ids = [c.id for c in CancelledClass.query.all()]
        if not all_ids:
            return jsonify({'count': 0})
        viewed_ids = [v.cancelled_class_id for v in
                      CancelledClassView.query.filter(
                          CancelledClassView.user_id == user_id,
                          CancelledClassView.cancelled_class_id.in_(all_ids)
                      ).all()]
        count = len(set(all_ids) - set(viewed_ids))
        return jsonify({'count': count})
    except Exception:
        return jsonify({'count': 0})


# ==========================================
# Routes — Profile
# ==========================================

# ==========================================
# Routes — Holiday Calendar (Task 3)
# ==========================================

@app.route('/api/calendar/holidays')
@login_required
def calendar_holidays():
    """
    GET /api/calendar/holidays?year=&month=
    روزهای یک ماه شمسی + تعطیلات رسمی + جمعه‌ها از کش آفلاین (data/*.json)
    + override های مدیر. هیچ محاسبهٔ جلالی‌ای سمت کلاینت لازم نیست؛
    امروز هم از همان منبع معتبر /api/now (now_tehran) می‌آید.
    """
    try:
        start_holiday_refresh()      # thread پس‌زمینه فقط یک بار (idempotent)
        year = request.args.get('year', type=int)
        month = request.args.get('month', type=int)
        if (year is None or month is None
                or not (1400 <= year <= 1499) or not (1 <= month <= 12)):
            return jsonify({'error': 'پارامتر year/month نامعتبر است'}), 400

        days = build_calendar_month(year, month)
        today_j = jdatetime.date.fromgregorian(date=now_tehran().date())
        seed = _read_holiday_seed(year)
        return jsonify({
            'year': year,
            'month': month,
            'month_name': JALALI_MONTHS_FA[month - 1],
            'days_in_month': jalali_month_days(year, month),
            'first_weekday_index': days[0]['weekday_index'],
            'days': days,
            'today': {
                'year': today_j.year,
                'month': today_j.month,
                'day': today_j.day,
                'weekday_index': today_j.weekday(),   # jdatetime: شنبه=۰ … جمعه=۶
                'gregorian': now_tehran().date().isoformat(),
            },
            'source': 'seed' if seed is not None else 'friday-only',
            'holidays_stored': len(seed or {}),
        })
    except Exception:
        app.logger.exception('/api/calendar/holidays failed')
        return jsonify({'error': 'خطا در دریافت تقویم'}), 500


@app.route('/api/holidays/<int:jy>/<int:jm>')
@login_required
def get_month_holidays(jy, jm):
    """
    سازگاری با کلاینت قدیمی — همان سرویس کش‌شدهٔ آفلاین (بدون فراخوانی زنده).
    خروجی: {day: {is_holiday, events}}
    """
    if not (1 <= jm <= 12) or not (1300 <= jy <= 1500):
        return jsonify({'error': 'پارامتر نامعتبر'}), 400

    month_data = {}
    for info in build_calendar_month(jy, jm):
        events = info['events']
        if info['is_friday'] and not events:
            events = ['جمعه']
        month_data[info['day']] = {
            'is_holiday': info['is_holiday'],
            'events': events,
        }
    return jsonify(month_data)


@app.route('/api/admin/holidays', methods=['GET', 'POST'])
def admin_holiday_overrides():
    """override های مدیر: GET = فهرست، POST = افزودن/حذف یک روز."""
    if not session.get('is_admin'):
        return jsonify({'error': 'دسترسی غیرمجاز'}), 403

    if request.method == 'GET':
        rows = HolidayOverride.query.order_by(HolidayOverride.id).all()
        return jsonify([{
            'id': r.id, 'year': r.year, 'month': r.month, 'day': r.day,
            'kind': r.kind, 'occasion': r.occasion,
        } for r in rows])

    data = request.get_json() or {}
    try:
        year = int(data.get('year'))
        month = int(data.get('month'))
        day = int(data.get('day'))
    except (TypeError, ValueError):
        return jsonify({'error': 'year/month/day باید عدد باشند'}), 400
    kind = data.get('kind', 'add')
    occasion = _clean_holiday_name(data.get('occasion'))
    if not (1400 <= year <= 1499 and 1 <= month <= 12
            and 1 <= day <= jalali_month_days(year, month)):
        return jsonify({'error': 'تاریخ شمسی نامعتبر است'}), 400
    if kind not in ('add', 'remove'):
        return jsonify({'error': "kind باید 'add' یا 'remove' باشد"}), 400
    if kind == 'add' and not occasion:
        return jsonify({'error': 'عنوان مناسبت برای افزودن الزامی است'}), 400

    try:
        ov = HolidayOverride(year=year, month=month, day=day, kind=kind,
                             occasion=occasion or None)
        db.session.add(ov)
        db.session.commit()
    except Exception:
        db.session.rollback()
        app.logger.exception('holiday override insert failed')
        return jsonify({'error': 'خطا در ذخیره‌سازی'}), 500

    jd = jdatetime.date(year, month, day)
    return jsonify({
        'status': 'success',
        'id': ov.id,
        'day': {
            'day': day,
            'weekday_index': jd.weekday(),
            'gregorian': jd.togregorian().isoformat(),
            'events': get_year_holidays(year).get('%02d-%02d' % (month, day), []),
        },
    })


@app.route('/api/admin/holidays/<int:oid>', methods=['DELETE'])
def admin_delete_holiday_override(oid):
    """حذف یک override مدیر."""
    if not session.get('is_admin'):
        return jsonify({'error': 'دسترسی غیرمجاز'}), 403
    ov = db.session.get(HolidayOverride, oid)
    if not ov:
        return jsonify({'error': 'رکورد یافت نشد'}), 404
    try:
        db.session.delete(ov)
        db.session.commit()
    except Exception:
        db.session.rollback()
        app.logger.exception('holiday override delete failed')
        return jsonify({'error': 'خطا در حذف'}), 500
    return jsonify({'status': 'success', 'id': oid})
# ==========================================
# Routes — Notifications
# ==========================================

@app.route('/api/notifications')
@login_required
def list_notifications():
    """دریافت اعلان‌های کاربر برای زنگوله نوار بالایی
    (پورت‌شده از app/routes/notifications.py — در مونولیت وجود نداشت)."""
    try:
        user_id = session['current_user_id']
        notifs = Notification.query.filter_by(user_id=user_id).order_by(
            Notification.created_at.desc()
        ).limit(15).all()
        unread = Notification.query.filter_by(user_id=user_id, is_read=False).count()
        return jsonify({
            'unread_count': unread,
            'notifications': [
                {
                    'id': n.id,
                    'message': n.message,
                    'is_read': bool(n.is_read),
                    # created_at در رکوردهای قدیمی ممکن است NULL باشد
                    'created_at': n.created_at.strftime('%Y-%m-%d %H:%M') if n.created_at else None
                }
                for n in notifs
            ]
        })
    except Exception:
        app.logger.exception("list_notifications failed")
        return jsonify({'error': 'خطا در دریافت اعلان‌ها. لطفاً دوباره تلاش کنید.'}), 500
@app.route('/mark_notification_read/<int:n_id>', methods=['POST'])
@login_required
def mark_notification_read(n_id):
    try:
        notif = Notification.query.get_or_404(n_id)
        if notif.user_id == session['current_user_id']:
            notif.is_read = True
            db.session.commit()
    except Exception:
        db.session.rollback()
    return jsonify({'status': 'ok'})


@app.route('/api/notifications/mark_all_read', methods=['POST'])
@login_required
def mark_all_notifications_read():
    try:
        Notification.query.filter_by(
            user_id=session['current_user_id'], is_read=False
        ).update({'is_read': True})
        db.session.commit()
        return jsonify({'status': 'success'})
    except Exception as e:
        db.session.rollback()
        return jsonify({'error': str(e)}), 500


# ==========================================
# Socket.IO Events
# ==========================================

@socketio.on('connect')
def handle_connect():
    uid = session.get('current_user_id')
    if uid:
        StateManager.set_online(uid)
        join_room(f"user_{uid}")
        try:
            user = db.session.get(User, uid)
            if user:
                user.last_seen = now_tehran()
                db.session.commit()
        except Exception:
            db.session.rollback()


@socketio.on('disconnect')
def handle_disconnect():
    uid = session.get('current_user_id')
    if uid:
        StateManager.set_offline(uid)
        try:
            user = db.session.get(User, uid)
            if user:
                user.last_seen = now_tehran()
                db.session.commit()
        except Exception:
            pass
# ==========================================
# Application Startup
# ==========================================
def _run_idempotent_migrations():
    """افزوده‌های اسکیما (فقط ADD COLUMN — هیچ داده‌ای حذف/بازنویسی نمی‌شود).

    قبل از ALTER TABLE، PRAGMA table_info بررسی می‌شود؛ اجرای چندباره بی‌خطر است.
    """
    from sqlalchemy import text
    inspector = db.inspect(db.engine)

    def cols(table):
        if table not in inspector.get_table_names():
            return None
        return {r['name'] for r in inspector.get_columns(table)}

    schedule_cols = cols('schedule')
    if schedule_cols is not None and 'units' not in schedule_cols:
        db.session.execute(text('ALTER TABLE schedule ADD COLUMN units FLOAT'))
        print('✓ migration: schedule.units (واحد اختیاری کلاس شخصی) افزوده شد')

    meeting_cols = cols('section_meeting')
    if meeting_cols is not None and 'is_active' not in meeting_cols:
        db.session.execute(text(
            'ALTER TABLE section_meeting ADD COLUMN is_active BOOLEAN '
            'NOT NULL DEFAULT 1'))
        print('✓ migration: section_meeting.is_active (حذف نرم جلسه) افزوده شد')
    db.session.commit()


with app.app_context():
    db.create_all()
    _run_idempotent_migrations()
    create_initial_data()

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5001))
    debug = os.environ.get('FLASK_DEBUG', 'false').lower() == 'true'
    host = os.environ.get('HOST', '127.0.0.1')
    start_clock_sync()
    start_holiday_refresh()      # کش تعطیلات: refresh روزانه در پس‌زمینه
    print(f"\n{'='*50}")
    print(f"  UniNet Dashboard — اجرای محلی")
    print(f"  آدرس: http://{host}:{port}")
    print(f"  ادمین: student_id=admin (رمز در لاگ اولیه نمایش داده شد)")
    print(f"{'='*50}\n")
    socketio.run(app, host=host, port=port, debug=debug)
