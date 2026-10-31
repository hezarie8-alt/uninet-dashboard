/* =====================================================
   UniNet — منبع واحد زمان سمت کلاینت (Task 2)
   -----------------------------------------------------
   • offset را از GET /api/now می‌گیرد (همان زمانی که سرور به آن اعتماد دارد)
   • همهٔ نمایش‌ها با Date.now() + offset و timezone صریح Asia/Tehran ساخته
     می‌شوند؛ یعنی به timezone یا خطای ساعتِ دستگاه وابسته نیست.
   • تقویم فارسی با Intl.DateTimeFormat('fa-IR-u-ca-persian') — بدون محاسبهٔ
     دستی جلالی. نام روزها/ماه‌ها با رشته‌های سرور بایت‌به‌بایت یکسان است
     (در تست تأیید می‌شود) تا رندر سرور و کلاینت پرش نداشته باشد.
   • مسیر پشتیبان: همان تقویم فارسی با locale en (ارقام لاتین) + فهرست سرور.
   • در Node هم قابل require است (تست واحد با لحظه‌های ثابت + ساعت mock).
   ===================================================== */
(function (root, factory) {
    if (typeof module === 'object' && module.exports) {
        module.exports = factory();
    } else {
        root.TehranTime = factory();
    }
}(typeof self !== 'undefined' ? self : this, function () {
    'use strict';

    var TIME_ZONE = 'Asia/Tehran';
    // فهرست‌های سرور — برای مسیر پشتیبان و تطبیق در تست
    var WEEKDAYS = ['شنبه', 'یکشنبه', 'دوشنبه', 'سه‌شنبه',
                    'چهارشنبه', 'پنجشنبه', 'جمعه'];
    var MONTHS = ['فروردین', 'اردیبهشت', 'خرداد', 'تیر', 'مرداد', 'شهریور',
                  'مهر', 'آبان', 'آذر', 'دی', 'بهمن', 'اسفند'];
    // خروجی weekday کوتاه en → ایندکس هفتهٔ فارسی (شنبه = 0)، مسیر پشتیبان
    var EN_WD_TO_INDEX = { Sun: 1, Mon: 2, Tue: 3, Wed: 4, Thu: 5, Fri: 6, Sat: 0 };

    var state = {
        offsetMs: 0,      // سرور − کلاینت؛ تا قبل از اولین sync موفق صفر است
        lastSync: null,   // یعنی حالت اضطراری: ساعت محلیِ دستگاه
        source: null,
        failed: false
    };

    function faNum(value) {
        return String(value).replace(/[0-9]/g, function (d) {
            return '۰۱۲۳۴۵۶۷۸۹'[+d];
        });
    }

    function toAsciiDigits(value) {
        return String(value).replace(/[۰-۹]/g, function (c) {
            return String('۰۱۲۳۴۵۶۷۸۹'.indexOf(c));
        });
    }

    function ts(d) {
        return (d instanceof Date) ? d.getTime() : d;
    }

    /* ---------- formatterها (ساخت تک‌باره) ---------- */
    var persianFmt = null;       // fa-IR-u-ca-persian (مسیر اصلی)
    var persianEnFmt = null;     // en-u-ca-persian  (پشتیبان: ارقام لاتین)
    var clockFmt = null;         // fa-IR ساعت ۲۴ ساعته
    var gregorianFmt = null;     // en-US میلادی عددی (قطعه‌های میلادی)

    function tryFormat(locale, opts) {
        try {
            return new Intl.DateTimeFormat(locale, opts);
        } catch (e) {
            return false;
        }
    }

    function ensureFormatters() {
        if (persianFmt === null) {
            persianFmt = tryFormat('fa-IR-u-ca-persian', {
                timeZone: TIME_ZONE, year: 'numeric', month: 'long',
                day: 'numeric', weekday: 'long'
            });
        }
        if (persianEnFmt === null) {
            persianEnFmt = tryFormat('en-u-ca-persian', {
                timeZone: TIME_ZONE, year: 'numeric', month: 'numeric',
                day: 'numeric', weekday: 'short'
            });
        }
        if (clockFmt === null) {
            clockFmt = tryFormat('fa-IR', {
                timeZone: TIME_ZONE, hour: '2-digit', minute: '2-digit',
                second: '2-digit', hourCycle: 'h23'
            });
        }
        if (gregorianFmt === null) {
            gregorianFmt = tryFormat('en-US', {
                timeZone: TIME_ZONE, year: 'numeric', month: 'numeric',
                day: 'numeric'
            });
        }
    }

    function collect(fmt, value) {
        var out = {};
        try {
            fmt.formatToParts(value).forEach(function (p) {
                if (p.type !== 'literal') out[p.type] = p.value;
            });
        } catch (e) {
            return null;
        }
        return out;
    }

    /**
     * قطعه‌های تاریخ به فارسی:
     *   {day:'۲۱', month:'مهر', year:'۱۴۰۵', weekday:'سه‌شنبه'}
     * مسیر اصلی: fa-IR-u-ca-persian (اعتبارسنجی: نام ماه باید فارسی باشد).
     * پشتیبان:  en-u-ca-persian + فهرست سرور (ارقام فارسی می‌شوند).
     */
    function dateParts(d) {
        ensureFormatters();
        var value = ts(d);

        if (persianFmt) {
            var p = collect(persianFmt, value);
            // اعتبارسنجی اینکه واقعاً تقویم فارسی بوده (نه سقوط بی‌صدا به میلادی)
            if (p && p.year && p.month && p.day && p.weekday &&
                    MONTHS.indexOf(p.month) !== -1) {
                return p;
            }
        }
        if (!persianEnFmt) return null;
        var f = collect(persianEnFmt, value);
        if (!f || !f.year || !f.month || !f.day) return null;
        var monthNum = +f.month;
        if (!(monthNum >= 1 && monthNum <= 12)) return null;
        var idx = EN_WD_TO_INDEX[f.weekday];
        return {
            day: faNum(+f.day),
            month: MONTHS[monthNum - 1],
            year: faNum(+f.year),
            weekday: WEEKDAYS[idx === undefined ? 0 : idx]
        };
    }

    function clockParts(d) {
        ensureFormatters();
        if (!clockFmt) return null;
        var p = collect(clockFmt, ts(d));
        if (!p || p.hour === undefined) return null;
        return p;
    }

    /**
     * قطعه‌های عددی جلالیِ امروز (بدون هیچ محاسبهٔ دستی — Task 3):
     *   {year:1405, month:7, day:23, weekdayIndex:5}
     * weekdayIndex مثل فهرست سرور: شنبه=۰ … جمعه=۶
     */
    function jalaliParts(d) {
        ensureFormatters();
        if (!persianEnFmt) return null;
        var f = collect(persianEnFmt, ts(d));
        if (!f || !f.year || !f.month || !f.day) return null;
        var year = parseInt(String(f.year).replace(/[^0-9۰-۹-]/g, '')
                            .replace(/[۰-۹]/g, function (c) {
                                return String('۰۱۲۳۴۵۶۷۸۹'.indexOf(c));
                            }), 10);
        var month = parseInt(toAsciiDigits(f.month), 10);
        var day = parseInt(toAsciiDigits(f.day), 10);
        var idx = EN_WD_TO_INDEX[f.weekday];
        if (isNaN(year) || isNaN(month) || isNaN(day) ||
                !(month >= 1 && month <= 12) || !(day >= 1 && day <= 31)) {
            return null;
        }
        return { year: year, month: month, day: day,
                 weekdayIndex: idx === undefined ? 0 : idx };
    }

    /** قطعه‌های عددی میلادی به وقت تهران: {year, month, day} */
    function gregorianParts(d) {
        ensureFormatters();
        if (!gregorianFmt) return null;
        var f = collect(gregorianFmt, ts(d));
        if (!f || !f.year || !f.month || !f.day) return null;
        return { year: +f.year, month: +f.month, day: +f.day };
    }

    /** «۲۰۲۶-۱۰-۱۵» لاتین (ISO) برای تطبیق due_date سرور */
    function gregorianIso(d) {
        var g = gregorianParts(d);
        if (!g) return null;
        function pad(n) { return (n < 10 ? '0' : '') + n; }
        return g.year + '-' + pad(g.month) + '-' + pad(g.day);
    }

    /** «۲۱ مهر ۱۴۰۵» — دقیقاً مثل jalali_text سرور */
    function formatDate(d) {
        var p = dateParts(d);
        if (!p) return null;
        return p.day + ' ' + p.month + ' ' + p.year;
    }

    /** «سه‌شنبه» */
    function formatWeekday(d) {
        var p = dateParts(d);
        return p ? p.weekday : null;
    }

    /** «سه‌شنبه ۲۱ مهر ۱۴۰۵» */
    function formatFull(d) {
        var p = dateParts(d);
        if (!p) return null;
        return p.weekday + ' ' + p.day + ' ' + p.month + ' ' + p.year;
    }

    /** «۰۳:۴۵:۱۲» — ۲۴ ساعته به وقت تهران با ارقام فارسی */
    function formatClock(d) {
        var p = clockParts(d);
        if (!p) return null;
        var hour = String(p.hour);
        var minute = String(p.minute);
        var second = String(p.second);
        if (/^[0-9]+$/.test(hour)) {         // خروجی لاتین (ICU محدود) → فارسی
            hour = faNum(hour); minute = faNum(minute); second = faNum(second);
        }
        if (hour === '۲۴' || hour === '24') {  // h24 بعضی ICUها → استاندارد ۰۰..۲۳
            hour = (hour === '24') ? '00' : '۰۰';
        }
        return hour + ':' + minute + ':' + second;
    }

    /** میلی‌ثانیه تا نیمه‌شب دقیق تهران (زمان‌بندی تغییر روز) */
    function msUntilTehranMidnight(d) {
        var p = clockParts(d);
        if (!p) return null;
        var hour = parseInt(toAsciiDigits(p.hour), 10);
        var minute = parseInt(toAsciiDigits(p.minute), 10);
        var second = parseInt(toAsciiDigits(p.second), 10);
        if (isNaN(hour) || isNaN(minute) || isNaN(second)) return null;
        var elapsed = (hour * 3600 + minute * 60 + second) * 1000;
        var ms = ts(d) % 1000;
        if (ms < 0) ms += 1000;      // کسر ثانیه در هر timezone یکسان است
        elapsed += ms;
        return Math.max(1, 86400000 - elapsed);
    }

    /** زمان اعتمادشده = ساعت دستگاه + offset سرور */
    function now() {
        return new Date(Date.now() + state.offsetMs);
    }

    /**
     * دریافت offset از سرور (غیر bloک‌کننده؛ خطا هرگز صفحه را نمی‌شکند).
     * نیمهٔ دوم RTT جبران می‌شود: لحظهٔ سرور ≈ وسط بازهٔ درخواست.
     * اگر شکست بخورد offset آخرین sync موفق باقی می‌ماند (در ابتدا صفر
     * یعنی حالت اضطراری: ساعت محلیِ دستگاه).
     */
    function sync(url) {
        var t0 = Date.now();
        return fetch(url || '/api/now', {
            cache: 'no-store',
            headers: { 'Accept': 'application/json' }
        }).then(function (resp) {
            if (!resp.ok) throw new Error('HTTP ' + resp.status);
            return resp.json();
        }).then(function (data) {
            var t1 = Date.now();
            if (typeof data.epoch_ms !== 'number') throw new Error('bad payload');
            state.offsetMs = data.epoch_ms - ((t0 + t1) / 2);
            state.lastSync = new Date().toISOString();
            state.source = (data.clock && data.clock.source) || null;
            state.failed = false;
            return data;
        }).catch(function (err) {
            state.failed = true;
            throw err;
        });
    }

    return {
        TIME_ZONE: TIME_ZONE,
        WEEKDAYS: WEEKDAYS,
        MONTHS: MONTHS,
        now: now,
        formatDate: formatDate,
        formatWeekday: formatWeekday,
        formatFull: formatFull,
        formatClock: formatClock,
        jalaliParts: jalaliParts,
        gregorianParts: gregorianParts,
        gregorianIso: gregorianIso,
        msUntilTehranMidnight: msUntilTehranMidnight,
        sync: sync,
        getState: function () { return Object.assign({}, state); },
        setOffsetMs: function (v) { state.offsetMs = v; }   // برای تست
    };
}));
