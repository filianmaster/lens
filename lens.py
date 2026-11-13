"""
Lens 2.8 — экранный переводчик с прозрачным изменяемым overlay.
Windows 10/11. OCR: Tesseract (в комплекте), 9 языков, авто/ручной режим.
Перевод: GoogleTranslator (требуется интернет).
"""
import sys, os, re, json, hashlib, threading, subprocess, tempfile, shutil, time
from pathlib import Path
from datetime import datetime
from html import escape
from concurrent.futures import ThreadPoolExecutor

if sys.platform != "win32":
    raise SystemExit("Lens работает только в Windows 10/11.")

import mss
import pytesseract
from pytesseract import Output
from PIL import Image, ImageFilter, ImageEnhance, ImageStat, ImageChops, ImageOps
from deep_translator import GoogleTranslator
from langdetect import detect, detect_langs, DetectorFactory
from langdetect.lang_detect_exception import LangDetectException

from PySide6.QtCore import QObject, QPointF, QRectF, Qt, QTimer, Signal, QSettings
from PySide6.QtGui import QColor, QFont, QFontMetrics, QImage, QPainter, QPainterPath, QPen, QIcon
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QLabel,
    QPushButton, QComboBox, QSlider, QTableWidget, QTableWidgetItem,
    QHeaderView, QTabWidget, QGroupBox, QLineEdit, QFrame, QGridLayout,
    QMessageBox, QAbstractItemView, QSizePolicy, QTextEdit
)

DetectorFactory.seed = 0

APP_DIR = Path(getattr(sys, "_MEIPASS", Path(__file__).resolve().parent))
if getattr(sys, "frozen", False):
    APP_DIR = Path(sys._MEIPASS)
TESS_DIR = APP_DIR / "tesseract"
TESS_EXE = TESS_DIR / "tesseract.exe"
TESSDATA = TESS_DIR / "tessdata"
if TESS_EXE.exists():
    pytesseract.pytesseract.tesseract_cmd = str(TESS_EXE)
if TESSDATA.exists():
    # Tesseract 4/5: TESSDATA_PREFIX указывает прямо на папку с *.traineddata.
    # Путь передаём через переменную окружения, а не через --tessdata-dir:
    # на Windows pytesseract оставляет кавычки частью пути, и Tesseract не находит файлы.
    os.environ["TESSDATA_PREFIX"] = str(TESSDATA)
os.environ.setdefault("OMP_THREAD_LIMIT", "1")

# key: UI key; values: display name, Tesseract model, Google Translate code, langdetect code
LANGS = {
    "auto": ("Автоопределение", "", "", ""),
    "en": ("English", "eng", "en", "en"),
    "ru": ("Русский", "rus", "ru", "ru"),
    "uk": ("Українська", "ukr", "uk", "uk"),
    "ja": ("日本語", "jpn", "ja", "ja"),
    "zh-CN": ("中文（简体）", "chi_sim", "zh-CN", "zh-cn"),
    "ko": ("한국어", "kor", "ko", "ko"),
    "de": ("Deutsch", "deu", "de", "de"),
    "fr": ("Français", "fra", "fr", "fr"),
    "es": ("Español", "spa", "es", "es"),
}
OCR_LANGS = "+".join(v[1] for k, v in LANGS.items() if k != "auto")
DETECT_TO_KEY = {v[3]: k for k, v in LANGS.items() if k != "auto"}
BLUR_LEVELS = {"Слабый": 0.25, "Средний": 0.5, "Сильный": 0.9}
POOL = ThreadPoolExecutor(max_workers=4)
_cache = {}
_cache_lock = threading.Lock()
LOG_FILE = Path(os.getenv("APPDATA", str(Path.home()))) / "Lens" / "lens_error.log"
HISTORY_FILE = Path(os.getenv("APPDATA", str(Path.home()))) / "Lens" / "history.json"

class RateLimited(Exception):
    """Google временно ограничил число запросов."""

MIN_GAP = 0.3          # минимальная пауза между запросами к Google, сек
BATCH_CHARS = 5000     # длина одного запроса (в URL-кодировке)
BATCH_ITEMS = 20       # максимум абзацев в одном запросе
MAX_BLOCKS = 40        # максимум абзацев на один кадр
_net_lock = threading.Lock()
_last_request = [0.0]
_cooldown = {"until": 0.0, "fails": 0}
_backends_order = ["google", "deep"]

def cooldown_left():
    return max(0.0, _cooldown["until"] - time.monotonic())

def _rate_message():
    return f"Google временно ограничил запросы — жду {int(cooldown_left()) + 1} с и повторю"

def _is_rate_limit(exc):
    return (getattr(exc, "code", None) in (429, 503)
            or type(exc).__name__ == "TooManyRequests"
            or "too many requests" in str(exc).lower())

def _translate_gtx(text, src, dst):
    import urllib.request, urllib.parse
    query = urllib.parse.urlencode({"client": "gtx", "sl": src, "tl": dst, "dt": "t", "q": text})
    req = urllib.request.Request("https://translate.googleapis.com/translate_a/single?" + query,
                                 headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=8) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return "".join(part[0] for part in data[0] if part and part[0])

def _translate_deep(text, src, dst):
    return GoogleTranslator(source=src, target=dst).translate(text)

def _fit(text, limit=BATCH_CHARS):
    import urllib.parse
    text = " ".join(text.split())
    while len(urllib.parse.quote(text)) > limit and len(text) > 20:
        text = text[: len(text) * 2 // 3]
    return text

def _google_text(text, src, dst):
    """Один запрос к переводчику (с паузой между запросами и запасным каналом)."""
    funcs = {"google": _translate_gtx, "deep": _translate_deep}
    order = list(_backends_order)
    errors, limited = [], 0
    for name in order:
        if cooldown_left() > 0:
            raise RateLimited(_rate_message())
        try:
            with _net_lock:
                wait = MIN_GAP - (time.monotonic() - _last_request[0])
                if wait > 0:
                    time.sleep(wait)
                try:
                    out = funcs[name](text, src, dst)
                finally:
                    _last_request[0] = time.monotonic()
        except Exception as exc:
            if _is_rate_limit(exc):
                limited += 1
            errors.append(f"{name}: {type(exc).__name__}: {str(exc)[:90]}")
            continue
        if out and out.strip():
            _cooldown["fails"] = 0
            if _backends_order[0] != name:
                _backends_order.remove(name)
                _backends_order.insert(0, name)
            return out
        errors.append(f"{name}: пустой ответ")
    if limited == len(order):
        _cooldown["fails"] = min(_cooldown["fails"] + 1, 4)
        _cooldown["until"] = time.monotonic() + min(120, 10 * 2 ** (_cooldown["fails"] - 1))
        raise RateLimited(_rate_message())
    raise RuntimeError("; ".join(errors))

def _chunks(items):
    cur, size = [], 0
    for text in items:
        import urllib.parse
        n = len(urllib.parse.quote(text)) + 3
        if cur and (size + n > BATCH_CHARS or len(cur) >= BATCH_ITEMS):
            yield cur
            cur, size = [], 0
        cur.append(text)
        size += n
    if cur:
        yield cur

def _translate_chunk(chunk, src, dst):
    if len(chunk) == 1:
        return [_google_text(chunk[0], src, dst).strip()]
    text = _google_text("\n".join(chunk), src, dst)   # все абзацы одним запросом
    parts = [x.strip() for x in text.split("\n")]
    while len(parts) > len(chunk) and not parts[-1]:
        parts.pop()
    if len(parts) == len(chunk) and all(parts):
        return parts
    return [_google_text(t, src, dst).strip() for t in chunk]   # строки склеились — переводим по одной

def translate_many(texts, src, dst):
    """Переводит список абзацев минимальным числом запросов; повторы берёт из кэша."""
    norm = [_fit(t) for t in texts]
    out = [None] * len(norm)
    pending = {}
    for i, t in enumerate(norm):
        if not t or src == dst:
            out[i] = t
            continue
        with _cache_lock:
            hit = _cache.get((t, src, dst))
        if hit is not None:
            out[i] = hit
        else:
            pending.setdefault(t, []).append(i)
    for chunk in _chunks(list(pending)):
        for t, tr in zip(chunk, _translate_chunk(chunk, src, dst)):
            with _cache_lock:
                if len(_cache) > 5000:
                    _cache.clear()
                _cache[(t, src, dst)] = tr
            for i in pending[t]:
                out[i] = tr
    return out

def translate_one(text, src, dst):
    return translate_many([text], src, dst)[0]

def check_translation(bridge):
    try:
        bridge.net.emit(True, translate_one("Hello, world", "en", "ru"))
    except Exception as exc:
        bridge.net.emit(False, str(exc)[:400])

def detect_language(text):
    try:
        detected = detect(text)
        return DETECT_TO_KEY.get(detected, "en")
    except LangDetectException:
        return "en"

def _weird_word(word):
    """Слово похоже на кириллицу, прочитанную латинской моделью: npAMo, TeKCT, Nogcka3ka."""
    core = "".join(ch for ch in word if ch.isalnum())
    if sum(ch.isalpha() for ch in core) >= 2 and any(ch.isdigit() for ch in core):
        return True
    for i in range(1, len(core)):
        if core[i-1].islower() and core[i].isupper():
            nxt = core[i+1] if i + 1 < len(core) else ""
            if not nxt or nxt.isupper():       # YouTube, iPhone — нормально; aKH, kcT — нет
                return True
    return False

def looks_like_garbage(words):
    weird = sum(_weird_word(w) for w in words)
    if len(words) == 1:
        return weird == 1
    return weird >= 2 and weird / len(words) >= 0.4

LINE_MIN_CONF = 58.0    # средняя уверенность строки; настоящий текст даёт 75–95, чужой алфавит ~40

LATIN_MODELS = ("eng", "deu", "fra", "spa")
_scale_hint = {"h": None}      # типичная высота слова на экране (px): по ней подбираем масштаб

def _median(values):
    values = sorted(values)
    return values[len(values) // 2] if values else 0

def choose_scale(img):
    h = _scale_hint["h"]
    if h is None:
        scale = 1.5 if max(img.size) < 1500 else 1.0
    elif h >= 20:
        scale = 1.0            # крупный текст — увеличивать незачем, так быстрее
    elif h >= 14:
        scale = 1.5
    else:
        scale = 2.0            # мелкий текст — чуть крупнее, чтобы точнее читался
    return max(1.0, min(scale, 3200 / max(img.size)))

def _prepare(img, scale):
    gray = img.convert("L")
    if ImageStat.Stat(gray).mean[0] < 110:
        gray = ImageOps.invert(gray)      # тёмная тема: Tesseract читает быстрее и точнее на светлом фоне
    if scale != 1:
        gray = gray.resize((max(1, int(gray.width * scale)), max(1, int(gray.height * scale))), Image.LANCZOS)
    return ImageEnhance.Contrast(gray).enhance(1.18)

def _read_words(work, model):
    data = pytesseract.image_to_data(work, lang=model, config="--oem 1 --psm 11",
                                     output_type=Output.DICT, timeout=15)
    words = []
    for i, text in enumerate(data["text"]):
        text = (text or "").strip()
        if not text:
            continue
        try:
            conf = float(data["conf"][i])
        except (ValueError, TypeError):
            continue
        if conf < 15:
            continue
        words.append({"t": text, "c": conf, "x": data["left"][i], "y": data["top"][i],
                      "w": data["width"][i], "h": data["height"][i]})
    return words

def _fix_word(text, model):
    if model == "eng":
        if text == "|":
            return "I"                         # «I» часто читается как палка
        if len(text) > 1 and text[0] == "|" and text[1].islower():
            return "I" + text[1:]              # |t's → It's
    return text

def _make_row(words):
    return {"words": words, "h": _median([w["h"] for w in words]),
            "x0": min(w["x"] for w in words), "y0": min(w["y"] for w in words),
            "x1": max(w["x"] + w["w"] for w in words), "y1": max(w["y"] + w["h"] for w in words)}

def build_rows(words):
    """Собирает слова в визуальные строки по координатам (не доверяя разбиению Tesseract).
    Сначала горизонтальные полосы по высоте центра слов, потом разрез полосы по широким пробелам (колонки)."""
    if not words:
        return []
    mh = _median([w["h"] for w in words]) or 10
    tol = 0.55 * mh
    bands = []
    for w in sorted(words, key=lambda w: w["y"] + w["h"] / 2):
        cy = w["y"] + w["h"] / 2
        if bands and abs(cy - bands[-1]["cy"]) <= tol:
            band = bands[-1]
            n = len(band["words"])
            band["words"].append(w)
            band["cy"] = (band["cy"] * n + cy) / (n + 1)
        else:
            bands.append({"words": [w], "cy": cy})
    rows = []
    for band in bands:
        ordered = sorted(band["words"], key=lambda w: w["x"])
        current = [ordered[0]]
        for w in ordered[1:]:
            if w["x"] - max(x["x"] + x["w"] for x in current) > 3.5 * mh:
                rows.append(_make_row(current))      # широкий пробел — это уже другая колонка
                current = [w]
            else:
                current.append(w)
        rows.append(_make_row(current))
    return rows

def rows_to_lines(rows, model, scale):
    lines, confs = [], []
    gate = 45.0 if model in ("jpn", "chi_sim", "kor") else LINE_MIN_CONF
    for r in rows:
        ws = sorted(r["words"], key=lambda w: w["x"])
        tokens = [_fix_word(w["t"], model) for w in ws]
        tokens = [t for t in tokens if any(ch.isalnum() for ch in t) or t not in "|¦_~^`\\/"]
        if not tokens:
            continue
        if sum(w["c"] for w in ws) / len(ws) < gate:
            continue                        # строка распознана неуверенно — скорее всего это другой алфавит
        if model in LATIN_MODELS and looks_like_garbage(tokens):
            continue                        # кириллица, прочитанная латинской моделью
        text = " ".join(tokens)
        if model in ("jpn", "chi_sim"):
            text = text.replace(" ", "")
        if not any(ch.isalpha() for ch in text):
            continue
        confs.extend(w["c"] for w in ws)
        lines.append((text, int(r["x0"] / scale), int(r["y0"] / scale), int(r["x1"] / scale), int(r["y1"] / scale)))
    return lines, confs

def _ocr_one(img, model, scale=None):
    scale = scale or choose_scale(img)
    words = _read_words(_prepare(img, scale), model)
    lines, confs = rows_to_lines(build_rows(words), model, scale)
    chars = sum(len(x[0]) for x in lines)
    score = (sum(confs) / len(confs)) * min(1.0, chars / 24) if confs else 0.0
    if lines and score >= 60:
        _scale_hint["h"] = _median([w["h"] / scale for w in words])
    return lines, score

# ---- определение языка: сначала алфавит по небольшому куску текста, потом язык внутри алфавита
LANG_GROUPS = (("en", "de", "fr", "es"), ("ru", "uk"))   # языки с одним алфавитом уточняем по тексту
SCRIPT_REPS = ("en", "ru", "ja", "zh-CN", "ko")          # по одному представителю на алфавит
AUTO_ACCEPT = 62.0      # если запомненный язык дал такую уверенность — определение заново не нужно
AUTO_HINT_TTL = 15.0    # раз в столько секунд язык определяется заново
DETECT_MIN = 40.0
_auto_hint = {"key": None, "time": 0.0}
_hint_lock = threading.Lock()

def reset_auto_hint():
    with _hint_lock:
        _auto_hint["key"] = None

def _set_hint(key):
    with _hint_lock:
        _auto_hint["key"] = key
        _auto_hint["time"] = time.monotonic()

def refine_language(key, lines):
    text = "\n".join(line[0] for line in lines)
    if key in ("ja", "zh-CN"):
        if re.search(r"[\u3040-\u30ff]", text):
            return "ja"                              # есть кана — это японский
        if re.search(r"[\u4e00-\u9fff]", text):
            return "zh-CN"
        return key
    for group in LANG_GROUPS:
        if key in group:
            if sum(ch.isalpha() for ch in text) < 30:
                return key                           # слишком мало текста, чтобы спорить с моделью
            try:
                top = detect_langs(text)[0]
                if top.prob >= 0.85 and DETECT_TO_KEY.get(top.lang) in group:
                    return DETECT_TO_KEY[top.lang]
            except Exception:
                pass
            return key
    return key

def pick_text_crop(img, max_w=520, max_h=170):
    """Самый «текстовый» кусок кадра (по плотности границ) — на нём быстро определяем алфавит."""
    if img.width <= max_w and img.height <= max_h:
        return img
    edges = img.convert("L").filter(ImageFilter.FIND_EDGES)
    best, best_box = -1.0, (0, 0, min(img.width, max_w), min(img.height, max_h))
    sx, sy = max(1, max_w // 2), max(1, max_h // 2)
    y = 0
    while True:
        y0 = min(y, max(0, img.height - max_h))
        x = 0
        while True:
            x0 = min(x, max(0, img.width - max_w))
            box = (x0, y0, min(img.width, x0 + max_w), min(img.height, y0 + max_h))
            value = ImageStat.Stat(edges.crop(box)).mean[0]
            if value > best:
                best, best_box = value, box
            if x0 + max_w >= img.width:
                break
            x += sx
        if y0 + max_h >= img.height:
            break
        y += sy
    return img.crop(best_box)

def detect_script(img, whole=False):
    """Возвращает ключ языка-представителя алфавита или None, если читаемого текста нет."""
    sample = img if whole else pick_text_crop(img)
    def run(k):
        try:
            lines, score = _ocr_one(sample, LANGS[k][1], scale=1.0 if whole else 1.5)
        except Exception:
            return k, [], -1.0
        return k, lines, score
    best_key, best_score = None, DETECT_MIN
    for k, lines, score in POOL.map(run, SCRIPT_REPS):
        if lines and score > best_score:
            best_key, best_score = k, score
    return best_key

def guess_language(img):
    return detect_script(img) or detect_script(img, whole=True)

def _finalize(img, key, lines, score):
    """Уточняет язык внутри алфавита; при необходимости перечитывает точной моделью."""
    refined = refine_language(key, lines)
    if refined != key:
        try:
            lines2, score2 = _ocr_one(img, LANGS[refined][1])
            if lines2 and score2 >= score - 3:
                lines, key = lines2, refined
        except Exception:
            pass
    _set_hint(key)
    return lines, key

def ocr_lines(img, src_key):
    if src_key != "auto":
        lines, _ = _ocr_one(img, LANGS[src_key][1])
        return lines, src_key
    with _hint_lock:
        hint, stamp = _auto_hint["key"], _auto_hint["time"]
    if hint and time.monotonic() - stamp < AUTO_HINT_TTL:
        try:
            lines, score = _ocr_one(img, LANGS[hint][1])
        except Exception:
            lines, score = [], -1.0
        if lines and score >= AUTO_ACCEPT:
            return _finalize(img, hint, lines, score)
    key = guess_language(img)
    if key is None:
        _set_hint(None)
        return [], "en"
    lines, score = _ocr_one(img, LANGS[key][1])
    if not lines:
        _set_hint(None)
        return [], key
    return _finalize(img, key, lines, score)

# ---- абзацы
def join_parts(parts):
    out = ""
    for part in parts:
        if out.endswith("-") and len(out) > 1 and out[-2].isalpha() and part[:1].islower():
            out = out[:-1] + part                    # перенос слова: inter- + national → international
        else:
            out = (out + " " + part) if out else part
    return out

def group_lines(lines):
    groups = []
    for text, x0, y0, x1, y1 in sorted(lines, key=lambda l: (l[2], l[1])):
        lh = max(1, y1 - y0)
        match = None
        for g in groups:
            glh = max(1, g["h"] / len(g["parts"]))
            gap = y0 - g["y1"]
            overlap = min(x1, g["x1"]) - max(x0, g["x0"])
            narrow = max(1, min(x1 - x0, g["x1"] - g["x0"]))
            if overlap < 0.3 * narrow:
                continue                             # другая колонка
            if -0.6 * glh <= gap <= 0.9 * glh and abs(lh - glh) <= 0.6 * glh:   # близко и тот же размер шрифта
                match = g
                break
        if match:
            match["parts"].append(text)
            match["h"] += y1 - y0
            match["x0"], match["y0"] = min(match["x0"], x0), min(match["y0"], y0)
            match["x1"], match["y1"] = max(match["x1"], x1), max(match["y1"], y1)
        else:
            groups.append({"parts": [text], "h": y1 - y0, "x0": x0, "y0": y0, "x1": x1, "y1": y1})
    return drop_overlaps(groups)

def drop_overlaps(groups):
    """Плашки не должны лежать друг на друге: мелкие, почти целиком внутри крупной, убираем."""
    def area(g):
        return max(1, g["x1"] - g["x0"]) * max(1, g["y1"] - g["y0"])
    kept = []
    for g in sorted(groups, key=area, reverse=True):
        a = area(g)
        dup = False
        for k in kept:
            ix = min(g["x1"], k["x1"]) - max(g["x0"], k["x0"])
            iy = min(g["y1"], k["y1"]) - max(g["y0"], k["y0"])
            if ix > 0 and iy > 0 and ix * iy > 0.5 * a:
                dup = True
                break
        if not dup:
            kept.append(g)
    return sorted(kept, key=lambda g: (g["y0"], g["x0"]))

def wrap(text, fm, width):
    out = []
    for para in text.split("\n"):
        cur = ""
        for word in para.split(" "):
            trial = word if not cur else cur + " " + word
            if fm.horizontalAdvance(trial) <= width:
                cur = trial
                continue
            if cur:
                out.append(cur); cur = ""
            while fm.horizontalAdvance(word) > width and len(word) > 1:
                n = len(word)
                while n > 1 and fm.horizontalAdvance(word[:n]) > width:
                    n -= 1
                out.append(word[:n]); word = word[n:]
            cur = word
        out.append(cur)
    return out

def text_layout(text, width, height, start_px):
    font = QFont("Segoe UI")
    font.setWeight(QFont.Weight.Medium)
    start = max(13, min(start_px, 26))
    for px in range(start, 10, -1):
        font.setPixelSize(px)
        fm = QFontMetrics(font)
        lines = wrap(text, fm, max(30, width))
        if len(lines) * fm.lineSpacing() <= max(12, height):
            break
    return font, lines, fm.lineSpacing(), fm.ascent()

class Bridge(QObject):
    done = Signal(object)
    history_add = Signal(str, str, str)
    net = Signal(bool, str)
    working = Signal(bool)

def grab_region(rect):
    left, top, right, bottom = rect
    with mss.mss() as sct:
        shot = sct.grab({"left": left, "top": top, "width": right - left, "height": bottom - top})
    return Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")

def set_capture_exclusion(hwnd):
    """True, если Windows подтвердила, что окно не попадает в снимки экрана (Windows 10 2004+)."""
    try:
        import ctypes
        from ctypes import wintypes
        user32 = ctypes.WinDLL("user32")
        user32.SetWindowDisplayAffinity.argtypes = [wintypes.HWND, wintypes.DWORD]
        user32.SetWindowDisplayAffinity.restype = wintypes.BOOL
        user32.GetWindowDisplayAffinity.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
        user32.GetWindowDisplayAffinity.restype = wintypes.BOOL
        if not user32.SetWindowDisplayAffinity(hwnd, 0x11):      # WDA_EXCLUDEFROMCAPTURE
            return False
        value = wintypes.DWORD(0)
        return bool(user32.GetWindowDisplayAffinity(hwnd, ctypes.byref(value))) and value.value == 0x11
    except Exception:
        return False

def scan(bridge, rect, src, dst, blur_k, last_sig, generation, img=None, prev_thumb=None):
    result = {"gen": generation, "blocks": [], "sig": last_sig, "same": False, "error": None, "info": None, "size": (1, 1), "thumb": None}
    try:
        left, top, right, bottom = rect
        width, height = right-left, bottom-top
        result["size"] = (width, height)
        if width < 35 or height < 35:
            return
        if cooldown_left() > 0:
            result["error"] = _rate_message()
            return
        if img is None:
            img = grab_region(rect)
        sig = hashlib.md5(img.tobytes()).hexdigest()
        result["sig"] = sig
        if sig == last_sig:
            result["same"] = True
            return
        thumb = img.convert("L").resize((48, 27)).tobytes()
        result["thumb"] = thumb
        big = (prev_thumb is None or len(prev_thumb) != len(thumb)
               or sum(abs(x - y) for x, y in zip(prev_thumb, thumb)) / len(thumb) > 5.0)
        bridge.working.emit(big)      # big=True — картинка под линзой сильно изменилась (прокрутка, другая страница)
        try:
            lines, actual_src = ocr_lines(img, src)
        except Exception as exc:
            result["error"] = f"Ошибка OCR: {exc}"
            return
        if not lines:
            hint = ""
            if src != "auto":
                hint = f". Проверьте «Язык на экране» (сейчас: {LANGS[actual_src][0]})"
                try:                                   # посмотрим, не другой ли язык на экране
                    sweep_key = guess_language(img)
                    if sweep_key and sweep_key != src:
                        hint = f". Похоже, на экране: {LANGS[sweep_key][0]} — выберите его или «Автоопределение»"
                except Exception:
                    pass
            result["info"] = "Текст не найден" + hint
            return
        groups = group_lines(lines)
        if actual_src == dst:
            result["info"] = "Текст уже на выбранном языке"
            return
        # При автоопределении исходный язык для перевода определяет сам Google — он точнее, чем догадка по тексту OCR.
        src_code, dst_code = ("auto" if src == "auto" else LANGS[actual_src][2]), LANGS[dst][2]
        jobs = []
        for g in groups[:MAX_BLOCKS]:
            original = join_parts(g["parts"])[:3000]
            if sum(c.isalpha() for c in original) >= 3:
                jobs.append((g, original))
        if not jobs:
            return
        try:
            translations = translate_many([o for _, o in jobs], src_code, dst_code)
        except RateLimited as exc:
            result["error"] = str(exc)
            return
        except Exception as exc:
            result["error"] = f"Ошибка перевода: проверьте интернет. ({str(exc)[:220]})"
            return
        for (g, original), translated in zip(jobs, translations):
            bridge.history_add.emit(original, translated, actual_src)
            line_h = max(12, g["h"] / len(g["parts"]))
            pad = int(line_h * 0.32)
            box = (max(0,g["x0"]-pad), max(0,g["y0"]-pad),
                   min(width,g["x1"]+pad), min(height,g["y1"]+pad))
            patch = img.crop(box).filter(ImageFilter.GaussianBlur(max(2.0,line_h*blur_k))).convert("RGBA")
            qimg = QImage(patch.tobytes(),patch.width,patch.height,patch.width*4,QImage.Format.Format_RGBA8888).copy()
            avg = tuple(int(v) for v in ImageStat.Stat(patch.convert("RGB")).mean)
            dark = (0.299*avg[0] + 0.587*avg[1] + 0.114*avg[2]) < 128
            result["blocks"].append({"box":box,"lh":line_h,"text":translated,"img":qimg,"avg":avg,"dark":dark})
    except Exception as exc:
        result["error"] = f"Сбой: {exc}"
    finally:
        bridge.done.emit(result)

class LensOverlay(QWidget):
    def __init__(self, main):
        super().__init__()
        self.main = main
        self.setWindowTitle("Lens — окно перевода")
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint | Qt.WindowType.Tool)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setMouseTracking(True)
        self.settle = QTimer(self)
        self.settle.setSingleShot(True)
        self.settle.setInterval(150)
        self.settle.timeout.connect(self.tick)
        self.setMinimumSize(180,90)
        self.resize(620,260)
        self.move(250,220)
        self.paused = False
        self.busy = False
        self.generation = 0
        self.last_sig = None
        self.blocks = []
        self.status = ""
        self.excluded = True          # окно не попадает в снимки экрана (проверяется calibrate())
        self.calibrated = False
        self.calib_pending = False
        self.baseline_pending = False
        self.visible_sig = None
        self.need_retry = False
        self.retry_at = 0.0
        self.working = False
        self.content_hidden = False   # True — окно рисует пустоту (на время снимка экрана)
        self._last_geom = None
        self.last_thumb = None
        self.blocks_key = None
        self.fade = 1.0
        self.fade_timer = QTimer(self)
        self.fade_timer.setInterval(16)
        self.fade_timer.timeout.connect(self.fade_step)
        self.bridge = Bridge()
        self.bridge.done.connect(self.on_result)
        self.bridge.working.connect(self.on_working)
        self.bridge.history_add.connect(self.main.add_history_entry)
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.timer.start(700)

    def showEvent(self, event):
        super().showEvent(event)
        # Окно перевода не должно попадать в снимки экрана, иначе OCR читает собственные плашки.
        ok = set_capture_exclusion(int(self.winId()))
        if not ok and not self.calibrated:
            self.excluded = False
            self.calibrated = True
            self.main.report("Этот Windows не умеет скрывать окно от снимков — включён режим скрытия на время снимка")
        elif ok and not self.calibrated:
            self.main.report("Windows подтвердил скрытие окна от снимков, проверяю…")
        if not self.calibrated:
            QTimer.singleShot(900, self.calibrate)

    def geometry_changed(self):
        g = self.geometry()
        cur = (g.x(), g.y(), g.width(), g.height())
        if cur == self._last_geom:
            return False
        self._last_geom = cur
        return True

    def moveEvent(self, event):
        super().moveEvent(event)
        if self.geometry_changed():       # только настоящее перемещение, не «эхо» системных событий
            self.reset()
            self.settle.start()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if self.geometry_changed():
            self.reset()
            self.settle.start()

    def rect_on_screen(self):
        from ctypes import wintypes
        import ctypes
        rect = wintypes.RECT()
        ctypes.windll.user32.GetWindowRect(wintypes.HWND(int(self.winId())), ctypes.byref(rect))
        return (rect.left,rect.top,rect.right,rect.bottom)

    def reset(self):
        self.generation += 1
        self.last_sig = None
        self.last_thumb = None
        self.visible_sig = None
        self.need_retry = False
        self.blocks = []
        self.blocks_key = None
        self.working = False
        self.fade = 1.0
        self.fade_timer.stop()
        self.update()

    # ---- снимок экрана без собственного окна
    def set_content_hidden(self, hidden):
        self.content_hidden = hidden
        self.repaint()                    # синхронно: окно остаётся на месте, но рисует пустоту

    def clean_capture(self, rect):
        """Снимок без плашек Lens. None — на экране ничего не изменилось."""
        vis = grab_region(rect)
        vsig = hashlib.md5(vis.tobytes()).hexdigest()
        if vsig == self.visible_sig and not self.need_retry:
            return None
        self.visible_sig = None
        self.set_content_hidden(True)
        try:
            time.sleep(0.06)              # дать Windows обновить экран
            return grab_region(rect)
        finally:
            self.set_content_hidden(False)

    def schedule_baseline(self):
        self.baseline_pending = True
        QTimer.singleShot(250, self.take_baseline)

    def take_baseline(self):
        self.baseline_pending = False
        if self.excluded or not self.isVisible():
            return
        try:
            self.visible_sig = hashlib.md5(grab_region(self.rect_on_screen()).tobytes()).hexdigest()
        except Exception:
            self.visible_sig = None

    def calibrate(self):
        """Один раз проверяет, видит ли снимок экрана наше окно: сравнивает кадр с окном и без него."""
        self.calib_pending = False
        if self.calibrated or not self.isVisible():
            return
        try:
            rect = self.rect_on_screen()
            a = grab_region(rect)
            a2 = grab_region(rect)                       # два кадра подряд — чтобы оценить «шум» (анимации на экране)
            self.set_content_hidden(True)
            try:
                time.sleep(0.06)
                b = grab_region(rect)
            finally:
                self.set_content_hidden(False)
            noise = sum(ImageStat.Stat(ImageChops.difference(a, a2)).mean)
            delta = sum(ImageStat.Stat(ImageChops.difference(a, b)).mean)
        except Exception:
            return
        if noise > 0.8:
            return                                       # под линзой что-то движется — проверим в другой раз
        if delta > max(0.8, noise * 3):
            self.excluded = False
            self.calibrated = True
            self.main.report("Окно перевода попадает в снимки экрана — включён режим скрытия на время снимка")
            self.schedule_baseline()
        elif self.blocks or self.status:
            self.excluded = True
            self.calibrated = True
            self.main.report("Окно перевода скрыто от снимков экрана — всё в порядке")

    def after_paint(self):
        if not self.calibrated:
            if (self.blocks or self.status) and not self.calib_pending:
                self.calib_pending = True
                QTimer.singleShot(300, self.calibrate)
        elif not self.excluded:
            self.schedule_baseline()

    def tick(self):
        if self.busy or self.paused or self.calib_pending or self.baseline_pending or not self.isVisible():
            return
        if QApplication.mouseButtons() & Qt.MouseButton.LeftButton:
            return
        if self.need_retry and time.monotonic() < self.retry_at:
            return
        rect = self.rect_on_screen()
        img = None
        if not self.excluded:
            try:
                img = self.clean_capture(rect)
            except Exception as exc:
                self.show_status(f"Ошибка снимка экрана: {exc}", 5000)
                return
            if img is None:
                return
        self.busy = True
        self.need_retry = False
        threading.Thread(target=scan, args=(self.bridge,rect,
            self.main.src_lang,self.main.dst_lang,self.main.blur_k,self.last_sig,self.generation,
            img,self.last_thumb),daemon=True).start()

    def on_working(self, stale):
        if self.busy:
            self.working = True
            if stale and self.blocks:      # картинка сменилась — старые плашки уже не к месту
                self.blocks = []
                self.blocks_key = None
            self.update()

    def fade_step(self):
        self.fade = min(1.0, self.fade + 0.12)
        if self.fade >= 1.0:
            self.fade_timer.stop()
        self.update()

    def on_result(self, result):
        self.busy = False
        self.working = False
        if result["gen"] != self.generation:
            if result["blocks"]:
                self.main.report("Результат отброшен: окно переместили или изменили, идёт новый перевод")
            self.update()
            return
        if result["error"]:
            self.need_retry = True
            self.retry_at = time.monotonic() + max(3.0, cooldown_left() + 0.5)
            self.show_status(result["error"], 9000)
            self.after_paint()
            return
        if result["same"]:
            self.update()
            self.after_paint()
            return
        self.last_sig = result["sig"]
        self.last_thumb = result.get("thumb")
        if result.get("info"):
            self.show_status(result["info"], 5000)
        w,h = result["size"]
        sx,sy = self.width()/max(1,w),self.height()/max(1,h)
        raw = sorted(result["blocks"], key=lambda b:(b["box"][1],b["box"][0]))
        rects = [QRectF(b["box"][0]*sx,b["box"][1]*sy,(b["box"][2]-b["box"][0])*sx,(b["box"][3]-b["box"][1])*sy) for b in raw]
        alpha = int(max(110, min(195, 195 - self.main.blur_k*90)))
        blocks=[]
        for b,patch in zip(raw,rects):
            # сколько места до ближайшей плашки ниже — чтобы длинный русский текст не наезжал на соседей
            below=[r.top() for r in rects if r.top()>patch.top()+2 and min(r.right(),patch.right())-max(r.left(),patch.left())>8]
            limit=(min(below) if below else self.height()-2)-patch.top()-2
            avail=max(patch.height(),limit)
            box=QRectF(patch)
            font,lines,ls,asc=text_layout(b["text"],box.width()-16,avail-8,int(b["lh"]*sy*.95))
            need=len(lines)*ls+10
            if need>box.height(): box.setHeight(need)
            blocks.append({"patch":patch,"box":box,"img":b["img"],"font":font,"lines":lines,"ls":ls,"asc":asc,
                           "avg":b["avg"],"dark":b["dark"],"alpha":alpha})
        key=tuple((round(x["box"].x()/4),round(x["box"].y()/4),"".join(x["lines"])) for x in blocks)
        if key!=self.blocks_key or not self.blocks:
            fade_in = (not self.blocks) and bool(blocks)
            self.blocks=blocks; self.blocks_key=key
            if fade_in:
                self.fade=0.0; self.fade_timer.start()
            elif not self.fade_timer.isActive():
                self.fade=1.0
        if blocks:
            self.main.report(f"Готово: переведено блоков — {len(blocks)}")
        self.update()
        self.after_paint()

    def show_status(self, text, ms):
        self._status_id = getattr(self, "_status_id", 0) + 1
        sid = self._status_id
        self.status = text
        self.main.report(text)
        QTimer.singleShot(ms, lambda: self.clear_status(sid))
        self.update()
        if self.calibrated and not self.excluded:
            self.schedule_baseline()

    def clear_status(self, sid=None):
        if sid is not None and sid != getattr(self, "_status_id", 0):
            return
        self.status=""
        self.update()
        if self.calibrated and not self.excluded:
            self.schedule_baseline()

    def paintEvent(self, event):
        p=QPainter(self)
        p.setRenderHints(QPainter.RenderHint.Antialiasing|QPainter.RenderHint.SmoothPixmapTransform|QPainter.RenderHint.TextAntialiasing)
        p.fillRect(self.rect(),QColor(0,0,0,2))
        if self.content_hidden:
            return
        p.setOpacity(self.fade)
        for b in self.blocks:
            box=b["box"]
            path=QPainterPath(); path.addRoundedRect(box,8,8)
            p.setClipPath(path)
            r,g,bl=b["avg"]
            p.fillRect(box,QColor(r,g,bl))                  # сплошная основа: закрывает оригинал, даже если плашка выше размытого куска
            p.drawImage(b["patch"],b["img"])                # размытый оригинал
            p.fillRect(box,QColor(8,10,16,b["alpha"]) if b["dark"] else QColor(255,255,255,b["alpha"]))
            p.setClipping(False)
            p.setBrush(Qt.BrushStyle.NoBrush); p.setPen(QPen(QColor(0,0,0,45),1))
            p.drawRoundedRect(box,8,8)
            p.setFont(b["font"]); p.setPen(QColor(246,248,255) if b["dark"] else QColor(18,22,31))
            top=box.top()+(box.height()-len(b["lines"])*b["ls"])/2
            for i,line in enumerate(b["lines"]):
                p.drawText(QPointF(box.left()+8,top+i*b["ls"]+b["asc"]),line)
        p.setOpacity(1.0)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(35,145,255,210),2))
        p.drawRoundedRect(QRectF(self.rect()).adjusted(1,1,-1,-1),8,8)
        if self.working:
            p.setFont(QFont("Segoe UI",8,QFont.Weight.Bold))
            r=QRectF(self.width()-90,self.height()-32,80,22)
            p.setPen(Qt.PenStyle.NoPen); p.setBrush(QColor(10,13,20,215)); p.drawRoundedRect(r,11,11)
            p.setPen(QColor(130,195,255)); p.drawText(QPointF(r.left()+13,r.top()+15),"перевод…")
        if self.paused or self.status:
            msg=("Ⅱ ПАУЗА" if self.paused else self.status)
            font=QFont("Segoe UI",9,QFont.Weight.Bold); p.setFont(font)
            fm=QFontMetrics(font)
            msg=fm.elidedText(msg,Qt.TextElideMode.ElideRight,max(40,self.width()-36))
            p.fillRect(QRectF(8,8,min(self.width()-16,fm.horizontalAdvance(msg)+20),26),QColor(10,13,20,220))
            p.setPen(Qt.GlobalColor.white); p.drawText(16,26,msg)

    def mouseMoveEvent(self,e):
        pos=e.position().toPoint(); edge=9
        l,r,t,b=pos.x()<=edge,pos.x()>=self.width()-edge,pos.y()<=edge,pos.y()>=self.height()-edge
        C=Qt.CursorShape
        if (l and t) or (r and b): cur=C.SizeFDiagCursor
        elif (r and t) or (l and b): cur=C.SizeBDiagCursor
        elif l or r: cur=C.SizeHorCursor
        elif t or b: cur=C.SizeVerCursor
        else: cur=C.SizeAllCursor
        self.setCursor(cur)

    def mousePressEvent(self,e):
        if e.button()!=Qt.MouseButton.LeftButton: return
        pos=e.position().toPoint(); edge=9
        flags=[(pos.x()<=edge,Qt.Edge.LeftEdge),(pos.x()>=self.width()-edge,Qt.Edge.RightEdge),
               (pos.y()<=edge,Qt.Edge.TopEdge),(pos.y()>=self.height()-edge,Qt.Edge.BottomEdge)]
        edges=[x for yes,x in flags if yes]
        handle=self.windowHandle()
        if edges:
            edge=edges[0]
            for other in edges[1:]: edge|=other
            handle.startSystemResize(edge)
        else:
            handle.startSystemMove()

    def keyPressEvent(self,e):
        if e.key()==Qt.Key.Key_Escape:
            self.hide(); self.main.update_toggle()
        elif e.key()==Qt.Key.Key_Space:
            self.paused=not self.paused; self.update()

    def contextMenuEvent(self,e):
        from PySide6.QtWidgets import QMenu
        menu=QMenu(self)
        action=menu.addAction("Снять паузу" if self.paused else "Пауза (Пробел)")
        action.triggered.connect(lambda: self.toggle_pause())
        menu.addSeparator()
        menu.addAction("Скрыть окно (Esc)").triggered.connect(lambda:(self.hide(),self.main.update_toggle()))
        menu.exec(e.globalPos())

    def toggle_pause(self):
        self.paused=not self.paused; self.update()

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Lens 2.8 — Экранный переводчик")
        self.resize(900,650)
        self.setMinimumSize(760,560)
        self.settings=QSettings("LensProject","Lens22")
        self.src_lang=self.settings.value("source","auto")
        self.dst_lang=self.settings.value("target","ru")
        self.blur_k=float(self.settings.value("blur",0.5))
        self.history=[]
        self.overlay=LensOverlay(self)
        self.build_ui()
        self.load_history()
        self.refresh_ocr_status()
        self.net_bridge=Bridge(); self.net_bridge.net.connect(self.on_net_status)
        self.check_net()

    def check_net(self):
        threading.Thread(target=check_translation,args=(self.net_bridge,),daemon=True).start()

    def on_net_status(self, ok, msg):
        if ok:
            self.net_badge.setText("Перевод работает"); self.net_badge.setToolTip("")
            self.net_badge.setStyleSheet("background:#173d32;color:#8ce3bd;padding:8px 12px;border-radius:10px;font-weight:600;")
        else:
            limit = msg.startswith("Google временно")
            self.net_badge.setText("Перевод: лимит Google" if limit else "Перевод: нет связи"); self.net_badge.setToolTip(msg)
            self.net_badge.setStyleSheet(("background:#4a3420;color:#ffd08a;" if limit else "background:#4a2028;color:#ff9ba7;")+"padding:8px 12px;border-radius:10px;font-weight:600;")
            self.report("Проверка перевода не прошла: "+msg)

    def report(self, text):
        self.diag.setText(f"Сообщения [{datetime.now().strftime('%H:%M:%S')}]: {text}")

    def build_ui(self):
        self.setStyleSheet("""
        QMainWindow,QWidget { background:#11151e; color:#e8edf7; font-family:'Segoe UI'; font-size:13px; }
        QTabWidget::pane { border:1px solid #293345; border-radius:12px; top:-1px; background:#151b27; }
        QTabBar::tab { background:#1b2331; color:#9eabc0; padding:12px 22px; margin-right:5px; border-radius:8px; }
        QTabBar::tab:selected { background:#263b59; color:#ffffff; }
        QGroupBox { border:1px solid #2a3547; border-radius:12px; margin-top:14px; padding:16px 12px 12px; font-weight:600; color:#91bfff; }
        QGroupBox::title { subcontrol-origin:margin; left:14px; padding:0 6px; }
        QLabel#muted { color:#9aa8bc; }
        QLabel#hero { font-size:24px; font-weight:700; color:#ffffff; }
        QLabel#sub { color:#9aa8bc; font-size:13px; }
        QPushButton { background:#26364d; color:#eaf2ff; border:1px solid #3b4c66; border-radius:9px; padding:10px 15px; font-weight:600; }
        QPushButton:hover { background:#314967; }
        QPushButton#launch { background:#1677e8; border:0; font-size:15px; padding:15px; }
        QPushButton#launch:hover { background:#2588f5; }
        QPushButton#launch:checked { background:#c44555; }
        QComboBox,QLineEdit { background:#0e1420; border:1px solid #344158; border-radius:8px; padding:9px; color:#f1f5fc; min-height:20px; }
        QComboBox QAbstractItemView { background:#172131; selection-background-color:#2864a5; color:white; }
        QSlider::groove:horizontal { height:6px; background:#2b3547; border-radius:3px; }
        QSlider::handle:horizontal { background:#48a0ff; width:16px; margin:-6px 0; border-radius:8px; }
        QTableWidget { background:#0e1420; alternate-background-color:#141d2b; gridline-color:#273247; border:1px solid #29364a; border-radius:9px; selection-background-color:#244c78; }
        QHeaderView::section { background:#202b3b; color:#c9d8ec; border:0; padding:10px; font-weight:600; }
        QTableWidget QTableCornerButton::section { background:#202b3b; border:0; }
        QScrollBar:vertical { background:#111824; width:10px; } QScrollBar::handle:vertical { background:#3a4a61; border-radius:5px; min-height:25px; }
        """)
        root=QWidget(); self.setCentralWidget(root)
        outer=QVBoxLayout(root); outer.setContentsMargins(24,20,24,22); outer.setSpacing(16)
        header=QHBoxLayout()
        brand=QVBoxLayout()
        title=QLabel("LENS 2.8"); title.setObjectName("hero")
        sub=QLabel("Экранный переводчик · OCR + перевод в реальном времени"); sub.setObjectName("sub")
        brand.addWidget(title); brand.addWidget(sub); header.addLayout(brand); header.addStretch()
        self.status_badge=QLabel("Проверка OCR…"); self.status_badge.setStyleSheet("background:#20344c;color:#9ecbff;padding:8px 12px;border-radius:10px;font-weight:600;")
        self.net_badge=QLabel("Перевод: проверка…"); self.net_badge.setStyleSheet("background:#20344c;color:#9ecbff;padding:8px 12px;border-radius:10px;font-weight:600;")
        badges=QVBoxLayout(); badges.setSpacing(6); badges.addWidget(self.status_badge); badges.addWidget(self.net_badge)
        header.addLayout(badges); outer.addLayout(header)

        self.tabs=QTabWidget(); outer.addWidget(self.tabs)
        control=QWidget(); lay=QVBoxLayout(control); lay.setContentsMargins(18,20,18,18); lay.setSpacing(15)
        intro=QLabel("Переводите текст прямо поверх любого окна"); intro.setObjectName("hero"); intro.setStyleSheet("font-size:19px;")
        lay.addWidget(intro)
        desc=QLabel("Изменяемая прозрачная область распознаёт текст, размывает оригинал и показывает перевод.")
        desc.setObjectName("sub"); desc.setWordWrap(True); lay.addWidget(desc)
        self.toggle_btn=QPushButton("▶  Запустить окно перевода"); self.toggle_btn.setObjectName("launch"); self.toggle_btn.setCheckable(True)
        self.toggle_btn.clicked.connect(self.toggle_overlay); lay.addWidget(self.toggle_btn)
        langs=QGroupBox("ЯЗЫКИ")
        grid=QGridLayout(langs); grid.setHorizontalSpacing(14); grid.setVerticalSpacing(10)
        grid.addWidget(QLabel("Язык на экране"),0,0); grid.addWidget(QLabel("Переводить на"),0,1)
        self.cb_src=QComboBox(); self.cb_dst=QComboBox()
        for key,val in LANGS.items():
            self.cb_src.addItem(val[0],key)
            if key!="auto": self.cb_dst.addItem(val[0],key)
        self.cb_src.setCurrentIndex(max(0,self.cb_src.findData(self.src_lang)))
        self.cb_dst.setCurrentIndex(max(0,self.cb_dst.findData(self.dst_lang)))
        self.cb_src.currentIndexChanged.connect(self.on_lang_changed); self.cb_dst.currentIndexChanged.connect(self.on_lang_changed)
        grid.addWidget(self.cb_src,1,0); grid.addWidget(self.cb_dst,1,1)
        lay.addWidget(langs)
        opts=QGroupBox("ВНЕШНИЙ ВИД И ПРОИЗВОДИТЕЛЬНОСТЬ")
        opt=QGridLayout(opts); opt.addWidget(QLabel("Размытие оригинального текста"),0,0)
        self.cb_blur=QComboBox()
        for name in BLUR_LEVELS: self.cb_blur.addItem(name)
        self.cb_blur.setCurrentIndex(1); self.cb_blur.currentIndexChanged.connect(self.on_blur_changed)
        opt.addWidget(self.cb_blur,0,1)
        opt.addWidget(QLabel("Интервал OCR"),1,0)
        self.slider=QSlider(Qt.Orientation.Horizontal); self.slider.setRange(400,2000); self.slider.setSingleStep(100); self.slider.setValue(700)
        self.interval_label=QLabel("700 мс"); self.slider.valueChanged.connect(self.on_interval); opt.addWidget(self.slider,1,1)
        opt.addWidget(self.interval_label,1,2); lay.addWidget(opts)
        hint=QLabel("Подсказка: наведите область на нужный текст. Пробел — пауза, Esc — скрыть окно. Если не уверены в языке текста — выберите «Автоопределение».")
        hint.setObjectName("sub"); hint.setWordWrap(True); lay.addWidget(hint)
        self.diag=QLabel("Сообщения: —"); self.diag.setObjectName("muted"); self.diag.setWordWrap(True)
        self.diag.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        lay.addWidget(self.diag)
        lay.addStretch()
        self.tabs.addTab(control,"Управление")

        history_tab=QWidget(); hl=QVBoxLayout(history_tab); hl.setContentsMargins(14,16,14,14); hl.setSpacing(10)
        top=QHBoxLayout(); self.search=QLineEdit(); self.search.setPlaceholderText("Поиск по оригиналу или переводу…")
        self.search.textChanged.connect(self.filter_history); top.addWidget(self.search,1)
        self.count_label=QLabel("0 записей"); top.addWidget(self.count_label); hl.addLayout(top)
        self.table=QTableWidget(0,3); self.table.setHorizontalHeaderLabels(["Время","Оригинал","Перевод"])
        self.table.horizontalHeader().setSectionResizeMode(0,QHeaderView.ResizeMode.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(1,QHeaderView.ResizeMode.Stretch)
        self.table.horizontalHeader().setSectionResizeMode(2,QHeaderView.ResizeMode.Stretch)
        self.table.setAlternatingRowColors(True); self.table.setWordWrap(True); self.table.setTextElideMode(Qt.TextElideMode.ElideNone)
        self.table.verticalHeader().setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.cellDoubleClicked.connect(self.copy_translation); hl.addWidget(self.table,3)
        self.detail=QTextEdit(); self.detail.setReadOnly(True); self.detail.setMinimumHeight(110); self.detail.setMaximumHeight(240)
        self.detail.setPlaceholderText("Выберите запись в списке — здесь появится полный перевод и оригинал целиком.")
        hl.addWidget(self.detail,1)
        self.table.itemSelectionChanged.connect(self.show_detail)
        bottom=QHBoxLayout()
        copy=QPushButton("Копировать перевод"); copy.clicked.connect(self.copy_selected); bottom.addWidget(copy)
        bottom.addStretch()
        clear=QPushButton("Очистить историю"); clear.clicked.connect(self.clear_history); bottom.addWidget(clear)
        hl.addLayout(bottom); self.tabs.addTab(history_tab,"История переводов")

    def refresh_ocr_status(self):
        red="background:#4a2028;color:#ff9ba7;padding:8px 12px;border-radius:10px;font-weight:600;"
        try:
            available=set(pytesseract.get_languages())
            required={v[1] for k,v in LANGS.items() if k!="auto"}
            missing=required-available
            if missing:
                self.status_badge.setText(f"OCR: не хватает {len(missing)} языков")
                self.status_badge.setToolTip("Нет моделей: "+", ".join(sorted(missing)))
                self.status_badge.setStyleSheet("background:#4a3420;color:#ffd08a;padding:8px 12px;border-radius:10px;font-weight:600;")
                return
            # Настоящая проверка: пробный запуск распознавания тем же способом, что и в окне перевода.
            pytesseract.image_to_data(Image.new("RGB",(80,40),"white"), lang="eng",
                                      config="--oem 1 --psm 11", timeout=10)
            self.status_badge.setText("OCR готов · 9 языков")
            self.status_badge.setToolTip("")
            self.status_badge.setStyleSheet("background:#173d32;color:#8ce3bd;padding:8px 12px;border-radius:10px;font-weight:600;")
        except Exception as exc:
            self.status_badge.setText("OCR: ошибка запуска")
            self.status_badge.setToolTip(str(exc)[:600])
            self.status_badge.setStyleSheet(red)

    def toggle_overlay(self):
        if self.toggle_btn.isChecked():
            self.overlay.show(); self.overlay.raise_(); self.check_net()
            self.toggle_btn.setText("■  Скрыть окно перевода")
        else:
            self.overlay.hide(); self.toggle_btn.setText("▶  Запустить окно перевода")

    def update_toggle(self):
        self.toggle_btn.setChecked(False); self.toggle_btn.setText("▶  Запустить окно перевода")

    def on_lang_changed(self):
        self.src_lang=self.cb_src.currentData(); self.dst_lang=self.cb_dst.currentData()
        self.settings.setValue("source",self.src_lang); self.settings.setValue("target",self.dst_lang)
        reset_auto_hint(); self.overlay.reset()

    def on_blur_changed(self):
        self.blur_k=BLUR_LEVELS[self.cb_blur.currentText()]
        self.settings.setValue("blur",self.blur_k); self.overlay.reset()

    def on_interval(self,value):
        self.interval_label.setText(f"{value} мс"); self.overlay.timer.setInterval(value)

    def add_history_entry(self, original, translated, language):
        if any(x["original"]==original and x["translated"]==translated for x in self.history):
            return
        self.history.insert(0,{"time":datetime.now().strftime("%H:%M:%S"),"original":original,"translated":translated,"language":language})
        self.history=self.history[:2000]
        self.save_history(); self.render_history()

    def render_history(self):
        query=self.search.text().lower() if hasattr(self,"search") else ""
        found=[x for x in self.history if query in (x["original"]+" "+x["translated"]).lower()]
        rows=found[:300]                      # показываем свежие 300, иначе длинные строки тормозят таблицу
        self.table.setRowCount(len(rows))
        for r,item in enumerate(rows):
            values=[item["time"],item["original"],item["translated"]]
            for c,value in enumerate(values):
                cell=QTableWidgetItem(value); cell.setToolTip(value); self.table.setItem(r,c,cell)
        self.count_label.setText(f"{len(found)} записей" + (f" (показаны последние {len(rows)})" if len(found)>len(rows) else ""))
        self.show_detail()

    def filter_history(self):
        self.render_history()

    def show_detail(self):
        rows=sorted({i.row() for i in self.table.selectedIndexes()})
        if not rows:
            self.detail.clear(); return
        orig=self.table.item(rows[0],1); tr=self.table.item(rows[0],2)
        if orig and tr:
            fmt=lambda t: escape(t).replace("\n","<br>")
            self.detail.setHtml(f"<b>Перевод</b><br>{fmt(tr.text())}<br><br><b>Оригинал</b><br>{fmt(orig.text())}")

    def copy_translation(self,row,col):
        item=self.table.item(row,2)
        if item: QApplication.clipboard().setText(item.text())

    def copy_selected(self):
        rows=sorted({i.row() for i in self.table.selectedIndexes()})
        texts=[self.table.item(r,2).text() for r in rows if self.table.item(r,2)]
        if texts: QApplication.clipboard().setText("\n".join(texts))

    def save_history(self):
        try:
            HISTORY_FILE.parent.mkdir(parents=True,exist_ok=True)
            HISTORY_FILE.write_text(json.dumps(self.history,ensure_ascii=False,indent=2),encoding="utf-8")
        except Exception: pass

    def load_history(self):
        try:
            if HISTORY_FILE.exists():
                data=json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
                if isinstance(data,list): self.history=data
        except Exception: self.history=[]
        self.render_history()

    def clear_history(self):
        self.history=[]; self.save_history(); self.render_history()

    def closeEvent(self,event):
        self.overlay.close()
        super().closeEvent(event)

def install_excepthook(get_window):
    import traceback
    def hook(exc_type, exc, tb):
        text = "".join(traceback.format_exception(exc_type, exc, tb))
        try:
            LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
            with open(LOG_FILE, "a", encoding="utf-8") as f:
                f.write(f"[{datetime.now():%Y-%m-%d %H:%M:%S}]\n{text}\n")
        except Exception:
            pass
        if threading.current_thread() is threading.main_thread():
            try:
                win = get_window()
                if win is not None:
                    win.report(f"Ошибка программы: {exc_type.__name__}: {str(exc)[:160]} (журнал: {LOG_FILE})")
            except Exception:
                pass
    sys.excepthook = hook
    threading.excepthook = lambda args: hook(args.exc_type, args.exc_value, args.exc_traceback)

def main():
    app=QApplication(sys.argv)
    app.setApplicationName("Lens 2.8")
    app.setStyle("Fusion")
    window=MainWindow()
    install_excepthook(lambda: window)
    window.show()
    sys.exit(app.exec())

if __name__=="__main__":
    main()
