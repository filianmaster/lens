"""
Lens 2.10 — экранный переводчик с прозрачным изменяемым overlay.
Windows 10/11. OCR: Tesseract (в комплекте), 9 языков, авто/ручной режим.
Перевод: GoogleTranslator (требуется интернет).
"""
import sys, os, re, json, hashlib, threading, subprocess, tempfile, shutil, time, http.client, difflib, atexit
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
    QMessageBox, QAbstractItemView, QSizePolicy, QTextEdit, QCheckBox
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
CACHE_FILE = Path(os.getenv("APPDATA", str(Path.home()))) / "Lens" / "cache.json"
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

def _safe_exc(exc):
    """Для сообщений и журнала: тип ошибки и код, а текст ошибки — только у сетевых (в нём нет текста со страницы)."""
    base = type(exc).__name__
    code = getattr(exc, "code", None)
    if code is not None:
        return f"{base} {code}"
    if isinstance(exc, OSError):
        return f"{base}: {str(exc)[:80]}"
    return base

def _is_rate_limit(exc):
    return (getattr(exc, "code", None) in (429, 503)
            or type(exc).__name__ == "TooManyRequests"
            or "too many requests" in str(exc).lower())

class HttpStatusError(Exception):
    def __init__(self, code):
        super().__init__(f"HTTP {code}")
        self.code = code

class KeepAliveClient:
    """GET-запросы по одному постоянному соединению: на повторных запросах не тратим время на TLS-рукопожатие."""
    def __init__(self, host, use_https=True, port=None):
        self.host, self.use_https, self.port = host, use_https, port
        self.conn = None
        self.lock = threading.Lock()

    def _drop(self):
        if self.conn is not None:
            try:
                self.conn.close()
            except Exception:
                pass
            self.conn = None

    def get(self, target, timeout=8):
        with self.lock:
            last = None
            for _ in range(2):                       # второй заход — на случай, если сервер закрыл простаивающее соединение
                try:
                    if self.conn is None:
                        cls = http.client.HTTPSConnection if self.use_https else http.client.HTTPConnection
                        self.conn = cls(self.host, self.port, timeout=timeout)
                    self.conn.request("GET", target, headers={"User-Agent": "Mozilla/5.0", "Accept-Encoding": "identity"})
                    resp = self.conn.getresponse()
                    body = resp.read()
                except (OSError, http.client.HTTPException) as exc:
                    last = exc
                    self._drop()
                    continue
                if resp.will_close:
                    self._drop()
                if resp.status != 200:
                    raise HttpStatusError(resp.status)
                return body
            raise last

_gtx_client = KeepAliveClient("translate.googleapis.com")
_gtx_state = {"fails": 0, "off_until": 0.0}

def _translate_gtx(text, src, dst):
    import urllib.request, urllib.parse
    query = urllib.parse.urlencode({"client": "gtx", "sl": src, "tl": dst, "dt": "t", "q": text})
    target = "/translate_a/single?" + query
    data = None
    if time.monotonic() >= _gtx_state["off_until"]:
        try:
            data = json.loads(_gtx_client.get(target).decode("utf-8"))
            _gtx_state["fails"] = 0
        except HttpStatusError:
            raise                                    # 429 и прочие ответы сервера — обработает вызывающий код
        except Exception:
            _gtx_state["fails"] += 1                 # прокси или сбой сети: пробуем обычным способом
            if _gtx_state["fails"] >= 2:
                _gtx_state["off_until"] = time.monotonic() + 120
    if data is None:
        req = urllib.request.Request("https://translate.googleapis.com" + target, headers={"User-Agent": "Mozilla/5.0"})
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
            errors.append(f"{name}: {_safe_exc(exc)}")
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

_recent = []            # (буквы текста, src, dst, текст) — для поиска «почти такого же» текста

def _norm(text):
    return "".join(ch for ch in text.lower() if ch.isalpha())

def _recent_add(text, src, dst):
    _recent.append((_norm(text), src, dst, text))
    if len(_recent) > 400:
        del _recent[:100]

def _fuzzy_lookup(text, src, dst):
    """Тот же абзац с мелкой ошибкой OCR (одна буква) не переводим заново — плашки не дёргаются, запросов меньше."""
    n = _norm(text)
    if not 20 <= len(n) <= 1500:
        return None
    for norm, s_, d_, original in reversed(_recent[-150:]):
        if s_ != src or d_ != dst or abs(len(norm) - len(n)) > 0.06 * max(len(norm), len(n)):
            continue
        m = difflib.SequenceMatcher(None, n, norm, autojunk=False)
        if m.real_quick_ratio() >= 0.96 and m.quick_ratio() >= 0.96 and m.ratio() >= 0.96:
            hit = _cache.get((original, s_, d_))
            if hit is not None:
                return hit
    return None

_save_timer = [None]

def _save_cache():
    _save_timer[0] = None
    if not STORE["on"]:
        return
    with _cache_lock:
        items = [[t, s_, d_, tr] for (t, s_, d_), tr in list(_cache.items())[-2000:]]
    try:
        secure_dump(CACHE_FILE, items)
    except Exception:
        pass

def _save_cache_soon():
    if STORE["on"] and _save_timer[0] is None:
        timer = threading.Timer(8.0, _save_cache)
        timer.daemon = True
        _save_timer[0] = timer
        timer.start()

def load_cache():
    if not STORE["on"]:
        return
    try:
        items = secure_load(CACHE_FILE)
    except Exception:
        return
    with _cache_lock:
        for item in items[-2000:]:
            try:
                t, s_, d_, tr = item
            except Exception:
                continue
            if isinstance(t, str) and isinstance(tr, str):
                _cache[(t, s_, d_)] = tr
                _recent_add(t, s_, d_)

def clear_translation_cache():
    timer = _save_timer[0]
    if timer is not None:
        timer.cancel()
        _save_timer[0] = None
    with _cache_lock:
        _cache.clear()
        _recent.clear()
    try:
        CACHE_FILE.unlink()
    except Exception:
        pass

atexit.register(lambda: _save_cache() if _cache else None)

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
            if hit is None:
                hit = _fuzzy_lookup(t, src, dst)
                if hit is not None:
                    _cache[(t, src, dst)] = hit
        if hit is not None:
            out[i] = hit
        else:
            pending.setdefault(t, []).append(i)
    for chunk in _chunks(list(pending)):
        for t, tr in zip(chunk, _translate_chunk(chunk, src, dst)):
            with _cache_lock:
                if len(_cache) > 5000:
                    for old in list(_cache)[:1000]:
                        del _cache[old]
                _cache[(t, src, dst)] = tr
                _recent_add(t, src, dst)
            for i in pending[t]:
                out[i] = tr
        _save_cache_soon()
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

def _band_gaps(ordered, mh):
    gaps, reach = [], ordered[0]["x"] + ordered[0]["w"]
    for w in ordered[1:]:
        if w["x"] - reach > 1.2 * mh:
            gaps.append((reach, w["x"]))
        reach = max(reach, w["x"] + w["w"])
    return gaps

def build_rows(words):
    """Собирает слова в визуальные строки по координатам (не доверяя разбиению Tesseract).
    Сначала горизонтальные полосы по высоте слов, потом разрез полосы на колонки: пустой промежуток
    считается границей колонок, если он очень широкий или повторяется в соседних строках (жёлоб между карточками)."""
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
    ordered_bands = [sorted(band["words"], key=lambda w: w["x"]) for band in bands]
    all_gaps = [_band_gaps(o, mh) for o in ordered_bands]
    rows = []
    for i, ordered in enumerate(ordered_bands):
        near = [j for j in range(max(0, i - 4), min(len(all_gaps), i + 5)) if j != i]
        need = min(3, len(near))
        cuts = []
        for g0, g1 in all_gaps[i]:
            c = (g0 + g1) / 2
            if g1 - g0 > 3.5 * mh:
                cuts.append(c)                       # очень широкий пробел — это точно другая колонка
                continue
            # жёлоб колонок — полоса шириной в высоту слова, свободная от букв сразу в нескольких строках рядом
            covered = sum(1 for j in near if any(n0 <= c - 0.5 * mh and n1 >= c + 0.5 * mh for n0, n1 in all_gaps[j]))
            if need >= 1 and covered >= need:
                cuts.append(c)
        current, ci = [], 0
        for w in ordered:
            while ci < len(cuts) and w["x"] >= cuts[ci]:
                if current:
                    rows.append(_make_row(current))
                    current = []
                ci += 1
            current.append(w)
        if current:
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

def refine_language(key, lines, sticky=False):
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
                if top.prob >= (0.95 if sticky else 0.85) and DETECT_TO_KEY.get(top.lang) in group:
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

def _finalize(img, key, lines, score, sticky=False):
    """Уточняет язык внутри алфавита; при необходимости перечитывает точной моделью."""
    refined = refine_language(key, lines, sticky)
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
            return _finalize(img, hint, lines, score, sticky=True)
    key = guess_language(img)
    if key is None:
        _set_hint(None)
        return [], "en"
    lines, score = _ocr_one(img, LANGS[key][1])
    if not lines:
        _set_hint(None)
        return [], key
    return _finalize(img, key, lines, score)

def row_ink(img, box):
    """Средний цвет самых контрастных пикселей строки (цвет букв) — заголовок обычно другого цвета, чем основной текст."""
    x0, y0, x1, y1 = box
    crop = img.crop((max(0, x0), max(0, y0), min(img.width, x1), min(img.height, y1)))
    if crop.width < 4 or crop.height < 4:
        return None
    rgb = crop.convert("RGB")
    bg = tuple(int(v) for v in ImageStat.Stat(rgb).median)
    diff = ImageChops.difference(rgb, Image.new("RGB", rgb.size, bg)).convert("L")
    hist = diff.histogram()
    target, acc, thr = sum(hist) * 0.10, 0, 255
    for v in range(255, -1, -1):
        acc += hist[v]
        if acc >= target:
            thr = v
            break
    if thr < 25:
        return None
    mask = diff.point(lambda q: 255 if q >= thr else 0)
    return tuple(int(v) for v in ImageStat.Stat(rgb, mask).mean)

def add_ink(img, lines):
    out = []
    for line in lines:
        text, x0, y0, x1, y1 = line[:5]
        try:
            ink = row_ink(img, (x0, y0, x1, y1))
        except Exception:
            ink = None
        out.append((text, x0, y0, x1, y1, ink))
    return out

def color_dist(a, b):
    return sum((x - y) ** 2 for x, y in zip(a, b)) ** 0.5

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
    for line in sorted(lines, key=lambda l: (l[2], l[1])):
        text, x0, y0, x1, y1 = line[:5]
        ink = line[5] if len(line) > 5 else None
        lh = max(1, y1 - y0)
        match = None
        for g in groups:
            glh = max(1, g["h"] / len(g["parts"]))
            gap = y0 - g["y1"]
            overlap = min(x1, g["x1"]) - max(x0, g["x0"])
            narrow = max(1, min(x1 - x0, g["x1"] - g["x0"]))
            if overlap < 0.3 * narrow:
                continue                             # другая колонка
            if ink and g.get("ink") and color_dist(ink, g["ink"]) > 80:
                continue                             # другой цвет букв — это заголовок или другой блок
            if len(g["tops"]) >= 2:                      # шаг строк абзаца известен — сравниваем с ним
                typical = _median([b - a for a, b in zip(g["tops"], g["tops"][1:])])
                near = gap >= -0.6 * glh and (y0 - g["tops"][-1]) <= 1.45 * typical
            else:
                near = -0.6 * glh <= gap <= 0.95 * glh
            if near and abs(lh - glh) <= 0.6 * glh:     # близко и тот же размер шрифта
                match = g
                break
        if match:
            match["parts"].append(text)
            match["tops"].append(y0)
            match["h"] += y1 - y0
            match["x0"], match["y0"] = min(match["x0"], x0), min(match["y0"], y0)
            match["x1"], match["y1"] = max(match["x1"], x1), max(match["y1"], y1)
        else:
            groups.append({"parts": [text], "h": y1 - y0, "x0": x0, "y0": y0, "x1": x1, "y1": y1, "ink": ink, "tops": [y0]})
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
    hotkey = Signal(int)

# =============================== БЕЗОПАСНОСТЬ ===============================
STORE = {"on": True}                     # False — ничего не пишем на диск (история и кэш живут только в памяти)
IDLE_LIMIT = 180.0                       # секунд без ввода с клавиатуры/мыши — пауза
LOCK_TEXT = "Скрыто: личные данные (в переводчик не отправлено)"

def _luhn_ok(digits):
    total, alt = 0, False
    for ch in reversed(digits):
        d = int(ch)
        if alt:
            d *= 2
            if d > 9:
                d -= 9
        total += d
        alt = not alt
    return total % 10 == 0

_RE_DIGITS = re.compile(r"(?<![\w])(?:\d[ \-]?){13,19}(?![\w])")
_RE_EMAIL = re.compile(r"[\w.+\-]+@[\w\-]+(?:\.[\w\-]+)+")
_RE_PHONE = re.compile(r"(?<![\w])\+?\d[\d\s().\-]{8,17}\d(?![\w])")
_RE_DATE = re.compile(r"^\d{1,2}[./-]\d{1,2}[./-]\d{2,4}$")
_RE_IBAN = re.compile(r"\b[A-Z]{2}\d{2}(?: ?[A-Z0-9]{4}){3,7}(?: ?[A-Z0-9]{1,4})?\b")
_KEYWORDS = r"(?:парол\w*|password|passcode|passwd|pin|пин|cvv|cvc|otp|2fa|смс|sms|код\w*|code|token|токен\w*|secret|секрет\w*)"
_RE_CODE_AFTER = re.compile(r"(?i)\b" + _KEYWORDS + r"\b\D{0,30}\b\d{4,8}\b")
_RE_CODE_BEFORE = re.compile(r"(?i)\b\d{4,8}\b\D{0,30}\b" + _KEYWORDS + r"\b")
_RE_PASSWORD_VALUE = re.compile(r"(?i)(?:парол\w*|password|passwd)\s*[:=]\s*\S{4,}")
_RE_TOKEN = re.compile(r"\b(?=[A-Za-z0-9_\-+/=]*\d)(?=[A-Za-z0-9_\-+/=]*[A-Za-z])[A-Za-z0-9_\-+/=]{32,}\b")
_RE_PRIVATE_KEY = re.compile(r"BEGIN [A-Z ]*PRIVATE KEY")

def sensitive_reason(text):
    """Название причины, если в тексте похоже на личные данные (в переводчик такой фрагмент не уходит), иначе None."""
    if _RE_PRIVATE_KEY.search(text) or _RE_TOKEN.search(text):
        return "ключ/токен"
    for m in _RE_DIGITS.finditer(text):
        digits = re.sub(r"\D", "", m.group())
        if 13 <= len(digits) <= 19 and _luhn_ok(digits):
            return "номер карты"
    if _RE_IBAN.search(text):
        return "IBAN"
    if _RE_PASSWORD_VALUE.search(text) or _RE_CODE_AFTER.search(text) or _RE_CODE_BEFORE.search(text):
        return "код/пароль"
    if _RE_EMAIL.search(text):
        return "e-mail"
    for m in _RE_PHONE.finditer(text):
        digits = re.sub(r"\D", "", m.group())
        if 10 <= len(digits) <= 15 and not _RE_DATE.match(m.group().strip()):
            return "телефон"
    return None

GUARD_TITLE_WORDS = (
    "пароль", "password", "passcode", "вход в ", "sign in", "log in", "login", "войти", "авторизац",
    "банк", "bank", "sber", "сбер", "tinkoff", "тинькофф", "kaspi", "каспи", "halyk", "jusan", "paypal",
    "payment", "оплат", "платеж", "платёж", "кошел", "wallet", "metamask", "binance",
    "госуслуг", "egov", "2fa", "verification code", "подтверждение входа",
)
GUARD_EXE_WORDS = ("keepass", "bitwarden", "1password", "lastpass", "dashlane", "enpass", "nordpass", "keeper", "authy", "winauth")

def guard_reason(title, exe):
    """Если окно под линзой похоже на банк / вход / менеджер паролей — возвращает название причины."""
    t, e = (title or "").lower(), (exe or "").lower()
    if any(w in e for w in GUARD_EXE_WORDS):
        return "менеджер паролей"
    if any(w in t for w in GUARD_TITLE_WORDS):
        return "окно банка, входа или пароля"
    return ""

def window_under(rect, own_hwnd):
    """(заголовок, имя exe) ближайшего видимого окна под линзой. При любой неудаче — пустые строки."""
    try:
        import ctypes
        from ctypes import wintypes
        user32 = ctypes.WinDLL("user32")
        kernel32 = ctypes.WinDLL("kernel32")
        user32.GetWindow.argtypes = [ctypes.c_void_p, wintypes.UINT]
        user32.GetWindow.restype = ctypes.c_void_p
        user32.IsWindowVisible.argtypes = [ctypes.c_void_p]
        user32.IsIconic.argtypes = [ctypes.c_void_p]
        user32.GetWindowRect.argtypes = [ctypes.c_void_p, ctypes.POINTER(wintypes.RECT)]
        user32.GetWindowTextW.argtypes = [ctypes.c_void_p, wintypes.LPWSTR, ctypes.c_int]
        user32.GetWindowThreadProcessId.argtypes = [ctypes.c_void_p, ctypes.POINTER(wintypes.DWORD)]
        kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        kernel32.OpenProcess.restype = ctypes.c_void_p
        kernel32.QueryFullProcessImageNameW.argtypes = [ctypes.c_void_p, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]
        kernel32.CloseHandle.argtypes = [ctypes.c_void_p]
        cx, cy = (rect[0] + rect[2]) // 2, (rect[1] + rect[3]) // 2
        hwnd = user32.GetWindow(own_hwnd, 2)               # GW_HWNDNEXT: следующее окно ниже нашего
        for _ in range(200):
            if not hwnd:
                break
            if user32.IsWindowVisible(hwnd) and not user32.IsIconic(hwnd):
                r = wintypes.RECT()
                user32.GetWindowRect(hwnd, ctypes.byref(r))
                if r.left <= cx < r.right and r.top <= cy < r.bottom:
                    buf = ctypes.create_unicode_buffer(512)
                    user32.GetWindowTextW(hwnd, buf, 512)
                    if buf.value:
                        pid = wintypes.DWORD(0)
                        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
                        exe = ""
                        handle = kernel32.OpenProcess(0x1000, False, pid.value)   # PROCESS_QUERY_LIMITED_INFORMATION
                        if handle:
                            size = wintypes.DWORD(512)
                            path = ctypes.create_unicode_buffer(512)
                            if kernel32.QueryFullProcessImageNameW(handle, 0, path, ctypes.byref(size)):
                                exe = os.path.basename(path.value)
                            kernel32.CloseHandle(handle)
                        return buf.value, exe
            hwnd = user32.GetWindow(hwnd, 2)
    except Exception:
        pass
    return "", ""

def idle_seconds():
    """Сколько секунд пользователь ничего не нажимал и не двигал мышью."""
    try:
        import ctypes
        class LASTINPUTINFO(ctypes.Structure):
            _fields_ = [("cbSize", ctypes.c_uint), ("dwTime", ctypes.c_uint)]
        info = LASTINPUTINFO()
        info.cbSize = ctypes.sizeof(info)
        user32, kernel32 = ctypes.WinDLL("user32"), ctypes.WinDLL("kernel32")
        kernel32.GetTickCount.restype = ctypes.c_uint
        if not user32.GetLastInputInfo(ctypes.byref(info)):
            return 0.0
        return ((kernel32.GetTickCount() - info.dwTime) & 0xFFFFFFFF) / 1000.0
    except Exception:
        return 0.0

class HotkeyListener(threading.Thread):
    """Глобальные горячие клавиши (работают из любого окна): Ctrl+Alt+P / T / L."""
    KEYS = {1: ord("P"), 2: ord("T"), 3: ord("L")}
    def __init__(self, bridge):
        super().__init__(daemon=True)
        self.bridge = bridge
        self.ok = {}
    def run(self):
        try:
            import ctypes
            from ctypes import wintypes
            user32 = ctypes.WinDLL("user32")
            user32.RegisterHotKey.argtypes = [ctypes.c_void_p, ctypes.c_int, wintypes.UINT, wintypes.UINT]
            user32.GetMessageW.argtypes = [ctypes.POINTER(wintypes.MSG), ctypes.c_void_p, wintypes.UINT, wintypes.UINT]
            mods = 0x0002 | 0x0001 | 0x4000                       # CONTROL | ALT | NOREPEAT
            for hid, vk in self.KEYS.items():
                self.ok[hid] = bool(user32.RegisterHotKey(None, hid, mods, vk))
            msg = wintypes.MSG()
            while user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                if msg.message == 0x0312:                          # WM_HOTKEY
                    self.bridge.hotkey.emit(int(msg.wParam))
        except Exception:
            pass

# ---- файлы: шифрование средствами Windows (DPAPI — только для вашей учётной записи Windows)
MAGIC = b"LENSv1\x00"
_crypto = {"ok": None, "err": ""}

def _dpapi(fn_name, data):
    import ctypes
    from ctypes import wintypes
    class DATA_BLOB(ctypes.Structure):
        _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]
    crypt32, kernel32 = ctypes.WinDLL("crypt32"), ctypes.WinDLL("kernel32")
    kernel32.LocalFree.argtypes = [ctypes.c_void_p]
    kernel32.LocalFree.restype = ctypes.c_void_p
    func = getattr(crypt32, fn_name)
    func.restype = wintypes.BOOL
    buf = ctypes.create_string_buffer(data, len(data))
    blob_in = DATA_BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
    blob_out = DATA_BLOB()
    if fn_name == "CryptProtectData":
        func.argtypes = [ctypes.POINTER(DATA_BLOB), wintypes.LPCWSTR, ctypes.POINTER(DATA_BLOB), ctypes.c_void_p,
                         ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(DATA_BLOB)]
        ok = func(ctypes.byref(blob_in), "Lens", None, None, None, 0, ctypes.byref(blob_out))
    else:
        func.argtypes = [ctypes.POINTER(DATA_BLOB), ctypes.POINTER(wintypes.LPWSTR), ctypes.POINTER(DATA_BLOB),
                         ctypes.c_void_p, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(DATA_BLOB)]
        ok = func(ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out))
    if not ok:
        raise OSError(f"{fn_name} failed")
    try:
        return ctypes.string_at(blob_out.pbData, blob_out.cbData)
    finally:
        kernel32.LocalFree(ctypes.cast(blob_out.pbData, ctypes.c_void_p))

def _protect_bytes(data):
    return _dpapi("CryptProtectData", data)

def _unprotect_bytes(blob):
    return _dpapi("CryptUnprotectData", blob)

def crypto_selftest():
    """Проверяет, что шифрование работает; если нет — файлы пишутся как раньше, а причина видна в диагностике."""
    try:
        sample = b"lens-selftest"
        good = _unprotect_bytes(_protect_bytes(sample)) == sample
        _crypto.update(ok=good, err="" if good else "проверка не прошла")
    except Exception as exc:
        _crypto.update(ok=False, err=type(exc).__name__)
    return _crypto["ok"]

def secure_dump(path, obj):
    raw = json.dumps(obj, ensure_ascii=False).encode("utf-8")
    data = raw
    if _crypto["ok"]:
        try:
            data = MAGIC + _protect_bytes(raw)
        except Exception as exc:
            _crypto.update(ok=False, err=type(exc).__name__)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_bytes(data)
    tmp.replace(path)

def secure_load(path):
    data = path.read_bytes()
    if data.startswith(MAGIC):
        data = _unprotect_bytes(data[len(MAGIC):])
    return json.loads(data.decode("utf-8"))

def wipe_stored_files(include_log=False):
    """Удаляет с диска историю и кэш (и по желанию журнал ошибок)."""
    timer = _save_timer[0]
    if timer is not None:
        timer.cancel()
        _save_timer[0] = None
    targets = [HISTORY_FILE, CACHE_FILE, HISTORY_FILE.with_name(HISTORY_FILE.name + ".tmp"), CACHE_FILE.with_name(CACHE_FILE.name + ".tmp")]
    if include_log:
        targets.append(LOG_FILE)
    for path in targets:
        try:
            path.unlink()
        except Exception:
            pass

def cleanup_stale_temp(max_age=900):
    """Удаляет забытые фрагменты экрана (tess_*), если программу когда-то закрыли аварийно во время распознавания."""
    now = time.time()
    try:
        for path in Path(tempfile.gettempdir()).glob("tess_*"):
            try:
                if now - path.stat().st_mtime >= max_age:
                    path.unlink()
            except Exception:
                pass
    except Exception:
        pass

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

def scan(bridge, rect, src, dst, blur_k, last_sig, generation, img=None, prev_thumb=None, protect=True):
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
        groups = group_lines(add_ink(img, lines))
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
        hidden = []
        if protect:                                  # личные данные в переводчик не отправляем
            keep = []
            for g, original in jobs:
                (hidden if sensitive_reason(original) else keep).append((g, original))
            jobs = keep
        if not jobs and not hidden:
            return
        try:
            translations = translate_many([o for _, o in jobs], src_code, dst_code) if jobs else []
        except RateLimited as exc:
            result["error"] = str(exc)
            return
        except Exception as exc:
            result["error"] = f"Ошибка перевода: проверьте интернет. ({str(exc)[:220]})"
            return
        entries = [(g, o, t, False) for (g, o), t in zip(jobs, translations)] + [(g, o, LOCK_TEXT, True) for g, o in hidden]
        entries.sort(key=lambda e: (e[0]["y0"], e[0]["x0"]))
        if hidden:
            result["info"] = f"Защита: фрагментов с личными данными скрыто — {len(hidden)} (в переводчик не отправлены)"
        for g, original, translated, locked in entries:
            if not locked:
                bridge.history_add.emit(original, translated, actual_src)
            line_h = max(12, g["h"] / len(g["parts"]))
            pad = int(line_h * 0.32)
            box = (max(0,g["x0"]-pad), max(0,g["y0"]-pad),
                   min(width,g["x1"]+pad), min(height,g["y1"]+pad))
            patch = img.crop(box).filter(ImageFilter.GaussianBlur(max(6.0, line_h*0.9) if locked else max(2.0, line_h*blur_k))).convert("RGBA")
            qimg = QImage(patch.tobytes(),patch.width,patch.height,patch.width*4,QImage.Format.Format_RGBA8888).copy()
            avg = tuple(int(v) for v in ImageStat.Stat(patch.convert("RGB")).mean)
            dark = (0.299*avg[0] + 0.587*avg[1] + 0.114*avg[2]) < 128
            result["blocks"].append({"box":box,"lh":line_h,"text":translated,"img":qimg,"avg":avg,"dark":dark,"locked":locked})
    except Exception as exc:
        result["error"] = f"Сбой: {_safe_exc(exc)}"
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
        self.trigger_once = False     # режим «по запросу»: один перевод по горячей клавише
        self.guard_text = ""          # причина, по которой перевод сейчас отключён защитой
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

    def clean_capture(self, rect, force=False):
        """Снимок без плашек Lens. None — на экране ничего не изменилось."""
        vis = grab_region(rect)
        vsig = hashlib.md5(vis.tobytes()).hexdigest()
        if vsig == self.visible_sig and not self.need_retry and not force:
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

    def translate_now(self):
        """Режим «по запросу»: перевести то, что сейчас под линзой (Ctrl+Alt+T)."""
        if not self.isVisible():
            return
        if self.paused:
            self.main.report("Сначала снимите паузу (Ctrl+Alt+P)")
            return
        self.trigger_once = True
        QTimer.singleShot(0, self.tick)

    def set_guard(self, text):
        if text == self.guard_text:
            return
        self.guard_text = text
        if text:                                   # то, что уже нарисовано, убираем
            self.blocks = []
            self.blocks_key = None
            self.working = False
            self.main.report(text)
        self.update()

    def border_color(self):
        if self.paused or self.guard_text:
            return QColor(150, 160, 175, 210)      # серая рамка — перевод сейчас не идёт
        if self.main.mode == "manual":
            return QColor(40, 200, 170, 210)       # бирюзовая — ждёт команды
        return QColor(35, 145, 255, 210)

    def tick(self):
        if self.busy or self.paused or self.calib_pending or self.baseline_pending or not self.isVisible():
            return
        if QApplication.mouseButtons() & Qt.MouseButton.LeftButton:
            return
        if self.need_retry and time.monotonic() < self.retry_at:
            return
        main = self.main
        if main.mode == "manual" and not self.trigger_once:
            return
        if main.idle_pause and idle_seconds() > IDLE_LIMIT:
            self.set_guard("Пауза: за компьютером никого нет — сдвиньте мышь")
            return
        rect = self.rect_on_screen()
        if main.protect_window:
            title, exe = window_under(rect, int(self.winId()))
            reason = guard_reason(title, exe)
            if reason:
                self.trigger_once = False
                self.set_guard(f"Защита: под линзой {reason} — перевод отключён")
                return
        self.set_guard("")
        force = self.trigger_once
        self.trigger_once = False
        img = None
        if not self.excluded:
            try:
                img = self.clean_capture(rect, force)
            except Exception as exc:
                self.show_status(f"Ошибка снимка экрана: {type(exc).__name__}", 5000)
                return
            if img is None:
                return
        self.busy = True
        self.need_retry = False
        threading.Thread(target=scan, args=(self.bridge,rect,
            main.src_lang,main.dst_lang,main.blur_k,None if force else self.last_sig,self.generation,
            img,self.last_thumb,main.protect_data),daemon=True).start()

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
                           "avg":b["avg"],"dark":b["dark"],"alpha":235 if b.get("locked") else alpha})
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
        p.setPen(QPen(self.border_color(),2))
        p.drawRoundedRect(QRectF(self.rect()).adjusted(1,1,-1,-1),8,8)
        hint = "перевод…" if self.working else ("Ctrl+Alt+T — перевести" if self.main.mode == "manual" and not self.blocks and not self.paused else "")
        if hint:
            pill_font=QFont("Segoe UI",8,QFont.Weight.Bold); p.setFont(pill_font)
            pw=QFontMetrics(pill_font).horizontalAdvance(hint)+26
            r=QRectF(self.width()-pw-10,self.height()-32,pw,22)
            p.setPen(Qt.PenStyle.NoPen); p.setBrush(QColor(10,13,20,215)); p.drawRoundedRect(r,11,11)
            p.setPen(QColor(130,195,255)); p.drawText(QPointF(r.left()+13,r.top()+15),hint)
        if self.paused or self.guard_text or self.status:
            msg=("Ⅱ ПАУЗА (Ctrl+Alt+P — продолжить)" if self.paused else (self.guard_text or self.status))
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
        self.paused=not self.paused
        if self.paused:
            self.trigger_once=False
        self.update()

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Lens 2.10 — Экранный переводчик")
        self.resize(900,650)
        self.setMinimumSize(760,560)
        self.settings=QSettings("LensProject","Lens22")
        self.src_lang=self.settings.value("source","auto")
        self.dst_lang=self.settings.value("target","ru")
        self.blur_k=float(self.settings.value("blur",0.5))
        self.mode="manual" if self.settings.value("mode","auto")=="manual" else "auto"
        self.protect_data=self._bool("protect_data",True)
        self.protect_window=self._bool("protect_window",True)
        self.idle_pause=self._bool("idle_pause",True)
        self.no_store=self._bool("no_store",False)
        self.clear_on_exit=self._bool("clear_on_exit",False)
        STORE["on"]=not self.no_store
        self.history=[]
        self.overlay=LensOverlay(self)
        self.build_ui()
        self.load_history()
        self.refresh_ocr_status()
        self.net_bridge=Bridge(); self.net_bridge.net.connect(self.on_net_status)
        self.check_net()
        self.hk_bridge=Bridge(); self.hk_bridge.hotkey.connect(self.on_hotkey)
        self.hotkeys=HotkeyListener(self.hk_bridge); self.hotkeys.start()
        if not _crypto["ok"]:
            self.report("Шифрование файлов Windows недоступно — история и кэш (если включены) хранятся без шифрования")

    def _bool(self, key, default):
        return str(self.settings.value(key, "1" if default else "0")).lower() in ("1", "true")

    def on_hotkey(self, hid):
        if hid == 1:
            self.overlay.toggle_pause()
            self.report("Пауза включена (Ctrl+Alt+P)" if self.overlay.paused else "Пауза снята")
        elif hid == 2:
            self.overlay.translate_now()
        elif hid == 3:
            self.toggle_btn.setChecked(not self.toggle_btn.isChecked()); self.toggle_overlay()

    def on_security_changed(self, *_):
        self.mode=self.cb_mode.currentData()
        self.protect_data=self.chk_protect.isChecked()
        self.protect_window=self.chk_window.isChecked()
        self.idle_pause=self.chk_idle.isChecked()
        self.no_store=self.chk_nostore.isChecked()
        self.clear_on_exit=self.chk_exit.isChecked()
        for key,value in (("mode",self.mode),("protect_data",self.protect_data),("protect_window",self.protect_window),
                          ("idle_pause",self.idle_pause),("no_store",self.no_store),("clear_on_exit",self.clear_on_exit)):
            self.settings.setValue(key, value if isinstance(value,str) else ("1" if value else "0"))
        STORE["on"]=not self.no_store
        if self.no_store:
            wipe_stored_files()                 # ничего не должно оставаться на диске
        self.overlay.reset(); self.overlay.update()

    def clear_everything(self):
        self.history=[]; self.render_history()
        clear_translation_cache(); wipe_stored_files(include_log=True); cleanup_stale_temp(max_age=0)
        self.report("Очищено: история, кэш переводов, журнал ошибок и временные файлы")

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
        stamp = datetime.now().strftime('%H:%M:%S')
        self.diag.setText(f"Сообщения [{stamp}]: {text}")
        if not hasattr(self, "report_log"):
            self.report_log = []
        self.report_log.append(f"[{stamp}] {text}")
        del self.report_log[:-40]

    def copy_diagnostics(self):
        QApplication.clipboard().setText(collect_diagnostics(self))
        self.report("Диагностика скопирована в буфер обмена — вставьте её в чат")

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
        QCheckBox { spacing:10px; padding:3px 0; }
        QCheckBox::indicator { width:18px; height:18px; border:1px solid #3b4c66; border-radius:5px; background:#0e1420; }
        QCheckBox::indicator:checked { background:#1677e8; border:1px solid #5aa6ff; }
        """)
        root=QWidget(); self.setCentralWidget(root)
        outer=QVBoxLayout(root); outer.setContentsMargins(24,20,24,22); outer.setSpacing(16)
        header=QHBoxLayout()
        brand=QVBoxLayout()
        title=QLabel("LENS 2.10"); title.setObjectName("hero")
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
        self.btn_diag=QPushButton("Скопировать диагностику"); self.btn_diag.clicked.connect(self.copy_diagnostics)
        lay.addWidget(self.btn_diag)
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

        sec=QWidget(); sl=QVBoxLayout(sec); sl.setContentsMargins(18,18,18,16); sl.setSpacing(11)
        sec_title=QLabel("Безопасность и приватность"); sec_title.setObjectName("hero"); sec_title.setStyleSheet("font-size:19px;"); sl.addWidget(sec_title)
        mode_row=QHBoxLayout(); mode_row.addWidget(QLabel("Режим работы"))
        self.cb_mode=QComboBox()
        self.cb_mode.addItem("Автоматически (в реальном времени)","auto")
        self.cb_mode.addItem("По запросу — только по Ctrl+Alt+T","manual")
        self.cb_mode.setCurrentIndex(1 if self.mode=="manual" else 0)
        mode_row.addWidget(self.cb_mode,1); sl.addLayout(mode_row)
        def check(text,value):
            box=QCheckBox(text); box.setChecked(value); sl.addWidget(box); return box
        self.chk_protect=check("Скрывать личные данные (карты, коды, пароли, e-mail, телефоны): в переводчик не отправлять",self.protect_data)
        self.chk_window=check("Не переводить, если под линзой окно банка, входа или менеджера паролей",self.protect_window)
        self.chk_idle=check("Пауза, если за компьютером никого нет (3 минуты без ввода)",self.idle_pause)
        self.chk_nostore=check("Не хранить историю и кэш на диске",self.no_store)
        self.chk_exit=check("Очищать историю и кэш при выходе",self.clear_on_exit)
        clear_btn=QPushButton("Очистить историю, кэш и журнал сейчас"); clear_btn.clicked.connect(self.clear_everything); sl.addWidget(clear_btn)
        enc="шифруются средствами Windows и открываются только вашей учётной записью" if _crypto["ok"] else "хранятся БЕЗ шифрования (шифрование Windows недоступно)"
        info=QLabel(f"Что сохраняется: история и кэш переводов в {HISTORY_FILE.parent} — {enc}; языки и размытие — в реестре; на время распознавания фрагмент экрана лежит во временной папке и сразу удаляется.\n\n"
                    "Что уходит в сеть: только распознанный текст — в Google Translate. Картинки не отправляются, телеметрии нет.\n\n"
                    "Горячие клавиши работают из любого окна: Ctrl+Alt+P — пауза, Ctrl+Alt+T — перевести сейчас, Ctrl+Alt+L — показать или скрыть линзу.")
        info.setObjectName("muted"); info.setWordWrap(True); sl.addWidget(info); sl.addStretch()
        self.tabs.addTab(sec,"Безопасность")
        self.cb_mode.currentIndexChanged.connect(self.on_security_changed)
        for box in (self.chk_protect,self.chk_window,self.chk_idle,self.chk_nostore,self.chk_exit):
            box.toggled.connect(self.on_security_changed)

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
        if self.no_store:
            return
        try:
            secure_dump(HISTORY_FILE, self.history)
        except Exception: pass

    def load_history(self):
        try:
            if self.no_store:
                wipe_stored_files()
            elif HISTORY_FILE.exists():
                data=secure_load(HISTORY_FILE)
                if isinstance(data,list): self.history=data
        except Exception: self.history=[]
        self.render_history()

    def clear_history(self):
        self.history=[]; self.save_history(); self.render_history()
        clear_translation_cache()            # вместе с историей стираем и сохранённые переводы

    def closeEvent(self,event):
        if self.clear_on_exit or self.no_store:
            self.history=[]; clear_translation_cache(); wipe_stored_files()
        else:
            _save_cache()
        self.overlay.close()
        super().closeEvent(event)

def collect_diagnostics(window):
    """Короткий отчёт о системе и состоянии Lens — чтобы не гадать, а видеть, что происходит на конкретном ПК."""
    out = [f"Lens 2.10 · {datetime.now():%Y-%m-%d %H:%M:%S}"]
    def add(title, fn):
        try:
            out.append(f"{title}: {fn()}")
        except Exception as exc:
            out.append(f"{title}: ошибка {type(exc).__name__}: {str(exc)[:120]}")
    ov = window.overlay
    add("Windows", lambda: ".".join(str(x) for x in sys.getwindowsversion()[:3]))
    add("Python / PySide6", lambda: f"{sys.version.split()[0]} / {__import__('PySide6').__version__}")
    add("Tesseract", lambda: str(pytesseract.get_tesseract_version()))
    add("Tesseract exe", lambda: f"{TESS_EXE} ({'есть' if TESS_EXE.exists() else 'нет, системный'})")
    add("Языки OCR", lambda: ", ".join(sorted(pytesseract.get_languages())))
    add("TESSDATA_PREFIX", lambda: os.environ.get("TESSDATA_PREFIX", "—"))
    add("Экран", lambda: f"{QApplication.primaryScreen().size().width()}x{QApplication.primaryScreen().size().height()}, масштаб {QApplication.primaryScreen().devicePixelRatio()}")
    add("Снимок экрана", lambda: ("окно скрыто системой" if ov.excluded else "окно прячется перерисовкой") + (", проверено" if ov.calibrated else ", не проверено"))
    add("Линза", lambda: f"{ov.width()}x{ov.height()}, плашек {len(ov.blocks)}")
    add("Языки", lambda: f"экран={window.src_lang}, перевод={window.dst_lang}, запомнен={_auto_hint['key']}")
    add("Размер текста на экране, px", lambda: _scale_hint["h"])
    add("Перевод", lambda: f"каналы {_backends_order}, пауза Google {cooldown_left():.0f} с, кэш {len(_cache)}")
    add("Защита", lambda: f"режим={window.mode}, личные данные={window.protect_data}, окна={window.protect_window}, пауза при бездействии={window.idle_pause}")
    add("Хранение", lambda: f"не хранить={window.no_store}, очищать при выходе={window.clear_on_exit}, шифрование файлов={'да' if _crypto['ok'] else 'нет ' + str(_crypto['err'])}")
    add("Горячие клавиши", lambda: ", ".join(f"{name}={'ок' if window.hotkeys.ok.get(i) else 'не занята/нет'}" for i, name in ((1, "Ctrl+Alt+P"), (2, "Ctrl+Alt+T"), (3, "Ctrl+Alt+L"))))
    out.append("Последние сообщения:")
    out.extend(getattr(window, "report_log", [])[-15:] or ["—"])
    try:
        tail = LOG_FILE.read_text(encoding="utf-8")[-1500:]
        out.append("Журнал ошибок (конец):\n" + tail)
    except Exception:
        out.append("Журнал ошибок: пуст")
    return "\n".join(out)

def install_excepthook(get_window):
    import traceback
    def hook(exc_type, exc, tb):
        text = "".join(traceback.format_exception(exc_type, exc, tb))
        try:
            LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
            if LOG_FILE.exists() and LOG_FILE.stat().st_size > 200_000:
                LOG_FILE.unlink()
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
    app.setApplicationName("Lens 2.10")
    app.setStyle("Fusion")
    crypto_selftest()
    cleanup_stale_temp()
    STORE["on"]=str(QSettings("LensProject","Lens22").value("no_store","0")).lower() not in ("1","true")
    load_cache()
    window=MainWindow()
    install_excepthook(lambda: window)
    window.show()
    if str(window.settings.value("notice_v1","0"))!="1":
        QMessageBox.information(window,"Lens: что нужно знать",
            "Lens распознаёт текст под прозрачной областью и отправляет его в Google Translate (только текст, не картинку).\n\n"
            "Не наводите линзу на пароли, банковские данные и личные переписки. По умолчанию Lens старается скрывать такие "
            "фрагменты и отключается над окнами банков и менеджеров паролей, но гарантировать это нельзя.\n\n"
            "Пауза из любого окна — Ctrl+Alt+P. Все настройки приватности — на вкладке «Безопасность».")
        window.settings.setValue("notice_v1","1")
    sys.exit(app.exec())

if __name__=="__main__":
    main()
