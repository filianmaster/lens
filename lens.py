"""
Lens 2.3 — экранный переводчик с прозрачным изменяемым overlay.
Windows 10/11. OCR: Tesseract (в комплекте), 9 языков, авто/ручной режим.
Перевод: GoogleTranslator (требуется интернет).
"""
import sys, os, re, json, hashlib, threading, subprocess, tempfile, shutil, time
from pathlib import Path
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor

if sys.platform != "win32":
    raise SystemExit("Lens работает только в Windows 10/11.")

import mss
import pytesseract
from pytesseract import Output
from PIL import Image, ImageFilter, ImageEnhance
from deep_translator import GoogleTranslator
from langdetect import detect, DetectorFactory
from langdetect.lang_detect_exception import LangDetectException

from PySide6.QtCore import QObject, QPointF, QRectF, Qt, QTimer, Signal, QSettings
from PySide6.QtGui import QColor, QFont, QFontMetrics, QImage, QPainter, QPen, QIcon
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QLabel,
    QPushButton, QComboBox, QSlider, QTableWidget, QTableWidgetItem,
    QHeaderView, QTabWidget, QGroupBox, QLineEdit, QFrame, QGridLayout,
    QMessageBox, QAbstractItemView, QSizePolicy
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
HISTORY_FILE = Path(os.getenv("APPDATA", str(Path.home()))) / "Lens" / "history.json"

def translate_one(text, src, dst):
    if not text.strip() or src == dst:
        return text
    key = (text, src, dst)
    with _cache_lock:
        if key in _cache:
            return _cache[key]
    result = GoogleTranslator(source=src, target=dst).translate(text)
    if not result or not result.strip():
        raise RuntimeError("Переводчик вернул пустой результат")
    with _cache_lock:
        _cache[key] = result
    return result

def detect_language(text):
    try:
        detected = detect(text)
        return DETECT_TO_KEY.get(detected, "en")
    except LangDetectException:
        return "en"

def _ocr_one(img, model):
    scale = 1.5 if max(img.size) < 1500 else 1.0
    work = img.resize((int(img.width * scale), int(img.height * scale))) if scale != 1 else img
    work = ImageEnhance.Contrast(work.convert("RGB")).enhance(1.18)
    config = "--oem 1 --psm 11"
    data = pytesseract.image_to_data(work, lang=model, config=config,
                                     output_type=Output.DICT, timeout=5)
    grouped, confidences = {}, []
    for i, word in enumerate(data["text"]):
        word = (word or "").strip()
        try:
            conf = float(data["conf"][i])
        except (ValueError, TypeError):
            conf = -1
        if not word or conf < 32:
            continue
        key = (data["block_num"][i], data["par_num"][i], data["line_num"][i])
        x, y, w, h = (int(data[k][i] / scale) for k in ("left", "top", "width", "height"))
        item = grouped.setdefault(key, {"words": [], "x0": x, "y0": y, "x1": x+w, "y1": y+h})
        item["words"].append(word)
        item["x0"], item["y0"] = min(item["x0"], x), min(item["y0"], y)
        item["x1"], item["y1"] = max(item["x1"], x+w), max(item["y1"], y+h)
        confidences.append(conf)
    lines = []
    for item in grouped.values():
        text = " ".join(item["words"])
        if model in ("jpn", "chi_sim"):
            text = text.replace(" ", "")
        if any(c.isalpha() for c in text):
            lines.append((text, item["x0"], item["y0"], item["x1"], item["y1"]))
    chars = sum(len(x[0]) for x in lines)
    score = (sum(confidences) / len(confidences)) * min(1.0, chars / 24) if confidences else 0
    return lines, score

LANG_GROUPS = (("en", "de", "fr", "es"), ("ru", "uk"))  # близкие языки уточняем по тексту
AUTO_ACCEPT = 50.0      # если запомненный язык дал такую уверенность — остальные модели не гоняем
AUTO_HINT_TTL = 20.0    # раз в столько секунд язык определяется заново
_auto_hint = {"key": None, "time": 0.0}
_hint_lock = threading.Lock()

def reset_auto_hint():
    with _hint_lock:
        _auto_hint["key"] = None

def refine_language(key, lines):
    for group in LANG_GROUPS:
        if key in group:
            detected = detect_language("\n".join(line[0] for line in lines))
            return detected if detected in group else key
    return key

def _auto_sweep(img):
    keys = [k for k in LANGS if k != "auto"]
    def run(k):
        try:
            lines, score = _ocr_one(img, LANGS[k][1])
        except Exception:
            return k, [], -1.0
        return k, lines, score
    best_lines, best_key, best_score = [], "en", -1.0
    # Модели сравниваем по отдельности (смесь из девяти портила распознавание), но параллельно.
    for k, lines, score in POOL.map(run, keys):
        if score > best_score:
            best_lines, best_key, best_score = lines, k, score
    return best_lines, best_key

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
            return lines, refine_language(hint, lines)
    lines, model_key = _auto_sweep(img)
    with _hint_lock:
        _auto_hint["key"] = model_key if lines else None
        _auto_hint["time"] = time.monotonic()
    return lines, (refine_language(model_key, lines) if lines else model_key)

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
    for px in range(max(start_px, 10), 7, -1):
        font.setPixelSize(px)
        fm = QFontMetrics(font)
        lines = wrap(text, fm, max(30, width))
        if len(lines) * fm.lineSpacing() <= max(12, height):
            break
    return font, lines, fm.lineSpacing(), fm.ascent()

class Bridge(QObject):
    done = Signal(object)
    history_add = Signal(str, str, str)

def scan(bridge, rect, src, dst, blur_k, last_sig, generation):
    result = {"gen": generation, "blocks": [], "sig": last_sig, "same": False, "error": None, "info": None, "size": (1, 1)}
    try:
        left, top, right, bottom = rect
        width, height = right-left, bottom-top
        result["size"] = (width, height)
        if width < 35 or height < 35:
            return
        with mss.mss() as sct:
            shot = sct.grab({"left": left, "top": top, "width": width, "height": height})
        img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
        sig = hashlib.md5(img.tobytes()).hexdigest()
        result["sig"] = sig
        if sig == last_sig:
            result["same"] = True
            return
        try:
            lines, actual_src = ocr_lines(img, src)
        except Exception as exc:
            result["error"] = f"Ошибка OCR: {exc}"
            return
        if not lines:
            return
        groups = []
        # Merge nearby lines into compact paragraph blocks.
        for line in sorted(lines, key=lambda x: (x[2], x[1])):
            text, x0, y0, x1, y1 = line
            match = None
            for g in groups:
                line_h = max(1, g["h"] / len(g["parts"]))
                gap = y0 - g["y1"]
                overlap = min(x1, g["x1"]) - max(x0, g["x0"])
                if -0.3*line_h <= gap <= 0.8*line_h and overlap > 0:
                    match = g; break
            if match:
                match["parts"].append(text)
                match["h"] += y1-y0
                match["x0"], match["y0"] = min(match["x0"],x0), min(match["y0"],y0)
                match["x1"], match["y1"] = max(match["x1"],x1), max(match["y1"],y1)
            else:
                groups.append({"parts":[text], "h":y1-y0, "x0":x0, "y0":y0, "x1":x1, "y1":y1})
        if actual_src == dst:
            result["info"] = "Текст уже на выбранном языке"
            return
        src_code, dst_code = LANGS[actual_src][2], LANGS[dst][2]
        jobs = []
        for g in groups:
            original = " ".join(g["parts"])[:3000]
            if original.strip():
                jobs.append((g, original, POOL.submit(translate_one, original, src_code, dst_code)))
        for g, original, future in jobs:
            try:
                translated = future.result()
            except Exception as exc:
                result["error"] = f"Ошибка перевода: проверьте интернет. ({str(exc)[:100]})"
                return
            bridge.history_add.emit(original, translated, actual_src)
            line_h = max(12, g["h"] / len(g["parts"]))
            pad = int(line_h * 0.32)
            box = (max(0,g["x0"]-pad), max(0,g["y0"]-pad),
                   min(width,g["x1"]+pad), min(height,g["y1"]+pad))
            patch = img.crop(box).filter(ImageFilter.GaussianBlur(max(2.0,line_h*blur_k))).convert("RGBA")
            qimg = QImage(patch.tobytes(),patch.width,patch.height,patch.width*4,QImage.Format.Format_RGBA8888).copy()
            result["blocks"].append({"box":box,"lh":line_h,"text":translated,"img":qimg})
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
        self.settle.setInterval(250)
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
        self.bridge = Bridge()
        self.bridge.done.connect(self.on_result)
        self.bridge.history_add.connect(self.main.add_history_entry)
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.timer.start(700)

    def showEvent(self, event):
        super().showEvent(event)
        # Keep the overlay itself out of screen captures, otherwise OCR may read its own translation.
        try:
            import ctypes
            from ctypes import wintypes
            ctypes.windll.user32.SetWindowDisplayAffinity(
                wintypes.HWND(int(self.winId())), 0x00000011  # WDA_EXCLUDEFROMCAPTURE
            )
        except Exception:
            pass

    def moveEvent(self, event):
        super().moveEvent(event)
        self.reset()
        self.settle.start()

    def resizeEvent(self, event):
        super().resizeEvent(event)
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
        self.blocks = []
        self.update()

    def tick(self):
        if self.busy or self.paused or not self.isVisible():
            return
        if QApplication.mouseButtons() & Qt.MouseButton.LeftButton:
            return
        self.busy = True
        threading.Thread(target=scan, args=(self.bridge,self.rect_on_screen(),
            self.main.src_lang,self.main.dst_lang,self.main.blur_k,self.last_sig,self.generation),daemon=True).start()

    def on_result(self, result):
        self.busy = False
        if result["gen"] != self.generation:
            return
        if result["error"]:
            self.status = result["error"]
            QTimer.singleShot(5000, self.clear_status)
            self.update()
            return
        if result["same"]:
            return
        self.last_sig = result["sig"]
        if result.get("info"):
            self.status = result["info"]
            QTimer.singleShot(3000, self.clear_status)
        w,h = result["size"]
        sx,sy = self.width()/max(1,w),self.height()/max(1,h)
        blocks=[]
        for b in result["blocks"]:
            x0,y0,x1,y1=b["box"]
            patch=QRectF(x0*sx,y0*sy,(x1-x0)*sx,(y1-y0)*sy)
            box=QRectF(patch)
            font,lines,ls,asc=text_layout(b["text"],box.width()-14,box.height()-8,min(28,int(b["lh"]*sy*.9)))
            need=len(lines)*ls+10
            if need>box.height(): box.setHeight(need)
            blocks.append({"patch":patch,"box":box,"img":b["img"],"font":font,"lines":lines,"ls":ls,"asc":asc})
        self.blocks=blocks
        self.update()

    def clear_status(self):
        self.status=""
        self.update()

    def paintEvent(self, event):
        p=QPainter(self)
        p.setRenderHints(QPainter.RenderHint.Antialiasing|QPainter.RenderHint.SmoothPixmapTransform|QPainter.RenderHint.TextAntialiasing)
        p.fillRect(self.rect(),QColor(0,0,0,2))
        for b in self.blocks:
            p.drawImage(b["patch"],b["img"])
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(15,19,29,72))
            p.drawRoundedRect(b["box"],7,7)
            p.setFont(b["font"]); p.setPen(QColor("#f4f7ff"))
            top=b["box"].top()+(b["box"].height()-len(b["lines"])*b["ls"])/2
            for i,line in enumerate(b["lines"]):
                p.drawText(QPointF(b["box"].left()+7,top+i*b["ls"]+b["asc"]),line)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(35,145,255,210),2))
        p.drawRoundedRect(QRectF(self.rect()).adjusted(1,1,-1,-1),8,8)
        if self.paused or self.status:
            msg=("Ⅱ ПАУЗА" if self.paused else self.status)
            p.setFont(QFont("Segoe UI",9,QFont.Weight.Bold))
            p.fillRect(QRectF(8,8,min(self.width()-16,360),26),QColor(10,13,20,220))
            p.setPen(Qt.GlobalColor.white); p.drawText(16,26,msg[:65])

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
        self.setWindowTitle("Lens 2.3 — Экранный переводчик")
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
        title=QLabel("LENS 2.3"); title.setObjectName("hero")
        sub=QLabel("Экранный переводчик · OCR + перевод в реальном времени"); sub.setObjectName("sub")
        brand.addWidget(title); brand.addWidget(sub); header.addLayout(brand); header.addStretch()
        self.status_badge=QLabel("Проверка OCR…"); self.status_badge.setStyleSheet("background:#20344c;color:#9ecbff;padding:8px 12px;border-radius:10px;font-weight:600;")
        header.addWidget(self.status_badge); outer.addLayout(header)

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
        hint=QLabel("Подсказка: наведите область на нужный текст. Пробел — пауза, Esc — скрыть окно.")
        hint.setObjectName("sub"); hint.setWordWrap(True); lay.addWidget(hint)
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
        self.table.setAlternatingRowColors(True); self.table.setWordWrap(True); self.table.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.cellDoubleClicked.connect(self.copy_translation); hl.addWidget(self.table)
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
            self.overlay.show(); self.overlay.raise_()
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
        rows=[x for x in self.history if query in (x["original"]+" "+x["translated"]).lower()]
        self.table.setRowCount(len(rows))
        for r,item in enumerate(rows):
            values=[item["time"],item["original"],item["translated"]]
            for c,value in enumerate(values):
                cell=QTableWidgetItem(value); cell.setToolTip(value); self.table.setItem(r,c,cell)
        self.count_label.setText(f"{len(rows)} записей")

    def filter_history(self):
        self.render_history()

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

def main():
    app=QApplication(sys.argv)
    app.setApplicationName("Lens 2.3")
    app.setStyle("Fusion")
    window=MainWindow(); window.show()
    sys.exit(app.exec())

if __name__=="__main__":
    main()
