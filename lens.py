"""
Lens 2.0 — Прозрачное окно-переводчик с панелью управления.
Работает на Windows 10 (2004+) и Windows 11.
"""
import sys

if sys.platform != "win32":
    sys.exit("Lens работает только в ОС Windows 10/11.")

import asyncio
import ctypes
import hashlib
import threading
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from ctypes import wintypes

import mss
import winocr
from deep_translator import GoogleTranslator
from PIL import Image, ImageFilter
from PySide6.QtCore import QObject, QPointF, QRectF, Qt, QTimer, Signal
from PySide6.QtGui import QColor, QFont, QFontMetrics, QImage, QPainter, QPen
from PySide6.QtWidgets import (
    QApplication, QMenu, QWidget, QMainWindow, QVBoxLayout, QHBoxLayout,
    QLabel, QPushButton, QComboBox, QSlider, QTableWidget, QTableWidgetItem,
    QHeaderView, QTabWidget, QGroupBox
)

LANGS = {
    "en": ("English", "en"),
    "ru": ("Русский", "ru"),
    "uk": ("Українська", "uk"),
    "ja": ("日本語", "ja"),
    "zh-CN": ("中文", "zh-Hans-CN"),
    "ko": ("한국어", "ko"),
    "de": ("Deutsch", "de"),
    "fr": ("Français", "fr"),
    "es": ("Español", "es"),
}

NO_SPACES = {"ja", "zh-CN"}
BLUR_LEVELS = {"Слабый": 0.25, "Средний": 0.5, "Сильный": 0.9}
EDGE = 8
WDA_EXCLUDEFROMCAPTURE = 0x11
user32 = ctypes.windll.user32

_cache = {}
_pool = ThreadPoolExecutor(max_workers=6)

def _translate_one(args):
    text, src, dst = args
    if src == dst:
        return text
    key = (text, src, dst)
    if key not in _cache:
        try:
            _cache[key] = GoogleTranslator(source=src, target=dst).translate(text) or text
        except Exception:
            _cache[key] = text
    return _cache[key]

def _g(obj, name):
    return obj[name] if isinstance(obj, dict) else getattr(obj, name)

def ocr_lines(img, src):
    res = asyncio.run(winocr.recognize_pil(img, LANGS[src][1]))
    lines = []
    for ln in _g(res, "lines"):
        x0 = y0 = 10 ** 9
        x1 = y1 = -1
        for wd in _g(ln, "words"):
            br = _g(wd, "bounding_rect")
            x, y, bw, bh = (_g(br, k) for k in ("x", "y", "width", "height"))
            x0, y0 = min(x0, x), min(y0, y)
            x1, y1 = max(x1, x + bw), max(y1, y + bh)
        if x1 < 0:
            continue
        text = _g(ln, "text")
        if src in NO_SPACES:
            text = text.replace(" ", "")
        lines.append((text, x0, y0, x1, y1))
    return lines

def group_paragraphs(lines):
    lines.sort(key=lambda s: (s[2], s[1]))
    groups = []
    for text, x0, y0, x1, y1 in lines:
        h = y1 - y0
        for g in groups:
            lh = g["h"] / len(g["t"])
            gap = y0 - g["y1"]
            overlap = min(x1, g["x1"]) - max(x0, g["x0"])
            if -0.3 * lh <= gap <= 0.7 * lh and overlap > 0 and abs(h - lh) <= 0.5 * lh:
                g["t"].append(text)
                g["h"] += h
                g["x0"], g["y0"] = min(g["x0"], x0), min(g["y0"], y0)
                g["x1"], g["y1"] = max(g["x1"], x1), max(g["y1"], y1)
                break
        else:
            groups.append({"t": [text], "h": h, "x0": x0, "y0": y0, "x1": x1, "y1": y1})
    return groups

class Bridge(QObject):
    done = Signal(object)
    history_add = Signal(str, str)

def scan(bridge, rect, src, dst, blur_k, last_sig, gen):
    out = {"gen": gen, "blocks": [], "sig": last_sig, "same": False, "error": None, "size": (1, 1)}
    try:
        left, top, right, bottom = rect
        w, h = right - left, bottom - top
        out["size"] = (w, h)
        if w < 30 or h < 30:
            return
        with mss.mss() as sct:
            shot = sct.grab({"left": left, "top": top, "width": w, "height": h})
        img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")

        sig = hashlib.md5(img.tobytes()).hexdigest()
        out["sig"] = sig
        if sig == last_sig:
            out["same"] = True
            return

        try:
            lines = ocr_lines(img, src)
        except Exception:
            out["error"] = f"OCR недоступен для «{LANGS[src][0]}»"
            return

        groups = []
        for g in group_paragraphs(lines):
            text = (" " if src not in NO_SPACES else "").join(g["t"])[:4500]
            if any(c.isalpha() for c in text):
                g["text"] = text
                groups.append(g)
        if not groups:
            return

        try:
            translated = list(_pool.map(_translate_one, [(g["text"], src, dst) for g in groups]))
        except Exception:
            out["error"] = "Ошибка сети"
            return

        for g, tr in zip(groups, translated):
            bridge.history_add.emit(g["text"], tr)
            lh = g["h"] / len(g["t"])
            pad = int(lh * 0.3)
            box = (max(0, int(g["x0"]) - pad), max(0, int(g["y0"]) - pad),
                   min(w, int(g["x1"]) + pad), min(h, int(g["y1"]) + pad))
            patch = (img.crop(box)
                     .filter(ImageFilter.GaussianBlur(max(2.0, lh * blur_k)))
                     .convert("RGBA"))
            qimg = QImage(patch.tobytes(), patch.width, patch.height, patch.width * 4,
                          QImage.Format.Format_RGBA8888).copy()
            out["blocks"].append({"box": box, "lh": lh, "text": tr, "img": qimg})
    except Exception as e:
        out["error"] = f"Сбой: {e}"
    finally:
        bridge.done.emit(out)

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
                out.append(cur)
                cur = ""
            while fm.horizontalAdvance(word) > width and len(word) > 1:
                n = len(word)
                while n > 1 and fm.horizontalAdvance(word[:n]) > width:
                    n -= 1
                out.append(word[:n])
                word = word[n:]
            cur = word
        out.append(cur)
    return out

def layout(text, width, height, start_px):
    font = QFont("Segoe UI")
    for px in range(max(start_px, 10), 7, -1):
        font.setPixelSize(px)
        fm = QFontMetrics(font)
        lines = wrap(text, fm, width)
        if len(lines) * fm.lineSpacing() <= height:
            break
    return font, lines, fm.lineSpacing(), fm.ascent()

class LensOverlay(QWidget):
    def __init__(self, main_window):
        super().__init__()
        self.main_win = main_window
        self.setWindowTitle("Lens Overlay")
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.WindowStaysOnTopHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setMouseTracking(True)
        self.setMinimumSize(100, 50)
        self.resize(600, 250)
        self.move(250, 250)

        self.paused = False
        self.menu_open = False
        self.busy = False
        self.gen = 0
        self.last_sig = None
        self.blocks = []
        self.status = ""
        self._affinity_done = False

        self.bridge = Bridge()
        self.bridge.done.connect(self.on_result)
        self.bridge.history_add.connect(self.main_win.add_history_entry)

        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.timer.start(600)

    def hwnd(self):
        return wintypes.HWND(int(self.winId()))

    def current_rect(self):
        r = wintypes.RECT()
        user32.GetWindowRect(self.hwnd(), ctypes.byref(r))
        return (r.left, r.top, r.right, r.bottom)

    def flash(self, text, ms=4000):
        self.status = text
        self.update()
        QTimer.singleShot(ms, lambda: self._clear_status(text))

    def _clear_status(self, text):
        if self.status == text:
            self.status = ""
            self.update()

    def reset(self):
        self.gen += 1
        self.last_sig = None
        self.blocks = []
        self.update()

    def showEvent(self, e):
        super().showEvent(e)
        if not self._affinity_done:
            self._affinity_done = True
            user32.SetWindowDisplayAffinity(self.hwnd(), WDA_EXCLUDEFROMCAPTURE)

    def resizeEvent(self, e):
        self.reset()

    def moveEvent(self, e):
        self.reset()

    def tick(self):
        if self.busy or self.paused or self.menu_open or not self.isVisible():
            return
        if QApplication.mouseButtons() & Qt.MouseButton.LeftButton:
            return
        self.busy = True
        threading.Thread(
            target=scan,
            args=(self.bridge, self.current_rect(), self.main_win.src_lang,
                  self.main_win.dst_lang, self.main_win.blur_k, self.last_sig, self.gen),
            daemon=True,
        ).start()

    def on_result(self, res):
        self.busy = False
        if res["gen"] != self.gen:
            return
        if res["error"]:
            self.flash(res["error"], 6000)
            return
        if res["same"]:
            return
        self.last_sig = res["sig"]

        pw, ph = res["size"]
        sx, sy = self.width() / pw, self.height() / ph
        blocks = []
        for b in res["blocks"]:
            x0, y0, x1, y1 = b["box"]
            patch = QRectF(x0 * sx, y0 * sy, (x1 - x0) * sx, (y1 - y0) * sy)
            box = QRectF(patch)
            start = int(b["lh"] * sy * 0.9)
            font, lines, ls, asc = layout(b["text"], box.width() - 8, box.height() - 4, min(40, start))
            need = len(lines) * ls + 4
            if need > box.height():
                box.setHeight(need)
            blocks.append({"patch": patch, "box": box, "img": b["img"],
                           "font": font, "lines": lines, "ls": ls, "asc": asc})
        self.blocks = blocks
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHints(QPainter.RenderHint.Antialiasing
                         | QPainter.RenderHint.SmoothPixmapTransform
                         | QPainter.RenderHint.TextAntialiasing)
        p.fillRect(self.rect(), QColor(0, 0, 0, 4))

        for b in self.blocks:
            p.drawImage(b["patch"], b["img"])
            p.fillRect(b["box"], QColor(12, 14, 20, 190))
            p.setFont(b["font"])
            p.setPen(QColor(255, 255, 255))
            box = b["box"]
            top = box.top() + (box.height() - len(b["lines"]) * b["ls"]) / 2
            for i, line in enumerate(b["lines"]):
                p.drawText(QPointF(box.left() + 4, top + i * b["ls"] + b["asc"]), line)

        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(0, 120, 215, 200), 2))
        p.drawRoundedRect(QRectF(self.rect()).adjusted(1, 1, -1, -1), 6, 6)

        text = ("⏸ ПАУЗА · " if self.paused else "") + self.status
        if text:
            p.setFont(QFont("Segoe UI", 9, QFont.Weight.Bold))
            fm = p.fontMetrics()
            text = fm.elidedText(text, Qt.TextElideMode.ElideRight, max(20, self.width() - 28))
            r = QRectF(4, 4, fm.horizontalAdvance(text) + 12, fm.height() + 6)
            p.fillRect(r, QColor(0, 0, 0, 200))
            p.setPen(QColor(255, 255, 255))
            p.drawText(QPointF(r.left() + 6, r.top() + 3 + fm.ascent()), text)

    def _zone(self, pos):
        return (pos.x() <= EDGE, pos.x() >= self.width() - EDGE,
                pos.y() <= EDGE, pos.y() >= self.height() - EDGE)

    def mouseMoveEvent(self, e):
        l, r, t, b = self._zone(e.position().toPoint())
        C = Qt.CursorShape
        if (l and t) or (r and b):
            c = C.SizeFDiagCursor
        elif (r and t) or (l and b):
            c = C.SizeBDiagCursor
        elif l or r:
            c = C.SizeHorCursor
        elif t or b:
            c = C.SizeVerCursor
        else:
            c = C.SizeAllCursor
        self.setCursor(c)

    def mousePressEvent(self, e):
        if e.button() != Qt.MouseButton.LeftButton:
            return
        l, r, t, b = self._zone(e.position().toPoint())
        E = Qt.Edge
        edges = [edge for flag, edge in ((l, E.LeftEdge), (r, E.RightEdge), (t, E.TopEdge), (b, E.BottomEdge)) if flag]
        handle = self.windowHandle()
        if edges:
            combined = edges[0]
            for x in edges[1:]:
                combined |= x
            handle.startSystemResize(combined)
        else:
            handle.startSystemMove()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.hide()
            self.main_win.update_toggle_btn()
        elif e.key() == Qt.Key.Key_Space:
            self.paused = not self.paused
            self.update()

    def contextMenuEvent(self, e):
        m = QMenu(self)
        pause = m.addAction("Пауза (Пробел)")
        pause.setCheckable(True)
        pause.setChecked(self.paused)
        pause.triggered.connect(lambda: setattr(self, 'paused', not self.paused))
        m.addSeparator()
        m.addAction("Скрыть окно перевода (Esc)").triggered.connect(lambda: (self.hide(), self.main_win.update_toggle_btn()))
        self.menu_open = True
        m.exec(e.globalPos())
        self.menu_open = False

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Lens 2.0 — Панель Управления")
        self.resize(750, 500)
        self.setStyleSheet("""
            QMainWindow { background-color: #1e1e24; }
            QWidget { color: #e0e0e0; font-family: 'Segoe UI', sans-serif; font-size: 13px; }
            QGroupBox { border: 1px solid #33333f; border-radius: 8px; margin-top: 10px; font-weight: bold; }
            QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 5px; color: #0078d7; }
            QPushButton { background-color: #0078d7; color: white; border: none; border-radius: 5px; padding: 8px 16px; font-weight: bold; }
            QPushButton:hover { background-color: #0063b1; }
            QPushButton:pressed { background-color: #004e8c; }
            QPushButton#toggleBtn { background-color: #28a745; font-size: 14px; padding: 12px; }
            QPushButton#toggleBtn:checked { background-color: #dc3545; }
            QComboBox { background-color: #2a2a35; border: 1px solid #3a3a4c; border-radius: 4px; padding: 5px; color: white; }
            QTableWidget { background-color: #18181c; gridline-color: #2a2a35; border: 1px solid #2a2a35; border-radius: 6px; }
            QHeaderView::section { background-color: #252530; color: white; padding: 5px; border: none; }
        """)

        self.src_lang = "en"
        self.dst_lang = "ru"
        self.blur_k = 0.5
        self.history_records = set()

        self.overlay = LensOverlay(self)
        self.init_ui()

    def init_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QVBoxLayout(central)

        tabs = QTabWidget()
        main_layout.addWidget(tabs)

        tab_main = QWidget()
        layout_main = QVBoxLayout(tab_main)

        self.toggle_btn = QPushButton("▶ Запустить Окно Перевода")
        self.toggle_btn.setObjectName("toggleBtn")
        self.toggle_btn.setCheckable(True)
        self.toggle_btn.clicked.connect(self.toggle_overlay)
        layout_main.addWidget(self.toggle_btn)

        group_langs = QGroupBox("Языки Перевода")
        l_layout = QHBoxLayout(group_langs)
        
        l_layout.addWidget(QLabel("Язык на экране:"))
        self.cb_src = QComboBox()
        for k, v in LANGS.items():
            self.cb_src.addItem(v[0], k)
        self.cb_src.setCurrentIndex(0)
        self.cb_src.currentIndexChanged.connect(self.on_lang_changed)
        l_layout.addWidget(self.cb_src)

        l_layout.addWidget(QLabel("→ Переводить на:"))
        self.cb_dst = QComboBox()
        for k, v in LANGS.items():
            self.cb_dst.addItem(v[0], k)
        self.cb_dst.setCurrentIndex(1)
        self.cb_dst.currentIndexChanged.connect(self.on_lang_changed)
        l_layout.addWidget(self.cb_dst)
        layout_main.addWidget(group_langs)

        group_opt = QGroupBox("Параметры Окна")
        opt_layout = QVBoxLayout(group_opt)
        
        b_box = QHBoxLayout()
        b_box.addWidget(QLabel("Интенсивность размытия оригинального текста:"))
        self.cb_blur = QComboBox()
        for k in BLUR_LEVELS.keys():
            self.cb_blur.addItem(k)
        self.cb_blur.setCurrentIndex(1)
        self.cb_blur.currentIndexChanged.connect(self.on_blur_changed)
        b_box.addWidget(self.cb_blur)
        opt_layout.addLayout(b_box)

        fps_box = QHBoxLayout()
        fps_box.addWidget(QLabel("Интервал обновления OCR (мс):"))
        self.slider_fps = QSlider(Qt.Orientation.Horizontal)
        self.slider_fps.setRange(200, 2000)
        self.slider_fps.setValue(600)
        self.slider_fps.setSingleStep(100)
        self.lbl_fps = QLabel("600 мс")
        self.slider_fps.valueChanged.connect(self.on_fps_changed)
        fps_box.addWidget(self.slider_fps)
        fps_box.addWidget(self.lbl_fps)
        opt_layout.addLayout(fps_box)

        layout_main.addWidget(group_opt)
        layout_main.addStretch()

        tabs.addTab(tab_main, "Управление")

        tab_hist = QWidget()
        layout_hist = QVBoxLayout(tab_hist)

        self.table = QTableWidget(0, 3)
        self.table.setHorizontalHeaderLabels(["Время", "Оригинал", "Перевод"])
        self.table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        self.table.horizontalHeader().setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        layout_hist.addWidget(self.table)

        btn_clear = QPushButton("Очистить Историю")
        btn_clear.clicked.connect(self.clear_history)
        layout_hist.addWidget(btn_clear)

        tabs.addTab(tab_hist, "История")

    def toggle_overlay(self):
        if self.toggle_btn.isChecked():
            self.overlay.show()
            self.toggle_btn.setText("⏹ Скрыть Окно Перевода")
        else:
            self.overlay.hide()
            self.toggle_btn.setText("▶ Запустить Окно Перевода")

    def update_toggle_btn(self):
        self.toggle_btn.setChecked(False)
        self.toggle_btn.setText("▶ Запустить Окно Перевода")

    def on_lang_changed(self):
        self.src_lang = self.cb_src.currentData()
        self.dst_lang = self.cb_dst.currentData()
        self.overlay.reset()

    def on_blur_changed(self):
        txt = self.cb_blur.currentText()
        self.blur_k = BLUR_LEVELS.get(txt, 0.5)
        self.overlay.reset()

    def on_fps_changed(self, val):
        self.lbl_fps.setText(f"{val} мс")
        self.overlay.timer.setInterval(val)

    def add_history_entry(self, src_text, dst_text):
        if (src_text, dst_text) in self.history_records:
            return
        self.history_records.add((src_text, dst_text))

        row = self.table.rowCount()
        self.table.insertRow(row)
        time_str = datetime.now().strftime("%H:%M:%S")

        self.table.setItem(row, 0, QTableWidgetItem(time_str))
        self.table.setItem(row, 1, QTableWidgetItem(src_text))
        self.table.setItem(row, 2, QTableWidgetItem(dst_text))

    def clear_history(self):
        self.table.setRowCount(0)
        self.history_records.clear()

    def closeEvent(self, e):
        self.overlay.close()
        super().closeEvent(e)

def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    win = MainWindow()
    win.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()