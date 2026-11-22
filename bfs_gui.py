"""
bfs_gui.py -- PySide6 visualizer for both BFS engines (improved visuals).

Tab 1: string BFS -- prefix tree, animated, hover-traceable, charted.
Tab 2: proof BFS -- live search monitor + animated proof-tree construction.

    pip install PySide6
    python bfs_gui.py    # beside string_bfs.py and proof_bfs.py
"""

import sys
import math
from collections import deque

import string_bfs
import proof_bfs as pb

from PySide6.QtCore import Qt, QTimer, QRectF, QPointF
from PySide6.QtGui import (QBrush, QColor, QFont, QFontMetricsF, QImage, QLineF,
                           QPainter, QPen, QToolTip)
from PySide6.QtWidgets import (QApplication, QCheckBox, QComboBox, QFileDialog,
                               QGraphicsDropShadowEffect, QGraphicsEllipseItem,
                               QGraphicsScene, QGraphicsView, QFormLayout,
                               QHBoxLayout, QLabel, QLineEdit, QListWidget,
                               QMainWindow, QMessageBox, QPushButton, QSlider,
                               QSpinBox, QSplitter, QTextEdit, QTabWidget,
                               QVBoxLayout, QWidget)

# ---------------------------------------------------------------- palette
PASS      = QColor("#4ade80"); PASS_RING = QColor("#166534"); PASS_EDGE = QColor(34, 197, 94, 170)
FAIL      = QColor("#fecaca"); FAIL_RING = QColor("#f87171"); FAIL_EDGE = QColor(248, 113, 113, 140)
NEUTRAL   = QColor("#e4e4e7"); NEUT_RING = QColor("#a1a1aa")
HOVER     = QColor("#2563eb"); HOVER_FILL = QColor("#93c5fd")
BG        = QColor("#fbfbf9")
CHAR_COL  = {'p': '#1d4ed8', 'q': '#1d4ed8', 'r': '#1d4ed8', 's': '#1d4ed8',
             '⊤': '#0f766e', '⊥': '#b91c1c', '¬': '#7c3aed',
             '∧': '#b45309', '∨': '#0e7490', '→': '#c2410c',
             '(': '#64748b', ')': '#64748b'}

MONO = QFont("Consolas"); MONO.setStyleHint(QFont.Monospace); MONO.setPointSize(10)

ROW, R = 84, 8


def rule_color(rule):
    if rule == 'Ax':                    return '#1a7f37'
    if rule == 'RAA':                   return '#a626a4'
    if rule.startswith(('∧I', '∨I', '→I', '¬I')): return '#1f6feb'
    return '#d4820a'


def human(v):
    for div, suf in ((1e9, 'G'), (1e6, 'M'), (1e3, 'k')):
        if v >= div:
            return f"{v / div:.0f}{suf}"
    return f"{v:.0f}"


def node_base(ok):
    if ok is None: return QBrush(NEUTRAL),  QPen(NEUT_RING, 1.2)
    if ok:         return QBrush(PASS),     QPen(PASS_RING, 1.4)
    return QBrush(FAIL), QPen(FAIL_RING, 1.0)


def edge_pen(ok):
    return QPen(PASS_EDGE, 1.1) if ok else QPen(FAIL_EDGE, 1.0)


def export_scene(parent, scene, default="proof.png"):
    path, _ = QFileDialog.getSaveFileName(parent, "Export image", default, "PNG (*.png)")
    if not path:
        return
    rect = scene.itemsBoundingRect().adjusted(-16, -16, 16, 16)
    img = QImage((rect.size() * 2).toSize(), QImage.Format_ARGB32_Premultiplied)
    img.fill(Qt.white)
    p = QPainter(img)
    p.setRenderHint(QPainter.Antialiasing)
    scene.render(p, QRectF(img.rect()), rect)
    p.end()
    img.save(path)


# ---------------------------------------------------------------- animator
class Animator:
    """Tiny tween engine: kinds 'p' (pos), 'l' (line), 'o' (opacity), 'r' (pulse)."""

    def __init__(self, scene, parent):
        self.scene = scene
        self.entries = []
        self.timer = QTimer(parent)
        self.timer.setInterval(16)
        self.timer.timeout.connect(self._frame)

    def add(self, kind, item, a, b, dur=0.35):
        self.entries.append([kind, item, a, b, 0.0, dur])
        self.timer.start()

    def clear(self):
        self.entries = []
        self.timer.stop()

    def _frame(self):
        dt = 1 / 60
        alive = []
        for e in self.entries:
            kind, item, a, b, p, dur = e
            p += dt / dur
            k = min(1.0, p)
            ease = 1 - (1 - k) ** 3
            if kind == 'p':
                item.setPos(QPointF(a.x() + (b.x() - a.x()) * ease,
                                    a.y() + (b.y() - a.y()) * ease))
            elif kind == 'l':
                item.setLine(QLineF(a.x1() + (b.x1() - a.x1()) * ease,
                                    a.y1() + (b.y1() - a.y1()) * ease,
                                    a.x2() + (b.x2() - a.x2()) * ease,
                                    a.y2() + (b.y2() - a.y2()) * ease))
            elif kind == 'o':
                for it in (item if isinstance(item, list) else [item]):
                    it.setOpacity(a + (b - a) * ease)
            elif kind == 'r':                       # expanding, fading ring
                rr = a + (b - a) * ease
                item.setRect(-rr, -rr, 2 * rr, 2 * rr)
                item.setOpacity(1 - k)
            e[4] = p
            if k < 1:
                alive.append(e)
            elif kind == 'r':
                self.scene.removeItem(item)
        self.entries = alive
        if not self.entries:
            self.timer.stop()


# ---------------------------------------------------------------- views
class ZoomView(QGraphicsView):
    """Wheel = zoom at cursor, drag = pan."""

    def __init__(self):
        super().__init__()
        self.setDragMode(QGraphicsView.ScrollHandDrag)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorViewCenter)
        self.setRenderHint(QPainter.Antialiasing)
        self.setBackgroundBrush(QBrush(BG))

    def wheelEvent(self, e):
        f = 1.25 ** (1 if e.angleDelta().y() > 0 else -1)
        self.scale(f, f)


class NodeEllipse(QGraphicsEllipseItem):
    """Hoverable tree node; the tab traces the root path on hover."""

    def __init__(self, tab, idx):
        super().__init__(-R, -R, 2 * R, 2 * R)
        self.tab, self.idx = tab, idx
        self.setAcceptHoverEvents(True)

    def hoverEnterEvent(self, _): self.tab.hover_node(self.idx, True)
    def hoverLeaveEvent(self, _): self.tab.hover_node(self.idx, False)


# ---------------------------------------------------------------- charts
class LevelChart(QWidget):
    """Log-scale bars with gridlines, survival %, and hover tooltips."""

    def __init__(self):
        super().__init__()
        self.data = []
        self.setMinimumHeight(130)
        self.setMouseTracking(True)

    def set_data(self, data):
        self.data = data
        self.update()

    def _geom(self):
        return 46, 22, 56, self.height() - 42          # x0, top, pitch, base

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.fillRect(self.rect(), QColor("#ffffff"))
        if not self.data:
            return
        x0, top, pitch, base = self._geom()
        maxt = max(t for t, _ in self.data)
        scale = lambda v: 0 if v <= 0 else (math.log10(v + 1) / math.log10(maxt + 1)) * (base - top)
        f_small = QFont(self.font()); f_small.setPointSize(7)

        for e in range(0, int(math.log10(max(10, maxt))) + 1):     # gridlines
            v = 10 ** e
            y = base - scale(v)
            p.setPen(QPen(QColor("#e4e4e7"), 0, Qt.DashLine))
            p.drawLine(x0, y, self.width() - 8, y)
            p.setPen(QPen(QColor("#a1a1aa"))); p.setFont(f_small)
            p.drawText(QRectF(2, y - 6, x0 - 6, 12), Qt.AlignRight, human(v))

        for i, (t, g) in enumerate(self.data):                     # bars
            x = x0 + i * pitch
            ht, hg = scale(t), scale(g)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor("#fda4af")); p.drawRect(x, base - ht, 11, ht)
            p.setBrush(PASS);              p.drawRect(x + 13, base - hg, 11, hg)
            p.setPen(QPen(QColor("#52525b"))); p.setFont(f_small)
            p.drawText(QRectF(x - 8, base + 4, pitch - 8, 12),
                       Qt.AlignHCenter, f"L{i+1}")
            p.setPen(QPen(QColor("#166534")))
            p.drawText(QRectF(x - 8, base - ht - 13, 40, 12),
                       Qt.AlignLeft, f"{100 * g / t:.0f}%")

        p.setFont(f_small)                                          # legend
        p.setBrush(QColor("#fda4af")); p.setPen(Qt.NoPen)
        p.drawRect(x0, 5, 8, 8)
        p.setPen(QPen(QColor("#52525b")))
        p.drawText(QRectF(x0 + 12, 2, 70, 12), Qt.AlignLeft, "tested")
        p.setBrush(PASS); p.setPen(Qt.NoPen)
        p.drawRect(x0 + 60, 5, 8, 8)
        p.setPen(QPen(QColor("#52525b")))
        p.drawText(QRectF(x0 + 72, 2, 90, 12), Qt.AlignLeft, "passed (WFF)")

    def mouseMoveEvent(self, e):
        if not self.data:
            return
        x0, _, pitch, _ = self._geom()
        i = int((e.position().x() - x0) // pitch)
        if 0 <= i < len(self.data) and 0 <= (e.position().x() - x0) % pitch < 44:
            t, g = self.data[i]
            QToolTip.showText(e.globalPosition().toPoint(),
                              f"L{i+1}: tested {t:,} · passed {g:,} "
                              f"({100 * g / t:.1f}%)", self)
        super().mouseMoveEvent(e)


class Sparkline(QWidget):
    """Three live polylines: expansions / queue / distinct states."""

    def __init__(self):
        super().__init__()
        self.series = [[], [], []]
        self.cols = ['#1f6feb', '#d4820a', '#7c3aed']
        self.names = ['expansions', 'queue', 'states']
        self.setMinimumHeight(96)
        self.setStyleSheet("background:#fff;border:1px solid #e4e4e7;border-radius:6px;")

    def reset(self):
        self.series = [[], [], []]
        self.update()

    def push(self, vals):
        for s, v in zip(self.series, vals):
            s.append(v)
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        allv = [v for s in self.series for v in s]
        if not allv:
            return
        mx = max(allv)
        w, h, pad = self.width() - 10, self.height() - 24, 6
        f = QFont(self.font()); f.setPointSize(7); p.setFont(f)
        x = lambda i: pad + (w - pad) * i / max(len(self.series[0]) - 1, 1)
        y = lambda v: 18 + (h - 18) * (1 - v / mx)
        for s, c in zip(self.series, self.cols):
            if len(s) < 2:
                continue
            p.setPen(QPen(QColor(c), 1.4))
            for i in range(1, len(s)):
                p.drawLine(QPointF(x(i - 1), y(s[i - 1])), QPointF(x(i), y(s[i])))
        p.setPen(QPen(QColor("#52525b")))
        for j, (c, name) in enumerate(zip(self.cols, self.names)):
            p.setBrush(QColor(c)); p.setPen(Qt.NoPen)
            p.drawRect(8 + j * 110, h + 6, 8, 8)
            p.setPen(QPen(QColor("#52525b")))
            p.drawText(QRectF(20 + j * 110, h + 2, 100, 12), Qt.AlignLeft,
                       f"{name} {human(self.series[j][-1]) if self.series[j] else 0}")


# ======================================================================
# Tab 1 -- string BFS
# ======================================================================
class StringTab(QWidget):
    def __init__(self):
        super().__init__()
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self._build_ui()
        self.reset_world()

    def _build_ui(self):
        root = QHBoxLayout(self)
        left = QVBoxLayout()

        form = QFormLayout()
        self.alph_edit = QLineEdit("pq¬→")
        self.n_spin = QSpinBox(); self.n_spin.setRange(1, 5); self.n_spin.setValue(4)
        form.addRow("alphabet", self.alph_edit)
        form.addRow("max length n", self.n_spin)

        self.speed = QSlider(Qt.Horizontal)
        self.speed.setRange(2, 150); self.speed.setValue(15)
        form.addRow("delay (ms)", self.speed)

        self.fade_fail = QCheckBox("fade failed nodes"); self.fade_fail.setChecked(True)
        form.addRow("", self.fade_fail)
        left.addLayout(form)

        btns = QHBoxLayout()
        self.btn_run = QPushButton("Start")
        b_step, b_reset = QPushButton("Step"), QPushButton("Reset")
        for b in (self.btn_run, b_step, b_reset):
            btns.addWidget(b)
        left.addLayout(btns)

        zoom = QHBoxLayout()
        b_in, b_out, b_fit = QPushButton("＋"), QPushButton("－"), QPushButton("Fit")
        for b in (b_in, b_out, b_fit):
            zoom.addWidget(b)
        left.addLayout(zoom)

        self.status = QLabel("idle"); self.status.setWordWrap(True)
        left.addWidget(self.status)
        self.chart = LevelChart()
        left.addWidget(self.chart)
        left.addWidget(QLabel("well-formed strings found:"))
        self.passed_list = QListWidget()
        left.addWidget(self.passed_list, 1)

        panel = QWidget(); panel.setLayout(left); panel.setFixedWidth(330)

        right = QVBoxLayout()
        self.hover_lbl = QLabel("hover a node to trace its string")
        self.hover_lbl.setStyleSheet("font-family:Consolas,monospace;color:#334155;")
        self.hover_lbl.setMinimumHeight(20)
        self.view = ZoomView()
        self.scene = QGraphicsScene(self)
        self.view.setScene(self.scene)
        right.addWidget(self.hover_lbl)
        right.addWidget(self.view, 1)
        rw = QWidget(); rw.setLayout(right)

        sp = QSplitter(); sp.addWidget(panel); sp.addWidget(rw)
        sp.setSizes([330, 910])
        root.addWidget(sp)

        self.animator = Animator(self.scene, self)

        self.btn_run.clicked.connect(self.toggle_run)
        b_step.clicked.connect(lambda: (not self.running) and self.tick())
        b_reset.clicked.connect(self.reset_world)
        b_in.clicked.connect(lambda: self.view.scale(1.25, 1.25))
        b_out.clicked.connect(lambda: self.view.scale(0.8, 0.8))
        b_fit.clicked.connect(self.fit)
        self.fade_fail.toggled.connect(self.apply_fade)
        self.alph_edit.editingFinished.connect(self.reset_world)
        self.n_spin.valueChanged.connect(self.reset_world)
        self.speed.valueChanged.connect(
            lambda v: self.timer.setInterval(v) if self.running else None)

    # ------------------------------------------------------------ world
    def reset_world(self):
        self.timer.stop(); self.animator.clear()
        self.running = False
        self.btn_run.setText("Start")
        self.scene.clear()
        self.passed_list.clear()
        self.chart.set_data([])

        raw = "".join(dict.fromkeys(self.alph_edit.text().replace(" ", "")))
        allowed = set("pqrs⊤⊥¬∧∨→()")
        if not raw or any(c not in allowed for c in raw):
            QMessageBox.warning(self, "alphabet",
                                f"chars must come from {''.join(sorted(allowed))}")
            raw = "pq¬→"; self.alph_edit.setText(raw)
        self.alpha = raw
        self.n_target = self.n_spin.value()

        cum = sum(len(raw) ** k for k in range(1, self.n_target + 1))
        self.btn_run.setEnabled(cum <= 40000)
        self.status.setText("idle" if cum <= 40000 else
                            f"{cum:,} nodes projected -- lower n")

        br, bp = node_base(None)
        root = NodeEllipse(self, 0)
        root.setBrush(br); root.setPen(bp)
        root.setZValue(1)
        self.scene.addItem(root)
        t = self.scene.addSimpleText("ε")
        t.setParentItem(root)
        t.setPos(-t.boundingRect().width() / 2, -t.boundingRect().height() / 2)

        self.nodes = [{'s': '', 'ch': '', 'parent': None, 'ok': None,
                       'x': 0.0, 'item': root, 'edge_in': None}]
        self.kids, self.rows = {}, {0: [0]}
        lab = self.scene.addSimpleText("length 0")
        lab.setDefaultTextColor(QColor("#71717a")); lab.setPos(-170, -28)

        self.work = deque([0])
        self.level = 0
        self.level_nodes = []
        self.cur_row = 1
        self.big = False
        self.chart_data = []
        self.gen_cnt = self.pass_cnt = 0
        self.level_total = len(raw); self.level_done = 0
        self.done = False
        self._stats()

    def fit(self):
        br = self.scene.itemsBoundingRect().adjusted(-40, -40, 40, 40)
        self.view.fitInView(br, Qt.KeepAspectRatio)

    # ------------------------------------------------------------ hover
    def hover_node(self, idx, on):
        chain, i = [], idx
        while i is not None:
            chain.append(i); i = self.nodes[i]['parent']
        for i in chain:
            n = self.nodes[i]
            it = n['item']
            if on:
                it.setPen(QPen(HOVER, 2.6)); it.setBrush(QBrush(HOVER_FILL))
                it.setZValue(2)
                if n['edge_in']:
                    n['edge_in'].setPen(QPen(HOVER, 2.2))
            else:
                br, pn = node_base(n['ok'])
                it.setPen(pn); it.setBrush(br); it.setZValue(1)
                if n['edge_in']:
                    n['edge_in'].setPen(edge_pen(n['ok']))
        s = ''.join(self.nodes[i]['ch'] for i in reversed(chain))
        if on:
            html = ''.join(f"<b style='color:{CHAR_COL.get(c, '#334155')}'>{c}</b>"
                           for c in s)
            self.hover_lbl.setText(html or "ε  (empty string)")

    def apply_fade(self, on):
        for n in self.nodes[1:]:
            if not n['ok']:
                n['item'].setOpacity(0.28 if on else 1.0)

    # ------------------------------------------------------------ run
    def toggle_run(self):
        if self.done:
            return
        self.running = not self.running
        self.btn_run.setText("Pause" if self.running else "Start")
        if self.running:
            self.timer.setInterval(self.speed.value()); self.timer.start()
        else:
            self.timer.stop()

    def tick(self):
        if self.done:
            return
        for _ in range(128):
            if not self.work:
                break
            pi = self.work.popleft()
            px = self.nodes[pi]['x']
            m = len(self.alpha)
            y = self.cur_row * ROW
            for ci, ch in enumerate(self.alpha):
                s = self.nodes[pi]['s'] + ch
                ok = string_bfs.is_wff(s)
                prov = px + (ci - (m - 1) / 2) * 6
                idx = len(self.nodes)
                faded = self.fade_fail.isChecked() and not ok
                if not self.big:
                    item = NodeEllipse(self, idx)
                    br, pn = node_base(ok)
                    item.setBrush(br); item.setPen(pn); item.setZValue(1)
                    item.setOpacity(0.28 if faded else 1.0)
                    item.setToolTip(s)
                    self.scene.addItem(item)
                    item.setPos(prov, y)
                    t = self.scene.addSimpleText(ch)
                    t.setParentItem(item)
                    t.setDefaultTextColor(QColor(CHAR_COL.get(ch, "#334155")))
                    t.setPos(-t.boundingRect().width() / 2,
                             -t.boundingRect().height() / 2)
                    ring = self.scene.addEllipse(-R - 2, -R - 2, 2 * (R + 2),
                                                 2 * (R + 2),
                                                 QPen(PASS if ok else FAIL, 2),
                                                 QBrush(Qt.NoBrush))
                    ring.setPos(prov, y); ring.setZValue(3)
                    self.animator.add('r', ring, R + 2, R + 10, dur=0.5)
                else:
                    item = self.scene.addRect(-2, -10, 4, 20, QPen(Qt.NoPen),
                                              QBrush(PASS if ok else FAIL))
                    item.setPos(prov, y)
                    item.setOpacity(0.3 if faded else 1.0)
                    item.setToolTip(s)
                self.nodes.append({'s': s, 'ch': ch, 'parent': pi, 'ok': ok,
                                   'x': prov, 'item': item, 'edge_in': None})
                self.kids.setdefault(pi, []).append(idx)
                self.level_nodes.append(idx)
                self.gen_cnt += 1; self.level_done += 1
                if ok:
                    self.pass_cnt += 1
                    if self.passed_list.count() < 2000:
                        self.passed_list.addItem(s)
        if not self.work:
            self.finish_level()
        self._stats()

    def finish_level(self):
        lvl = self.level + 1
        idxs = self.level_nodes
        spacing = max(6.0, min(26.0, 2400.0 / max(len(idxs), 1)))

        rail = self.scene.addLine(-180, lvl * ROW, 2500, lvl * ROW,
                                  QPen(QColor("#e4e4e7"), 0, Qt.DashLine))
        rail.setZValue(-2)
        lab = self.scene.addSimpleText(f"length {lvl}")
        lab.setDefaultTextColor(QColor("#71717a")); lab.setPos(-170, lvl * ROW - 28)

        for i, idx in enumerate(idxs):                      # children glide to slots
            fx = (i + 0.5) * spacing
            item = self.nodes[idx]['item']
            self.animator.add('p', item, item.pos(), QPointF(fx, lvl * ROW))
            self.nodes[idx]['x'] = fx

        for pi in self.rows[lvl - 1]:                       # parents re-center
            ks = self.kids.get(pi, [])
            if not ks:
                continue
            mx = sum(self.nodes[k]['x'] for k in ks) / len(ks)
            item = self.nodes[pi]['item']
            self.animator.add('p', item, item.pos(), QPointF(mx, (lvl - 1) * ROW))
            self.nodes[pi]['x'] = mx
            y0, y1 = (lvl - 1) * ROW + R, lvl * ROW - R
            for k in ks:
                fx = self.nodes[k]['x']
                pen = edge_pen(self.nodes[k]['ok'])
                edge = self.scene.addLine(mx, y0, mx, y0, pen)
                edge.setZValue(-1)
                self.nodes[k]['edge_in'] = edge
                self.animator.add('l', edge, QLineF(mx, y0, mx, y0),
                                  QLineF(mx, y0, fx, y1), dur=0.4)

        self.chart_data.append((len(idxs),
                                sum(1 for i in idxs if self.nodes[i]['ok'])))
        self.chart.set_data(self.chart_data)
        self.rows[lvl] = idxs

        if lvl < self.n_target:
            self.level = lvl
            self.work = deque(idxs)
            self.level_nodes = []
            self.cur_row = lvl + 1
            self.big = len(idxs) * len(self.alpha) > 1200
            self.level_total = len(idxs) * len(self.alpha)
            self.level_done = 0
        else:
            self.done = True
            self.running = False
            self.timer.stop()
            self.btn_run.setText("Start")
            self.status.setText(f"done -- {self.gen_cnt:,} tested, "
                                f"{self.pass_cnt:,} well-formed")
        self.fit()

    def _stats(self):
        if self.done:
            return
        self.status.setText(
            f"|Σ|={len(self.alpha)}   level {self.level + 1}/{self.n_target}   "
            f"({min(self.level_done, self.level_total):,}/{self.level_total:,})\n"
            f"generated {self.gen_cnt:,}   passed {self.pass_cnt:,}   "
            f"survival {100 * self.pass_cnt / max(self.gen_cnt, 1):.1f}%")


# ======================================================================
# Tab 2 -- proof BFS
# ======================================================================
def search_events(goal, classical, max_steps):
    univ = sorted(pb.subformulas(goal) | {pb.Neg(g) for g in pb.subformulas(goal)},
                  key=pb.show)
    start = ((frozenset(), goal),)
    seen = {start}
    queue = deque([(start, ())])
    expanded = 0
    while queue:
        state, actions = queue.popleft()
        if not state:
            yield ('found', pb.build_tree(goal, actions), len(actions))
            return
        if len(actions) >= max_steps:
            continue
        expanded += 1
        G, phi = state[0]
        for rule, premises in pb.sequent_moves(G, phi, univ, classical):
            new_state = state[1:] + tuple(premises)
            if new_state and new_state in seen:
                continue
            if new_state:
                seen.add(new_state)
            queue.append((new_state, actions + ((G, phi, rule, premises),)))
        yield ('step', expanded, len(queue), len(seen),
               sequent_text(G, phi))


def sequent_text(G, phi):
    ctx = ", ".join(sorted(pb.show(a) for a in G))
    return (ctx + " ⊢ " if ctx else "⊢ ") + pb.show(phi)


P, Q = pb.Atom('p'), pb.Atom('q')
GOALS = [
    ("⊢ p → p   (identity)",                  pb.Imp(P, P), 10),
    ("⊢ ¬(p ∧ ¬p)   (non-contradiction)",     pb.Neg(pb.And(P, pb.Neg(P))), 10),
    ("⊢ (¬p→¬q) → (q→p)   (contraposition)",
     pb.Imp(pb.Imp(pb.Neg(P), pb.Neg(Q)), pb.Imp(Q, P)), 12),
    ("Peirce: ⊢ ((p→q)→p) → p   (classical)",
     pb.Imp(pb.Imp(pb.Imp(P, Q), P), P), 12),
    ("Peirce   (intuitionistic → NO PROOF)",
     pb.Imp(pb.Imp(pb.Imp(P, Q), P), P), 8),
]

RULE_TIP = {
    'Ax': 'axiom: the goal is literally an assumption',
    '∧I': 'conjunction introduction: prove both halves',
    '→I': 'implication introduction: assume the antecedent',
    '¬I': 'negation introduction: assume the formula, derive ⊥',
    '∨I': 'disjunction introduction: one disjunct suffices',
    '→E': 'modus ponens',
    '¬E': 'contradiction: a and ¬a yield ⊥',
    '⊥E': 'ex falso quodlibet',
    'RAA': 'reductio (classical only)',
}


class ProofTab(QWidget):
    def __init__(self):
        super().__init__()
        self.gen = None
        self.timer = QTimer(self); self.timer.timeout.connect(self.tick)
        self.reveal_timer = QTimer(self)
        self.reveal_timer.timeout.connect(self.reveal_tick)
        self._build_ui()

    def _build_ui(self):
        root = QHBoxLayout(self)
        left = QVBoxLayout()

        self.combo = QComboBox()
        for label, f, k in GOALS:
            self.combo.addItem(label, (f, k))
        left.addWidget(self.combo)

        form = QFormLayout()
        self.k_spin = QSpinBox(); self.k_spin.setRange(3, 30); self.k_spin.setValue(10)
        self.chk = QCheckBox("classical (RAA)"); self.chk.setChecked(True)
        self.chunk = QSlider(Qt.Horizontal)
        self.chunk.setRange(10, 2000); self.chunk.setValue(300)
        form.addRow("max proof steps", self.k_spin)
        form.addRow("", self.chk)
        form.addRow("expansions / tick", self.chunk)
        left.addLayout(form)

        btns = QHBoxLayout()
        self.btn_run = QPushButton("Search")
        b_reset = QPushButton("Reset")
        b_png = QPushButton("Save PNG")
        for b in (self.btn_run, b_reset, b_png):
            btns.addWidget(b)
        left.addLayout(btns)

        self.lbl = QLabel("idle"); self.lbl.setWordWrap(True)
        left.addWidget(self.lbl)
        self.cur_lbl = QLabel(" ")
        self.cur_lbl.setStyleSheet("font-family:Consolas,monospace;color:#64748b;")
        left.addWidget(self.cur_lbl)
        self.spark = Sparkline()
        left.addWidget(self.spark)
        left.addStretch(1)

        panel = QWidget(); panel.setLayout(left); panel.setFixedWidth(340)

        right = QVBoxLayout()
        self.view = ZoomView()
        self.scene = QGraphicsScene(self)
        self.view.setScene(self.scene)
        self.log = QTextEdit(); self.log.setReadOnly(True)
        self.log.setMaximumHeight(140); self.log.setFont(MONO)
        right.addWidget(self.view, 1)
        right.addWidget(QLabel("search log:"))
        right.addWidget(self.log)
        rw = QWidget(); rw.setLayout(right)

        sp = QSplitter(); sp.addWidget(panel); sp.addWidget(rw)
        sp.setSizes([340, 900])
        root.addWidget(sp)

        self.animator = Animator(self.scene, self)

        self.combo.currentIndexChanged.connect(
            lambda i: self.k_spin.setValue(self.combo.itemData(i)[1]))
        self.btn_run.clicked.connect(self.search)
        b_reset.clicked.connect(self.reset)
        b_png.clicked.connect(lambda: export_scene(self, self.scene, "proof.png"))

    def reset(self):
        self.timer.stop(); self.reveal_timer.stop(); self.animator.clear()
        self.gen = None
        self.scene.clear()
        self.spark.reset()
        self.lbl.setText("idle"); self.cur_lbl.setText(" ")
        self.log.append("-- reset --")

    def search(self):
        goal, _ = self.combo.currentData()
        self.timer.stop(); self.reveal_timer.stop(); self.animator.clear()
        self.scene.clear(); self.spark.reset()
        self.gen = search_events(goal, self.chk.isChecked(), self.k_spin.value())
        self.expanded = self.q = self.seen = 0
        self.last_log = 0
        self.lbl.setText("searching…")
        self.log.append(f"search: {self.combo.currentText()}  k≤{self.k_spin.value()} "
                        f"classical={self.chk.isChecked()}")
        self.btn_run.setEnabled(False); self.btn_run.setText("Searching…")
        self.timer.setInterval(15); self.timer.start()

    def tick(self):
        for _ in range(self.chunk.value()):
            ev = next(self.gen, None)
            if ev is None:
                self.timer.stop()
                self.btn_run.setEnabled(True); self.btn_run.setText("Search")
                self.lbl.setText(f"NO PROOF -- space exhausted "
                                 f"(≤ {self.k_spin.value()} steps, "
                                 f"{self.expanded:,} expansions)")
                self.log.append("exhausted: no proof within bound")
                return
            if ev[0] == 'step':
                self.expanded, self.q, self.seen = ev[1], ev[2], ev[3]
                self.cur_lbl.setText("expanding: " + ev[4])
                self.spark.push((self.expanded, self.q, self.seen))
                if self.expanded - self.last_log >= 2000:
                    self.last_log = self.expanded
                    self.log.append(f"  … {self.expanded:,} expansions, "
                                    f"queue {self.q:,}, states {self.seen:,}")
            elif ev[0] == 'found':
                self.timer.stop()
                self.btn_run.setEnabled(True); self.btn_run.setText("Search")
                tree, k = ev[1], ev[2]
                self.lbl.setText(f"PROOF FOUND -- {k} rule applications "
                                 f"({self.expanded:,} expansions)")
                self.log.append(f"found: {k} rule applications")
                self.show_tree(tree)
                return
        self.lbl.setText(f"searching…  expansions {self.expanded:,}   "
                         f"queue {self.q:,}   states {self.seen:,}")

    # ------------------------------------------------------------ tree
    def show_tree(self, tree):
        self.scene.clear(); self.animator.clear()
        self.gens = {}
        f_seq = QFont(MONO); f_seq.setPointSize(9)
        f_rule = QFont(self.font()); f_rule.setPointSize(8); f_rule.setItalic(True)
        fm = QFontMetricsF(f_seq)
        KG, VG = 30, 16
        M = {}

        def shadow(item):
            eff = QGraphicsDropShadowEffect(blurRadius=10, offset=1.0)
            eff.setColor(QColor(0, 0, 0, 45))
            item.setGraphicsEffect(eff)

        def measure(nd):
            rule, seq, *kids = nd
            cw = fm.horizontalAdvance(sequent_text(*seq)) + 14
            if not kids:
                M[id(nd)] = (cw, fm.height() + 8, 0)
                return M[id(nd)]
            res = [measure(k) for k in kids]
            w = max(sum(r[0] for r in res) + KG * (len(kids) - 1), cw)
            h = max(r[1] for r in res) + VG + fm.height() + 10
            g = 1 + max(r[2] for r in res)
            M[id(nd)] = (w, h, g)
            return M[id(nd)]

        def place(nd, x, y):
            w, h, g = M[id(nd)]
            rule, seq, *kids = nd
            if not kids:                                   # axiom leaf
                t = self.scene.addSimpleText(sequent_text(*seq), f_seq)
                t.setBrush(QColor("#1a7f37")); shadow(t)
                fx, fy = x + (w - fm.horizontalAdvance(t.text())) / 2, y + 4
                t.setPos(fx, fy - 6)
                t.setOpacity(0)
                t.setToolTip("axiom -- nothing to prove")
                self.gens.setdefault(0, []).append(('t', t, QPointF(fx, fy)))
                return
            res = [M[id(k)] for k in kids]
            kw = sum(r[0] for r in res) + KG * (len(kids) - 1)
            kh = max(r[1] for r in res)
            off = x + (w - kw) / 2
            centers = []
            for k, rw in zip(kids, res):
                place(k, off, y)
                centers.append(off + rw[0] / 2)
                off += rw[0] + KG
            bar_y = y + kh + 8
            col = rule_color(rule)
            full = QLineF(centers[0] - 6, bar_y, centers[-1] + 6, bar_y)
            cx = (full.x1() + full.x2()) / 2
            ln = self.scene.addLine(cx, bar_y, cx, bar_y, QPen(QColor(col), 1.8))
            ln.setZValue(-1)
            ln.setToolTip(RULE_TIP.get(rule.rstrip(':LR').split('[')[0], rule))
            rl = self.scene.addSimpleText(rule, f_rule)
            rl.setBrush(QColor(col)); shadow(rl)
            rl.setOpacity(0)
            rl_final = QPointF(centers[-1] + 10,
                               bar_y - rl.boundingRect().height() / 2)
            rl.setPos(rl_final + QPointF(0, -6))
            txt = sequent_text(*seq)
            ct = self.scene.addSimpleText(txt, f_seq)
            ct.setBrush(QColor("#111")); shadow(ct)
            ct.setOpacity(0)
            ct_final = QPointF(x + (w - fm.horizontalAdvance(txt)) / 2, bar_y + 7)
            ct.setPos(ct_final + QPointF(0, -6))
            self.gens.setdefault(g, []).extend([
                ('l', ln, QLineF(cx, bar_y, cx, bar_y), full),
                ('t', rl, rl_final), ('t', ct, ct_final)])

        measure(tree)
        place(tree, 0, 0)

        bx = self.scene.itemsBoundingRect()
        for j, (col, name) in enumerate([('#1a7f37', 'axiom'), ('#1f6feb', 'introduction'),
                                         ('#d4820a', 'elimination'), ('#a626a4', 'classical')]):
            dot = self.scene.addEllipse(bx.left() + j * 95, bx.top() - 22, 8, 8,
                                        QPen(Qt.NoPen), QBrush(QColor(col)))
            dot.setOpacity(0)
            t = self.scene.addSimpleText(name, f_rule)
            t.setDefaultTextColor(QColor("#52525b"))
            t.setPos(bx.left() + j * 95 + 12, bx.top() - 24)
            t.setOpacity(0)
            self.gens.setdefault(999, []).extend(
                [('t', dot, dot.pos()), ('t', t, t.pos())])

        self.fit()
        self.reveal_order = sorted(self.gens)
        self.reveal_i = 0
        self.reveal_timer.setInterval(320)
        self.reveal_timer.start()

    def reveal_tick(self):
        if self.reveal_i >= len(self.reveal_order):
            self.reveal_timer.stop()
            return
        for entry in self.gens[self.reveal_order[self.reveal_i]]:
            if entry[0] == 'l':
                self.animator.add('l', entry[1], entry[2], entry[3], dur=0.3)
            else:
                _, item, final = entry
                self.animator.add('o', item, 0.0, 1.0, dur=0.35)
                self.animator.add('p', item, item.pos(), final, dur=0.35)
        self.reveal_i += 1

    def fit(self):
        br = self.scene.itemsBoundingRect().adjusted(-30, -30, 30, 30)
        self.view.fitInView(br, Qt.KeepAspectRatio)


# ======================================================================
QSS = """
QWidget { font-size: 10pt; }
QPushButton { background:#fff; border:1px solid #d4d4d8; border-radius:6px;
              padding:5px 14px; }
QPushButton:hover { border-color:#71717a; }
QPushButton:disabled { color:#a1a1aa; }
QLineEdit, QSpinBox, QComboBox { background:#fff; border:1px solid #d4d4d8;
              border-radius:6px; padding:4px 6px; }
QListWidget, QTextEdit { background:#fff; border:1px solid #e4e4e7;
              border-radius:6px; }
QTabWidget::pane { border:1px solid #e4e4e7; }
QTabBar::tab { padding:8px 16px; background:#f4f4f5;
               border:1px solid #e4e4e7; border-bottom:none; }
QTabBar::tab:selected { background:#fff; }
QLabel { color:#3f3f46; }
"""


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("BFS visualizer -- string generate-and-test vs inference-step proof search")
        tabs = QTabWidget()
        tabs.addTab(StringTab(), "string BFS (append + test)")
        tabs.addTab(ProofTab(), "proof BFS (inference steps)")
        self.setCentralWidget(tabs)
        self.statusBar().showMessage(
            "scroll = zoom at cursor · drag = pan · hover nodes to trace · Save PNG exports the scene")
        self.resize(1280, 800)


if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyleSheet(QSS)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())
