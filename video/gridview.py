# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Drawing helpers for the video: a grid of cells, endpoints, paths, cuts, and captions."""
import hashlib
import os
import re
import textwrap

import numpy as np
from manim import (DOWN, LEFT, RIGHT, UP, ORIGIN, Circle, Create, DashedLine, DashedVMobject,
                   FadeIn, FadeOut, Line, MathTex, Rectangle, Scene, Square, Text, VGroup,
                   VMobject, Write, LineJointType, CapStyleType, linear)

BG = "#16181d"
FG = "#e9e9ec"
DIM = "#8a909c"
GRIDLINE = "#3b404c"
BORDER = "#cfd3da"
COL = {"A": "#2fbf8f", "B": "#f0773f"}
# Extra pair colours, for the many-pair puzzle.
#
PAIR = ["#2fbf8f", "#f0773f", "#5b8def", "#c678dd", "#e5c07b"]
CUT = "#a39bf5"
YEL = "#f2c94c"
CHECK = "#353b47"
FONT = "Noto Sans"
MONO = "DejaVu Sans Mono"


class Grid(VGroup):
    """An R x C grid of square cells of side cs. Cell (r, c) has row r counted downward."""

    def __init__(self, R, C, cs=None, height=6.0, width=12.0, center=ORIGIN, line=1.2):
        super().__init__()
        if cs is None:
            cs = min(height / R, width / C)
        self.R, self.C, self.cs = R, C, cs
        w, h = C * cs, R * cs
        lines = VGroup()
        for r in range(1, R):
            y = h / 2 - r * cs
            lines.add(Line(np.array([-w / 2, y, 0]), np.array([w / 2, y, 0])))
        for c in range(1, C):
            x = -w / 2 + c * cs
            lines.add(Line(np.array([x, h / 2, 0]), np.array([x, -h / 2, 0])))
        lines.set_stroke(GRIDLINE, width=line)

        # Lines and frame sit above cell shading (checkerboard, tints), below paths.
        #
        self.lines = lines.set_z_index(1)
        self.box = Rectangle(width=w, height=h).set_stroke(BORDER, 2.5).set_z_index(1)
        self.add(lines, self.box)
        self.move_to(center)

    # Positions are read from the border rectangle, so they follow the grid when it moves.
    #
    def pt(self, r, c):
        return self.box.get_corner(UP + LEFT) + RIGHT * c * self.cs + DOWN * r * self.cs

    def cc(self, x):
        return self.pt(x[0] + 0.5, x[1] + 0.5)

    def width_px(self):
        return max(2.5, min(9.0, self.cs * 15))

    def squares(self, cells, color, opacity=1.0):
        return VGroup(*[Square(self.cs, stroke_width=0, fill_color=color, fill_opacity=opacity)
                        .move_to(self.cc(x)) for x in cells])

    def checker(self):
        cells = [(r, c) for r in range(self.R) for c in range(self.C) if (r + c) % 2 == 0]
        return self.squares(cells, CHECK, 1.0)

    def endpoint(self, x, label, col):
        d = Circle(radius=0.40 * self.cs, stroke_width=0, fill_color=COL.get(col, col), fill_opacity=1)
        d.move_to(self.cc(x))
        g = VGroup(d)
        if label and self.cs >= 0.22:
            t = MathTex(label, color=BG)
            t.scale_to_fit_height(0.36 * self.cs)
            t.move_to(self.cc(x))
            g.add(t)
        return g.set_z_index(5)

    def ends(self, I, labels=True):
        from data import ends
        return VGroup(*[self.endpoint(x, lab if labels else "", col) for x, lab, col in ends(I)])

    def virtual(self, x, col):
        ring = DashedVMobject(Circle(radius=0.40 * self.cs).set_stroke(COL[col], 3), num_dashes=10)
        disk = Circle(radius=0.40 * self.cs, stroke_width=0, fill_color=BG, fill_opacity=1)
        return VGroup(disk, ring).move_to(self.cc(x)).set_z_index(4)

    def path(self, cells, col, width=None, opacity=1.0):
        m = VMobject()
        m.set_points_as_corners([self.cc(x) for x in cells])
        m.set_stroke(COL[col] if col in COL else col, width or self.width_px(), opacity)
        m.joint_type = LineJointType.ROUND
        m.cap_style = CapStyleType.ROUND
        return m.set_z_index(2)

    def edge(self, a, b, col, width=None):
        e = Line(self.cc(a), self.cc(b))
        e.set_stroke(COL[col] if col in COL else col, width or self.width_px())
        e.cap_style = CapStyleType.ROUND
        return e.set_z_index(2)

    def tint(self, cells, col, opacity=0.17):
        return self.squares(cells, COL[col], opacity)

    def solution(self, paths, tint=True):
        """VGroup(tints, path A, path B)."""
        g = VGroup()
        g.add(VGroup(self.tint(paths[0], "A"), self.tint(paths[1], "B")) if tint else VGroup())
        g.add(self.path(paths[0], "A"), self.path(paths[1], "B"))
        return g

    def cut(self, axis, k, color=CUT):
        """axis 0: the line between rows k-1 and k; axis 1: between columns k-1 and k."""
        o = 0.18
        if axis == 0:
            a, b = self.pt(k, 0) + LEFT * o, self.pt(k, self.C) + RIGHT * o
        else:
            a, b = self.pt(0, k) + UP * o, self.pt(self.R, k) + DOWN * o
        return DashedLine(a, b, dash_length=0.12).set_stroke(color, 4).set_z_index(3)

    def place(self, corner):
        """Move the grid so that its top-left corner is at `corner`."""
        return self.shift(corner - self.box.get_corner(UP + LEFT))

    def rows(self, rows):
        return [(r, c) for r in rows for c in range(self.C)]

    def cols(self, cols):
        return [(r, c) for r in range(self.R) for c in cols]


def collapse_rows(scene, g, d, squash=(), movers=(), run_time=1.4):
    """Delete rows d, d+1 of grid g smoothly: the rows above stay, the two rows shrink to
    nothing, the rows below slide up. `squash` shrinks with the rows, `movers` slide with the
    rows below. Returns the new (R-2) x C grid, in place of g."""
    R, C, cs = g.R, g.C, g.cs
    parts = []
    for r0, r1 in ((0, d), (d, d + 2), (d + 2, R)):
        if r1 > r0:
            p = Grid(r1 - r0, C, cs=cs).place(g.pt(r0, 0))
            p.box.set_stroke(GRIDLINE, 1.2)
            parts.append((r0, p))
        else:
            parts.append((r0, None))
    frame = g.box.copy()
    new = Grid(R - 2, C, cs=cs).place(g.pt(0, 0))
    scene.remove(g)
    scene.add(*[p for _, p in parts if p is not None], frame)
    mid = VGroup(parts[1][1], *squash)
    anims = [mid.animate.stretch(0.001, 1, about_edge=UP).set_opacity(0),
             frame.animate.stretch_to_fit_height((R - 2) * cs, about_edge=UP)]
    below = VGroup(*[m for m in movers])
    if parts[2][1] is not None:
        below.add(parts[2][1])
    if len(below):
        anims.append(below.animate.shift(UP * 2 * cs))
    scene.play(*anims, run_time=run_time)
    scene.remove(frame, *[p for _, p in parts if p is not None], *squash)
    scene.add(new)
    return new


def caption(text, width=78, size=28):
    lines = []
    for para in text.split("\n"):
        lines += textwrap.wrap(para, width) or [""]
    t = Text("\n".join(lines), font=FONT, font_size=size, color=FG, line_spacing=0.9)
    if t.width > 13.4:
        t.scale_to_fit_width(13.4)
    return t.to_edge(DOWN, buff=0.35)


# Narration. Each caption is spoken by Kokoro (kokoro-onnx), synthesised once and cached in
# audio/ under a hash of the voice and the spoken text. ZZN_NARRATE=0 turns it off, and the
# captions then use read_time. ZZN_VOICE picks the voice, ZZN_KOKORO the model directory.
#
HERE = os.path.dirname(os.path.abspath(__file__))
AUDIO_DIR = os.path.join(HERE, "audio")
NARRATE = os.environ.get("ZZN_NARRATE", "1") == "1"
VOICE = os.environ.get("ZZN_VOICE", "af_river:0.5+am_liam:0.5")
SPEED = float(os.environ.get("ZZN_SPEED", "1.07"))
PAUSE = 0.2
MODEL_DIR = os.environ.get("ZZN_KOKORO", os.path.expanduser("~/claude/models/kokoro"))
_kokoro = None

# Whole phrases first, then symbols. The captions are written to be read; these rewrite them
# to be heard.
#
SPOKEN = [
    ("O((R + C)\u00b7R\u00b7C)", "order R plus C, times R times C"),
    ("docs/ALGORITHM.md, section 8", "the algorithm document in the repository, section 8"),
    ("Adcock et al., 2015", "Adcock and others, 2015"),
    ("16 \u2265 13", "16 is at least 13"),
    ("Give each endpoint \u03c3 = +1 if black and \u22121 if white.",
     "Give each endpoint a sign, sigma, of plus one if black and minus one if white."),
    ("+1, \u22121 or 0", "plus one, minus one or zero"),
    ("(S) strip.", "The strip reduction."),
    ("(K) compression.", "The compression reduction."),
    ("(I) does the same", "Interior compression does the same"),
    ("reduction (S)", "the strip reduction"),
    ("10\u2075", "ten to the fifth"),
    ("\u03a3\u03c3", "the sum of sigma"),
    ("\u03c3", "sigma"),
    ("2/2", "two-two"),
    ("1/3", "one-three"),
    ("NP-complete", "N P complete"),
    ("\u00d7", "by"),
    ("\u00b7", " times "),
    ("\u2265", "at least"),
    ("\u2264", "at most"),
    ("\u2260", "is not"),
    ("\u21d2", "so"),
    ("\u2212", "minus "),
    ("+1", "plus one"),
    (" + ", " plus "),
    (" = ", " is "),
]


def spoken(text):
    s = text
    for a, b in SPOKEN:
        s = s.replace(a, b)
    s = re.sub(r"([st])([\u2080\u2081])", lambda m: m.group(1) + (" zero" if m.group(2) == "\u2080" else " one"), s)
    s = re.sub(r"\bIPS\b", "I P S", s)
    s = re.sub(r"\bDP\b", "D P", s)
    s = re.sub(r"\(([SKI])\)", r"\1", s)
    return re.sub(r"\s+", " ", s).strip()


def voice_style(k, spec):
    """A voice name, or a blend written as "af_heart:0.5+am_michael:0.5"."""
    if ":" not in spec:
        return spec
    style = None
    for part in spec.split("+"):
        name, w = part.split(":")
        v = k.get_voice_style(name) * float(w)
        style = v if style is None else style + v
    return style


# A word can carry its own pronunciation, as [word](/phonemes/), when the default reading is
# wrong ("alternate" as a verb, for instance).
#
PRON = re.compile(r"\[([^\]]+)\]\(/([^/]+)/\)")


def kokoro():
    global _kokoro
    if _kokoro is None:
        from kokoro_onnx import Kokoro
        _kokoro = Kokoro(os.path.join(MODEL_DIR, "kokoro-v1.0.onnx"),
                         os.path.join(MODEL_DIR, "voices-v1.0.bin"))
    return _kokoro


def synth(say, voice=None):
    k = kokoro()
    style = voice_style(k, voice or VOICE)
    if PRON.search(say):
        parts, last = [], 0
        for m in PRON.finditer(say):
            if say[last:m.start()].strip():
                parts.append(k.tokenizer.phonemize(say[last:m.start()], "en-us"))
            parts.append(m.group(2))
            last = m.end()
        if say[last:].strip():
            parts.append(k.tokenizer.phonemize(say[last:], "en-us"))
        return k.create(" ".join(parts), voice=style, speed=SPEED, is_phonemes=True)
    return k.create(say, voice=style, speed=SPEED, lang="en-us")


def narration(text, speak=None):
    """(wav path, duration) of the spoken caption, synthesised on first use. `speak`, when
    given, is said instead of the caption."""
    import soundfile
    say = spoken(speak if speak is not None else text)
    h = hashlib.sha1((VOICE + "|" + str(SPEED) + "|" + say).encode()).hexdigest()[:16]
    path = os.path.join(AUDIO_DIR, h + ".wav")
    if not os.path.exists(path):
        samples, rate = synth(say)
        os.makedirs(AUDIO_DIR, exist_ok=True)
        tmp = path + f".{os.getpid()}.tmp.wav"
        soundfile.write(tmp, samples, rate)
        os.replace(tmp, path)
        with open(os.path.join(AUDIO_DIR, "index.tsv"), "a") as f:
            f.write(f"{h}\t{say}\n")
    return path, soundfile.info(path).duration


def read_time(text):
    return 0.8 + len(text.split()) / 3.0


class Base(Scene):
    """A scene with a timed caption line at the bottom and a heading at the top left."""

    def setup(self):
        self.camera.background_color = BG
        self.cap = None
        self.due = 0.0
        self.head = None

    def now(self):
        return self.renderer.time

    def settle(self):
        rem = self.due - self.now()
        if rem > 0.05:
            self.wait(rem)

    def say(self, text, extra=0.0, speak=None):
        """Show a caption; the next say() waits until this one has been on long enough."""
        self.settle()
        new = caption(text)

        # The speech starts as the old caption fades, so the changeover costs no time.
        #
        t0 = self.now()
        hold = read_time(text)
        if NARRATE:
            path, dur = narration(text, speak)
            self.add_sound(path)
            hold = dur + PAUSE
        if self.cap is not None:
            self.play(FadeOut(self.cap), run_time=0.2)
        self.play(FadeIn(new, shift=0.1 * UP), run_time=0.3)
        self.cap = new
        self.due = t0 + hold + extra

    def narrate(self, text):
        """Speak without a caption (the title)."""
        self.settle()
        if NARRATE:
            path, dur = narration(text)
            self.add_sound(path)
            self.due = self.now() + dur + PAUSE

    def unsay(self):
        self.settle()
        if self.cap is not None:
            self.play(FadeOut(self.cap), run_time=0.4)
            self.cap = None

    def heading(self, text):
        t = Text(text, font=FONT, font_size=34, color=FG, weight="BOLD").to_corner(UP + LEFT, buff=0.4)
        anims = [Write(t, run_time=0.8)]
        if self.head is not None:
            anims.append(FadeOut(self.head))
        self.play(*anims)
        self.head = t
        return t

    def finish(self):
        self.settle()
        self.wait(0.3)
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=0.8)


def draw_path(grid, cells, col, speed=14.0):
    """Create animation for a path, at `speed` cells per second."""
    p = grid.path(cells, col)
    return p, Create(p, run_time=max(0.6, len(cells) / speed), rate_func=linear)


def label(text, size=24, color=FG, mono=False):
    return Text(text, font=MONO if mono else FONT, font_size=size, color=color)
