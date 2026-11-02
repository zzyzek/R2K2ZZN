# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The explainer video, one Manim scene per section. Render with render.sh."""
import os

import numpy as np
from manim import config
from manim import (Brace, Circle, DashedLine, MathTex, BOLD, Group, DOWN, LEFT, RIGHT, UP, ORIGIN, UL, UR, DL, DR, AnimationGroup, Arrow,
                   Create, FadeIn, FadeOut, GrowFromCenter, Indicate, LaggedStart, Line,
                   ReplacementTransform, RoundedRectangle, SurroundingRectangle, Text,
                   Transform, VGroup, VMobject, Write, linear, smooth, DashedVMobject)

import data
from data import Instance, fires
from gridview import (BG, FG, DIM, COL, CUT, YEL, FONT, MONO, PAIR, BORDER, Base, Grid, caption,
                      collapse_rows, draw_path, label)

# Scenes render in parallel; a LaTeX directory per process keeps their temporary files apart.
#
config.tex_dir = os.path.join("media", "Tex", str(os.getpid()))

RED = "#ff5c6c"
CENTER = UP * 0.25


def text(s, size=26, color=FG, weight=None, mono=False):
    kw = dict(font=MONO if mono else FONT, font_size=size, color=color, line_spacing=0.9)
    if weight:
        kw["weight"] = weight
    return Text(s, **kw)


def runs_of(paths, side):
    """Split each path into maximal runs on one side of a cut. Returns (runs, crossings):
    runs = [(side, cells, colour)], crossings = [(a, b, colour)]."""
    runs, xs = [], []
    for p, col in zip(paths, "AB"):
        cur = [p[0]]
        for a, b in zip(p, p[1:]):
            if side(a) != side(b):
                runs.append((side(a), cur, col))
                xs.append((a, b, col))
                cur = [b]
            else:
                cur.append(b)
        runs.append((side(cur[0]), cur, col))
    return runs, xs


class MoveMixin:
    """Animate a move: cut the grid, pull the pieces apart, solve them, glue them back."""

    def split_move(self, g, I, endm, sol, axis, k, gap=0.6, speed=18.0, between=None):
        side = (lambda x: x[0] >= k) if axis == 0 else (lambda x: x[1] >= k)
        if axis == 0:
            ga, gb = Grid(k, g.C, cs=g.cs), Grid(g.R - k, g.C, cs=g.cs)
            ga.place(g.pt(0, 0)), gb.place(g.pt(k, 0))
            off = (UP * gap / 2, DOWN * gap / 2)
            loc = (lambda x: x, lambda x: (x[0] - k, x[1]))
        else:
            ga, gb = Grid(g.R, k, cs=g.cs), Grid(g.R, g.C - k, cs=g.cs)
            ga.place(g.pt(0, 0)), gb.place(g.pt(0, k))
            off = (LEFT * gap / 2, RIGHT * gap / 2)
            loc = (lambda x: x, lambda x: (x[0], x[1] - k))
        pieces = (ga, gb)
        cells = [I.s0, I.t0, I.s1, I.t1]
        ends_by = (VGroup(*[e for e, x in zip(endm, cells) if not side(x)]),
                   VGroup(*[e for e, x in zip(endm, cells) if side(x)]))
        cutl = g.cut(axis, k)
        self.play(Create(cutl), run_time=0.8)
        self.remove(g)
        self.add(ga, gb)
        self.play(VGroup(ga, ends_by[0]).animate.shift(off[0]),
                  VGroup(gb, ends_by[1]).animate.shift(off[1]),
                  FadeOut(cutl), run_time=1.0)
        runs, xs = runs_of(sol, side)
        real = set(cells)
        virt = (VGroup(), VGroup())
        paths = (VGroup(), VGroup())
        for s, cs_, col in runs:
            pg = pieces[s]
            for x in (cs_[0], cs_[-1]):
                if x not in real:
                    virt[s].add(pg.virtual(loc[s](x), col))
            paths[s].add(pg.path([loc[s](x) for x in cs_], col))
        self.play(FadeIn(virt[0]), FadeIn(virt[1]), run_time=0.6)
        if between:
            between()
        n = max(len(r[1]) for r in runs)
        self.play(*[Create(p, rate_func=linear) for p in [*paths[0], *paths[1]]],
                  run_time=max(1.2, n / speed))
        self.wait(0.4)
        self.play(VGroup(ga, ends_by[0], virt[0], paths[0]).animate.shift(-off[0]),
                  VGroup(gb, ends_by[1], virt[1], paths[1]).animate.shift(-off[1]), run_time=1.0)
        edges = VGroup(*[g.edge(a, b, col) for a, b, col in xs])
        self.play(Create(edges), FadeOut(virt[0]), FadeOut(virt[1]), run_time=0.8)
        full = g.solution(sol)
        self.remove(ga, gb, paths[0], paths[1], edges)
        self.add(g, full[1], full[2])
        self.play(FadeIn(full[0]), run_time=0.5)
        return full


# ---------------------------------------------------------------------------------------------

class S01Title(Base):
    def construct(self):
        I, S = data.W0, data.S0
        g = Grid(I.R, I.C, height=5.6, center=RIGHT * 4.5 + UP * 0.1)
        ends = g.ends(I, labels=False)
        t1 = Text("Two-path\nZig-Zag Numberlink", font=FONT, font_size=52, color=FG, weight=BOLD,
                  line_spacing=0.8)
        t2 = text("on rectangles", 36, DIM)
        #t3 = text("Thin grids: a dynamic program. Larger grids: a finite\n"
        #          "catalogue of forbidden patterns. Solved in polynomial\n"
        #          "time, and checked in Lean 4.", 22, FG)
        t3 = text("(aka two-path Flow Free)\n"
                  "A polynomial time algorithm, verified in Lean 4.", 22, FG)
        col = VGroup(t1, t2, t3).arrange(DOWN, aligned_edge=LEFT, buff=0.45)
        col.to_edge(LEFT, buff=0.8).shift(UP * 0.3)
        self.play(FadeIn(g), LaggedStart(*[GrowFromCenter(e) for e in ends], lag_ratio=0.2))
        self.narrate("Two-path Zig-Zag Numberlink on rectangles, also known as two-path Flow Free. "
                     "A polynomial-time algorithm, verified in Lean 4.")
        self.play(Write(t1), run_time=1.5)
        self.play(FadeIn(t2, shift=0.1 * UP))
        pa, pb = g.path(S[0], "A"), g.path(S[1], "B")
        self.play(Create(pa, rate_func=linear), Create(pb, rate_func=linear), FadeIn(t3),
                  run_time=5)
        self.play(FadeIn(g.tint(S[0], "A")), FadeIn(g.tint(S[1], "B")))
        self.settle()
        self.wait(1)
        self.finish()


def x_mark(g, x, color=None):
    """A red cross over cell x: where an attempted path runs into the other colour."""
    c, d = g.cc(x), 0.28 * g.cs
    m = VGroup(Line(c + np.array([-d, -d, 0]), c + np.array([d, d, 0])),
               Line(c + np.array([-d, d, 0]), c + np.array([d, -d, 0])))
    return m.set_stroke(color or RED, 7).set_z_index(7)


def dashed_path(g, cells, col):
    p = g.path(cells, col)
    return DashedVMobject(p, num_dashes=max(6, 3 * len(cells))).set_z_index(2)


def fit_between(m, top, bottom, cx, wmax):
    """Scale m to fit the band between y = top and y = bottom (and width wmax), centred."""
    m.scale_to_fit_height(top - bottom)
    if m.width > wmax:
        m.scale_to_fit_width(wmax)
    return m.move_to(np.array([cx, (top + bottom) / 2, 0]))


def side_title(title, sub=None, x=3.4, y=2.0):
    """The condition's name, in the empty space to the right of the grid."""
    t = text(title, 40, FG, BOLD)
    g = VGroup(t)
    if sub:
        g.add(text(sub, 26, DIM))
    g.arrange(DOWN, aligned_edge=LEFT, buff=0.2)
    return g.move_to(np.array([x, y, 0]), aligned_edge=UP + LEFT)


class S02Problem(Base):
    def construct(self):
        self.heading("The problem")
        I, S = data.PROBLEM, data.PROBLEM_SOL
        g = Grid(I.R, I.C, height=4.0, center=CENTER + DOWN * 0.15)
        ends = g.ends(I)
        bR = Brace(g.box, LEFT, buff=0.15, color=DIM)
        bC = Brace(g.box, UP, buff=0.12, color=DIM)
        lR = MathTex("R", color=FG).next_to(bR, LEFT, buff=0.15)
        lC = MathTex("C", color=FG).next_to(bC, UP, buff=0.12)
        self.play(Create(g), run_time=1.2)
        self.say("The problem setup is on an R \u00d7 C grid of cells, with two pairs of endpoints.")
        self.play(GrowFromCenter(bR), FadeIn(lR), GrowFromCenter(bC), FadeIn(lC))
        self.play(LaggedStart(*[GrowFromCenter(e) for e in ends], lag_ratio=0.25))
        self.say("The goal is to find a path from s\u2080 to t\u2080 and one from s\u2081 to t\u2081, so that "
                 "the two paths never meet, stay within the rectangle and, together, visit every "
                 "cell of the grid exactly once.")
        pa, anim = draw_path(g, S[0], "A", speed=9)
        self.play(anim)
        ta = g.tint(S[0], "A")
        self.play(FadeIn(ta), run_time=0.5)
        pb, anim = draw_path(g, S[1], "B", speed=9)
        self.play(anim)
        tb = g.tint(S[1], "B")
        self.play(FadeIn(tb), run_time=0.5)
        two = VGroup(g, ends, bR, bC, lR, lC, pa, pb, ta, tb)

        # Many pairs: the general puzzle.
        #
        self.say("With more pairs this is Zig-Zag Numberlink, the puzzle known as Flow Free. With "
                 "any number of pairs it is NP-complete (Adcock et al., 2015).",
                 speak="With more pairs this is Zig-Zag Numberlink, the puzzle known as Flow Free. "
                       "With any number of pairs it is NP-complete.")
        kg = Grid(7, 9, height=4.2, center=CENTER)
        kends = VGroup()
        for a, b, i in data.KPAIRS:
            kends.add(kg.endpoint(a, "", PAIR[i]), kg.endpoint(b, "", PAIR[i]))
        self.play(FadeOut(two), FadeIn(kg))
        self.play(LaggedStart(*[GrowFromCenter(e) for e in kends], lag_ratio=0.12))
        kpaths = VGroup(*[kg.path(p, PAIR[i]) for i, p in enumerate(data.KPAIRS_PATHS)])
        self.play(*[Create(p, rate_func=linear) for p in kpaths], run_time=2.5)

        # One pair: Hamiltonian paths, and the IPS test.
        #
        self.say("For one path there is a well-known polynomial-time algorithm (Itai, Papadimitriou "
                 "and Szwarcfiter, 1982).",
                 speak="For one path there is a well-known polynomial-time algorithm.")
        gi = Grid(5, 7, height=3.4, center=CENTER)
        ei = VGroup(gi.endpoint((0, 0), "s", "A"), gi.endpoint((4, 6), "t", "A"))
        self.play(FadeOut(VGroup(kg, kends, kpaths)), FadeIn(gi), FadeIn(ei))
        p, anim = draw_path(gi, data.IPS_YES_PATH, "A", speed=12)
        self.play(anim)
        one = VGroup(gi, ei, p)
        self.say("The single-path algorithm rejects endpoints whose checkerboard colours do not fit "
                 "the grid, and three placements on grids 1, 2 or 3 cells wide. Every other pair has "
                 "a path.")
        self.play(one.animate.scale(0.75).move_to(LEFT * 4.3 + CENTER))
        panels = VGroup()
        for name, R, C, s, t in data.IPS_NO:
            h = Grid(R, C, cs=0.34)
            chk = h.checker()
            e = VGroup(h.endpoint(s, "s", "A"), h.endpoint(t, "t", "A"))
            lab = text(name, 24, FG, BOLD)
            no = text("no path", 22, RED)
            panels.add(VGroup(lab, VGroup(h, chk, e), no).arrange(DOWN, buff=0.18))
        panels.arrange_in_grid(rows=2, cols=2, buff=(0.6, 0.45)).move_to(RIGHT * 2.6 + CENTER)
        self.play(LaggedStart(*[FadeIn(q) for q in panels], lag_ratio=0.3), run_time=2.4)

        # Two pairs: this work.
        #
        self.say("In this work, we show that two paths also have a polynomial-time algorithm, and "
                 "we check the proof in Lean 4.")
        back = two.copy()
        self.play(FadeOut(one), FadeOut(panels), FadeIn(back))
        self.finish()


class S03Result(Base):
    def construct(self):
        self.heading("Overview")
        w, h = 6.2, 4.6
        pl = RoundedRectangle(corner_radius=0.2, width=w, height=h).set_stroke(DIM, 2)
        pr = pl.copy()
        VGroup(pl, pr).arrange(RIGHT, buff=0.6).move_to(CENTER + DOWN * 0.1)
        hl = text("A side ≤ 10 (thin)", 30, FG, BOLD).next_to(pl.get_top(), DOWN, buff=0.3)
        hr = text("Both sides ≥ 11", 30, FG, BOLD).next_to(pr.get_top(), DOWN, buff=0.3)
        bl = text("plug DP, exact, linear\nin the long side", 24, FG)
        bl.next_to(pl.get_bottom(), UP, buff=0.3)
        br = text("solvable exactly when no\nforbidden pattern is found", 24, FG)
        br.next_to(pr.get_bottom(), UP, buff=0.3)

        # Each picture sits in the band between its heading and its footer, with clear space.
        #
        gl = Grid(data.PLUG.R, data.PLUG.C, cs=0.4)
        sl = VGroup(gl, gl.ends(data.PLUG, labels=False), gl.solution(data.PLUG_SOL))
        fit_between(sl, hl.get_bottom()[1] - 0.4, bl.get_top()[1] + 0.4, pl.get_center()[0], w - 1.0)
        gr = Grid(data.W3.R, data.W3.C, cs=0.2)
        sr = VGroup(gr, gr.ends(data.W3, labels=False), gr.solution(data.S3))
        fit_between(sr, hr.get_bottom()[1] - 0.4, br.get_top()[1] + 0.4, pr.get_center()[0], w - 1.0)
        self.say("Our two-path Zig-Zag Numberlink algorithm first looks at the shortest side of the "
                 "grid, to decide whether it is thin or not.")
        self.play(Create(pl), Create(pr), FadeIn(hl), FadeIn(hr))
        self.say("In the thin case, where a side is at most 10, a dynamic programming algorithm "
                 "decides it (the plug DP).")
        self.play(FadeIn(sl), FadeIn(bl))
        self.say("If both sides are at least 11, a finite catalogue of forbidden patterns is "
                 "consulted to decide solvability.")
        self.play(FadeIn(sr), FadeIn(br))
        self.say("Together, the two give a polynomial-time algorithm, O((R + C)\u00b7R\u00b7C).",
                 speak="Together, the two give a polynomial-time algorithm.")
        self.finish()


def plug_state(S, R, order, k):
    """The plug DP state after k cells (column-major order): the W + 1 frontier slots, each
    (edge or None, colour or None, id or None). Two slots with the same id are the two ends of
    one path piece; an id that appears once leads back to an endpoint."""
    P = set(order[:k])
    r, c = order[k]
    slots = []
    for row in range(R + 1):
        if row < r:
            e = ((row, c), (row, c + 1))
        elif row == r:
            e = ((r - 1, c), (r, c)) if r > 0 else None
        else:
            e = ((row - 1, c - 1), (row - 1, c)) if c > 0 else None
        slots.append(e)
    end_of = {}
    for p, col in zip(S, "AB"):
        i = 0
        while i < len(p):
            if p[i] not in P:
                i += 1
                continue
            j = i
            while j + 1 < len(p) and p[j + 1] in P:
                j += 1
            run = (col, i)
            if i > 0:
                end_of[frozenset((p[i - 1], p[i]))] = run
            if j < len(p) - 1:
                end_of[frozenset((p[j], p[j + 1]))] = run
            i = j + 1
    ids, out = {}, []
    for e in slots:
        run = end_of.get(frozenset(e)) if e else None
        if run is None:
            out.append((e, None, None))
            continue
        if run not in ids:
            ids[run] = len(ids) + 1
        out.append((e, run[0], ids[run]))
    return out, (r, c)


class S04PlugDP(Base):
    def construct(self):
        self.heading("Thin grids (side ≤ 10), plug DP")
        I, S = data.PLUG, data.PLUG_SOL
        R = I.R
        g = Grid(I.R, I.C, cs=0.66)
        g.place(np.array([-6.3, 2.0, 0]))
        ends = g.ends(I)
        self.play(FadeIn(g), FadeIn(ends))
        order = [(r, c) for c in range(I.C) for r in range(I.R)]
        edges = [(p[i], p[i + 1], col) for p, col in zip(S, "AB") for i in range(len(p) - 1)]
        top, bot = g.pt(0, 0)[1], g.pt(R, 0)[1]
        bx = g.pt(0, I.C)[0] + 2.6
        slot_title = text("frontier state", 24, DIM).move_to(np.array([bx, top + 0.45, 0]))
        slot_y = [top + (bot - top) * (i + 0.5) / (R + 1) for i in range(R + 1)]

        def marker_pos(e, i, r, c):
            if e is not None:
                return (g.cc(e[0]) + g.cc(e[1])) / 2
            return g.pt(0, c + 0.5) if i == r else g.pt(i - 1 + 0.5, 0)

        def state(k):
            P = set(order[:k])
            grp = VGroup()
            grp.add(g.squares(list(P), "#ffffff", 0.07))
            for a, b, col in edges:
                ina, inb = a in P, b in P
                if ina and inb:
                    grp.add(g.edge(a, b, col))
                elif ina or inb:
                    u, v = (a, b) if ina else (b, a)
                    m = (g.cc(u) + g.cc(v)) / 2
                    grp.add(Line(g.cc(u), m).set_stroke(COL[col], g.width_px()).set_z_index(2))
            if k == len(order):
                return grp
            slots, (r, c) = plug_state(S, R, order, k)
            pts = [g.pt(0, c + 1), g.pt(r, c + 1), g.pt(r, c), g.pt(R, c)] if r > 0 else \
                  [g.pt(0, c), g.pt(R, c)]
            grp.add(VMobject().set_points_as_corners(pts).set_stroke(YEL, 5).set_z_index(3))
            grp.add(g.squares([(r, c)], YEL, 0.0).set_stroke(YEL, 3).set_z_index(3))
            for i, (e, col, sid) in enumerate(slots):
                mp = marker_pos(e, i, r, c)
                box = RoundedRectangle(corner_radius=0.06, width=0.44, height=0.44)
                box.move_to(np.array([bx, slot_y[i], 0])).set_stroke(DIM, 2)
                dot = Circle(radius=0.17).move_to(mp).set_z_index(8)
                lead = DashedLine(mp + RIGHT * 0.17, box.get_left(), dash_length=0.06)
                lead.set_stroke(DIM, 1.5, 0.7).set_z_index(1)
                grp.add(lead)
                if col:
                    box.set_fill(COL[col], 1)
                    dot.set_fill(COL[col], 1).set_stroke(BG, 1.5)
                    n1 = text(str(sid), 22, BG, BOLD).move_to(box)
                    n2 = text(str(sid), 14, BG, BOLD).move_to(dot).set_z_index(9)
                    grp.add(box, n1, dot, n2)
                else:
                    dot.set_fill(BG, 1).set_stroke(DIM, 1.5)
                    grp.add(box, dot)
            return grp

        cur = state(0)
        self.add(cur)
        self.play(FadeIn(slot_title))
        self.say("For thin grids, a plug dynamic programming algorithm is used. Plug DP sweeps the "
                 "cells column by column, top to bottom. The yellow frontier separates the processed "
                 "cells from the rest.")
        for k in range(1, len(order) + 1):
            if k == 9:
                self.say("Each of the W + 1 edges crossing the frontier is a slot. A used slot holds "
                         "a colour and an id, and two slots with the same id are the ends of one "
                         "path piece.")
            if k == 17:
                self.say("An id that appears only once leads back to an endpoint. Unlike the "
                         "standard plug DP, which tracks only ids, each slot also carries a colour, "
                         "so green and orange pieces can never join.")
            if k == 27:
                self.say("A grid of short side W has W + 1 frontier edges, so the number of states "
                         "depends only on W ≤ 10, making the running time linear in the long "
                         "side.")
            new = state(k)
            self.remove(cur)
            self.add(new)
            cur = new
            self.wait(0.4)
        self.play(FadeIn(g.solution(S)[0]), FadeOut(slot_title))
        self.say("The instance is solvable exactly when the sweep ends in the empty state. "
                 "Width 10 needs about 10⁵ states, which is large but fixed.")
        self.finish()


class S05Parity(Base):
    def construct(self):
        self.heading("Forbidden patterns")
        self.say("For both sides ≥ 11, a finite catalogue of forbidden patterns decides "
                 "solvability.")
        base = data.SYM_BASE
        cs = 0.42

        def panel(J, name):
            h = Grid(J.R, J.C, cs=cs)
            return VGroup(VGroup(h, h.ends(J)), text(name, 24, DIM))

        p0 = panel(base, "as listed")
        targets = [panel(J, n) for n, J in data.SYMS]
        row = VGroup(p0, *targets)
        for p in row:
            p[1].next_to(p[0], DOWN, buff=0.3)
        row.arrange(RIGHT, buff=0.9, aligned_edge=DOWN).move_to(CENTER)
        self.play(FadeIn(p0))
        self.say("Each pattern also counts when the grid is rotated or mirrored, and when the "
                 "colours are swapped.")
        for t in targets:
            src = p0[0].copy()
            self.play(ReplacementTransform(src, t[0]), FadeIn(t[1]), run_time=1.4)
        self.settle()
        self.play(FadeOut(row))

        I = data.PARITY
        g = Grid(I.R, I.C, cs=0.8, center=LEFT * 3.3 + CENTER)
        chk = g.checker()
        ends = g.ends(I)
        head = side_title("Parity", "P", x=0.9)
        self.play(FadeIn(g), FadeIn(ends), FadeIn(head))
        self.say("For the parity condition, consider colouring the cells like a checkerboard. A single "
                 "path alternates colours, so its black count minus its white count is +1, \u22121 or "
                 "0, set by its two ends.")
        self.play(FadeIn(chk))
        signs = VGroup()
        for x in (I.s0, I.t0, I.s1, I.t1):
            s = "+1" if (x[0] + x[1]) % 2 == 0 else "−1"
            t = text(s, 24, YEL, BOLD).move_to(g.cc(x) + (UP + RIGHT) * g.cs * 0.55)
            signs.add(t.set_z_index(6))
        self.say("Give each endpoint σ = +1 if black and −1 if white. Since the paths cover "
                 "the grid, Σσ must be twice the grid's surplus of black cells, 0 if R·C "
                 "is even and 2 if odd.")
        self.play(LaggedStart(*[FadeIn(s) for s in signs], lag_ratio=0.3))
        eq = VGroup(text("Σσ = +1 +1 +1 −1 = 2", 30),
                    text("a 4 × 5 grid needs Σσ = 0", 30),
                    text("2 ≠ 0  ⇒  infeasible", 30, RED, BOLD))
        eq.arrange(DOWN, aligned_edge=LEFT, buff=0.35).next_to(head, DOWN, buff=0.6, aligned_edge=LEFT)
        self.say("Here Σσ = 2 on a 4 × 5 grid, which needs 0, so the parity condition "
                 "makes the instance infeasible.")
        self.play(LaggedStart(*[FadeIn(e) for e in eq], lag_ratio=0.5))
        self.finish()


class S05Topology(Base):
    def attempt(self, g, green, tries, head):
        pg, anim = draw_path(g, green, "A", speed=8)
        self.play(anim)
        marks = VGroup()
        for p in tries:
            d = dashed_path(g, p, "B")
            self.play(Create(d, rate_func=linear), run_time=max(0.8, len(p) / 8))
            x = x_mark(g, p[-1])
            self.play(GrowFromCenter(x), run_time=0.4)
            marks.add(d, x)
        return pg, marks

    def construct(self):
        self.heading("Forbidden patterns")
        I = data.T1_I
        g = Grid(I.R, I.C, cs=0.66, center=LEFT * 3.3 + CENTER)
        ends = g.ends(I)
        head = side_title("Alternating border", "T1, a topological condition", x=0.9)
        self.play(FadeIn(g), FadeIn(ends), FadeIn(head))
        self.say("For the alternating border test, all four endpoints lie on the border, and their "
                 "colours alternate around it.",
                 speak="For the alternating border test, all four endpoints lie on the border, and "
                       "their colours [alternate](/ˈɔltɚnˌeɪt/) around it.")
        self.say("Any green path from s₀ to t₀ cuts the grid in two, with one orange "
                 "endpoint on each side.")
        pg, marks = self.attempt(g, data.T1_GREEN, [], head)
        hi = {r: max(c for rr, c in data.T1_GREEN if rr == r) for r in range(I.R)}
        lo = {r: min(c for rr, c in data.T1_GREEN if rr == r) for r in range(I.R)}
        up = [(r, c) for r in range(I.R) for c in range(I.C) if c > hi[r]]
        dn = [(r, c) for r in range(I.R) for c in range(I.C) if c < lo[r]]
        self.play(FadeIn(g.squares(up, YEL, 0.14)), FadeIn(g.squares(dn, CUT, 0.2)))
        self.say("So every orange path from s₁ to t₁ runs into the green one. This "
                 "topological condition makes the instance infeasible.")
        for p in data.T1_TRIES:
            d = dashed_path(g, p, "B")
            self.play(Create(d, rate_func=linear), run_time=max(0.8, len(p) / 8))
            self.play(GrowFromCenter(x_mark(g, p[-1])), run_time=0.4)
        verdict = text("every orange path meets\nthe green one  ⇒  infeasible", 28, RED)
        verdict.next_to(head, DOWN, buff=0.6, aligned_edge=LEFT)
        self.play(FadeIn(verdict))
        self.settle()
        self.play(*[FadeOut(m) for m in self.mobjects if m not in (self.head, self.cap)])

        I = data.T2_I
        g = Grid(I.R, I.C, cs=0.66, center=LEFT * 3.3 + CENTER)
        ends = g.ends(I)
        head = side_title("Alternating square", "T2, T1 turned inside out", x=0.9)
        self.play(FadeIn(g), FadeIn(ends), FadeIn(head))
        self.say("T2 is T1 turned inside out. The endpoints fill a 2 × 2 square with each "
                 "colour on a diagonal, so the same alternation sits around a small square inside "
                 "the grid instead of around the border.")
        pg, anim = draw_path(g, data.T2_GREEN, "A", speed=8)
        self.play(anim)
        self.say("Green has to leave the square and come back, and the loop it makes shuts in an "
                 "orange endpoint. Again every orange path runs into it.")
        for p in data.T2_TRIES:
            d = dashed_path(g, p, "B")
            self.play(Create(d, rate_func=linear), run_time=max(0.8, len(p) / 8))
            self.play(GrowFromCenter(x_mark(g, p[-1])), run_time=0.4)
        verdict = text("every orange path meets\nthe green one  ⇒  infeasible", 28, RED)
        verdict.next_to(head, DOWN, buff=0.6, aligned_edge=LEFT)
        self.play(FadeIn(verdict))
        self.finish()


class S06Local(Base):
    def construct(self):
        self.heading("Local patterns")
        items = data.CATALOGUE[2:]
        panels = VGroup()
        grids = {}
        for name, I, _ in items:
            g = Grid(I.R, I.C, cs=min(2.3 / I.C, 1.45 / I.R))
            ends = g.ends(I)
            mark = VGroup()
            if name in data.CATALOGUE_MARK:
                mark.add(text("?", 26, YEL, BOLD).move_to(g.cc(data.CATALOGUE_MARK[name])))
            pan = VGroup(text(name, 28, FG, BOLD), VGroup(g, ends, mark)).arrange(DOWN, buff=0.2)
            grids[name] = (pan, g, I, ends)
            panels.add(pan)
        top = VGroup(*panels[:4]).arrange(RIGHT, buff=0.55)
        bottom = VGroup(*panels[4:]).arrange(RIGHT, buff=0.55)
        VGroup(top, bottom).arrange(DOWN, buff=0.45).move_to(CENTER + UP * 0.35)
        self.say("Small patterns at a corner or along an edge also make an instance infeasible.")
        self.play(LaggedStart(*[FadeIn(p) for p in panels], lag_ratio=0.15), run_time=2.5)

        def focus(name, msg):
            box = SurroundingRectangle(grids[name][0], color=YEL, buff=0.12, corner_radius=0.1)
            self.say(msg)
            self.play(Create(box), run_time=0.6)
            return box

        b1 = focus("L1", "L1. The endpoint s₀ is boxed in, every neighbour is an endpoint of "
                         "the other colour, so its path cannot leave it.")
        pan, g, I, ends = grids["L1"]
        ring = Circle(radius=0.62 * g.cs).move_to(g.cc(I.s0)).set_stroke(YEL, 5).set_z_index(9)
        self.play(Create(ring), Indicate(ends[0], color=YEL, scale_factor=1.4), run_time=1.0)
        b2 = focus("L2", "L2. The empty corner cell has just two neighbours, endpoints of different "
                         "colours, so whatever covers it would join green to orange.")
        self.play(FadeOut(b1), FadeOut(ring), run_time=0.3)
        self.say("L3 to L6 and E1 are similar wedges, forks, traps and closed corners. Each is "
                 "proved by following forced moves, since a cell that is not an endpoint needs "
                 "exactly two path neighbours, until two colours must meet.")
        self.play(FadeOut(b2), run_time=0.3)
        self.finish()


def window_thumb(k, cells, cs):
    """A k x k corner window with endpoints [(cell, colour)], no labels."""
    h = Grid(k, k, cs=cs, line=0.6)
    h.box.set_stroke(BORDER, 1.5)
    return VGroup(h, VGroup(*[h.endpoint(x, "", col) for x, col in cells]))


def win_size(cells):
    return 6 if all(x[0] < 6 and x[1] < 6 for x in cells) else 8


class S06Corner(Base):
    def show(self, thumbs, groups, rep, msg_list, msg_rep, rep_note=None):
        """thumbs arranged in rows; then one comes forward as the instance `rep`."""
        for m in msg_list:
            self.say(m)
            if m is msg_list[0]:
                self.play(*[FadeIn(gr) for gr in groups],
                          LaggedStart(*[FadeIn(t) for t in thumbs], lag_ratio=0.03), run_time=2.2)
        self.say(msg_rep)
        first = thumbs[0]
        self.play(*[t.animate.set_opacity(0.15) for t in thumbs[1:]],
                  *[gr.animate.set_opacity(0.15) for gr in groups],
                  Indicate(first, color=YEL), run_time=0.8)
        self.play(FadeOut(VGroup(*thumbs[1:], *groups)), ReplacementTransform(first, rep),
                  run_time=1.3)
        if rep_note is not None:
            self.play(FadeIn(rep_note))
        self.settle()
        self.play(FadeOut(rep), *([FadeOut(rep_note)] if rep_note is not None else []))

    def rep_grid(self, I, k):
        g = Grid(I.R, I.C, cs=0.34, center=CENTER)
        sh = g.squares([(r, c) for r in range(k) for c in range(k)], YEL, 0.16)
        return VGroup(g, sh, g.ends(I))

    def construct(self):
        self.heading("Corner patterns checked by computer")
        A, B = "A", "B"

        # B: three endpoints in the corner window, the fourth on the border outside it.
        #
        th, labs = [], VGroup()
        for kind in ("even", "odd"):
            row = [window_thumb(6, [(e[0], A), (e[1], A), (e[2], B)], 0.165)
                   for e, k in data.B_LIST if k == kind]
            th.append(row)
        rows = VGroup(VGroup(*th[0][:11]).arrange(RIGHT, buff=0.22),
                      VGroup(*th[0][11:]).arrange(RIGHT, buff=0.22),
                      VGroup(*th[1]).arrange(RIGHT, buff=0.22))
        l1 = text("R·C even, 21 patterns", 24, DIM)
        l2 = text("R and C odd, 5 patterns", 24, DIM)
        blk = VGroup(l1, rows[0], rows[1], l2, rows[2]).arrange(DOWN, buff=0.25, aligned_edge=LEFT)
        blk.move_to(CENTER)
        rep = self.rep_grid(data.CAT_B, 6)
        note = text("the other orange endpoint\nis on the border, outside", 24, FG)
        note.next_to(rep, RIGHT, buff=0.5)
        self.show(th[0] + th[1], [l1, l2], rep,
                  ["B lists 26 patterns with three endpoints in a 6 × 6 corner window, and "
                   "the fourth on the border outside it."],
                  "Here is one of them on a 12 × 12 grid. Green at two cells of the window, "
                  "orange at a third, and the other orange endpoint out on the border.", note)

        # C and D: all four endpoints in the corner window.
        #
        thc = [window_thumb(win_size(a + b), [(x, A) for x in a] + [(x, B) for x in b], 0.115)
               for a, b in data.C_LIST]
        rows = VGroup(*[VGroup(*thc[i:i + 12]).arrange(RIGHT, buff=0.2, aligned_edge=UP)
                        for i in range(0, 36, 12)]).arrange(DOWN, buff=0.3, aligned_edge=LEFT)
        lc = text("R·C even, 36 patterns", 24, DIM)
        VGroup(lc, rows).arrange(DOWN, buff=0.3, aligned_edge=LEFT).move_to(CENTER)
        a, b = data.C_LIST[0]
        self.show(thc, [lc], self.rep_grid(data.CAT_C, win_size(a + b)),
                  ["C lists 36 patterns with all four endpoints inside a corner window, for grids "
                   "with an even number of cells."],
                  "Here is one of them, on a 12 × 12 grid.")
        thd = [window_thumb(win_size(a + b), [(x, A) for x in a] + [(x, B) for x in b], 0.32)
               for a, b in data.D_LIST]
        rowd = VGroup(*thd).arrange(RIGHT, buff=0.8)
        ld = text("R·C odd, 3 patterns", 24, DIM)
        VGroup(ld, rowd).arrange(DOWN, buff=0.3).move_to(CENTER)
        a, b = data.D_LIST[0]
        self.show(thd, [ld], self.rep_grid(data.CAT_D, win_size(a + b)),
                  ["D lists 3 more such patterns, for grids with an odd number of cells."],
                  "Here is one of them, on an 11 × 11 grid.")
        reps = VGroup()
        for name, I, k in (("B", data.CAT_B, 6), ("C", data.CAT_C, win_size(data.C_LIST[0][0] + data.C_LIST[0][1])),
                           ("D", data.CAT_D, win_size(data.D_LIST[0][0] + data.D_LIST[0][1]))):
            rg = self.rep_grid(I, k).scale(0.7)
            reps.add(VGroup(text(name, 30, FG, BOLD), rg).arrange(DOWN, buff=0.2))
        reps.arrange(RIGHT, buff=0.8).move_to(CENTER)
        self.play(FadeIn(reps))
        self.say("None of these can be solved. Each is proved by a window certificate. A computer "
                 "lists every way the two paths can cover the corner window, and shows that none "
                 "of them can be joined up outside it.")
        self.finish()


class S06Routes(Base):
    def construct(self):
        self.heading("Forbidden patterns")
        I = data.CAT_R
        g = Grid(I.R, I.C, cs=0.46)
        g.place(np.array([-6.3, 2.75, 0]))
        ends = g.ends(I)
        head = side_title("Forced corner routes", "R, then the T1 argument", x=0.9)
        self.play(FadeIn(g), FadeIn(ends), FadeIn(head))
        self.say("In some corner patterns a path's first steps are forced. An endpoint next to an "
                 "empty corner, for instance, must run through that corner.")
        settled = g.squares(data.R_SETTLED, DIM, 0.6)
        routes = VGroup(*[g.path(p, "AB"[col]) for p, col in data.R_ROUTES])
        virt = VGroup(*[g.virtual(p[-1], "AB"[col]) for p, col in data.R_ROUTES])
        self.play(FadeIn(settled))
        self.play(*[Create(r, rate_func=linear) for r in routes], run_time=1.6)
        self.play(FadeIn(virt))
        self.say("Following the forced steps settles the grey cells and moves each endpoint to a "
                 "dashed circle.")
        self.say("The moved endpoints now alternate in colour around the border of what is left, so "
                 "the T1 argument applies and the instance is infeasible.",
                 speak="The moved endpoints now [alternate](/ˈɔltɚnˌeɪt/) in colour around the border of what is left, so "
                       "the T1 argument applies and the instance is infeasible.")
        verdict = text("moved endpoints alternate\naround the border  ⇒  infeasible", 28, RED)
        verdict.next_to(head, DOWN, buff=0.6, aligned_edge=LEFT)
        self.play(FadeIn(verdict))
        self.settle()
        self.play(*[FadeOut(m) for m in self.mobjects if m not in (self.head, self.cap)])

        rows = [("parity", "P"), ("topology", "T1  T2"), ("forced moves", "L1  L2  L3  L4  L5  L6  E1"),
                ("window certificates", "B  C  D"), ("forced routes, then topology", "R")]
        tab = VGroup()
        for kind, names in rows:
            tab.add(VGroup(text(kind, 28, DIM), text(names, 32, FG, BOLD)))
        for r in tab:
            r[0].move_to(np.array([-1.0, 0, 0]), aligned_edge=RIGHT)
            r[1].move_to(np.array([-0.4, 0, 0]), aligned_edge=LEFT)
        tab.arrange(DOWN, buff=0.45).move_to(CENTER)
        for r in tab:
            r[0].align_to(np.array([-1.0, 0, 0]), RIGHT)
            r[1].align_to(np.array([-0.4, 0, 0]), LEFT)
        self.heading("The whole catalogue")
        self.say("There are fourteen kinds of forbidden pattern in all. Finding any one shows there is "
                 "no solution, and for both sides \u2265 11, finding none shows there is one.")
        self.play(LaggedStart(*[FadeIn(r) for r in tab], lag_ratio=0.3), run_time=2.5)
        self.finish()


class S07Reduce(Base):
    def construct(self):
        self.heading("Reductions")
        I = data.RED_S
        g = Grid(I.R, I.C, height=5.2, center=LEFT * 3 + CENTER)
        ends = g.ends(I)
        self.play(FadeIn(g), FadeIn(ends))
        self.say("For larger grids, with both sides at least 11, the instance can often be shrunk "
                 "by deleting two endpoint-free rows or columns.")
        gap = g.squares(g.rows(range(2, 4)), CUT, 0.15)
        dele = g.squares(g.rows(range(0, 2)), CUT, 0.45)
        self.say("(S) strip. An edge gap of 4 or more endpoint-free rows, on a side of 13 or more. "
                 "Delete the outer two.")
        self.play(FadeIn(gap), FadeIn(dele))
        g2 = collapse_rows(self, g, 0, squash=[dele], movers=[ends, gap])
        self.settle()

        I = data.RED_K
        h = Grid(I.R, I.C, height=5.4, center=RIGHT * 3 + CENTER)
        he = h.ends(I)
        top = min(x[0] for x in I[2:] if x[0] > 10)
        gap_a = h.squares(h.rows(range(4, 8)), CUT, 0.15)
        gap_b = h.squares(h.rows(range(10, top)), CUT, 0.15)
        delk = h.squares(h.rows(range(8, 10)), CUT, 0.45)
        self.say("(K) compression. An internal gap of 10 or more endpoint-free rows. Delete two "
                 "from its middle. (I) does the same for shorter gaps away from the corners.")
        self.play(FadeIn(h), FadeIn(he))
        self.play(FadeIn(gap_a), FadeIn(gap_b), FadeIn(delk))
        below = VGroup(*[e for e, x in zip(he, I[2:]) if x[0] >= 10])
        collapse_rows(self, h, 8, squash=[delk], movers=[below, gap_b])
        self.say("Deleting two endpoint-free lines in this way changes neither the order of the "
                 "endpoints around the border nor what the 8 × 8 corner windows contain.")
        self.say("A side of 23 or more always has a reduction, so after reducing, both sides are "
                 "between 11 and 22.")
        self.finish()


class S08Band(Base):
    def construct(self):
        self.heading("Band extension")
        I, S, B, r = data.BAND_BEFORE, data.BAND_BEFORE_SOL, data.BAND, data.BAND_ROW
        cs = 0.46
        g = Grid(I.R, I.C, cs=cs)
        g.place(np.array([-3.4 - g.C * cs / 2, 2.9, 0]))
        ends = g.ends(I)
        sol = g.solution(S)
        self.say("A reduction leaves a smaller instance to solve. Its solution then has to be turned "
                 "back into a solution of the original, with the two deleted rows put back.")
        self.play(FadeIn(g), FadeIn(ends), FadeIn(sol))
        log = VGroup()

        def note(s):
            t = text(s, 28, FG)
            if len(log):
                t.next_to(log[-1], DOWN, aligned_edge=LEFT, buff=0.4)
            else:
                t.move_to(np.array([-0.8, 1.8, 0]), aligned_edge=LEFT)
            log.add(t)
            self.play(FadeIn(t, shift=0.1 * RIGHT), run_time=0.5)

        self.say("Band extension does this. Insert two empty rows below an endpoint-free row, then "
                 "reroute the paths so they cover the new cells.")
        cutl = g.cut(0, r + 1, YEL)
        self.play(Create(cutl))
        J = data.BAND_AFTER
        g2 = Grid(J.R, J.C, cs=cs).place(g.pt(0, 0))
        below = VGroup(*[e for e, x in zip(ends, I[2:]) if x[0] > r])
        pa, pb = g2.path(B["shifted"][0], "A"), g2.path(B["shifted"][1], "B")
        self.say("1. Every path edge that crosses there is stretched through the two new rows.")
        note("1. stretch the crossing edges")
        self.play(FadeOut(sol[0]), FadeOut(cutl))
        self.play(ReplacementTransform(g, g2), below.animate.shift(DOWN * 2 * cs),
                  Transform(sol[1], pa), Transform(sol[2], pb), run_time=1.5)
        self.remove(sol[1], sol[2])
        pa, pb = g2.path(B["stretched"][0], "A"), g2.path(B["stretched"][1], "B")
        self.add(pa, pb)
        xs = B["xs"]
        bounds = [-1] + xs + [J.C]
        blocks = VGroup()
        for i in range(len(bounds) - 1):
            lo, hi = bounds[i] + 1, bounds[i + 1] - 1
            if lo <= hi:
                cells = [(rr, c) for rr in (r + 1, r + 2) for c in range(lo, hi + 1)]
                blocks.add(g2.squares(cells, YEL, 0.18))
        self.say("2. The new rows split into blocks between the crossings. A crossing absorbs the "
                 "block beside it with a U-shaped detour.")
        self.play(FadeIn(blocks))
        note("2. U-detours absorb the blocks")
        qa, qb = g2.path(B["detoured"][0], "A"), g2.path(B["detoured"][1], "B")
        self.play(Transform(pa, qa), Transform(pb, qb), run_time=1.8)
        self.say("3. The last block is absorbed by a square flip. A path edge along the row above "
                 "is swapped for a loop around the block.")
        cyc = B["block"]
        loop = VMobject().set_points_as_corners([g2.cc(x) for x in cyc + cyc[:1]])
        loop = DashedVMobject(loop.set_stroke(YEL, 4), num_dashes=16).set_z_index(3)
        (u, v) = B["flip"]
        hl = Line(g2.cc(u), g2.cc(v)).set_stroke(RED, 10).set_z_index(3)
        note("3. a square flip absorbs the last one")
        self.play(Create(loop), Create(hl))
        self.play(Indicate(hl, color=RED))
        fa, fb = g2.path(B["final"][0], "A"), g2.path(B["final"][1], "B")
        self.play(Transform(pa, fa), Transform(pb, fb), FadeOut(loop), FadeOut(hl), FadeOut(blocks),
                  run_time=1.6)
        self.play(FadeIn(g2.tint(B["final"][0], "A")), FadeIn(g2.tint(B["final"][1], "B")))
        self.say("A counting argument shows that the edge needed for the flip always exists. "
                 "The result solves the original, larger instance.")
        self.finish()


class S09Moves(MoveMixin, Base):
    def construct(self):
        self.heading("Moves, cut, solve, glue")
        pieces = {
            "Strip": "two-path piece\n+ empty block",
            "1/3": "one-path piece (IPS)\n+ two-path piece",
            "2/2 cross": "two two-path pieces",
            "2/2 same": "two one-path pieces (IPS)",
            "Excursion": "two two-path pieces",
        }
        for i, (name, J, sol, p, note) in enumerate(data.MOVES):
            g = Grid(J.R, J.C, cs=0.5)
            g.place(np.array([-4.6, 2.65, 0]))
            ends = g.ends(J)
            t = text(name, 40, FG, BOLD).move_to(RIGHT * 3.2 + UP * 1.6)
            d = text(pieces[name], 26, DIM).next_to(t, DOWN, buff=0.4)
            self.play(FadeIn(g), FadeIn(ends))
            if i == 0:
                self.say("If no reduction applies, both sides are at most 22, and a computer check "
                         "shows that every instance of those sizes with no forbidden pattern has a valid move.")
                self.say("A move is a straight cut plus a choice of where the paths cross it. Each "
                         "crossing cell becomes a virtual endpoint (dashed) of its piece.",
                         speak="A move is a straight cut plus a choice of where the paths cross "
                               "it. Each crossing cell becomes a virtual endpoint of its piece.")
            self.play(FadeIn(t), FadeIn(d))
            self.say(note + ".")
            if name == "Strip":
                self.strip(g, J, ends, sol, p)
            else:
                self.split_move(g, J, ends, sol, 0, p)
            if name == "1/3":
                self.say("A two-path piece is solved by the plug DP if it is thin, and by the whole "
                         "algorithm, recursively, if not.")
            self.settle()
            self.wait(0.2)
            self.play(*[FadeOut(m) for m in self.mobjects if m not in (self.head, self.cap)])
        self.finish()

    def strip(self, g, J, ends, sol, p):
        near, cyc, a, glued = data.strip_parts(J, p)
        cutl = g.cut(0, p)
        self.play(Create(cutl))
        gb = Grid(J.R - p, J.C, cs=g.cs).place(g.pt(p, 0))
        ga = Grid(p, J.C, cs=g.cs).place(g.pt(0, 0))
        self.remove(g)
        self.add(ga, gb)
        self.play(VGroup(ga, ends).animate.shift(UP * 0.3), gb.animate.shift(DOWN * 0.3),
                  FadeOut(cutl))
        na, nb = ga.path(near[0], "A"), ga.path(near[1], "B")
        self.play(Create(na, rate_func=linear), Create(nb, rate_func=linear), run_time=1.6)
        self.say("Solve the side with the endpoints. The empty block has a Hamiltonian cycle using "
                 "every edge along its top row.")
        loc = [(x[0] - p, x[1]) for x in cyc]
        loop = VMobject().set_points_as_corners([gb.cc(x) for x in loc + loc[:1]])
        loop.set_stroke(YEL, 4).set_z_index(2)
        self.play(Create(loop), run_time=1.6)
        self.play(VGroup(ga, ends, na, nb).animate.shift(DOWN * 0.3),
                  VGroup(gb, loop).animate.shift(UP * 0.3))
        e1 = Line(g.cc((p - 1, a)), g.cc((p - 1, a + 1))).set_stroke(RED, 10).set_z_index(3)
        e2 = Line(g.cc((p, a)), g.cc((p, a + 1))).set_stroke(RED, 10).set_z_index(3)
        self.say("Once each sub-grid has been solved, splice the two back together at a pair of "
                 "parallel edges. The cycle then becomes part of one of the paths.")
        self.play(Create(e1), Create(e2))
        full = g.solution(glued)
        self.remove(ga, gb)
        self.add(g)
        self.play(FadeOut(na), FadeOut(nb), FadeOut(loop), FadeOut(e1), FadeOut(e2),
                  FadeIn(full), run_time=1.2)


class S10Example(MoveMixin, Base):
    def construct(self):
        self.heading("A worked example, 16 × 13")
        W0, W1, W2, W3 = data.W0, data.W1, data.W2, data.W3
        cs = 0.33
        top = 2.95
        g0 = Grid(W0.R, W0.C, cs=cs)
        g0.place(np.array([-4.8, top, 0]))
        e0 = g0.ends(W0)
        self.play(FadeIn(g0), FadeIn(e0))
        self.say("This 16 × 13 instance has no forbidden pattern. The solver works as follows.")
        log = VGroup()

        def note(s):
            t = text(s, 24, FG)
            if len(log):
                t.next_to(log[-1], DOWN, aligned_edge=LEFT, buff=0.24)
            else:
                t.move_to(np.array([1.0, 2.6, 0]), aligned_edge=LEFT)
            log.add(t)
            self.play(FadeIn(t, shift=0.1 * RIGHT), run_time=0.5)

        gapc = g0.squares(g0.rows(range(2, 4)), CUT, 0.15)
        delc = g0.squares(g0.rows(range(0, 2)), CUT, 0.45)
        self.say("Rows 0 to 3 are endpoint-free and 16 ≥ 13, so reduction (S) deletes rows 0 and 1.")
        self.play(FadeIn(gapc), FadeIn(delc))
        note("1. strip reduction, delete rows 0, 1")
        self.play(FadeOut(gapc), run_time=0.4)
        g1 = collapse_rows(self, g0, 0, squash=[delc], movers=[e0])
        e1 = e0

        self.say("14 × 13 has no reduction. Rows 12 and 13 are empty, so a strip move sets them "
                 "aside, to be spliced back later.")
        c1 = g1.cut(0, 12)
        self.play(Create(c1))
        g2 = Grid(W2.R, W2.C, cs=cs).place(g1.pt(0, 0))
        blk_r = Grid(2, W1.C, cs=cs).place(g1.pt(12, 0))
        self.remove(g1)
        self.add(g2, blk_r)
        self.play(blk_r.animate.shift(DOWN * 0.35).set_stroke(opacity=0.45), FadeOut(c1))
        note("2. strip move, set rows 12–13 aside")

        self.say("Then columns 11 and 12 are empty, and another strip move sets them aside.")
        c2 = g2.cut(1, 11)
        self.play(Create(c2))
        g3 = Grid(W3.R, W3.C, cs=cs).place(g2.pt(0, 0))
        blk_c = Grid(W2.R, 2, cs=cs).place(g2.pt(0, 11))
        self.remove(g2)
        self.add(g3, blk_c)
        self.play(blk_c.animate.shift(RIGHT * 0.35).set_stroke(opacity=0.45), FadeOut(c2))
        note("3. strip move, set columns 11–12 aside")

        axis, k = data.CUT3
        self.say("The 12 \u00d7 11 piece is cut with both paths crossing the cut. Both halves are "
                 "thin, so the plug DP solves them.")
        note("4. crossing cut, plug DP on both halves")
        full3 = self.split_move(g3, W3, e1, data.S3, axis, k, gap=0.4, speed=22)

        self.say("Glue back the set-aside columns, then the rows, by strip splices.")
        g2b = Grid(W2.R, W2.C, cs=cs).place(g3.pt(0, 0))
        full2 = g2b.solution(data.S2)
        self.play(FadeOut(full3), FadeOut(blk_c), ReplacementTransform(g3, g2b), FadeIn(full2),
                  run_time=1.4)
        g1b = Grid(W1.R, W1.C, cs=cs).place(g2b.pt(0, 0))
        full1 = g1b.solution(data.S1)
        self.play(FadeOut(full2), FadeOut(blk_r), ReplacementTransform(g2b, g1b), FadeIn(full1),
                  run_time=1.4)
        note("5. strip splices, columns, then rows")

        self.say("Finally, band extension puts back the two deleted rows. The result solves the "
                 "16 × 13 instance.")
        g0b = Grid(W0.R, W0.C, cs=cs).place(g1b.pt(0, 0))
        full0 = g0b.solution(data.S0)
        e0b = g0b.ends(W0)
        self.play(FadeOut(full1), ReplacementTransform(g1b, g0b), ReplacementTransform(e1, e0b),
                  FadeIn(full0), run_time=1.6)
        note("6. band extension puts rows 0, 1 back")
        self.finish()


class S11Proof(Base):
    def construct(self):
        self.heading("Correctness")

        def box(lines, w, h, color=DIM):
            r = RoundedRectangle(corner_radius=0.15, width=w, height=h).set_stroke(color, 2)
            t = text(lines, 24, FG)
            if t.width > w - 0.3:
                t.scale_to_fit_width(w - 0.3)
            return VGroup(r, t.move_to(r))

        tb = box("Soundness\nIf a forbidden pattern is found,\nthere is no solution.", 6.4, 1.45, RED)
        ta = box("Completeness\nWith both sides \u2265 11 and no forbidden\npattern, there is a solution.",
                 6.4, 1.45, COL["A"])
        VGroup(tb, ta).arrange(RIGHT, buff=0.4).move_to(UP * 2.3)
        how = text("proved by parity, topology, forced moves\nand window certificates", 20, DIM)
        how.next_to(tb, DOWN, buff=0.12)
        self.say("The soundness theorem proves that if a forbidden pattern is found, no solution "
                 "exists.")
        self.play(FadeIn(tb), FadeIn(how))
        self.say("The completeness theorem proves the catalogue is complete. Every instance with both "
                 "sides \u2265 11 and no forbidden pattern is solvable. The proof is an induction on "
                 "area.")
        self.play(FadeIn(ta))

        n1 = box("no forbidden pattern, both sides \u2265 11", 5.4, 0.65)
        n2 = box("a reduction applies, so solve the\nsmaller instance by induction,\nthen extend back",
                 4.6, 1.3)
        n3 = box("no reduction, so sides \u2264 22, and a\nvalid move exists (computer\ncheck of 144 box sizes)",
                 4.6, 1.3)
        n4 = box("solve the pieces by a single Hamiltonian path,\nthe plug DP, or induction, then glue them", 6.6, 0.9)
        n1.move_to(RIGHT * 2.2 + UP * 0.85)
        VGroup(n2, n3).arrange(RIGHT, buff=1.2).next_to(n1, DOWN, buff=0.35).set_x(0)
        n4.next_to(n3, DOWN, buff=0.3).align_to(n3, RIGHT)
        arr = VGroup(Arrow(n1.get_bottom(), n2.get_top(), buff=0.06, stroke_width=3),
                     Arrow(n1.get_bottom(), n3.get_top(), buff=0.06, stroke_width=3),
                     Arrow(n3.get_bottom(), n4.get_top(), buff=0.06, stroke_width=3))
        arr.set_color(DIM)
        self.play(FadeIn(n1))
        self.play(Create(arr[0]), FadeIn(n2), Create(arr[1]), FadeIn(n3))
        self.say("Either a reduction gives a smaller instance, still free of forbidden patterns, or both sides are at most 22, "
                 "where a computer check found a valid move.")
        self.play(Create(arr[2]), FadeIn(n4))
        self.say("The pieces of a move are solved by a single Hamiltonian path, by the plug DP, or by "
                 "induction, and glued.")
        self.settle()
        self.play(*[FadeOut(m) for m in (tb, ta, how, n1, n2, n3, n4, arr)])

        lean = VGroup(
            text("theorem passes_iff_solvable", 28, COL["A"], mono=True),
            text("    both sides ≥ 11, no forbidden pattern ↔ solvable", 24, FG, mono=True),
            text("theorem solvableB_iff", 28, COL["A"], mono=True),
            text("    every rectangle, the decision procedure is correct", 24, FG, mono=True),
            text("theorem thinBF_iff", 28, COL["A"], mono=True),
            text("    the plug DP is exact", 24, FG, mono=True),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.22).move_to(UP * 1.0)
        trust = text("The finite checks are certificates checked by the Lean kernel.\n"
                     "The results use only the standard axioms.", 22, DIM)
        trust.next_to(lean, DOWN, buff=0.5)
        self.say("All of this is checked in Lean 4, in three main theorems.")
        self.play(LaggedStart(*[FadeIn(l) for l in lean], lag_ratio=0.25), run_time=2.5)
        self.say("The finite checks are certificates, and Lean's kernel checks every proof.")
        self.play(FadeIn(trust))
        self.say("This shows that two-path Zig-Zag Numberlink on rectangles is decided, and solved, "
                 "in polynomial time, with the whole argument checked in Lean 4.")
        self.settle()
        self.play(FadeOut(lean), FadeOut(trust), FadeOut(self.head))
        self.head = None

        end = VGroup(text("Two-path Zig-Zag Numberlink on rectangles", 36, FG, BOLD),
                     text("Paper, Lean proofs, and Python, JavaScript and C code", 26, DIM),
                     text("github.com/zzyzek/R2K2ZZN", 32, COL["A"], mono=True),
                     text("CC0 1.0", 22, DIM)).arrange(DOWN, buff=0.4).move_to(UP * 0.4)
        self.unsay()
        self.narrate("The paper, the Lean proof and reference implementations can be found at the "
                     "repository listed.")
        self.play(LaggedStart(*[FadeIn(e) for e in end], lag_ratio=0.3), run_time=2)
        self.settle()
        self.wait(2)
        self.play(FadeOut(end))


SCENES = ["S01Title", "S02Problem", "S03Result", "S04PlugDP", "S05Parity", "S05Topology",
          "S06Local", "S06Corner", "S06Routes", "S07Reduce", "S08Band", "S09Moves", "S10Example",
          "S11Proof"]
