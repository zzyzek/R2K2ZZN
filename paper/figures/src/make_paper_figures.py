# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Figures made for the paper (the others come from docs/figures/make_figures.py).

    python3 make_paper_figures.py      (writes SVG here and PDF into paper/figures, via Inkscape)
"""
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..", "..")
sys.path.insert(0, os.path.join(ROOT, "docs", "figures"))
sys.path.insert(0, os.path.join(ROOT, "lib", "python"))

from fig import grid_svg, inst_ends, sol_paths, save
from zzn import Instance, solve, fires, check_solution, hamiltonian_path
from zzn.catalogue import rewrite_all, walk3

os.chdir(HERE)
GRAY, YEL, PUR = "#9aa0a6", "#F2C94C", "#7F77DD"
OUT = []


def out(name, svg):
    save(name + ".svg", svg)
    OUT.append(name)


# 1. Splash: an instance, a solution, and an unsolvable instance ---------------------------------
I = Instance(7, 10, (1, 1), (5, 8), (5, 2), (1, 7))
S = solve(I)
assert S is not None and check_solution(I, S)
out("splash_instance", grid_svg(7, 10, inst_ends(I), title="An instance", cs=24))
out("splash_solution", grid_svg(7, 10, inst_ends(I), sol_paths(S), title="A solution", cs=24))
U = Instance(7, 10, (0, 2), (6, 7), (0, 7), (6, 2))
assert fires(*U) == "T1" and solve(U) is None
out("splash_unsolvable", grid_svg(7, 10, inst_ends(U), title="Unsolvable", cs=24,
                                  note="the pairs alternate around the border"))

# 2. Definitions -------------------------------------------------------------------------------
# Black and white cells, and sigma.
I = Instance(4, 6, (0, 0), (3, 4), (1, 4), (2, 2))
assert solve(I) is not None
assert [1 if (r + c) % 2 == 0 else -1 for r, c in (I.s0, I.t0, I.s1, I.t1)] == [1, -1, -1, 1]
ends = {I.s0, I.t0, I.s1, I.t1}
signs = [((r, c), "+" if (r + c) % 2 == 0 else "−") for r in range(4) for c in range(6)
         if (r, c) not in ends]
out("def_sigma", grid_svg(4, 6, inst_ends(I), checker=True, marks=signs, cs=26,
                          title="Signs σ",
                          note="endpoints: +1 −1 −1 +1"))

# Lines and gaps (rows): edge gaps at the top and bottom, an internal gap between endpoint rows.
I = Instance(13, 7, (4, 1), (5, 5), (9, 2), (4, 4))
out("def_gaps", grid_svg(13, 7, inst_ends(I), cs=16, title="Gaps",
                         shade=[([(r, c) for r in range(4) for c in range(7)], PUR, 0.25),
                                ([(r, c) for r in (6, 7, 8) for c in range(7)], YEL, 0.35),
                                ([(r, c) for r in (10, 11, 12) for c in range(7)], PUR, 0.25)]))

# IPS: an acceptable pair with its Hamiltonian path, and a pair failing the colour condition.
s, t = (0, 0), (2, 3)
p = hamiltonian_path(4, 5, s, t)
assert p is not None
out("def_ips_yes", grid_svg(4, 5, [(s, "s", "A"), (t, "t", "A")], [("A", p)], checker=True, cs=26,
                            title="Acceptable"))
s, t = (0, 0), (2, 2)
assert hamiltonian_path(4, 5, s, t) is None
out("def_ips_no", grid_svg(4, 5, [(s, "s", "A"), (t, "t", "A")], checker=True, cs=26,
                           title="Not acceptable"))

# A cut, its crossing pairs, and the two pieces with their virtual endpoints.
J = Instance(9, 6, (0, 1), (8, 4), (1, 4), (7, 1))
SJ = solve(J)
assert SJ is not None


def crossings(sol, p):
    out_ = []
    for col, path in (("A", sol[0]), ("B", sol[1])):
        for i in range(len(path) - 1):
            a, b = path[i], path[i + 1]
            if {a[0], b[0]} == {p - 1, p} and a[1] == b[1]:
                out_.append((col, a if a[0] == p - 1 else b, b if a[0] == p - 1 else a))
    return out_


cut = next(p for p in range(2, J.R - 1) if len(crossings(SJ, p)) == 2 and
           {c for c, _, _ in crossings(SJ, p)} == {"A", "B"})
xs = crossings(SJ, cut)

# Drawn rotated 90 degrees counterclockwise, so the cut is vertical: the upper piece becomes the
# left piece and the lower piece the right one; each piece shows the cut on its cut side.
#
rot = lambda x: (J.C - 1 - x[1], x[0])
rends = [(rot(x), lab, col) for x, lab, col in inst_ends(J)]
rpaths = [(col, [rot(x) for x in p_]) for col, p_ in sol_paths(SJ)]
rvirt = [(rot(u), "", col) for col, u, v in xs] + [(rot(v), "", col) for col, u, v in xs]
out("def_cut", grid_svg(J.C, J.R, rends, rpaths, cuts=[("v", cut)], virtual=rvirt,
                        title="A cut", cs=22))
left_ends = [(x, lab, col) for x, lab, col in rends if x[1] < cut]
right_ends = [((x[0], x[1] - cut), lab, col) for x, lab, col in rends if x[1] >= cut]
left_paths = [(col, [x for x in p_ if x[1] < cut]) for col, p_ in rpaths]
right_paths = [(col, [(x[0], x[1] - cut) for x in p_ if x[1] >= cut]) for col, p_ in rpaths]
out("def_piece_left", grid_svg(J.C, cut, left_ends, left_paths, cuts=[("v", cut)],
                               virtual=[(rot(u), "", col) for col, u, v in xs],
                               title="Left", cs=22))
out("def_piece_right", grid_svg(J.C, J.R - cut, right_ends, right_paths, cuts=[("v", 0)],
                                virtual=[((rot(v)[0], rot(v)[1] - cut), "", col) for col, u, v in xs],
                                title="Right", cs=22))

# 3. Catalogue: T2 ------------------------------------------------------------------------------
I = Instance(5, 6, (1, 2), (2, 3), (1, 3), (2, 2))
assert fires(*I) == "T2", fires(*I)
out("cat_T2", grid_svg(5, 6, inst_ends(I), cs=22, title="T2: alternating square"))

# 4. The R entry: the three rules at a corner, and full examples ---------------------------------
# Rule panels: the top-left 5 x 5 corner; green is a colour gamma, orange the other colour.
def open_corner(svg, R, C, cs, top, left, ext):
    """Draw a grid as the top-left corner of a larger one: only the top and left borders are
    solid; the grid lines run on past the bottom and right edges and fade out."""
    W, H = left + C * cs + ext + 4, top + R * cs + ext + 4
    svg = re.sub(r'width="\d+" height="\d+" viewBox="0 0 \d+ \d+"',
                 f'width="{W}" height="{H}" viewBox="0 0 {W} {H}"', svg, count=1)
    x0, y0, x1, y1 = left, top, left + C * cs, top + R * cs
    border = re.search(r'<rect x="[\d.]+" y="[\d.]+" width="[\d.]+" height="[\d.]+" fill="none" stroke="#333" stroke-width="1.4"/>', svg)
    lines = ['<defs><linearGradient id="fr" x1="0" y1="0" x2="1" y2="0">'
             '<stop offset="0" stop-color="#c8c8c8"/><stop offset="1" stop-color="#c8c8c8" stop-opacity="0"/>'
             '</linearGradient><linearGradient id="fd" x1="0" y1="0" x2="0" y2="1">'
             '<stop offset="0" stop-color="#c8c8c8"/><stop offset="1" stop-color="#c8c8c8" stop-opacity="0"/>'
             '</linearGradient></defs>']
    for r in range(R + 1):
        y = y0 + r * cs
        lines.append(f'<rect x="{x1}" y="{y - 0.3}" width="{ext}" height="0.6" fill="url(#fr)"/>')
    for c in range(C + 1):
        x = x0 + c * cs
        lines.append(f'<rect x="{x - 0.3}" y="{y1}" width="0.6" height="{ext}" fill="url(#fd)"/>')
    lines.append(f'<line x1="{x0}" y1="{y0}" x2="{x1 + ext}" y2="{y0}" stroke="#333" stroke-width="1.4"/>')
    lines.append(f'<line x1="{x0}" y1="{y0}" x2="{x0}" y2="{y1 + ext}" stroke="#333" stroke-width="1.4"/>')
    return svg[:border.start()] + "\n".join(lines) + svg[border.end():]


def rule(name, ends_, routes, settled, eff, title):
    cs = 24
    svg = grid_svg(5, 5, ends_, routes, shade=[(settled, GRAY, 0.45)],
                   virtual=[(x, "", col) for x, col in eff], cs=cs, title=title)
    out(name, open_corner(svg, 5, 5, cs, top=14 + 22, left=14, ext=cs))


rule("rule_R1", [((0, 1), "", "A")], [("A", [(0, 1), (0, 0), (1, 0)])], [(0, 0), (0, 1)],
     [((1, 0), "A")], "R1")
rule("rule_R2", [((0, 0), "", "A"), ((1, 1), "", "A")],
     [("A", [(0, 0), (0, 1), (0, 2)]), ("A", [(1, 1), (1, 0), (2, 0)])],
     [(0, 0), (0, 1), (1, 0), (1, 1)], [((0, 2), "A"), ((2, 0), "A")], "R2")
rule("rule_R3", [((1, 2), "", "A"), ((2, 1), "", "B")],
     [("A", [(1, 2), (0, 2), (0, 3)]), ("B", [(2, 1), (1, 1), (0, 1), (0, 0), (1, 0), (2, 0), (3, 0)])],
     [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (1, 2), (2, 1)], [((0, 3), "A"), ((3, 0), "B")],
     "R3")


def r_example(name, J):
    pts = [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]
    eff, removed, _ = rewrite_all(J.R, J.C, pts)
    walk = walk3(J.R, J.C, removed)
    real = {J.s0, J.t0, J.s1, J.t1}
    print(name, J, "settled:", sorted(removed))
    out(name, grid_svg(J.R, J.C, inst_ends(J), cs=18, title=f"R fires ({J.R} x {J.C})",
                       shade=[(walk, PUR, 0.18), (removed, GRAY, 0.55)],
                       virtual=[(q[0], "", "A" if q[1] == 0 else "B") for q in eff if q[0] not in real]))


def find_r(seed, want_rule3):
    rng = random.Random(seed)
    for _ in range(400000):
        R, C = 11, 12
        pts = set()
        while len(pts) < 4:
            cr, cc = rng.choice([0, R - 1]), rng.choice([0, C - 1])
            r = cr + (rng.randint(0, 2) if cr == 0 else -rng.randint(0, 2))
            c = cc + (rng.randint(0, 2) if cc == 0 else -rng.randint(0, 2))
            pts.add((r, c))
        J = Instance(R, C, *list(pts))
        if fires(*J) != "R":
            continue
        _, removed, _ = rewrite_all(R, C, [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)])
        if want_rule3 == (len(removed) >= 8):
            return J
    raise RuntimeError("no example found")


r_example("r_example1", find_r(5, False))
r_example("r_example2", find_r(7, True))

# 5. PDF ----------------------------------------------------------------------------------------
for name in OUT:
    subprocess.run(["inkscape", name + ".svg", "--export-type=pdf",
                    "--export-filename=" + os.path.join("..", name + ".pdf")],
                   check=True, capture_output=True)
print("written:", " ".join(OUT))
