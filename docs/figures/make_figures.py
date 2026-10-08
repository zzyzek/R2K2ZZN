# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Generate the figures of docs/ALGORITHM.md and docs/PLUGDP.md.  python3 make_figures.py"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "lib", "python"))

from fig import grid_svg, inst_ends, sol_paths, save
from zzn import Instance, solve, check_solution, fires
from zzn import lift
from zzn.solver import _Solver, delete_lines
from zzn.catalogue import rewrite_all, walk3
from zzn.plugdp import solve_paths

os.chdir(HERE)
GRAY, YEL, PUR = "#9aa0a6", "#F2C94C", "#7F77DD"


def E(cells_labels):
    return cells_labels


# 1. the problem --------------------------------------------------------------------------
I = Instance(4, 4, (0, 0), (0, 3), (1, 0), (1, 3))
S = solve(I)
save("problem.svg", grid_svg(4, 4, inst_ends(I), title="Instance"))
save("solution.svg", grid_svg(4, 4, inst_ends(I), sol_paths(S), title="Solution"))

# 2. parity ---------------------------------------------------------------------------------
I = Instance(4, 5, (0, 0), (2, 4), (1, 1), (3, 2))
save("cat_P.svg", grid_svg(4, 5, inst_ends(I), checker=True, title="P: parity",
                           note="signs +1 +1 +1 -1: sum 2, needs 0"))

# 3. catalogue entries ----------------------------------------------------------------------
cat = {
    "T1": (Instance(5, 7, (0, 0), (4, 6), (0, 6), (4, 0)), "T1: alternate on the border"),
    "T2": (Instance(4, 4, (1, 1), (2, 2), (1, 2), (2, 1)), "T2: alternating unit square"),
    "L1": (Instance(4, 5, (0, 0), (3, 3), (0, 1), (1, 0)), "L1: isolated endpoint"),
    "L2": (Instance(4, 5, (0, 1), (3, 3), (1, 0), (2, 4)), "L2: corner block"),
    "L3": (Instance(4, 5, (0, 2), (1, 1), (1, 0), (3, 4)), "L3: corner wedge"),
    "L4": (Instance(4, 5, (0, 0), (1, 1), (0, 2), (3, 4)), "L4: corner fork"),
    "L5": (Instance(4, 5, (0, 0), (3, 4), (0, 2), (2, 0)), "L5: corner trap"),
    "L6": (Instance(4, 6, (0, 1), (1, 0), (0, 4), (1, 5)), "L6: two closed corners"),
    "E1": (Instance(4, 7, (0, 1), (1, 2), (0, 4), (1, 3)), "E1: edge closure"),
}
for name, (inst, title) in cat.items():
    f = fires(inst.R, inst.C, inst.s0, inst.t0, inst.s1, inst.t1)
    assert f is not None, (name, inst)
    marks = [((0, 0), "?")] if name in ("L2", "L3", "L5") else []
    save(f"cat_{name}.svg", grid_svg(inst.R, inst.C, inst_ends(inst), marks=marks, title=title))

# B: corner triple (0,0) A, (1,1) A, (1,2) B, the other B far away on the border
I = Instance(12, 12, (0, 0), (1, 1), (1, 2), (11, 8))
assert fires(*I) == "B", fires(*I)
save("cat_B.svg", grid_svg(12, 12, inst_ends(I), cs=18, title="B: corner triple + far partner",
                           shade=[([(r, c) for r in range(6) for c in range(6)], YEL, 0.25)]))
# C: corner configuration (A at (0,1),(0,3), B at (1,1),(1,3)), R*C even
I = Instance(12, 12, (0, 1), (0, 3), (1, 1), (1, 3))
assert fires(*I) == "C4", fires(*I)
save("cat_C.svg", grid_svg(12, 12, inst_ends(I), cs=18, title="C: corner configuration",
                           shade=[([(r, c) for r in range(8) for c in range(8)], YEL, 0.25)]))
# R: find a small instance where only R fires
import random
rng = random.Random(5)
found = None
for _ in range(200000):
    R, C = 11, 12
    pts = set()
    while len(pts) < 4:
        cr, cc = rng.choice([0, R - 1]), rng.choice([0, C - 1])
        r = cr + (rng.randint(0, 2) if cr == 0 else -rng.randint(0, 2))
        c = cc + (rng.randint(0, 2) if cc == 0 else -rng.randint(0, 2))
        pts.add((r, c))
    p = list(pts)
    J = Instance(R, C, *p)
    if fires(*J) == "R":
        found = J
        break
I = found
pts = [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]
eff, removed, _ = rewrite_all(I.R, I.C, pts)
walk = walk3(I.R, I.C, removed)
save("cat_R.svg", grid_svg(I.R, I.C, inst_ends(I), cs=20, title="R: forced corner routes",
                           shade=[(removed, GRAY, 0.55)],
                           virtual=[(q[0], "", "A" if q[1] == 0 else "B") for q in eff
                                    if q[0] not in (I.s0, I.t0, I.s1, I.t1)]))
R_EXAMPLE = I

# 4. reductions -----------------------------------------------------------------------------
I = Instance(15, 11, (5, 2), (12, 8), (7, 9), (13, 3))
save("red_S.svg", grid_svg(I.R, I.C, inst_ends(I), cs=16, title="(S) strip: 4 empty edge rows",
                           shade=[([(r, c) for r in range(2) for c in range(I.C)], PUR, 0.35),
                                  ([(r, c) for r in range(2, 4) for c in range(I.C)], PUR, 0.12)]))
I = Instance(24, 11, (2, 2), (20, 8), (3, 9), (21, 3))
save("red_K.svg", grid_svg(I.R, I.C, inst_ends(I), cs=12, title="(K) compression: gap of 10+",
                           shade=[([(r, c) for r in range(4, 20) for c in range(I.C)], PUR, 0.12),
                                  ([(r, c) for r in range(8, 10) for c in range(I.C)], PUR, 0.35)]))
I = Instance(22, 11, (2, 2), (12, 8), (3, 9), (16, 3))
save("red_I.svg", grid_svg(I.R, I.C, inst_ends(I), cs=12, title="(I) interior compression",
                           shade=[([(r, c) for r in range(4, 12) for c in range(I.C)], PUR, 0.12),
                                  ([(r, c) for r in range(8, 10) for c in range(I.C)], PUR, 0.35)]))

# 5. band extension -------------------------------------------------------------------------
Ip = Instance(6, 9, (0, 0), (0, 8), (5, 0), (5, 8))
Sp = solve_paths(6, 9, [(Ip.s0, 0), (Ip.t0, 0), (Ip.s1, 1), (Ip.t1, 1)])
Sp = (Sp[0], Sp[1])
save("band_before.svg", grid_svg(6, 9, inst_ends(Ip), sol_paths(Sp), cuts=[("h", 3)],
                                 title="Before: insert below row 2"))
ext = lift.extend(6, 9, [list(Sp[0]), list(Sp[1])], 0, 3)
Iq = Instance(8, 9, (0, 0), (0, 8), (7, 0), (7, 8))
from zzn.grid import orient
Sq = orient(Iq, ext)
assert check_solution(Iq, Sq)
save("band_after.svg", grid_svg(8, 9, inst_ends(Iq), sol_paths(Sq),
                                shade=[([(r, c) for r in (3, 4) for c in range(9)], PUR, 0.18)],
                                title="After: two rows, every path extended"))

# 6. moves (canonical cut between rows p-1 and p) ---------------------------------------------
def move_fig(name, J, t, m, title, cs=22):
    res = None
    for mm in [m] + list(range(11)):
        res = _Solver().canon(t, mm, J)
        if res is not None:
            break
    if res is None:  # fall back: a random small instance with this move
        rng2 = random.Random(sum(map(ord, name)))
        while res is None:
            pts = set()
            while len(pts) < 4:
                pts.add((rng2.randrange(J.R), rng2.randrange(J.C)))
            J = Instance(J.R, J.C, *list(pts))
            for mm in range(11):
                res = _Solver().canon(t, mm, J)
                if res is not None:
                    break
        print("  ", name, "uses", J)
    sol, p = res
    from zzn.grid import orient as orient_
    sol = orient_(J, sol)
    assert check_solution(J, sol), name
    xs = []
    for col, path in (("A", sol[0]), ("B", sol[1])):
        for i in range(len(path) - 1):
            a, b = path[i], path[i + 1]
            if {a[0], b[0]} == {p - 1, p} and a[1] == b[1]:
                xs += [(a, "", col), (b, "", col)]
    save(name, grid_svg(J.R, J.C, inst_ends(J), sol_paths(sol), cuts=[("h", p)], virtual=xs,
                        title=title, cs=cs))
    return p


move_fig("move_strip.svg", Instance(9, 6, (0, 0), (4, 1), (0, 5), (4, 4)), 0, 5, "Strip")
move_fig("move_13.svg", Instance(9, 6, (1, 1), (7, 4), (5, 0), (8, 4)), 2, 6, "1/3: one endpoint alone")
move_fig("move_cross.svg", Instance(9, 6, (0, 1), (8, 4), (1, 4), (7, 1)), 3, 5, "2/2 cross")
move_fig("move_same.svg", Instance(9, 6, (0, 0), (2, 5), (5, 0), (8, 4)), 1, 0, "2/2 same colour")
move_fig("move_exc.svg", Instance(9, 6, (0, 0), (2, 5), (6, 1), (8, 4)), 4, 6, "Excursion")

# 7. worked example: each stage's solution lifted from the one below it -----------------------
from zzn.grid import orient as orient_w
W0 = Instance(16, 13, (5, 2), (12, 10), (6, 9), (13, 3))
W1 = delete_lines(W0, 0, 0)                                  # strip reduction: rows 0, 1
W2 = Instance(12, 13, (3, 2), (10, 10), (4, 9), (11, 3))      # strip move: rows 12-13 empty
W3 = Instance(12, 11, (3, 2), (10, 10), (4, 9), (11, 3))      # strip move: columns 11-12 empty
tr3 = []
S3 = solve(W3, tr3)
cut3 = tr3[0][3]
tp = lambda paths: [[(c, r) for r, c in p] for p in paths]
S2 = orient_w(W2, tp(lift.add_block(11, 12, tp(S3), 2)))
S1 = orient_w(W1, lift.add_block(12, 13, list(S2), 2))
S0 = orient_w(W0, lift.extend(14, 13, list(S1), 0, 0))
for J, Sx in ((W3, S3), (W2, S2), (W1, S1), (W0, S0)):
    assert check_solution(J, Sx), J
save("ex_0.svg", grid_svg(W0.R, W0.C, inst_ends(W0), cs=18, title="16 x 13 instance", coords=True))
save("ex_1.svg", grid_svg(W0.R, W0.C, inst_ends(W0), cs=18, title="Step 1: strip reduction",
                          shade=[([(r, c) for r in range(2) for c in range(W0.C)], PUR, 0.35),
                                 ([(r, c) for r in range(2, 4) for c in range(W0.C)], PUR, 0.12)]))
save("ex_2.svg", grid_svg(W1.R, W1.C, inst_ends(W1), cs=18, cuts=[("h", 12)],
                          shade=[([(r, c) for r in (12, 13) for c in range(W1.C)], PUR, 0.18)],
                          title="Step 2: 14 x 13, strip move"))
save("ex_3.svg", grid_svg(W2.R, W2.C, inst_ends(W2), cs=18, cuts=[("v", 11)],
                          shade=[([(r, c) for r in range(W2.R) for c in (11, 12)], PUR, 0.18)],
                          title="Step 3: 12 x 13, strip move"))
save("ex_4.svg", grid_svg(W3.R, W3.C, inst_ends(W3), sol_paths(S3), cs=18,
                          cuts=[("h" if cut3[0] == 0 else "v", cut3[1])],
                          title="Step 4: 12 x 11, 2/2 cross"))
save("ex_5.svg", grid_svg(W1.R, W1.C, inst_ends(W1), sol_paths(S1), cs=18,
                          shade=[([(r, c) for r in (12, 13) for c in range(W1.C)] +
                                  [(r, c) for r in range(12) for c in (11, 12)], PUR, 0.15)],
                          title="Step 5: blocks spliced back"))
save("ex_final.svg", grid_svg(W0.R, W0.C, inst_ends(W0), sol_paths(S0), cs=18,
                              shade=[([(r, c) for r in (0, 1) for c in range(W0.C)], PUR, 0.15)],
                              title="Step 6: two rows inserted: solution"))
with open("ex_trace3.txt", "w") as f:
    for step in tr3:
        f.write(repr(step) + "\n")

# 8. plug DP frontier -----------------------------------------------------------------------
I = Instance(5, 8, (0, 0), (0, 7), (4, 0), (4, 7))
S = solve(I)
proc = [(r, c) for c in range(3) for r in range(5)] + [(r, 3) for r in range(3)]
save("plugdp_frontier.svg", grid_svg(5, 8, inst_ends(I), [("A", [x for x in S[0] if x in proc]),
                                                          ("B", [x for x in S[1] if x in proc])],
                                     shade=[(proc, GRAY, 0.25)], marks=[((3, 3), "*")], cs=28,
                                     title="Processed cells (shaded); next cell *"))
print("figures written")
