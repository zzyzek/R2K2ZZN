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
from zzn import lift, blocks, reduce2, look
from zzn.catalogue import rewrite_all, walk3
from zzn.plugdp import solve_paths

os.chdir(HERE)
GRAY, YEL, PUR = "#9aa0a6", "#F2C94C", "#7F77DD"


def E(cells_labels):
    return cells_labels


# 1. the problem --------------------------------------------------------------------------
I = Instance(4, 4, (0, 0), (0, 3), (1, 0), (1, 3))
S = solve(I)
save("problem.svg", grid_svg(4, 4, inst_ends(I)))
save("solution.svg", grid_svg(4, 4, inst_ends(I), sol_paths(S)))

# 2. parity ---------------------------------------------------------------------------------
I = Instance(4, 5, (0, 0), (2, 4), (1, 1), (3, 2))
save("cat_P.svg", grid_svg(4, 5, inst_ends(I), checker=True, title="P: parity",
                           note="signs +1 +1 +1 -1: sum 2, needs 0"))

# 3. catalogue entries ----------------------------------------------------------------------
cat = {
    "T1": (Instance(11, 11, (0, 0), (10, 10), (0, 5), (10, 0)), "T1, border endpoints alternate"),
    "T2": (Instance(4, 4, (1, 1), (2, 2), (1, 2), (2, 1)), "T2, alternating unit square"),
    "L1": (Instance(4, 5, (0, 0), (3, 3), (0, 1), (1, 0)), "L1, isolated endpoint"),
    "L2": (Instance(4, 5, (0, 1), (3, 3), (1, 0), (2, 4)), "L2, corner block"),
    "L3": (Instance(4, 5, (0, 2), (1, 1), (1, 0), (3, 4)), "L3, corner wedge"),
    "L4": (Instance(4, 5, (0, 0), (1, 1), (0, 2), (3, 4)), "L4, corner fork"),
    "L5": (Instance(4, 5, (0, 0), (3, 4), (0, 2), (2, 0)), "L5, corner trap"),
    "L6": (Instance(4, 6, (0, 1), (1, 0), (0, 4), (1, 5)), "L6, two closed corners"),
    "E1": (Instance(4, 7, (0, 1), (1, 2), (0, 4), (1, 3)), "E1, edge closure"),
}
for name, (inst, title) in cat.items():
    f = fires(inst.R, inst.C, inst.s0, inst.t0, inst.s1, inst.t1)
    assert f is not None, (name, inst)
    assert name != "T1" or f == "T1", (name, f)
    marks = [((0, 0), "?")] if name in ("L2", "L3", "L5") else []
    kw = {"cs": 18} if inst.R > 6 else {}
    save(f"cat_{name}.svg", grid_svg(inst.R, inst.C, inst_ends(inst), marks=marks, title=title, **kw))

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
save("cat_R.svg", grid_svg(I.R, I.C, inst_ends(I), cs=20, title="R, forced corner routes",
                           shade=[(removed, GRAY, 0.55)],
                           virtual=[(q[0], "", "A" if q[1] == 0 else "B") for q in eff
                                    if q[0] not in (I.s0, I.t0, I.s1, I.t1)]))
R_EXAMPLE = I

# 4. reductions -----------------------------------------------------------------------------
# Each figure shows lines d, d + 1 (dark) satisfying one clause of RedX (reduce2.red_x).
I = Instance(15, 11, (5, 2), (12, 8), (7, 9), (13, 3))
assert reduce2.red_x(I, 0) and reduce2.find_red2(I) == 0
save("red_S.svg", grid_svg(I.R, I.C, inst_ends(I), cs=16, title="RedX strip: rows 0-1",
                           shade=[([(r, c) for r in range(2) for c in range(I.C)], PUR, 0.35),
                                  ([(r, c) for r in range(2, 4) for c in range(I.C)], PUR, 0.12)]))
I = Instance(24, 11, (2, 2), (20, 8), (3, 9), (21, 3))
assert reduce2.red_x(I, 8)
save("red_K.svg", grid_svg(I.R, I.C, inst_ends(I), cs=12, title="RedX compression: rows 8-9",
                           shade=[([(r, c) for r in range(4, 20) for c in range(I.C)], PUR, 0.12),
                                  ([(r, c) for r in range(8, 10) for c in range(I.C)], PUR, 0.35)]))
I = Instance(22, 11, (2, 2), (12, 8), (3, 9), (16, 3))
assert reduce2.red_x(I, 8)
save("red_I.svg", grid_svg(I.R, I.C, inst_ends(I), cs=12, title="RedX interior: rows 8-9",
                           shade=[([(r, c) for r in range(4, 12) for c in range(I.C)], PUR, 0.12),
                                  ([(r, c) for r in range(8, 10) for c in range(I.C)], PUR, 0.35)]))

# 5. band extension (reduce2.band_ext, the Lean `bandExtE`) ----------------------------------
Ip = Instance(6, 9, (0, 0), (0, 8), (5, 0), (5, 8))
Sp = solve_paths(6, 9, [(Ip.s0, 0), (Ip.t0, 0), (Ip.s1, 1), (Ip.t1, 1)])
Sp = (list(Sp[0]), list(Sp[1]))
save("band_before.svg", grid_svg(6, 9, inst_ends(Ip), sol_paths(Sp), cuts=[("h", 3)]))
Iq = Instance(8, 9, (0, 0), (0, 8), (7, 0), (7, 8))
Sq = reduce2.band_ext(Ip, 2, Sp[0], Sp[1])
assert check_solution(Iq, Sq)
save("band_after.svg", grid_svg(8, 9, inst_ends(Iq), sol_paths(Sq),
                                shade=[([(r, c) for r in (3, 4) for c in range(9)], PUR, 0.18)]))
I = Instance(15, 11, (2, 2), (10, 8), (3, 9), (11, 3))
assert reduce2.find_red2(I) == 5 and not any(reduce2.red_x(I, d) for d in range(I.R))
save("red_B.svg", grid_svg(I.R, I.C, inst_ends(I), cs=14, title="RedB: rows 5-6 of a 6-row gap",
                           shade=[([(r, c) for r in range(4, 10) for c in range(I.C)], PUR, 0.12),
                                  ([(r, c) for r in (5, 6) for c in range(I.C)], PUR, 0.35)]))

# 5b. block lifts (blocks.py, the Lean `Blk.lift`) -------------------------------------------
Jb = Instance(6, 9, (0, 0), (0, 8), (5, 0), (5, 8))
Sb = solve_paths(6, 9, [(Jb.s0, 0), (Jb.t0, 0), (Jb.s1, 1), (Jb.t1, 1)])
Sb = (list(Sb[0]), list(Sb[1]))
step = next((L[j], L[j + 1]) for L in Sb for j in range(len(L) - 1)
            if L[j][0] == 5 and L[j + 1][0] == 5)
# The step starts at the endpoint s1, whose label marks that cell. The star marks the other cell.
# The caption in the paper names the step this way.
#
assert step[0] == Jb.s1
save("blk_edge_before.svg", grid_svg(6, 9, inst_ends(Jb), sol_paths(Sb), marks=[(step[1], "*")]))
Ib = Instance(10, 9, (0, 0), (0, 8), (5, 0), (5, 8))
Se = blocks.lift(("right", 2), Jb, Sb[0], Sb[1])
assert check_solution(Ib, Se)
save("blk_edge_after.svg", grid_svg(10, 9, inst_ends(Ib), sol_paths(Se),
                                    shade=[([(r, c) for r in range(6, 10) for c in range(9)], PUR, 0.18)]))
r0 = 2
save("blk_inner_before.svg", grid_svg(6, 9, inst_ends(Jb), sol_paths(Sb), cuts=[("h", r0 + 1)]))
Ii = Instance(10, 9, (0, 0), (0, 8), (9, 0), (9, 8))
Si = blocks.lift(("inner", r0, 2), Jb, Sb[0], Sb[1])
assert check_solution(Ii, Si)
save("blk_inner_after.svg", grid_svg(10, 9, inst_ends(Ii), sol_paths(Si),
                                     shade=[([(r, c) for r in range(r0 + 1, r0 + 5) for c in range(9)],
                                             PUR, 0.18)]))

# 6. the leaf lookup: a template's cuts on a symmetric copy of the canonical leaf ---------------
def cut_segments(T, P):
    """The cut segments of an instantiated template T on piece P (as look.check walks it)."""
    if T is None:
        return []
    vert, pos, ks, left, right = T
    ox, oy, pw, ph, _ = P
    seg = (ox, pos, ox + pw, pos) if vert else (pos, oy, pos, oy + ph)
    L, R = look.split(vert, pos, ks, P[4], ([], []))
    return ([seg] + cut_segments(left, look.piece_lo(P, vert, pos, L)) +
            cut_segments(right, look.piece_hi(P, vert, pos, R)))


def lookup_fig(name, L, title):
    sigma = look.canon_sym(L)
    K = look.apply_sym(sigma, L)
    tr = {}
    assert look.look_k(K, tr) is not None and tr["entry"][0] == "pair"
    d = look.tab_all(K.R, K.C)[tr["slice"]]
    i = tr["entry"][1]
    T, tau = look.template(d[1][2 * i]), look.sym_of_int(d[1][2 * i + 1])
    J = look.apply_sym(tau, K)
    S = look.tsol(T, J)
    assert check_solution(J, S)
    segs = cut_segments(look.inst_of(T, J), look.root_piece(J))
    save(name, grid_svg(J.R, J.C, inst_ends(J), sol_paths(S), segs=segs, cs=18, title=title))
    return J


# 7. worked example: the instance, its blocks and reductions, the leaf, the solution ----------
W0 = Instance(16, 13, (5, 2), (12, 10), (6, 9), (13, 3))
tr0 = []
S0 = solve(W0, tr0)
assert [st[0] for st in tr0] == ["block", "reduce", "reduce", "leaf"], tr0
B, bsteps = blocks.plan(W0)
assert bsteps[0][0] == ("left", 1)
L, rsteps = reduce2.plan2(B)
name = lambda P, d: "RedX" if reduce2.red_x(P, d) else "RedB"
(P1, d1, t1), (P2, d2, t2) = rsteps
assert (d1, t1, d2, t2) == (5, False, 5, True)
save("ex_0.svg", grid_svg(W0.R, W0.C, inst_ends(W0), cs=18, title="16 x 13 instance", coords=True))
save("ex_1.svg", grid_svg(W0.R, W0.C, inst_ends(W0), cs=18, title="Step 1: left block, rows 0-1",
                          shade=[([(r, c) for r in range(2) for c in range(W0.C)], PUR, 0.35)]))
save("ex_2.svg", grid_svg(B.R, B.C, inst_ends(B), cs=18, title=f"Step 2: {name(P1, d1)}, rows 5-6",
                          shade=[([(r, c) for r in (5, 6) for c in range(B.C)], PUR, 0.35)]))
B2 = reduce2.delete_at(B, 5)
save("ex_3.svg", grid_svg(B2.R, B2.C, inst_ends(B2), cs=18, title=f"Step 3: {name(P2, d2)}, columns 5-6",
                          shade=[([(r, c) for r in range(B2.R) for c in (5, 6)], PUR, 0.35)]))
SL = look.look_j(L)
assert check_solution(L, SL)
LT = reduce2.transpose(L)
SLT = tuple([(c, r) for r, c in p] for p in SL)
save("ex_4.svg", grid_svg(LT.R, LT.C, inst_ends(LT), sol_paths(SLT), cs=18,
                          title=f"{LT.R} x {LT.C} leaf solved from the table"))
lookup_fig("ex_look.svg", L, "A template, on a symmetric copy")
# The deleted lines, in the coordinates of the 16 x 13 grid: the top block (rows 0, 1), the
# pair d1, d1 + 1 of the instance without the block (two rows further down), and the columns
# d2, d2 + 1, which no earlier deletion moves.
#
ex_rows = [0, 1, d1 + 2, d1 + 3]
ex_cols = [d2, d2 + 1]
save("ex_final.svg", grid_svg(W0.R, W0.C, inst_ends(W0), sol_paths(S0), cs=18,
                              shade=[([(r, c) for r in range(W0.R) for c in range(W0.C)
                                       if (r in ex_rows) or (c in ex_cols)], PUR, 0.3)]))

# One stored template on two instances: the template of the example's leaf, and the same
# instance with t0 moved two columns right. Cuts anchored on t0's column move with it.
def tsegs(Ti, P):
    if Ti is None:
        return []
    vert, pos, ks, l, r = Ti
    ox, oy, pw, ph, _ = P
    s = (ox, pos, ox + pw, pos) if vert else (pos, oy, pos, oy + ph)
    Lp, Rp = look.split(vert, pos, ks, P[4], ([], []))
    return [s] + tsegs(l, look.piece_lo(P, vert, pos, Lp)) + tsegs(r, look.piece_hi(P, vert, pos, Rp))
Kc = look.apply_sym(look.canon_sym(L), L)
trc = {}
look.look_k(Kc, trc)
dc = look.tab_all(Kc.R, Kc.C)[trc["slice"]]
ic = trc["entry"][1]
Tc, tauc = look.template(dc[1][2 * ic]), look.sym_of_int(dc[1][2 * ic + 1])
J1 = look.apply_sym(tauc, Kc)
J2 = Instance(J1.R, J1.C, J1.s0, (3, 9), J1.s1, J1.t1)
for J, fn in ((J1, "template_same_a.svg"), (J2, "template_same_b.svg")):
    assert look.tcheck(Tc, J)
    S = look.tsol(Tc, J)
    assert check_solution(J, S)
    save(fn, grid_svg(J.R, J.C, inst_ends(J), sol_paths(S),
                      segs=tsegs(look.inst_of(Tc, J), look.root_piece(J)), cs=24))

# 8. plug DP frontier -----------------------------------------------------------------------
I = Instance(5, 8, (0, 0), (0, 7), (4, 0), (4, 7))
S = solve(I)
proc = [(r, c) for c in range(3) for r in range(5)] + [(r, 3) for r in range(3)]
save("plugdp_frontier.svg", grid_svg(5, 8, inst_ends(I), [("A", [x for x in S[0] if x in proc]),
                                                          ("B", [x for x in S[1] if x in proc])],
                                     shade=[(proc, GRAY, 0.25)], marks=[((3, 3), "*")], cs=28,
                                     title="Processed cells (shaded); next cell *"))
print("figures written")
