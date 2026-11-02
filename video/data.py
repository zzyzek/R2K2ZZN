# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Instances and solutions shown in the video, all computed by the library in lib/python.

Every solution is checked with check_solution and every catalogue example with fires, so the
video shows only what the solver actually produces.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "lib", "python"))

from zzn import Instance, solve, check_solution, fires, hamiltonian_path, acceptable  # noqa: E402
from zzn import lift  # noqa: E402
from zzn.solver import _Solver, delete_lines  # noqa: E402
from zzn.grid import orient  # noqa: E402
from zzn.catalogue import rewrite_all  # noqa: E402
from zzn.plugdp import solve_paths  # noqa: E402


def ends(I):
    """[(cell, label, colour)] for the four endpoints."""
    return [(I.s0, "s_0", "A"), (I.t0, "t_0", "A"), (I.s1, "s_1", "B"), (I.t1, "t_1", "B")]


def plug(I):
    """The plug DP's solution of I, oriented s -> t."""
    d = solve_paths(I.R, I.C, [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)])
    S = orient(I, (d[0], d[1]))
    assert check_solution(I, S), I
    return [list(S[0]), list(S[1])]


def solved(I):
    S = solve(I)
    assert check_solution(I, S), I
    return [list(S[0]), list(S[1])]


# 1. The problem ------------------------------------------------------------------------------
PROBLEM = Instance(6, 8, (1, 1), (4, 6), (4, 1), (1, 6))
PROBLEM_SOL = solved(PROBLEM)

# One path only: the Hamiltonian path problem of Itai, Papadimitriou and Szwarcfiter.
IPS_YES_PATH = hamiltonian_path(5, 7, (0, 0), (4, 6))
assert acceptable(5, 7, (0, 0), (4, 6))
assert not acceptable(5, 7, (0, 0), (0, 1))

# 2. Catalogue examples (as in docs/figures/make_figures.py) -----------------------------------
PARITY = Instance(4, 5, (0, 0), (2, 4), (1, 1), (3, 2))
assert fires(*PARITY) == "P"
CATALOGUE = [
    ("T1", Instance(6, 7, (0, 0), (5, 6), (0, 6), (5, 0)),
     "All four endpoints on the border, colours alternating around it.\n"
     "Green's path would cut orange's endpoints apart."),
    ("T2", Instance(4, 4, (1, 1), (2, 2), (1, 2), (2, 1)),
     "The endpoints fill a 2\u00d72 square, each colour on a diagonal."),
    ("L1", Instance(5, 6, (0, 0), (2, 2), (0, 1), (1, 0)),
     "An endpoint whose neighbours are all endpoints of the other colour."),
    ("L2", Instance(5, 6, (0, 1), (2, 2), (1, 0), (2, 4)),
     "The empty corner cell has two neighbours, both endpoints of different colours:\n"
     "covering it would join green to orange."),
    ("L3", Instance(4, 5, (0, 2), (1, 1), (1, 0), (3, 4)), "Corner wedge."),
    ("L4", Instance(5, 7, (0, 0), (1, 1), (0, 2), (2, 3)), "Corner fork."),
    ("L5", Instance(5, 7, (0, 0), (2, 3), (0, 2), (2, 0)), "Corner trap."),
    ("L6", Instance(4, 6, (0, 1), (1, 0), (0, 4), (1, 5)), "A closed corner of each colour."),
    ("E1", Instance(4, 7, (0, 1), (1, 2), (0, 4), (1, 3)), "Edge closure."),
]
for name, I, _ in CATALOGUE:
    assert fires(*I) == name, (name, fires(*I))
# The empty corner cell that L2, L3 and L5 make impossible to cover.
CATALOGUE_MARK = {"L2": (0, 0), "L3": (0, 0), "L5": (0, 0)}

CAT_B = Instance(12, 12, (0, 0), (1, 1), (1, 2), (11, 8))
assert fires(*CAT_B) == "B"
CAT_C = Instance(12, 12, (0, 1), (0, 3), (1, 1), (1, 3))
assert fires(*CAT_C) == "C4"


def _find_r():
    """A small instance on which R fires (the search of make_figures.py)."""
    import random
    rng = random.Random(5)
    for _ in range(200000):
        R, C = 11, 12
        pts = set()
        while len(pts) < 4:
            cr, cc = rng.choice([0, R - 1]), rng.choice([0, C - 1])
            r = cr + (rng.randint(0, 2) if cr == 0 else -rng.randint(0, 2))
            c = cc + (rng.randint(0, 2) if cc == 0 else -rng.randint(0, 2))
            pts.add((r, c))
        J = Instance(R, C, *list(pts))
        if fires(*J) == "R":
            return J
    raise RuntimeError("no R example")


CAT_R = _find_r()
_eff, CAT_R_SETTLED, _ = rewrite_all(CAT_R.R, CAT_R.C, [(CAT_R.s0, 0), (CAT_R.t0, 0),
                                                       (CAT_R.s1, 1), (CAT_R.t1, 1)])
CAT_R_EFFECTIVE = [(q[0], "A" if q[1] == 0 else "B") for q in _eff
                   if q[0] not in (CAT_R.s0, CAT_R.t0, CAT_R.s1, CAT_R.t1)]

# 3. Plug DP sweep ----------------------------------------------------------------------------
PLUG = Instance(5, 8, (2, 2), (2, 6), (4, 1), (2, 7))
PLUG_SOL = plug(PLUG)

# 4. Reductions and band extension ------------------------------------------------------------
RED_S = Instance(15, 11, (5, 2), (12, 8), (7, 9), (13, 3))
RED_K = Instance(24, 11, (2, 2), (20, 8), (3, 9), (21, 3))


def band_steps(R, C, paths, r):
    """lift._band_rows with a snapshot of the paths after each step: [stretched, detoured,
    flipped]. Also returns the crossing columns and the flipped edge."""
    _splice, block_cycle, _flip_path = lift._splice, lift.block_cycle, lift._flip_path
    shift = lambda x: x if x[0] <= r else (x[0] + 2, x[1])
    paths = [[shift(x) for x in p] for p in paths]
    n1, n2 = r + 1, r + 2
    xs = []
    for p in paths:
        for i in range(len(p) - 1):
            a, b = p[i], p[i + 1]
            if a[1] == b[1] and {a[0], b[0]} == {r, r + 3}:
                xs.append(a[1])
    xs.sort()
    shifted = [list(p) for p in paths]
    for c in xs:
        _splice(paths, (r, c), (r + 3, c), [(n1, c), (n2, c)])
    stretched = [list(p) for p in paths]
    bounds = [-1] + xs + [C]
    runs = [(bounds[i] + 1, bounds[i + 1] - 1) for i in range(len(bounds) - 1)]
    horiz = set()
    for p in paths:
        for i in range(len(p) - 1):
            a, b = p[i], p[i + 1]
            if a[0] == b[0] == r and abs(a[1] - b[1]) == 1:
                horiz.add(min(a[1], b[1]))
    j = next((i for i, (lo, hi) in enumerate(runs) if lo > hi), None)
    if j is None:
        j = next(i for i, (lo, hi) in enumerate(runs) if any(lo <= a < hi for a in horiz))
    for i, c in enumerate(xs, start=1):
        lo, hi = runs[i - 1] if i <= j else runs[i]
        if lo > hi:
            continue
        if i <= j:
            mid = [(n1, y) for y in range(c - 1, lo - 1, -1)] + [(n2, y) for y in range(lo, c)]
        else:
            mid = [(n1, y) for y in range(c + 1, hi + 1)] + [(n2, y) for y in range(hi, c, -1)]
        _splice(paths, (n1, c), (n2, c), mid)
    detoured = [list(p) for p in paths]
    lo, hi = runs[j]
    flip = None
    block = []
    if lo <= hi:
        a = next(a for a in sorted(horiz) if lo <= a < hi)
        block = [(n1 + i, lo + y) for i, y in block_cycle(2, hi - lo + 1)]
        _splice(paths, (r, a), (r, a + 1), _flip_path(block, a - lo))
        flip = ((r, a), (r, a + 1))
    return dict(shifted=shifted, stretched=stretched, detoured=detoured, final=paths,
                xs=xs, flip=flip, block=block)


# 5. Moves (canonical: horizontal cut between rows p-1 and p) ---------------------------------
MOVE_TYPES = {"strip": 0, "2/2 same": 1, "1/3": 2, "2/2 cross": 3, "excursion": 4}


def move(J, t, m, fig):
    """A canonical move of type t on J, or, failing that, on the random instance that
    make_figures.py draws for the figure `fig` (same seed, same instance)."""
    import random
    sv = _Solver()
    res = None
    for mm in [m] + list(range(11)):
        res = sv.canon(t, mm, J)
        if res is not None:
            break
    if res is None:
        rng = random.Random(sum(map(ord, fig)))
        while res is None:
            pts = set()
            while len(pts) < 4:
                pts.add((rng.randrange(J.R), rng.randrange(J.C)))
            J = Instance(J.R, J.C, *list(pts))
            for mm in range(11):
                res = sv.canon(t, mm, J)
                if res is not None:
                    break
    sol, p = res
    sol = orient(J, sol)
    assert check_solution(J, sol)
    return J, [list(sol[0]), list(sol[1])], p


MOVES = [
    ("Strip", "move_strip.svg", Instance(9, 6, (0, 0), (4, 1), (0, 5), (4, 4)), 0, 5,
     "If all four endpoints are on one side, with the other side empty, a strip operation is performed"),
    ("1/3", "move_13.svg", Instance(9, 6, (1, 1), (7, 4), (5, 0), (8, 4)), 2, 6,
     "If one endpoint is alone on its side, a single Hamiltonian path gives a solution from that endpoint to the crossing"),
    ("2/2 cross", "move_cross.svg", Instance(9, 6, (0, 1), (8, 4), (1, 4), (7, 1)), 3, 5,
     "If one endpoint of each colour is on each side, the two paths must cross at the cut"),
    ("2/2 same", "move_same.svg", Instance(9, 6, (0, 0), (2, 5), (5, 0), (8, 4)), 1, 0,
     "If each pair lands on its own side, each can be solved as a single Hamiltonian path problem, with no crossing"),
    ("Excursion", "move_exc.svg", Instance(9, 6, (0, 0), (2, 5), (6, 1), (8, 4)), 4, 6,
     "Rarely, none of the simpler moves works, and one path makes an excursion, dipping into the far side and coming back"),
]
MOVES = [(name, *move(J, t, m, fig), note) for name, fig, J, t, m, note in MOVES]

# Band extension shown on the 2/2 cross solution: two rows inserted below row 3 meet two
# crossings, two U-detours and one square flip.
#
_, BAND_BEFORE, BAND_BEFORE_SOL, _, _ = MOVES[2]
BAND_ROW = 3
_sh2 = lambda x: x if x[0] <= BAND_ROW else (x[0] + 2, x[1])
BAND_AFTER = Instance(BAND_BEFORE.R + 2, BAND_BEFORE.C, *[_sh2(x) for x in BAND_BEFORE[2:]])
BAND = band_steps(BAND_BEFORE.R, BAND_BEFORE.C, BAND_BEFORE_SOL, BAND_ROW)
assert check_solution(BAND_AFTER, BAND["final"])
assert BAND["final"] == lift.extend(BAND_BEFORE.R, BAND_BEFORE.C, BAND_BEFORE_SOL, 0, BAND_ROW + 1)
assert BAND["flip"] is not None and len(BAND["xs"]) == 2


def strip_parts(J, p):
    """For a strip move at row p: the near piece's own solution, the far block's Hamiltonian
    cycle, the column a of the flipped edge pair, and the glued solution (as lift.add_block)."""
    L = Instance(p, J.C, J.s0, J.t0, J.s1, J.t1)
    near = solved(L)
    cyc = [(p + i, y) for i, y in lift.block_cycle(J.R - p, J.C)]
    a = None
    for q in near:
        for i in range(len(q) - 1):
            x, y = q[i], q[i + 1]
            if x[0] == y[0] == p - 1 and abs(x[1] - y[1]) == 1:
                a = min(x[1], y[1])
                break
        if a is not None:
            break
    glued = lift.add_block(p, J.C, near, J.R - p)
    assert check_solution(J, glued)
    return near, cyc, a, glued


# 6. Worked example (as in make_figures.py and docs/ALGORITHM.md section 8) -------------------
W0 = Instance(16, 13, (5, 2), (12, 10), (6, 9), (13, 3))
W1 = delete_lines(W0, 0, 0)
W2 = Instance(12, 13, (3, 2), (10, 10), (4, 9), (11, 3))
W3 = Instance(12, 11, (3, 2), (10, 10), (4, 9), (11, 3))
_tr3 = []
S3 = solve(W3, _tr3)
CUT3 = _tr3[0][3]
assert _tr3[0][2] == "2/2 cross", _tr3
_tp = lambda paths: [[(c, r) for r, c in p] for p in paths]
S2 = orient(W2, _tp(lift.add_block(11, 12, _tp(S3), 2)))
S1 = orient(W1, lift.add_block(12, 13, list(S2), 2))
S0 = orient(W0, lift.extend(14, 13, list(S1), 0, 0))
for _J, _S in ((W3, S3), (W2, S2), (W1, S1), (W0, S0)):
    assert check_solution(_J, _S), _J
S0, S1, S2, S3 = ([list(q) for q in S] for S in (S0, S1, S2, S3))
assert solved(W0) is not None
W_TRACE = []
solve(W0, W_TRACE)


if __name__ == "__main__":
    print("problem", PROBLEM, "R example", CAT_R)
    for name, J, sol, p, _ in MOVES:
        print(name, J, "cut", p)
    print("band crossings", BAND["xs"], "flip", BAND["flip"])
    print("W3 cut", CUT3)
    for step in W_TRACE:
        print(" ", step[0], step[1:])


# 7. Additions for the second draft -----------------------------------------------------------

# Five pairs (general Zig-Zag Numberlink): a Hamiltonian path of the 7 x 9 grid cut into five
# pieces; each piece's two ends are a pair.
#
_H = hamiltonian_path(7, 9, (0, 0), (6, 8))
_cuts = [0, 11, 24, 37, 50, 63]
KPAIRS = [(_H[_cuts[i]], _H[_cuts[i + 1] - 1], i) for i in range(5)]
KPAIRS_PATHS = [_H[_cuts[i]:_cuts[i + 1]] for i in range(5)]

# The IPS rejections: one per rule, each colour compatible except the first.
#
from zzn.ips import color_compatible  # noqa: E402
IPS_NO = [
    ("colours", 5, 7, (0, 0), (4, 1)),
    ("width 1", 1, 7, (0, 0), (0, 2)),
    ("width 2", 2, 7, (0, 1), (1, 1)),
    ("width 3", 3, 6, (0, 1), (0, 4)),
]
for _n, _R, _C, _s, _t in IPS_NO:
    assert not acceptable(_R, _C, _s, _t)
    assert (_n == "colours") != color_compatible(_R, _C, _s, _t)


def sym_rotate(I):
    """Quarter turn clockwise: (r, c) -> (c, R-1-r) in a C x R grid."""
    f = lambda x: (x[1], I.R - 1 - x[0])
    return Instance(I.C, I.R, *[f(x) for x in I[2:]])


def sym_mirror(I):
    f = lambda x: (x[0], I.C - 1 - x[1])
    return Instance(I.R, I.C, *[f(x) for x in I[2:]])


def sym_swap(I):
    return Instance(I.R, I.C, I.s1, I.t1, I.s0, I.t0)


SYM_BASE = CATALOGUE[3][1]
SYMS = [("rotated", sym_rotate(SYM_BASE)), ("mirrored", sym_mirror(SYM_BASE)),
        ("colours swapped", sym_swap(SYM_BASE))]
for _n, _J in SYMS:
    assert fires(*_J) == "L2", (_n, fires(*_J))

# T1 and T2: a green path, and orange attempts that run into it (the last cell is the collision).
#
T1_I = CATALOGUE[0][1]
T1_GREEN = [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (3, 4), (4, 4), (4, 5),
            (5, 5), (5, 6)]
T1_TRIES = [[(0, 6), (1, 6), (2, 6), (2, 5), (3, 5), (3, 4)],
            [(0, 6), (0, 5), (0, 4), (0, 3), (0, 2), (1, 2)],
            [(0, 6), (1, 6), (2, 6), (3, 6), (4, 6), (4, 5)]]
T2_I = Instance(6, 6, (2, 2), (3, 3), (2, 3), (3, 2))
assert fires(*T2_I) == "T2"
T2_GREEN = [(2, 2), (2, 1), (3, 1), (4, 1), (4, 2), (4, 3), (3, 3)]
T2_TRIES = [[(2, 3), (1, 3), (1, 2), (1, 1), (1, 0), (2, 0), (3, 0), (3, 1)],
            [(2, 3), (2, 4), (3, 4), (4, 4), (5, 4), (5, 3), (4, 3)]]
for _I, _g, _tries in ((T1_I, T1_GREEN, T1_TRIES), (T2_I, T2_GREEN, T2_TRIES)):
    assert _g[0] == _I.s0 and _g[-1] == _I.t0
    for _p in _tries:
        assert _p[0] == _I.s1 and _p[-1] in _g and not set(_p[:-1]) & set(_g)
        assert all(abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1 for a, b in zip(_p, _p[1:]))

# B, C and D: the lists themselves, and one instance of each.
#
from zzn.catalogue import BOUNDARY3_EVEN, BOUNDARY3_ODD, CORNER4, CORNER4_ODD  # noqa: E402
B_LIST = [(e, "even") for e in BOUNDARY3_EVEN] + [(e, "odd") for e in BOUNDARY3_ODD]
C_LIST = list(CORNER4)
D_LIST = list(CORNER4_ODD)
CAT_D = Instance(11, 11, (0, 0), (0, 1), (1, 1), (2, 0))
assert fires(*CAT_D) == "C4"


def r_routes(I):
    """The forced corner routes of R: for each moved endpoint, the cells from it to its new
    position, through the settled cells (a disjoint cover of them, found by search)."""
    pts = [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]
    eff, settled, _ = rewrite_all(I.R, I.C, pts)
    moves = [(a[0], b[0], a[1]) for a, b in zip(pts, eff) if a[0] != b[0]]
    S = set(settled)
    adj = lambda x, y: abs(x[0] - y[0]) + abs(x[1] - y[1]) == 1

    def go(i, used):
        if i == len(moves):
            return [] if used == S else None
        a, b, col = moves[i]

        def walk(p, used):
            x = p[-1]
            if adj(x, b):
                rest = go(i + 1, used)
                if rest is not None:
                    return [(p + [b], col)] + rest
            for y in S - used:
                if adj(x, y):
                    r = walk(p + [y], used | {y})
                    if r is not None:
                        return r
            return None
        return walk([a], used | {a})
    routes = go(0, set())
    assert routes is not None
    return routes, settled


R_ROUTES, R_SETTLED = r_routes(CAT_R)
