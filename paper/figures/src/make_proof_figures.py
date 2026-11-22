# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Figures of the paper's proofs: the plug DP frontier, the two separation arguments (border
alternation, crossed square), the local entries, and the three kinds of pair deletion.

    python3 make_proof_figures.py      (writes SVG here and PDF into paper/figures, via Inkscape)

The local-entry panels are drawn from the entry definitions in proof/ZZN/Statement.lean (testL2,
testL3, testL4, testL5, edgeClosure); each panel's endpoints are checked to make the entry fire
in the reference implementation. The deletion panels are checked against the reference
implementation of RedX and RedB (lib/python/zzn/reduce2.py).
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..", "..")
sys.path.insert(0, os.path.join(ROOT, "docs", "figures"))
sys.path.insert(0, os.path.join(ROOT, "lib", "python"))

from fig import COL, LIGHT, grid_svg, inst_ends, sol_paths, save
from zzn import Instance, solve, check_solution, fires
from zzn import reduce2

os.chdir(HERE)
GRAY, PUR, RED = "#9aa0a6", "#7F77DD", "#C0392B"
OUT = []


def out(name, svg):
    save(name + ".svg", svg)
    OUT.append(name)


def head(W, H):
    return [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" '
            f'font-family="Helvetica, Arial, sans-serif">', '<rect width="100%" height="100%" fill="white"/>']


# 1. The plug DP frontier. Rows of the short side (5 cells) are processed top to bottom, each left
# to right. The pieces are the runs of a solution inside the processed cells that are not a whole
# path (ZZN/Thin/Inside.lean, Piece). A plug is an end of a piece that is not an endpoint: the
# path goes on from there into an unprocessed cell. The solution is given by hand and checked.
#
I = Instance(6, 5, (0, 0), (5, 0), (5, 1), (5, 4))
S = ([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 4), (1, 3), (1, 2), (1, 1), (1, 0), (2, 0), (3, 0),
      (4, 0), (5, 0)],
     [(5, 1), (4, 1), (3, 1), (2, 1), (2, 2), (3, 2), (4, 2), (5, 2), (5, 3), (4, 3), (3, 3), (2, 3),
      (2, 4), (3, 4), (4, 4), (5, 4)])
assert check_solution(I, S)
NPROC = 18
proc = [(i // I.C, i % I.C) for i in range(NPROC)]
nxt = (NPROC // I.C, NPROC % I.C)


def runs(path):
    """Maximal runs of `path` inside the processed cells, as (first index, last index)."""
    out_, st = [], None
    for i, v in enumerate(path):
        if v in proc:
            st = i if st is None else st
        elif st is not None:
            out_.append((st, i - 1))
            st = None
    if st is not None:
        out_.append((st, len(path) - 1))
    return [(a, b) for a, b in out_ if not (a == 0 and b == len(path) - 1)]


def frontier_svg(I, S, cs=30):
    m = 6
    R, C = I.R, I.C
    W, H = 2 * m + C * cs, 2 * m + R * cs
    X = lambda c: m + c * cs
    Y = lambda r: m + r * cs
    cx = lambda c: X(c) + cs / 2
    cy = lambda r: Y(r) + cs / 2
    o = head(W, H)
    for r, c in proc:
        o.append(f'<rect x="{X(c)}" y="{Y(r)}" width="{cs}" height="{cs}" fill="{GRAY}" fill-opacity="0.3"/>')
    for r in range(R + 1):
        o.append(f'<line x1="{X(0)}" y1="{Y(r)}" x2="{X(C)}" y2="{Y(r)}" stroke="#c8c8c8" stroke-width="0.6"/>')
    for c in range(C + 1):
        o.append(f'<line x1="{X(c)}" y1="{Y(0)}" x2="{X(c)}" y2="{Y(R)}" stroke="#c8c8c8" stroke-width="0.6"/>')
    o.append(f'<rect x="{X(0)}" y="{Y(0)}" width="{C * cs}" height="{R * cs}" fill="none" stroke="#333" stroke-width="1.4"/>')
    nplug = 0
    for col, path in (("A", S[0]), ("B", S[1])):
        for a, b in runs(path):
            pts = [(cx(c), cy(r)) for r, c in path[a:b + 1]]
            # A plug: the piece goes on into the unprocessed cell next on the path. The stub
            # ends a quarter of a cell past the frontier.
            #
            if a > 0:
                (r0, c0), (r1, c1) = path[a], path[a - 1]
                pts.insert(0, (cx(c0) + 0.75 * cs * (c1 - c0), cy(r0) + 0.75 * cs * (r1 - r0)))
                nplug += 1
            if b < len(path) - 1:
                (r0, c0), (r1, c1) = path[b], path[b + 1]
                pts.append((cx(c0) + 0.75 * cs * (c1 - c0), cy(r0) + 0.75 * cs * (r1 - r0)))
                nplug += 1
            o.append(f'<polyline points="{" ".join(f"{x},{y}" for x, y in pts)}" fill="none" '
                     f'stroke="{COL[col]}" stroke-width="4" stroke-linejoin="round" stroke-linecap="butt"/>')
    # The frontier: below the processed cells of the current row, up its right side, and below
    # the unprocessed cells' upper neighbours in the row above.
    #
    r, c = nxt
    f = [(X(0), Y(r + 1)), (X(c), Y(r + 1)), (X(c), Y(r)), (X(C), Y(r))]
    o.append(f'<polyline points="{" ".join(f"{x},{y}" for x, y in f)}" fill="none" stroke="{PUR}" '
             f'stroke-width="2.6" stroke-dasharray="7 4"/>')
    for v, col in ((I.s0, "A"), (I.t0, "A"), (I.s1, "B"), (I.t1, "B")):
        o.append(f'<circle cx="{cx(v[1])}" cy="{cy(v[0])}" r="{cs * 0.34}" fill="{COL[col]}"/>')
    o.append(f'<text x="{cx(c) + cs * 0.2}" y="{cy(r) + cs * 0.62}" font-size="{int(cs * 0.95)}" font-weight="700" '
             f'fill="#222" text-anchor="middle">*</text>')
    o.append("</svg>")
    return "\n".join(o), nplug


svg, nplug = frontier_svg(I, S)
# The caption states the size, the number of processed cells, the number of pieces and plugs.
#
assert (I.R, I.C, NPROC, nxt) == (6, 5, 18, (3, 3))
assert len(runs(S[0])) == 1 and len(runs(S[1])) == 2 and nplug == 5
out("plugdp_frontier", svg)


# 2. Separation arguments. Cells are lattice points (cell centres); the closed walk is drawn
# through them and filled with the even-odd rule, which marks crossing parity 1.
#
def sep_svg(R, C, A, closing, ends, cs=30, centre=None):
    m = cs
    W, H = 2 * m + C * cs, 2 * m + R * cs
    px = lambda c: m + c * cs + cs / 2
    py = lambda r: m + r * cs + cs / 2
    o = head(W, H)
    poly = A + closing
    pts = " ".join(f"{px(c)},{py(r)}" for r, c in poly)
    o.append(f'<polygon points="{pts}" fill="{LIGHT["A"]}" fill-rule="evenodd" stroke="none"/>')
    for r in range(R + 1):
        o.append(f'<line x1="{m}" y1="{m + r * cs}" x2="{m + C * cs}" y2="{m + r * cs}" stroke="#c8c8c8" stroke-width="0.6"/>')
    for c in range(C + 1):
        o.append(f'<line x1="{m + c * cs}" y1="{m}" x2="{m + c * cs}" y2="{m + R * cs}" stroke="#c8c8c8" stroke-width="0.6"/>')
    o.append(f'<rect x="{m}" y="{m}" width="{C * cs}" height="{R * cs}" fill="none" stroke="#333" stroke-width="1.4"/>')
    a = " ".join(f"{px(c)},{py(r)}" for r, c in A)
    o.append(f'<polyline points="{a}" fill="none" stroke="{COL["A"]}" stroke-width="3.4" stroke-linejoin="round"/>')
    cl = " ".join(f"{px(c)},{py(r)}" for r, c in [A[-1]] + closing + [A[0]])
    o.append(f'<polyline points="{cl}" fill="none" stroke="{COL["A"]}" stroke-width="2.2" '
             f'stroke-dasharray="6 4" stroke-linejoin="round"/>')
    if centre is not None:
        o.append(f'<circle cx="{px(centre[1])}" cy="{py(centre[0])}" r="3" fill="#222"/>')
    rad = cs * 0.36
    for (r, c), lab, col in ends:
        o.append(f'<circle cx="{px(c)}" cy="{py(r)}" r="{rad}" fill="{COL[col]}"/>')
        o.append(f'<text x="{px(c)}" y="{py(r) + 3.8}" font-size="{int(cs * 0.36)}" font-weight="700" '
                 f'fill="white" text-anchor="middle">{lab}</text>')
    o.append("</svg>")
    return "\n".join(o)


# Border alternation: chain A from s0 = (0,2) to t0 = (5,5); the connector runs clockwise on the
# ring outside the grid from the ring point above s0 to the ring point below t0. s1 lies on the
# clockwise arc between them (inside), t1 on the other arc (outside).
#
A = [(0, 2), (1, 2), (2, 2), (2, 3), (3, 3), (4, 3), (4, 4), (4, 5), (5, 5)]
ring = [(6, 5), (6, 6), (6, 7), (6, 8), (5, 8), (4, 8), (3, 8), (2, 8), (1, 8), (0, 8), (-1, 8),
        (-1, 7), (-1, 6), (-1, 5), (-1, 4), (-1, 3), (-1, 2)]
I = Instance(6, 8, A[0], A[-1], (2, 7), (3, 0))
assert fires(*I) == "T1"
out("sep_t1", sep_svg(6, 8, A, ring, inst_ends(I)))

# Crossed square: s0 = (1,1), t0 = (2,2), s1 = (1,2), t1 = (2,1). The walk is closed through the
# midpoint of (2,2)-(2,1), the centre of the square, and the midpoint of (1,1)-(1,2).
#
P = [(1, 1), (0, 1), (0, 2), (0, 3), (1, 3), (2, 3), (2, 2)]
I = Instance(4, 4, P[0], P[-1], (1, 2), (2, 1))
assert fires(*I) == "T2"
out("sep_t2", sep_svg(4, 4, P, [(2, 1.5), (1.5, 1.5), (1, 1.5)], inst_ends(I), centre=(1.5, 1.5)))


# 3. Local entries in the identity frame: the top-left corner of a grid (top and left sides
# thick), the forced path steps, and the cell where the contradiction appears (red cross).
#
def corner_svg(R, C, ends, segs, cross, cs=26):
    m = 10
    W, H = 2 * m + C * cs + 8, 2 * m + R * cs + 8
    X = lambda c: m + c * cs
    Y = lambda r: m + r * cs
    cx = lambda c: X(c) + cs / 2
    cy = lambda r: Y(r) + cs / 2
    o = head(W, H)
    for r in range(R + 1):
        o.append(f'<line x1="{X(0)}" y1="{Y(r)}" x2="{X(C) + 8}" y2="{Y(r)}" stroke="#c8c8c8" stroke-width="0.6"/>')
    for c in range(C + 1):
        o.append(f'<line x1="{X(c)}" y1="{Y(0)}" x2="{X(c)}" y2="{Y(R) + 8}" stroke="#c8c8c8" stroke-width="0.6"/>')
    o.append(f'<polyline points="{X(C) + 8},{Y(0)} {X(0)},{Y(0)} {X(0)},{Y(R) + 8}" fill="none" '
             f'stroke="#333" stroke-width="1.6"/>')
    for col, path in segs:
        pts = " ".join(f"{cx(c)},{cy(r)}" for r, c in path)
        stroke = COL[col] if col in COL else "#555"
        dash = ' stroke-dasharray="5 3"' if col not in COL else ""
        o.append(f'<polyline points="{pts}" fill="none" stroke="{stroke}" stroke-width="3.6" '
                 f'stroke-linejoin="round" stroke-linecap="round"{dash}/>')
    rad = cs * 0.32
    for (r, c), col in ends.items():
        o.append(f'<circle cx="{cx(c)}" cy="{cy(r)}" r="{rad}" fill="{COL[col]}"/>')
    for r, c in cross:
        d = cs * 0.28
        o.append(f'<path d="M{cx(c) - d},{cy(r) - d} L{cx(c) + d},{cy(r) + d} M{cx(c) - d},{cy(r) + d} '
                 f'L{cx(c) + d},{cy(r) - d}" stroke="{RED}" stroke-width="3"/>')
    o.append("</svg>")
    return "\n".join(o)


# Each panel: endpoints (frame cell -> 'A' for colour a, 'B' for the other colour), forced steps,
# crosses. Far cells complete an 11 x 11 or 12 x 12 instance on which the entry is the first to fire in the
# reference implementation (so parity holds and no earlier entry fires).
#
LOCAL = [
    ("local_L2", {(0, 1): "A", (1, 0): "B"}, [("X", [(0, 1), (0, 0), (1, 0)])], [(0, 0)], "L2"),
    ("local_L3", {(0, 2): "A", (1, 1): "A", (1, 0): "B"}, [("B", [(1, 0), (0, 0), (0, 1)])],
     [(0, 1)], "L3"),
    ("local_L4", {(0, 0): "A", (1, 1): "A", (0, 2): "B"}, [("A", [(0, 0), (0, 1), (1, 1)])],
     [(1, 0)], "L4"),
    ("local_L5", {(0, 0): "A", (0, 2): "B", (2, 0): "B"},
     [("A", [(0, 0), (0, 1)]), ("B", [(2, 0), (1, 0), (1, 1)])], [(0, 1)], "L5"),
    ("local_E1", {(0, 1): "A", (1, 2): "A", (1, 3): "B", (0, 4): "B"},
     [("A", [(0, 1), (0, 2), (1, 2)]), ("B", [(1, 3), (0, 3), (0, 4)])], [], "E1"),
]
FAR = lambda n: [(r, c) for r in range(5, n) for c in range(5, n)]


def completes(at, entry):
    need = {"A": 2, "B": 2}
    for col in at.values():
        need[col] -= 1
    if need["A"] + need["B"] == 0:
        cand = lambda n: [[]]
    elif need["A"] + need["B"] == 1:
        col = "A" if need["A"] else "B"
        cand = lambda n: [[(x, col)] for x in FAR(n)]
    else:
        cand = lambda n: [[(x, "A"), (y, "B")] for x in FAR(n) for y in FAR(n) if x != y]
    for n in (11, 12):
        for far in cand(n):
            pts = list(at.items()) + far
            a = [c for c, col in pts if col == "A"]
            b = [c for c, col in pts if col == "B"]
            if fires(n, n, a[0], a[1], b[0], b[1]) == entry:
                return n, far
    raise AssertionError(entry)


for name, at, segs, cross, entry in LOCAL:
    print(name, completes(at, entry))
    out(name, corner_svg(4, 6 if name != "local_E1" else 7, at, segs, cross))


# 4. The three kinds of pair deletion on the x-axis (rows), each on a 13 x 11 grid. Dark: the
# deleted lines d, d + 1. Light: the further free lines the kind requires. Even rows are numbered
# at the left. Each panel is a deletion that only its kind allows, and the distant-endpoint panel
# has exactly one free line next to the pair. The kinds are checked against the reference
# implementation of RedX and RedB (lib/python/zzn/reduce2.py). The interior clause of RedX is
# contained in RedB and is no kind of its own.
#
def strip_at(I, d):
    w = I.R
    return ( (13 <= w) and
             ( ((d == 0) and all(reduce2.free_line(I, k) for k in range(4))) or
               ((d + 2 == w) and all(reduce2.free_line(I, k) for k in range(w - 4, w))) ) )


def gap_runs(I, d):
    w = I.R
    return [lo for lo in range(d + 1)
            if ( (13 <= w) and (d + 1 <= lo + 9) and (lo + 10 <= w) and
                 all(reduce2.free_line(I, lo + j) for j in range(10)) and
                 reduce2.end_below(I, lo) and reduce2.end_above(I, lo + 9) )]


def deletion(name, I, d, light, kind):
    kinds = {"strip": strip_at(I, d), "gap": bool(gap_runs(I, d)), "distant": reduce2.red_b(I, d)}
    assert kinds[kind] and sum(kinds.values()) == 1, (name, kinds)
    assert reduce2.red_x(I, d) == (kinds["strip"] or kinds["gap"]), name
    assert all(reduce2.free_line(I, k) for k in list(light) + [d, d + 1]), name
    # Each panel shows a pair deletion of a passing instance.
    #
    assert not fires(*I), (name, fires(*I))
    if kind == "gap":
        lo = gap_runs(I, d)[0]
        assert sorted(list(light) + [d, d + 1]) == list(range(lo, lo + 10)), name
    if kind == "distant":
        assert [k for k in (d - 1, d + 2) if reduce2.free_line(I, k)] == list(light), name
    rows = lambda rr: [(r, c) for r in rr for c in range(I.C)]
    cs, m, left, fs = 14, 14, 24, 18
    inner = grid_svg(I.R, I.C, inst_ends(I, labels=("", "", "", "")), cs=cs,
                     shade=[(rows(light), PUR, 0.12), (rows((d, d + 1)), PUR, 0.4)])
    W, H = left + 2 * m + I.C * cs, 2 * m + I.R * cs
    o = head(W, H)
    o.append(inner.replace("<svg ", f'<svg x="{left}" y="0" ', 1))
    for r in range(0, I.R, 2):
        o.append(f'<text x="{left + m - 4}" y="{m + r * cs + cs / 2 + fs * 0.36}" font-size="{fs}" '
                 f'fill="#444" text-anchor="end">{r}</text>')
    o.append("</svg>")
    out(name, "\n".join(o))


# Edge strip: lines 0 to 3 free, d = 0.
deletion("del_strip", Instance(13, 11, (5, 2), (12, 8), (7, 9), (9, 3)), 0, range(2, 4), "strip")
# Wide-gap: lines 1 to 10 free (10 lines), endpoints on lines 0, 11 and 12; d = 3 < 5, so the
# deletion is no distant-endpoint compression.
deletion("del_gap", Instance(13, 11, (0, 2), (12, 8), (0, 9), (11, 3)), 3,
         [1, 2] + list(range(5, 11)), "gap")
# Distant-endpoint: d = 5, endpoints on lines 2, 3, 7, 10. Line 4 is free and line 7 is not. The
# longest run of free lines has 3 lines.
deletion("del_distant", Instance(13, 11, (2, 2), (7, 7), (3, 9), (10, 3)), 5, [4], "distant")

for name in OUT:
    subprocess.run(["inkscape", name + ".svg", "--export-type=pdf",
                    "--export-filename=" + os.path.join("..", name + ".pdf")],
                   check=True, capture_output=True)
print("written:", " ".join(OUT))
