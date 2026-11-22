# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The three forced-route rules and the bypass walk (paper Figure "Forced corner routes").

The rules and the staircase are transcribed from `rewritesAt` and `staircase` in
proof/ZZN/Statement.lean. Each panel shows the top-left corner of an 11 x 11 grid in the identity
frame. The script checks the transcription against the walk `walk3` of the reference
implementation (lib/python/zzn/catalogue.py) on an 11 x 11 instance with the panel's endpoints.

        python3 make_forced_figures.py      (writes SVG here and PDF into paper/figures, via Inkscape)
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..", "..")
sys.path.insert(0, os.path.join(ROOT, "docs", "figures"))
sys.path.insert(0, os.path.join(ROOT, "lib", "python"))

from fig import COL, save
from zzn.catalogue import rewrite_all, walk3

os.chdir(HERE)
GRAY = "#9aa0a6"
WALK = "#3b5bdb"


# rewritesAt (Statement.lean), on a view given as a dict cell -> colour, with H, W >= 4.
# Returns (settled cells, moves) or None.
#
def rewrites_at(at):
    e = lambda r, c: at.get((r, c))
    empty = lambda cells: all(e(*x) is None for x in cells)
    if ( (e(1, 2) is not None) and (e(2, 1) is not None) and (e(1, 2) != e(2, 1)) and
              empty([(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)]) ):
        return ([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (1, 2), (2, 1)],
                        [((1, 2), (0, 3)), ((2, 1), (3, 0))])
    if ( (e(0, 0) is not None) and (e(1, 1) == e(0, 0)) and
              empty([(0, 1), (1, 0), (0, 2), (2, 0)]) ):
        return ([(0, 0), (0, 1), (1, 0), (1, 1)], [((0, 0), (0, 2)), ((1, 1), (2, 0))])
    if (e(0, 1) is not None) and empty([(0, 0), (1, 0)]):
        return ([(0, 0), (0, 1)], [((0, 1), (1, 0))])
    return None


# staircase and notchLen (Statement.lean), identity frame.
#
def staircase(removed):
    lam = lambda i: sum(1 for j in range(4) if (i, j) in removed)
    k = sum(1 for i in range(4) if lam(i) > 0)
    out = [(k, 0)]
    for i in reversed(range(k)):
        out += [(i + 1, lam(i + 1) + 1 + j) for j in range(max(0, lam(i) - lam(i + 1)))]
        out.append((i, lam(i)))
    return out


# Panels: the endpoints at the corner (cell -> colour 0 or 1) and the far endpoints that complete
# an 11 x 11 instance for the cross-check.
#
N = 11
PANELS = [
    ("forced_r1", "Corner turn", {(0, 1): 0}, [((10, 10), 0), ((10, 5), 1), ((5, 10), 1)]),
    ("forced_r2", "Diagonal pair", {(0, 0): 0, (1, 1): 0}, [((10, 5), 1), ((5, 10), 1)]),
    ("forced_r3", "Staircase pair", {(1, 2): 0, (2, 1): 1}, [((10, 10), 0), ((10, 5), 1)]),
]
EXPECT = {
    "forced_r1": [(1, 0), (1, 1), (1, 2), (0, 2)],
    "forced_r2": [(2, 0), (2, 1), (2, 2), (1, 2), (0, 2)],
    "forced_r3": [(3, 0), (3, 1), (3, 2), (2, 2), (2, 3), (1, 3), (0, 3)],
}

S = 6
CS = 30
M = 16


# The panels carry no title. What each panel shows is said in the caption of the figure.
#
def panel_svg(at, removed, moves, stair):
    top = M
    W = 2 * M + S * CS + 10
    H = top + S * CS + M
    X = lambda c: M + c * CS
    Y = lambda r: top + r * CS
    cx = lambda c: X(c) + CS / 2
    cy = lambda r: Y(r) + CS / 2
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" '
              f'font-family="Helvetica, Arial, sans-serif">', '<rect width="100%" height="100%" fill="white"/>',
              '<defs><marker id="ar" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="5" markerHeight="5" '
              'orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="#222"/></marker>'
              f'<marker id="aw" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="4" markerHeight="4" '
              f'orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="{WALK}"/></marker></defs>']
    for r, c in removed:
        o.append(f'<rect x="{X(c)}" y="{Y(r)}" width="{CS}" height="{CS}" fill="{GRAY}" fill-opacity="0.55"/>')
    for r in range(S + 1):
        o.append(f'<line x1="{X(0)}" y1="{Y(r)}" x2="{X(S) + 8}" y2="{Y(r)}" stroke="#c8c8c8" stroke-width="0.6"/>')
    for c in range(S + 1):
        o.append(f'<line x1="{X(c)}" y1="{Y(0)}" x2="{X(c)}" y2="{Y(S) + 8}" stroke="#c8c8c8" stroke-width="0.6"/>')
    # The grid border: the top and left sides of the corner.
    #
    o.append(f'<polyline points="{X(S) + 8},{Y(0)} {X(0)},{Y(0)} {X(0)},{Y(S) + 8}" fill="none" '
                      f'stroke="#333" stroke-width="1.6"/>')
    # The bypass walk near the corner: up the left side to the staircase, along it, then right
    # along the top side.
    #
    k, l0 = stair[0][0], stair[-1][1]
    walk = [(r, 0) for r in range(S - 1, k, -1)] + stair + [(0, c) for c in range(l0 + 1, S)]
    for r, c in stair:
        o.append(f'<rect x="{X(c) + 2}" y="{Y(r) + 2}" width="{CS - 4}" height="{CS - 4}" fill="none" '
                          f'stroke="{WALK}" stroke-width="1.6"/>')
    pts = " ".join(f"{cx(c)},{cy(r)}" for r, c in walk)
    o.append(f'<polyline points="{pts}" fill="none" stroke="{WALK}" stroke-width="2" stroke-opacity="0.7" '
                      f'stroke-linejoin="round" marker-end="url(#aw)"/>')
    rad = CS * 0.34
    for a, b in moves:
        col = "A" if at[a] == 0 else "B"
        o.append(f'<circle cx="{cx(b[1])}" cy="{cy(b[0])}" r="{rad}" fill="white" stroke="{COL[col]}" '
                          f'stroke-width="2" stroke-dasharray="3 2"/>')
    for (r, c), colour in at.items():
        o.append(f'<circle cx="{cx(c)}" cy="{cy(r)}" r="{rad}" fill="{COL["A" if colour == 0 else "B"]}"/>')
    for a, b in moves:
        x0, y0, x1, y1 = cx(a[1]), cy(a[0]), cx(b[1]), cy(b[0])
        dx, dy = x1 - x0, y1 - y0
        d = (dx * dx + dy * dy) ** 0.5
        sh = rad + 1
        o.append(f'<line x1="{x0 + dx * sh / d}" y1="{y0 + dy * sh / d}" x2="{x1 - dx * sh / d}" '
                          f'y2="{y1 - dy * sh / d}" stroke="#222" stroke-width="1.6" marker-end="url(#ar)"/>')
    o.append("</svg>")
    return "\n".join(o)


OUT = []
for name, title, at, far in PANELS:
    rw = rewrites_at(at)
    assert rw is not None, name
    removed, moves = rw
    stair = staircase(removed)
    assert stair == EXPECT[name], (name, stair)
    # Cross-check with the reference implementation on a full 11 x 11 instance.
    #
    pts = [(c, col) for c, col in at.items()] + far
    eff, rem, anyrw = rewrite_all(N, N, pts)
    assert anyrw and sorted(rem) == sorted(removed), (name, rem)
    w = walk3(N, N, rem)
    i = w.index(stair[0])
    assert w[i:i + len(stair)] == stair, (name, w)
    for a, b in moves:
        assert (b, at[a]) in eff, (name, eff)
    save(name + ".svg", panel_svg(at, removed, moves, stair))
    OUT.append(name)

for name in OUT:
    subprocess.run(["inkscape", name + ".svg", "--export-type=pdf",
                                    "--export-filename=" + os.path.join("..", name + ".pdf")],
                                  check=True, capture_output=True)
print("written:", " ".join(OUT))
