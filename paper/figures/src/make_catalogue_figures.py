# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The catalogue examples of the paper (Figure "Instances on which an entry fires"), titled with
the paper's entry names. The instances are those of docs/figures/make_figures.py.

    python3 make_catalogue_figures.py      (writes SVG here and PDF into paper/figures, via Inkscape)
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..", "..")
sys.path.insert(0, os.path.join(ROOT, "docs", "figures"))
sys.path.insert(0, os.path.join(ROOT, "lib", "python"))

from fig import grid_svg, inst_ends, save
from zzn import Instance, fires
from zzn.catalogue import rewrite_all, walk3

os.chdir(HERE)
GRAY = "#9aa0a6"
OUT = []


def out(name, svg):
    save(name + ".svg", svg)
    OUT.append(name)


# Border alternation, split corner, edge interlock. T1 and L2 are the two unsolvable instances of
# the Introduction's first figure, drawn without titles on 4 x 5 grids chosen for the paper (they
# are not the instances of docs/figures/make_figures.py). T1 must not fire on the L2 instance,
# so that the two panels show different entries.
#
cat = {
    "T1": (Instance(4, 5, (0, 0), (3, 4), (0, 2), (3, 0)), None),
    "L2": (Instance(4, 5, (0, 1), (2, 2), (1, 0), (3, 3)), None),
    "E1": (Instance(4, 7, (0, 1), (1, 2), (0, 4), (1, 3)), "Edge interlock"),
}
for name, (inst, title) in cat.items():
    f = fires(inst.R, inst.C, inst.s0, inst.t0, inst.s1, inst.t1)
    assert f is not None, (name, inst)
    assert name != "T1" or f == "T1", (name, f)
    assert name != "L2" or f == "L2", (name, f)
    marks = [((0, 0), "?")] if name == "L2" else []
    kw = {"cs": 18} if inst.R > 6 else {}
    out(f"cat_{name}", grid_svg(inst.R, inst.C, inst_ends(inst), marks=marks, title=title, **kw))

# Forced-route alternation: the first 11 x 12 instance of the search on which only it fires.
#
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
    J = Instance(R, C, *list(pts))
    if fires(*J) == "R":
        found = J
        break
I = found
eff, removed, _ = rewrite_all(I.R, I.C, [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)])
svg = grid_svg(I.R, I.C, inst_ends(I), cs=20,
               shade=[(removed, GRAY, 0.55)],
               virtual=[(q[0], "", "A" if q[1] == 0 else "B") for q in eff
                        if q[0] not in (I.s0, I.t0, I.s1, I.t1)])
# The bypass walk (walk3), drawn as a closed blue line through the cell centres, under the
# endpoints. grid_svg places cell (r, c) at x = 14 + 20 c, y = 14 + 20 r (no title, no
# coordinates).
#
walk = walk3(I.R, I.C, removed)
pts = " ".join(f"{14 + 20 * c + 10},{14 + 20 * r + 10}" for r, c in walk)
line = (f'<polygon points="{pts}" fill="none" stroke="#3b5bdb" stroke-width="2" '
        f'stroke-opacity="0.7" stroke-linejoin="round"/>')
i = svg.index("<circle")
out("cat_R", svg[:i] + line + "\n" + svg[i:])

for name in OUT:
    subprocess.run(["inkscape", name + ".svg", "--export-type=pdf",
                    "--export-filename=" + os.path.join("..", name + ".pdf")],
                   check=True, capture_output=True)
print("written:", " ".join(OUT))
