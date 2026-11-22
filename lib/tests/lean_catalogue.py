# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The Python catalogue (python/zzn/catalogue.py) against the Lean definition `fires3`, from lib/:

    python3 tests/lean_catalogue.py N SEED --proof=DIR [--cases=FILE]

Draws N instances (layouts: random, corners, border, planted catalogue patterns; sides 11-40 and
thin sizes), records the Python verdict of each entry, and runs
`lake env lean --run tests/lean/CatEval.lean FILE` in DIR (a built `proof/`), which evaluates
`fires3` and each of its entries in Lean and compares. C and JavaScript are compared with Python
by compare.py.

Writes one line per instance:  R C r0 c0 r1 c1 r2 c2 r3 c3 FIRES MASK NAME
where the endpoints are s0 t0 s1 t1, FIRES is 1/0 for zzn.catalogue.fires(...) is not None,
MASK is a 13-character 0/1 string with one flag per entry, evaluated independently
(order P T1 T2 L1 L6 L2 L3 L4 L5 E1 B C4 R), and NAME the first entry name or '-'.
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "python"))
from zzn import catalogue as K  # noqa: E402

ENTRIES = ["P", "T1", "T2", "L1", "L6", "L2", "L3", "L4", "L5", "E1", "B", "C4", "R"]


def mask(R, C, s0, t0, s1, t1):
    pts = [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
    vs = [K.View(R, C, f, pts) for f in K.FRAMES]
    fl = [
        not K.parity_ok(R, C, pts),
        K.t1_fires(R, C, pts),
        K.t2_fires([s0, t0, s1, t1]),
        K.l1_fires(R, C, pts),
        K.l6_fires(R, C, pts),
        any(K.test_l2(v) for v in vs),
        any(K.test_l3(v) for v in vs),
        any(K.test_l4(v) for v in vs),
        any(K.test_l5(v) for v in vs),
        any(K.edge_closure(v) for v in vs),
        any(K.boundary_only(R, C, f, pts) for f in K.FRAMES),
        R >= 10 and C >= 10 and any(K.corner4(R, C, f, pts) for f in K.FRAMES),
        K.eff_alt(R, C, pts),
    ]
    return "".join("1" if x else "0" for x in fl)


def perim(rng, R, C):
    k = rng.randrange(2 * (R + C))
    side = rng.randrange(4)
    if side == 0:
        return (0, rng.randrange(C))
    if side == 1:
        return (R - 1, rng.randrange(C))
    if side == 2:
        return (rng.randrange(R), 0)
    return (rng.randrange(R), C - 1)


def near_corner(rng, R, C, k, corner=None):
    cr, cc = corner if corner else (rng.choice([0, R - 1]), rng.choice([0, C - 1]))
    dr, dc = rng.randrange(min(k, R)), rng.randrange(min(k, C))
    return (dr if cr == 0 else R - 1 - dr, dc if cc == 0 else C - 1 - dc)


def plant(rng, R, C, cells_frame):
    """Map frame cells back to the grid through a random frame."""
    f = rng.choice(K.FRAMES)
    H, W = (C, R) if f[2] else (R, C)
    out = []
    for (i, j) in cells_frame:
        if i >= H or j >= W:
            return None
        out.append(K.frame_back(R, C, f, (i, j)))
    return out


def jitter(rng, R, C, p):
    """Move a cell by one step (to make near misses), staying in the grid."""
    dr, dc = rng.choice([(1, 0), (-1, 0), (0, 1), (0, -1)])
    return (min(max(p[0] + dr, 0), R - 1), min(max(p[1] + dc, 0), C - 1))


def draw(rng, layout, R, C):
    need_par = rng.random() < 0.85
    tries = 0
    while True:
        tries += 1
        if tries > 200:
            layout = "random"
        if layout == "random":
            pts = [(rng.randrange(R), rng.randrange(C)) for _ in range(4)]
        elif layout == "corner":
            k = rng.randint(3, 8)
            corner = (rng.choice([0, R - 1]), rng.choice([0, C - 1]))
            pts = [near_corner(rng, R, C, k, corner) for _ in range(4)]
        elif layout == "corners":
            pts = [near_corner(rng, R, C, 3) for _ in range(4)]
        elif layout == "border":
            pts = [perim(rng, R, C) for _ in range(4)]
        elif layout == "mixed":
            corner = (rng.choice([0, R - 1]), rng.choice([0, C - 1]))
            pts = [near_corner(rng, R, C, 4, corner) for _ in range(3)] + [perim(rng, R, C)]
            rng.shuffle(pts)
        elif layout == "plantB":
            lst = K.BOUNDARY3_ODD if (R % 2 == 1 and C % 2 == 1) else K.BOUNDARY3_EVEN
            a1, a2, b = rng.choice(lst)
            pl = plant(rng, R, C, [a1, a2, b])
            if pl is None:
                continue
            pts = [pl[0], pl[1], pl[2], perim(rng, R, C)]
            pts = [pts[0], pts[1], pts[2], pts[3]] if rng.random() < 0.5 else [pts[2], pts[3], pts[0], pts[1]]
            if rng.random() < 0.3:
                i = rng.randrange(4)
                pts[i] = jitter(rng, R, C, pts[i])
        elif layout == "plantC":
            lst = K.CORNER4 if (R * C) % 2 == 0 else K.CORNER4_ODD
            A, B = rng.choice(lst)
            pl = plant(rng, R, C, A + B)
            if pl is None:
                continue
            pts = pl if rng.random() < 0.5 else pl[2:] + pl[:2]
            if rng.random() < 0.3:
                i = rng.randrange(4)
                pts[i] = jitter(rng, R, C, pts[i])
        elif layout == "plantL":
            pat = rng.choice(["L1", "L2", "L3", "L4", "L5", "E1", "L6", "T2", "R3", "R2", "R1"])
            if pat == "T2":
                if R < 2 or C < 2:
                    continue
                r, c = rng.randrange(R - 1), rng.randrange(C - 1)
                lab = [((r, c), 0), ((r + 1, c + 1), 0), ((r, c + 1), 1), ((r + 1, c), 1)]
            elif pat == "L6":
                fs = rng.sample(K.FRAMES, 2)
                lab = []
                for col, f in zip((0, 1), fs):
                    for x in ((0, 1), (1, 0)):
                        lab.append((K.frame_back(R, C, f, x), col))
            else:
                W = max(R, C)
                k = rng.randrange(max(W - 3, 1))
                tmpl = {"L1": [((0, 0), 0), ((0, 1), 1), ((1, 0), 1)],
                        "L2": [((0, 1), 0), ((1, 0), 1)],
                        "L3": [((0, 2), 0), ((1, 1), 0), ((1, 0), 1)],
                        "L4": [((0, 0), 0), ((1, 1), 0), ((0, 2), 1)],
                        "L5": [((0, 0), 0), ((0, 2), 1), ((2, 0), 1)],
                        "E1": [((0, k), 0), ((1, k + 1), 0), ((1, k + 2), 1), ((0, k + 3), 1)],
                        "R3": [((1, 2), 0), ((2, 1), 1)],
                        "R2": [((0, 0), 0), ((1, 1), 0)],
                        "R1": [((0, 1), rng.randrange(2))]}[pat]
                pl = plant(rng, R, C, [x for x, _ in tmpl])
                if pl is None:
                    continue
                lab = list(zip(pl, [c for _, c in tmpl]))
            cnt = [sum(1 for _, c in lab if c == col) for col in (0, 1)]
            if cnt[0] > 2 or cnt[1] > 2:
                continue
            for col in (0, 1):
                while cnt[col] < 2:
                    u = rng.random()
                    x = (near_corner(rng, R, C, 4) if u < 0.4 else perim(rng, R, C) if u < 0.7
                         else (rng.randrange(R), rng.randrange(C)))
                    lab.append((x, col))
                    cnt[col] += 1
            if rng.random() < 0.2:
                i = rng.randrange(4)
                lab[i] = (jitter(rng, R, C, lab[i][0]), lab[i][1])
            sw = rng.randrange(2)
            c0 = [x for x, c in lab if c == sw]
            c1 = [x for x, c in lab if c != sw]
            pts = c0 + c1
        else:
            raise ValueError(layout)
        if rng.random() < 0.5:
            pts[0], pts[1] = pts[1], pts[0]
        if len(set(pts)) == 4:
            ok = K.parity_ok(R, C, [(pts[0], 0), (pts[1], 0), (pts[2], 1), (pts[3], 1)])
            if ok or not need_par or tries > 400:
                return pts


def main():
    nums = [a for a in sys.argv[1:] if not a.startswith("--")]
    n, seed = int(nums[0]), int(nums[1])
    proof = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--proof=")), None)
    out = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--cases=")), None)
    if proof is None:
        print(__doc__)
        return 2
    if out is None:
        fd, out = tempfile.mkstemp(suffix=".txt")
        os.close(fd)
    rng = random.Random(seed)
    layouts = ["random", "corner", "corners", "border", "mixed", "plantB", "plantC", "plantL", "plantL"]
    with open(out, "w") as fo:
        for i in range(n):
            layout = layouts[i % len(layouts)]
            u = rng.random()
            if u < 0.8:
                R, C = rng.randint(11, 40), rng.randint(11, 40)
            elif u < 0.95:
                R, C = rng.randint(1, 10), rng.randint(1, 40)
                if rng.random() < 0.5:
                    R, C = C, R
            else:
                R, C = rng.randint(1, 10), rng.randint(1, 10)
            if R * C < 4:
                R, C = 2, 2
            pts = draw(rng, layout, R, C)
            name = K.fires(R, C, *pts)
            m = mask(R, C, *pts)
            flat = " ".join(f"{p[0]} {p[1]}" for p in pts)
            fo.write(f"{R} {C} {flat} {0 if name is None else 1} {m} {name or '-'} {layout}\n")
    lean = os.path.join(HERE, "lean", "CatEval.lean")
    return subprocess.run(["lake", "env", "lean", "--run", lean, os.path.abspath(out)], cwd=proof).returncode


if __name__ == "__main__":
    sys.exit(main())
