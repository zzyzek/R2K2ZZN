# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Cross-language test: run the Python, JavaScript and C command-line programs on the same random
instances and require identical output (same verdicts, same paths), and check every reported
solution.

    python3 tests/compare.py N SEED [RMIN RMAX] [--trace] [--optimized] [--irreducible]  (from lib/)

--irreducible draws only passing instances with sides 11-22 that no reduction applies to, so every
instance reaches the same-colour split or the move search. --programs=c,js limits the programs run.
With ZZN_SKIP_MOVES=1 in the environment the programs skip the move search and solve such instances
with the exact plug DP algorithm (slow in Python: minutes per instance at width 11-12).
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(LIB, "python"))
from zzn import Instance, check_solution  # noqa: E402
from zzn.catalogue import fires  # noqa: E402
from zzn.solver import find_reduction  # noqa: E402

PROGRAMS = {
    "python": ["python3", os.path.join(LIB, "python", "zzn_cli.py")],
    "js": ["node", os.path.join(LIB, "js", "cli.js")],
    "c": [os.path.join(LIB, "c", "zzn")],
}


def rand_inst(rng, rmin, rmax):
    R, C = rng.randint(rmin, rmax), rng.randint(rmin, rmax)
    pts = set()
    while len(pts) < 4:
        if rng.random() < 0.6:
            cr, cc = rng.choice([0, R - 1]), rng.choice([0, C - 1])
            r = cr + (rng.randint(0, 4) if cr == 0 else -rng.randint(0, 4))
            c = cc + (rng.randint(0, 4) if cc == 0 else -rng.randint(0, 4))
            pts.add((min(R - 1, max(0, r)), min(C - 1, max(0, c))))
        else:
            pts.add((rng.randrange(R), rng.randrange(C)))
    p = list(pts)
    rng.shuffle(p)
    return Instance(R, C, *p)


def axis_coords(rng, n):
    """Four coordinates on an axis of length n, biased towards tuples no reduction applies to:
    one near each end (edge gaps <= 3), two anywhere."""
    if n < 13:
        return [rng.randrange(n) for _ in range(4)]
    return [rng.randint(0, 3), rng.randint(n - 4, n - 1), rng.randrange(n), rng.randrange(n)]


def rand_irreducible(rng, rmin, rmax):
    """A passing instance with sides in [max(rmin, 11), min(rmax, 22)] and no reduction."""
    lo, hi = max(rmin, 11), min(rmax, 22)
    while True:
        R, C = rng.randint(lo, hi), rng.randint(lo, hi)
        rs, cs = axis_coords(rng, R), axis_coords(rng, C)
        rng.shuffle(cs)
        pts = list(zip(rs, cs))
        if len(set(pts)) < 4:
            continue
        rng.shuffle(pts)
        I = Instance(R, C, *pts)
        if find_reduction(I) is None and fires(R, C, *pts) is None:
            return I


def parse(out):
    """Split CLI output into per-instance blocks (each starts with solvable/unsolvable)."""
    blocks, cur = [], None
    for line in out.splitlines():
        if line.startswith("solvable") or line.startswith("unsolvable") or line.startswith("error"):
            cur = [line]
            blocks.append(cur)
        elif cur is not None:
            cur.append(line)
    return blocks


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    rmin, rmax = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (3, 24)
    extra = [a for a in ("--trace", "--optimized") if a in sys.argv]
    gen = rand_irreducible if "--irreducible" in sys.argv else rand_inst
    insts = [gen(rng, rmin, rmax) for _ in range(n)]
    text = "\n".join(" ".join(map(str, [I.R, I.C, *I.s0, *I.t0, *I.s1, *I.t1])) for I in insts) + "\n"
    want = next((a.split("=", 1)[1].split(",") for a in sys.argv if a.startswith("--programs=")),
                list(PROGRAMS))
    outs = {}
    for name, cmd in PROGRAMS.items():
        if name not in want:
            continue
        if not os.path.exists(cmd[-1] if name != "c" else cmd[0]):
            print(f"skipping {name}: not built")
            continue
        outs[name] = parse(subprocess.run(cmd + extra, input=text, capture_output=True, text=True).stdout)
    names = list(outs)
    bad = 0
    for i, I in enumerate(insts):
        blocks = [outs[nm][i] if i < len(outs[nm]) else None for nm in names]
        if any(b != blocks[0] for b in blocks):
            bad += 1
            print("outputs differ:", I, {nm: (b[0] if b else None) for nm, b in zip(names, blocks)})
            continue
        b = blocks[0]
        if b and b[0] == "solvable":
            path = lambda line: [tuple(map(int, x.split(","))) for x in line.split()[1:]]
            if not check_solution(I, (path(b[1]), path(b[2]))):
                bad += 1
                print("invalid solution:", I)
    solved = sum(1 for b in outs[names[0]] if b[0] == "solvable")
    print(f"instances {n}, programs {names}, solvable {solved}, problems {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
