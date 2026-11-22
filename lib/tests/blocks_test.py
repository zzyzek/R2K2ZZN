# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Tests of the block layer (python/zzn/blocks.py), from lib/:

    python3 tests/blocks_test.py [N] [SEED] [MMIN] [MMAX]

N passing instances (default 300) with sides in MMIN … MMAX (default 11 … 80), drawn with the three
endpoint layouts of bench.py (random, corner, spread). For each: the blocks are deleted as in
`blocks.plan`, the leaf is solved by the library solver, and every lift is checked: the lifted
paths must solve the instance the block was deleted from (check_solution at every level, not only
at the top). Prints the number of instances, of lifts of each kind (inner lifts with and without
the flip of seedW), and the largest leaf.
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "python"))
from bench import draw  # noqa: E402
from zzn import check_solution  # noqa: E402
from zzn import blocks  # noqa: E402
from zzn.solver import _Solver  # noqa: E402


def check_levels(I):
    """Plan, solve the leaf, lift step by step and check each level. Returns (leaf, kinds), where
    kinds lists the lifts as "left", "right", "inner" or "inner flip" (seedW's flag set)."""
    leaf, steps = blocks.plan(I)
    p, q = _Solver().solve(leaf)
    assert check_solution(leaf, (p, q)), ("leaf", I, leaf)

    # The instance each step was deleted from, in the frame of that step.
    #
    parents = []
    cur = I
    for b, J, t in steps:
        parents.append(blocks.transpose(cur) if t else cur)
        cur = J
    kinds = []
    for (b, J, t), P in zip(reversed(steps), reversed(parents)):
        assert blocks.delete(b, P) == J, ("delete", I, b)
        flip = b[0] == "inner" and blocks.seed_w(J.C, p, q, b[1])[1]
        kinds.append("inner flip" if flip else b[0])
        p, q = blocks.lift(b, J, p, q)
        assert check_solution(P, (p, q)), ("lift", I, b, J)
        if t:
            p = [(c, r) for r, c in p]
            q = [(c, r) for r, c in q]
    assert check_solution(I, (p, q)), ("top", I)
    return leaf, kinds


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    lo = int(sys.argv[3]) if len(sys.argv) > 3 else 11
    hi = int(sys.argv[4]) if len(sys.argv) > 4 else 80
    count = {"left": 0, "right": 0, "inner": 0, "inner flip": 0}
    big = (0, 0)
    for i in range(n):
        layout = ("random", "corner", "spread")[i % 3]
        I = draw(rng, layout, rng.randint(lo, hi), rng.randint(lo, hi))
        leaf, kinds = check_levels(I)
        for k in kinds:
            count[k] += 1
        big = max(big, (max(leaf.R, leaf.C), min(leaf.R, leaf.C)))
    print(f"{n} instances OK; lifts: {count}; largest leaf {big[0]} x {big[1]}")


if __name__ == "__main__":
    main()
