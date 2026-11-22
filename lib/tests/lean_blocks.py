# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The Python block layer (python/zzn/blocks.py) against the Lean definitions, from lib/:

    python3 tests/lean_blocks.py N SEED MMIN MMAX --proof=DIR [--cases=FILE]

Draws N passing instances with sides in MMIN … MMAX and the three endpoint layouts of bench.py. It
runs `blocks.plan`, solves the leaf with the library solver and lifts back one block at a time. It
writes every step (instance, block, reduced instance, solution before and after the lift) and every
leaf to FILE (default: a temporary file). Then it runs

    lake env lean --run tests/lean/BlocksEval.lean FILE

in DIR, a `proof/` directory whose `ZZN.Constr.Round` is built, so that the Lean definitions
`blkX`, `Blk.del` and `Blk.lift` are evaluated on the same data and compared (see BlocksEval.lean).
C and JavaScript are compared with Python by compare.py. Exit status: Lean's.
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "python"))
from bench import draw  # noqa: E402
from zzn import check_solution  # noqa: E402
from zzn import blocks  # noqa: E402
from zzn.solver import _Solver  # noqa: E402


def inst_s(I):
    return " ".join(map(str, [I.R, I.C, *I.s0, *I.t0, *I.s1, *I.t1]))


def cells_s(L):
    return " ".join(f"{r},{c}" for r, c in L)


def blk_s(b):
    return {"left": "0", "right": "1", "inner": "2"}[b[0]] + " " + " ".join(map(str, b[1:]))


def cases(I):
    """The case lines of one instance."""
    leaf, steps = blocks.plan(I)
    out = ["leaf\t" + inst_s(leaf)]
    p, q = _Solver().solve(leaf)

    # The instance before each step, in the frame of the previous step.
    #
    before = [I] + [J for _, J, _ in steps[:-1]]
    for (b, J, tr), U in zip(reversed(steps), reversed(before)):
        p2, q2 = blocks.lift(b, J, p, q)
        out.append("\t".join(["step", inst_s(U), "1" if tr else "0", blk_s(b), inst_s(J),
                              cells_s(p), cells_s(q), cells_s(p2), cells_s(q2)]))
        p, q = p2, q2
        if tr:
            p = [(c, r) for r, c in p]
            q = [(c, r) for r, c in q]
    assert check_solution(I, (p, q)), I
    return out


def main():
    nums = [a for a in sys.argv[1:] if not a.startswith("--")]
    n, seed, lo, hi = (int(x) for x in nums[:4])
    proof = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--proof=")), None)
    path = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--cases=")), None)
    if proof is None:
        print(__doc__)
        return 2
    rng = random.Random(seed)
    lines = []
    for i in range(n):
        layout = ("random", "corner", "spread")[i % 3]
        lines += cases(draw(rng, layout, rng.randint(lo, hi), rng.randint(lo, hi)))
    if path is None:
        fd, path = tempfile.mkstemp(suffix=".txt")
        os.close(fd)
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    lean = os.path.join(HERE, "lean", "BlocksEval.lean")
    return subprocess.run(["lake", "env", "lean", "--run", lean, os.path.abspath(path)], cwd=proof).returncode


if __name__ == "__main__":
    sys.exit(main())
