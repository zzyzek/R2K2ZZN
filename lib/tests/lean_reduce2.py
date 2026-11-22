# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""The Python two-line reductions (python/zzn/reduce2.py) against the Lean definitions, from lib/:

    python3 tests/lean_reduce2.py N SEED MMIN MMAX --proof=DIR [--cases=FILE]

Draws N passing instances (sides MMIN … MMAX, the three layouts of bench.py), deletes blocks
(`blocks.plan`), then runs `reduce2.plan2` on what is left, solves its leaf with the library solver
and lifts back one reduction at a time. Writes every step and leaf to FILE and runs
`lake env lean --run tests/lean/ReduceEval.lean FILE` in DIR (a `proof/` with
`ZZN.Constr.Solve2` built), which compares `findRed2`, `liftE` and the leaf condition with Lean.
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
from lean_blocks import inst_s, cells_s  # noqa: E402
from zzn import check_solution, blocks, reduce2  # noqa: E402
from zzn.solver import _Solver  # noqa: E402


def cases(I):
    B, _ = blocks.plan(I)
    leaf, steps = reduce2.plan2(B)
    out = ["leaf\t" + inst_s(leaf)]
    p, q = _Solver().solve(leaf)
    before = [B] + [reduce2.delete_at(P, d) for P, d, _ in steps[:-1]]
    for (P, d, tr), U in zip(reversed(steps), reversed(before)):
        p2, q2 = reduce2.lift_e(P, d, p, q)
        out.append("\t".join(["step", inst_s(U), "1" if tr else "0", str(d),
                              cells_s(p), cells_s(q), cells_s(p2), cells_s(q2)]))
        p, q = p2, q2
        if tr:
            p = [(c, r) for r, c in p]
            q = [(c, r) for r, c in q]
    assert check_solution(B, (p, q)), I
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
    lean = os.path.join(HERE, "lean", "ReduceEval.lean")
    return subprocess.run(["lake", "env", "lean", "--run", lean, os.path.abspath(path)], cwd=proof).returncode


if __name__ == "__main__":
    sys.exit(main())
