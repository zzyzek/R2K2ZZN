# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Time and peak memory of the C plug DP algorithm, one process per instance (from lib/, after
make -C c). Prints a Markdown table: per size, N random instances whose endpoints pass parity.
Sizes with a side of 10 or less run the thin solver; 11 x 11 and 12 x 12 run passing irreducible
instances with ZZN_SKIP_MOVES=1, so the whole instance goes to the plug DP algorithm (the fallback).

    python3 tests/dp_cost.py [N] [SEED]
"""
import os
import random
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "python"))
from compare import rand_irreducible  # noqa: E402
from zzn import Instance  # noqa: E402
from zzn.plugdp import parity_ok  # noqa: E402

PROG = os.path.join(os.path.dirname(HERE), "c", "zzn")
SIZES = [(8, 40), (9, 40), (10, 10), (10, 20), (10, 40), (11, 11), (12, 12)]


def rand_thin(rng, R, C):
    while True:
        pts = set()
        while len(pts) < 4:
            pts.add((rng.randrange(R), rng.randrange(C)))
        p = list(pts)
        if parity_ok(R, C, [(p[0], 0), (p[1], 0), (p[2], 1), (p[3], 1)]):
            return Instance(R, C, *p)


def run(I, env):
    line = " ".join(map(str, [I.R, I.C, *I.s0, *I.t0, *I.s1, *I.t1])) + "\n"
    r = subprocess.run(["/usr/bin/time", "-f", "%e %M", PROG], input=line, capture_output=True,
                       text=True, env=env)
    secs, kb = r.stderr.strip().splitlines()[-1].split()
    return float(secs), int(kb) / 1024, r.stdout.startswith("solvable")


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    print("| Size | Solver | Instances (solvable) | Time median / max (s) | Peak memory median / max (MB) |")
    print("|---|---|---|---|---|")
    for R, C in SIZES:
        env = dict(os.environ)
        if min(R, C) > 10:
            env["ZZN_SKIP_MOVES"] = "1"
            insts = [rand_irreducible(rng, R, R) for _ in range(n)]
            kind = "fallback"
        else:
            insts = [rand_thin(rng, R, C) for _ in range(n)]
            kind = "thin"
        res = [run(I, env) for I in insts]
        t = [x[0] for x in res]
        m = [x[1] for x in res]
        ok = sum(x[2] for x in res)
        print(f"| {R} × {C} | {kind} | {n} ({ok}) | {statistics.median(t):.2f} / {max(t):.2f} | "
              f"{statistics.median(m):.0f} / {max(m):.0f} |", flush=True)


if __name__ == "__main__":
    main()
