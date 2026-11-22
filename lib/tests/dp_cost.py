# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Time and peak memory of the C plug DP algorithm on thin instances (a side at most 10), one
process per instance (from lib/, after make -C c). Prints a Markdown table: per size, N random
instances whose endpoints pass parity.

    python3 tests/dp_cost.py [N] [SEED] [SIZES] [TIMEOUT]

SIZES is a comma-separated list such as 10x20,10x80 (default: the table below), each with a side
at most 10. An instance
running longer than TIMEOUT seconds (default: none) is killed. An instance that is killed (timeout
or memory cap) is reported separately and left out of the medians; larger sizes are then skipped.
"""
import os
import random
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "python"))
from zzn import Instance  # noqa: E402
from zzn.plugdp import parity_ok  # noqa: E402

PROG = os.path.join(os.path.dirname(HERE), "c", "zzn")
SIZES = [(8, 40), (9, 40), (10, 10), (10, 20), (10, 40)]


def rand_thin(rng, R, C):
    while True:
        pts = set()
        while len(pts) < 4:
            pts.add((rng.randrange(R), rng.randrange(C)))
        p = list(pts)
        if parity_ok(R, C, [(p[0], 0), (p[1], 0), (p[2], 1), (p[3], 1)]):
            return Instance(R, C, *p)


def run(I, env, timeout):
    line = " ".join(map(str, [I.R, I.C, *I.s0, *I.t0, *I.s1, *I.t1])) + "\n"
    lim = ["timeout", "-s", "KILL", str(timeout)] if timeout else []
    r = subprocess.run(["/usr/bin/time", "-f", "%e %M"] + lim + [PROG], input=line,
                       capture_output=True, text=True, env=env)
    secs, kb = r.stderr.strip().splitlines()[-1].split()
    if r.returncode != 0:
        return float(secs), int(kb) / 1024, None
    return float(secs), int(kb) / 1024, r.stdout.startswith("solvable")


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    sizes = SIZES
    if len(sys.argv) > 3:
        sizes = [tuple(int(v) for v in s.split("x")) for s in sys.argv[3].split(",")]
    timeout = float(sys.argv[4]) if len(sys.argv) > 4 else None
    if any(min(R, C) > 10 for R, C in sizes):
        sys.exit("every size needs a side at most 10")
    print("| Size | Instances (solvable) | Time median / max (s) | Peak memory median / max (MB) |")
    print("|---|---|---|---|")
    for R, C in sizes:
        env = dict(os.environ)
        insts = [rand_thin(rng, R, C) for _ in range(n)]
        res = []
        for I in insts:
            res.append(run(I, env, timeout))
            if res[-1][2] is None:
                break
        done = [x for x in res if x[2] is not None]
        ok = sum(1 for x in done if x[2])
        note = "".join(f", killed at {x[0]:.0f} s and {x[1]:.0f} MB" for x in res if x[2] is None)
        if done:
            t = [x[0] for x in done]
            m = [x[1] for x in done]
            tm = f"{statistics.median(t):.2f} / {max(t):.2f} | {statistics.median(m):.0f} / {max(m):.0f}"
        else:
            tm = "- | -"
        print(f"| {R} × {C} | {len(res)} ({ok}{note}) | {tm} |", flush=True)
        if len(done) < len(res):
            break


if __name__ == "__main__":
    main()
