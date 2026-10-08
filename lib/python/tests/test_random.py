# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Randomized tests: solutions are valid, decide() agrees with solve(), and decide() agrees with
an exact solver.

    python3 tests/test_random.py N SEED [RMIN RMAX] [--exact ./feascheck]

--exact names a program that reads "R C s0r s0c t0r t0c s1r s1c t1r t1c" lines and prints 1/0
(an independent exact solver); without it, instances with both sides <= 13 are
checked with the Python plug DP."""
import random
import subprocess
import sys
import time

sys.path.insert(0, ".")
from zzn import Instance, decide, solve, check_solution
from zzn.plugdp import solvable_paths


def rand_inst(rng, rmin, rmax):
    R, C = rng.randint(rmin, rmax), rng.randint(rmin, rmax)
    pts = set()
    while len(pts) < 4:
        if rng.random() < 0.6:  # near a random corner
            cr, cc = rng.choice([0, R - 1]), rng.choice([0, C - 1])
            r = cr + (rng.randint(0, 4) if cr == 0 else -rng.randint(0, 4))
            c = cc + (rng.randint(0, 4) if cc == 0 else -rng.randint(0, 4))
            pts.add((min(R - 1, max(0, r)), min(C - 1, max(0, c))))
        else:
            pts.add((rng.randrange(R), rng.randrange(C)))
    p = list(pts)
    rng.shuffle(p)
    return Instance(R, C, *p)


def line(I):
    return " ".join(map(str, [I.R, I.C, *I.s0, *I.t0, *I.s1, *I.t1]))


def main():
    args = [a for a in sys.argv[1:]]
    exact = None
    if "--exact" in args:
        k = args.index("--exact")
        exact = args[k + 1:k + 2] + ["--feascheck"]
        del args[k:k + 2]
    n = int(args[0]) if args else 100
    rng = random.Random(int(args[1]) if len(args) > 1 else 1)
    rmin, rmax = (int(args[2]), int(args[3])) if len(args) > 3 else (3, 30)
    insts = [rand_inst(rng, rmin, rmax) for _ in range(n)]
    stats = {"solved": 0, "unsolvable": 0, "bad": 0, "exact_checked": 0, "exact_mismatch": 0}
    t0 = time.time()
    dec = []
    for i, I in enumerate(insts):
        d = decide(I)
        s = solve(I)
        dec.append(d)
        ok = (s is None and not d) or (s is not None and d and check_solution(I, s))
        stats["solved" if s else "unsolvable"] += 1
        if not ok:
            stats["bad"] += 1
            print("BAD:", I, d, s is not None, flush=True)
        if (i + 1) % 25 == 0:
            print(f"  {i + 1}/{n} {round(time.time() - t0)} s", flush=True)
    if exact:
        out = subprocess.run(exact, input="\n".join(map(line, insts)) + "\n", capture_output=True,
                             text=True).stdout.split()
        for I, d, e in zip(insts, dec, out):
            stats["exact_checked"] += 1
            if (e == "1") != d:
                stats["exact_mismatch"] += 1
                print("decide disagrees with the exact solver:", I, d, e)
    else:
        for I, d in zip(insts, dec):
            if max(I.R, I.C) <= 13 and min(I.R, I.C) >= 11:
                stats["exact_checked"] += 1
                if solvable_paths(I.R, I.C, [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]) != d:
                    stats["exact_mismatch"] += 1
                    print("decide disagrees with the exact DP:", I)
    stats["seconds"] = round(time.time() - t0, 1)
    print(stats)
    return 0 if stats["bad"] == 0 and stats["exact_mismatch"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
