# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Time and peak memory of `solve` and `decide` as the grid grows, one process per instance, for
the C, JavaScript and Python command-line programs (from lib/, after make -C c).

    python3 tests/bench.py [--sizes=20,40,80] [--n=3] [--seed=1] [--programs=c,js,python]
                           [--modes=solve,decide] [--layouts=random,corner,spread]
                           [--shapes=square,wide] [--timeout=600]

Sizes are M x M (square), M x 2M (wide) and 6 x M (thin: decided and solved by the plug DP
algorithm). Endpoint layouts, each redrawn until the instance
passes the catalogue (so it is solvable):
  random   four endpoints anywhere;
  corner   all four endpoints in the 5 x 5 corner at the top left (large edge blocks);
  spread   one endpoint in each fifth of each axis (gaps between endpoints in both directions).
Every reported solution is checked with check_solution. For a program, layout, shape and mode,
larger sizes are skipped after the first size where an instance times out or fails.

Prints a Markdown table (median and maximum time in seconds, median and maximum peak resident
memory in MB) and, per row group, the exponent e of time ~ M^e fitted by least squares on the
logarithms of the medians over the sizes with median at least 0.05 s.
"""
import json
import math
import os
import random
import signal
import statistics
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(LIB, "python"))
from zzn import Instance, check_solution  # noqa: E402
from zzn.catalogue import fires  # noqa: E402
from zzn import plugdp  # noqa: E402

PROGRAMS = {
    "c": [os.path.join(LIB, "c", "zzn")],
    "js": ["node", os.path.join(LIB, "js", "cli.js")],
    "python": ["python3", os.path.join(LIB, "python", "zzn_cli.py")],
}


def opt(name, default):
    for a in sys.argv[1:]:
        if a.startswith(f"--{name}="):
            return a.split("=", 1)[1]
    return default


def passing(R, C, pts):
    if len(set(pts)) != 4:
        return False
    if min(R, C) <= 10:
        return plugdp.solvable_paths(R, C, [(pts[0], 0), (pts[1], 0), (pts[2], 1), (pts[3], 1)])
    return fires(R, C, *pts) is None


def draw(rng, layout, R, C):
    while True:
        if layout == "random":
            pts = [(rng.randrange(R), rng.randrange(C)) for _ in range(4)]
        elif layout == "corner":
            pts = [(rng.randrange(5), rng.randrange(5)) for _ in range(4)]
        else:
            rs = [rng.randrange(i * R // 5, max(i * R // 5 + 1, (i + 1) * R // 5)) for i in (1, 2, 3, 4)]
            cs = [rng.randrange(i * C // 5, (i + 1) * C // 5) for i in (1, 2, 3, 4)]
            rng.shuffle(cs)
            pts = list(zip(rs, cs))
            rng.shuffle(pts)
        if passing(R, C, pts):
            return Instance(R, C, *pts)


def run(cmd, I, mode, timeout):
    """(seconds, peak MB, status) for one instance; status 'ok', 'timeout' or an error text."""
    args = cmd + [str(v) for v in (I.R, I.C, *I.s0, *I.t0, *I.s1, *I.t1)] + ["--json"]
    if mode == "decide":
        args.append("--decide")
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        p = subprocess.Popen(["/usr/bin/time", "-f", "%e %M"] + args, stdout=out, stderr=err,
                             start_new_session=True)
        try:
            p.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            return timeout, 0.0, "timeout"
        err.seek(0)
        lines = err.read().decode().strip().splitlines()
        try:
            secs, kb = lines[-1].split()
            secs, mb = float(secs), int(kb) / 1024
        except (IndexError, ValueError):
            return 0.0, 0.0, "no timing: " + " / ".join(lines[-3:])
        if p.returncode != 0:
            return secs, mb, f"exit {p.returncode}: " + " / ".join(lines[-3:-1])
        out.seek(0)
        try:
            res = json.loads(out.read().decode())
        except ValueError:
            return secs, mb, "bad output"
        if not res.get("solvable"):
            return secs, mb, "answered unsolvable"
        if mode == "solve":
            sol = tuple([tuple(x) for x in path] for path in res["paths"])
            if not check_solution(I, sol):
                return secs, mb, "invalid solution"
        return secs, mb, "ok"


def slope(pts):
    pts = [(math.log(m), math.log(t)) for m, t in pts if t >= 0.05]
    if len(pts) < 2:
        return None
    mx = sum(x for x, _ in pts) / len(pts)
    my = sum(y for _, y in pts) / len(pts)
    sxx = sum((x - mx) ** 2 for x, _ in pts)
    return sum((x - mx) * (y - my) for x, y in pts) / sxx if sxx else None


def main():
    sizes = [int(x) for x in opt("sizes", "20,40,80,160,320,640").split(",")]
    n = int(opt("n", "3"))
    seed = int(opt("seed", "1"))
    progs = opt("programs", "c,js,python").split(",")
    modes = opt("modes", "solve,decide").split(",")
    layouts = opt("layouts", "random,corner,spread").split(",")
    shapes = opt("shapes", "square,wide").split(",")
    timeout = float(opt("timeout", "600"))

    print("| Program | Mode | Layout | Shape | M | Time median / max (s) | Memory median / max (MB) | Status |")
    print("|---|---|---|---|---|---|---|---|", flush=True)
    fits = []
    for mode in modes:
        for layout in layouts:
            for shape in shapes:
                insts = {}
                for M in sizes:
                    R, C = {"square": (M, M), "wide": (M, 2 * M), "thin": (6, M)}[shape]
                    rng = random.Random(f"{seed}-{layout}-{shape}-{M}")
                    insts[M] = [draw(rng, layout, R, C) for _ in range(n)]
                for prog in progs:
                    meds = []
                    for M in sizes:
                        res = [run(PROGRAMS[prog], I, mode, timeout) for I in insts[M]]
                        bad = [s for _, _, s in res if s != "ok"]
                        t = [x[0] for x in res]
                        m = [x[1] for x in res]
                        status = "ok" if not bad else f"{len(bad)} failed ({bad[0]})"
                        print(f"| {prog} | {mode} | {layout} | {shape} | {M} | "
                              f"{statistics.median(t):.3f} / {max(t):.3f} | "
                              f"{statistics.median(m):.0f} / {max(m):.0f} | {status} |", flush=True)
                        if bad:
                            break
                        meds.append((M, statistics.median(t)))
                    e = slope(meds)
                    fits.append((prog, mode, layout, shape, e, meds[-1][0] if meds else None))
    print()
    print("| Program | Mode | Layout | Shape | Exponent | Largest M completed |")
    print("|---|---|---|---|---|---|")
    for prog, mode, layout, shape, e, mx in fits:
        es = "-" if e is None else f"{e:.2f}"
        print(f"| {prog} | {mode} | {layout} | {shape} | {es} | {mx if mx else '-'} |")


if __name__ == "__main__":
    main()
