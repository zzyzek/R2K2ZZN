# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Dump Python look_j answers for js/look_check.js, from lib/:

    python3 js/look_dump.py N SEED OUT.json [--lanes]

N irreducible passing instances per box R x C, 11 <= R, C <= 16 (drawn as in tests/look_test.py),
and with --lanes the instance of every stored solution (the slice's rows, the lane's columns),
each with look_j's answer and trace; for the lanes also entry_p's answer on the lane's slice.
"""
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(LIB, "python"))
sys.path.insert(0, os.path.join(LIB, "tests"))
from zzn import look  # noqa: E402
from zzn.grid import Instance  # noqa: E402
from look_test import draw  # noqa: E402


def rec(I, kind, extra=None):
    tr = {}
    t0 = time.perf_counter()
    s = look.look_j(I, tr)
    dt = time.perf_counter() - t0
    r = {"kind": kind, "I": [I.R, I.C, I.s0, I.t0, I.s1, I.t1], "sol": s,
         "sym": look.sym_to_int(tr["sym"]) if "sym" in tr else None,
         "slice": tr.get("slice"), "entry": tr.get("entry")}
    if extra:
        r.update(extra)
    return r, dt


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    n, seed, out = int(args[0]), int(args[1]), args[2]
    rng = random.Random(seed)
    look.data()
    recs, tsum = [], 0.0
    for R in range(11, 17):
        for C in range(11, 17):
            for _ in range(n):
                I = draw(rng, R, C)
                r, dt = rec(I, "leaf")
                tsum += dt
                recs.append(r)
    nleaf = len(recs)
    if "--lanes" in sys.argv:
        for (w, h), sl in sorted(look.data()["boxes"].items()):
            for si, d in enumerate(sl):
                for e in d[2]:
                    j = e[0]
                    cols = [(j // h ** (3 - i)) % h for i in range(4)]
                    K = Instance(w, h, *[(d[0][i], cols[i]) for i in range(4)])
                    ep = look.entry_p(K, d)
                    r, dt = rec(K, "lane", {"box": "%dx%d" % (w, h), "sliceIdx": si,
                                            "entryP": None if ep is None else [ep[0], ep[1]]})
                    recs.append(r)
    with open(out, "w") as f:
        json.dump(recs, f)
    print("dumped %d records (%d leaves, mean Python look_j on leaves %.2f ms)" %
          (len(recs), nleaf, 1000 * tsum / max(nleaf, 1)))


if __name__ == "__main__":
    main()
