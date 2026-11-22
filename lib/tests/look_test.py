# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Tests of the certificate lookup (python/zzn/look.py), from lib/:

    python3 tests/look_test.py [N] [SEED]

1. Irreducible leaves: for each of the 36 boxes R x C with 11 <= R, C <= 16 (both orientations),
   N instances (default 30) that are well formed, pass the catalogue (`zzn.catalogue.fires` is
   None) and admit no reduction on either axis in Lean's sense (`findRed2 I = none` and
   `findRed2 I.transpose = none`, transcribed below). `look_j` must answer, and the answer must
   pass `check_solution` (this is `lookJ_complete` and `lookJ_sound` on these instances).
   Instances are drawn per axis: a row tuple and a column tuple, each with no reduction on its
   axis (a reduction on the x-axis depends only on the x-coordinates), then combined.
2. Stored solutions: for every stored solution (lane, …) of every slice, the lane's instance K
   (the slice's rows, the lane's columns): `entry_p(K, d)` must answer with a solution of K.
3. Soundness on random passing instances with sides 11-16 (reducible ones included): every
   answer of `look_j` is a solution.

Prints counts per box, the entries used (template pairs or stored solutions) and the mean time of
`look_j`. Exit status 1 on any failure.
"""
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "python"))
from zzn import check_solution, well_formed  # noqa: E402
from zzn.catalogue import fires  # noqa: E402
from zzn.grid import Instance, ends  # noqa: E402
from zzn import look  # noqa: E402


def _sub(a, b):
    return a - b if a > b else 0


# --- reductions, transcribed from Lean -------------------------------------------------------
# Only the x-coordinates of the endpoints matter, so these take the side w and the tuple xs.

def free_line_b(xs, k):
    """`freeLineB` (`proof/ZZN/Statement.lean:496`)."""
    return all(e != k for e in xs)


def end_below_b(xs, k):
    """`endBelowB` (`proof/ZZN/Statement.lean:497`)."""
    return any(e < k for e in xs)


def end_above_b(xs, k):
    """`endAboveB` (`proof/ZZN/Statement.lean:498`)."""
    return any(k < e for e in xs)


def red_b(w, xs, d):
    """`redB` (`proof/ZZN/Statement.lean:500`): `RedX I d`, decided."""
    if not 13 <= w:
        return False
    if d == 0 and all(free_line_b(xs, k) for k in range(4)):
        return True
    if d + 2 == w and all((not (w <= k + 4)) or free_line_b(xs, k) for k in range(w)):
        return True
    for lo in range(d + 1):
        if (d + 1 <= lo + 9 and lo + 10 <= w and all(free_line_b(xs, lo + j) for j in range(10)) and
                end_below_b(xs, lo) and end_above_b(xs, lo + 9)):
            return True
    return (8 <= d and d + 10 <= w and free_line_b(xs, d) and free_line_b(xs, d + 1) and
            ((1 <= d and free_line_b(xs, _sub(d, 1))) or free_line_b(xs, d + 2)) and
            end_below_b(xs, d) and end_above_b(xs, d + 1))


def red_bb(w, xs, d):
    """`redBB` (`proof/ZZN/Constr/Solve2.lean:163`): `RedB I d`, decided."""
    return (13 <= w and 5 <= d and d + 7 <= w and free_line_b(xs, d) and free_line_b(xs, d + 1) and
            ((1 <= d and free_line_b(xs, _sub(d, 1))) or free_line_b(xs, d + 2)) and
            end_below_b(xs, d) and end_above_b(xs, d + 1))


def find_red2(w, xs):
    """`findRed2` (`proof/ZZN/Constr/Solve2.lean:186`): the first d < w with `redAny`."""
    return next((d for d in range(w) if red_b(w, xs, d) or red_bb(w, xs, d)), None)


def no_red(I):
    """No reduction on either axis: `findRed2 I = none` and `findRed2 I.transpose = none`."""
    return (find_red2(I.R, [e[0] for e in ends(I)]) is None and
            find_red2(I.C, [e[1] for e in ends(I)]) is None)


# --- drawing irreducible instances -----------------------------------------------------------

_IRR = {}


def irreducible_tuples(w):
    """All coordinate tuples (x_s0, x_t0, x_s1, x_t1) on a side w with no reduction."""
    if w not in _IRR:
        good = {}
        out = []
        for a in range(w):
            for b in range(w):
                for c in range(w):
                    for d in range(w):
                        key = frozenset((a, b, c, d))
                        if key not in good:
                            good[key] = find_red2(w, sorted(key)) is None
                        if good[key]:
                            out.append((a, b, c, d))
        _IRR[w] = out
    return _IRR[w]


def draw(rng, R, C, tries=200000):
    xs, ys = irreducible_tuples(R), irreducible_tuples(C)
    for _ in range(tries):
        x, y = rng.choice(xs), rng.choice(ys)
        cells = [(x[i], y[i]) for i in range(4)]
        I = Instance(R, C, *cells)
        if well_formed(I) and fires(R, C, *cells) is None:
            return I
    return None


def main():
    nums = [int(a) for a in sys.argv[1:] if not a.startswith("--")]
    n = nums[0] if len(nums) > 0 else 30
    seed = nums[1] if len(nums) > 1 else 1
    rng = random.Random(seed)
    bad = 0
    look.data()

    print("irreducible tuples per side: " +
          ", ".join("%d: %d" % (w, len(irreducible_tuples(w))) for w in range(11, 17)))

    # 1. Irreducible leaves on every box and its transpose.
    #
    total, t_sum, used = 0, 0.0, {"pair": 0, "sol": 0}
    for R in range(11, 17):
        line = []
        for C in range(11, 17):
            got = 0
            for _ in range(n):
                I = draw(rng, R, C)
                if I is None:
                    print("FAIL: no irreducible passing instance drawn for %dx%d" % (R, C))
                    bad += 1
                    break
                assert no_red(I)
                tr = {}
                t0 = time.perf_counter()
                s = look.look_j(I, tr)
                t_sum += time.perf_counter() - t0
                total += 1
                if s is None or not check_solution(I, s):
                    print("FAIL: %r -> %s" % (I, "None" if s is None else "invalid"))
                    bad += 1
                    continue
                got += 1
                used[tr["entry"][0]] += 1
            line.append("%dx%d %d/%d" % (R, C, got, n))
        print("  " + ", ".join(line))
    print("irreducible leaves: %d instances, entries used: template pairs %d, stored solutions %d, "
          "mean look_j %.2f ms" % (total, used["pair"], used["sol"], 1000 * t_sum / max(total, 1)))

    # 2. Every stored solution of the table, through entry_p.
    #
    nsol, nfall = 0, 0
    for (w, h), sl in sorted(look.data()["boxes"].items()):
        for d in sl:
            for e in d[2]:
                j = e[0]
                cols = [(j // h ** (3 - i)) % h for i in range(4)]
                K = Instance(w, h, *[(d[0][i], cols[i]) for i in range(4)])
                nsol += 1
                r = look.entry_p(K, d)
                if r is None or not check_solution(K, r[0]):
                    print("FAIL: stored solution of slice %r lane %d" % (d[0], j))
                    bad += 1
                    continue
                if r[1][0] == "sol":
                    nfall += 1
                if not look.sol_f(K, look.dec_path(e[1], e[2]), look.dec_path(e[3], e[4])):
                    print("FAIL: stored paths of slice %r lane %d are not a solution" % (d[0], j))
                    bad += 1
    print("stored solutions: %d lanes, entry_p valid on all of them unless reported; "
          "%d answered by the stored paths" % (nsol, nfall))

    # 3. Soundness on random passing instances.
    #
    m, answered = 0, 0
    while m < 20 * n:
        R, C = rng.randint(11, 16), rng.randint(11, 16)
        cells = rng.sample([(r, c) for r in range(R) for c in range(C)], 4)
        if fires(R, C, *cells) is not None:
            continue
        I = Instance(R, C, *cells)
        m += 1
        s = look.look_j(I)
        if s is not None:
            answered += 1
            if not check_solution(I, s):
                print("FAIL: invalid answer on %r" % (I,))
                bad += 1
    print("random passing instances: %d, answered %d, every answer valid unless reported" % (m, answered))
    print("FAILED %d" % bad if bad else "ALL PASSED")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
