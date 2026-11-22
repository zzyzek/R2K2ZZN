# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Evaluate the step constants of the paper (Section "Step counts").

A transcription of `wcnt`, `Nw` (proof/ZZN/Timed/ThinWord.lean) and `LgW`, `KsR`, `KwR`
(proof/ZZN/Timed/ThinRopeCost.lean). Lean does not evaluate these at b = 10 or b = 16. The values
at b = 2 and b = 3 were evaluated in Lean with `#eval` and are checked below.

    python3 paper/tools/kwr.py
"""
from functools import lru_cache


@lru_cache(None)
def wcnt(m, d, u, v):
  if m == 0:
    return ((2 if u == 0 else 1) * (2 if v == 0 else 1)) if d == 0 else 0
  r = wcnt(m - 1, d, u, v) + wcnt(m - 1, d + 1, u, v)
  if d > 0: r += wcnt(m - 1, d - 1, u, v)
  if u < 2: r += wcnt(m - 1, d, u + 1, v)
  if v < 2: r += wcnt(m - 1, d, u, v + 1)
  return r


def Nw(b):  return wcnt(b + 1, 0, 0, 0)


# Nat.log2 n + 1, with Nat.log2 n = floor(log2 n) for n >= 1.
#
def LgW(b): return (2 * Nw(b)).bit_length() - 1 + 1


def KsR(b):
  N = Nw(b)
  return ( 4 + N * (9 * (b + 1) + 31) + 2 * N * (b + 3) +
           (2 * N + 1 + ((b + 8) * (2 * N) * (LgW(b) + 1) + 1) + 2 * N * (b + 3)) )


def KwR(b): return KsR(b) + 2 * Nw(b) + 30


# Values printed by Lean's #eval.
#
assert (Nw(2), KwR(2), Nw(3), KwR(3)) == (64, 16804, 202, 63666)

K10, K16 = KwR(10), KwR(16)
BL = 74 * 700 * 38**2 + (37 * 10 + 1) * K10 + 28000000 + 3 * (16 * 37 + 1)**2 + 10
BR = 74 * 700 * 38**2 + (16 * 37 + 1) * K16 + 3 * (16 * 37 + 1)**2 + 10
print("N(10) =", Nw(10), " K(10) =", K10)
print("N(16) =", Nw(16), " K(16) =", K16, f"({K16:.3e})")
print("C = K(10) + 300000 =", K10 + 300000)
print("B_L =", BL, f"({BL:.3e})", " B_R =", BR, f"({BR:.3e})")
# 37 (80 (M+1)^2 + 400) + (10M+1) K(10) + 3 (10M+1)^2 + 10 + B_L, expanded in M.
#
print("M^2:", 37 * 80 + 300, " M:", 37 * 160 + 10 * K10 + 60,
      " constant:", 37 * 480 + K10 + 3 + 10 + BL, f"({37 * 480 + K10 + 13 + BL:.4e})")
