-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Statement
import ZZN.Catalogue
import Mathlib.Data.Nat.Pairing

/-!
# The plug DP for thin rectangles (copied from the window DP, `WinCheck.lean`)

Pieces are coded with `Nat.pair` instead of `32 x + y`, so the long side is unbounded.

# Window certificates: the computation

A port of the window-certificate program used during development, written to be evaluated by the
kernel and reasoned about.

Window `W` = rows `0 … a−1`, columns `0 … b−1` at the top-left corner. Cells are processed in
row-major order. A partial covering is abstracted to its **pieces**: maximal runs of processed
cells along a solution path, each with two **ends**, coded as naturals:
- `c` (`c < b`): a plug down from column `c` into the next row;
- `b`: a plug right, into the next cell of the row;
- `b + 1 + s`: exit slot `s` (`s < a`: right of row `s`; `s = a + j`: below column `b − 1 − j`);
- `a + 2b + 1 + col`: an endpoint of colour `col`.
A piece is the code `32 x + y` of its ends `x ≤ y` (all ends are below 32 for `a, b ≤ 8`).
A state is the sorted list of piece codes and a bitmask of the colours whose path is complete.
-/

namespace ZZN.Thin



def isExit (a b e : ℕ) : Bool := decide (b + 1 ≤ e) && decide (e < a + 2 * b + 1)














/-- All final states: the inside signatures of the window. -/
def inside (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : List St :=
  (List.range (a * b)).foldl (stage a b tm) [([], 0)]


end ZZN.Thin
