-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Main
import ZZN.Thin.Fast

/-!
# A decision procedure for every rectangle

Both sides at least 11: the catalogue (`passes_iff_solvable`). Otherwise: the plug DP with the
short side as the frontier (`thinBF_iff`).
-/

namespace ZZN

open Thin

def solvableB (J : Inst) : Bool :=
  if 11 ≤ J.w ∧ 11 ≤ J.h then !(fires3 J.w J.h J.s0 J.t0 J.s1 J.t1) else thinBF J

/-- **Solvability of two-colour Zig-Zag Numberlink on rectangles is decided by `solvableB`.** -/
theorem solvableB_iff {J : Inst} (hwf : J.WellFormed) : solvableB J = true ↔ Solvable J := by
  unfold solvableB
  split_ifs with h
  · rw [← passes_iff_solvable J hwf h.1 h.2]
    unfold Passes
    simp
  · exact thinBF_iff hwf

end ZZN
