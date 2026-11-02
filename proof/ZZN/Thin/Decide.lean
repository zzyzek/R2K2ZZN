/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Statement
public import ZZN.Main
public import ZZN.Thin.Fast

@[expose] public section

/-!
# A decision procedure for every rectangle

Both sides at least 11: the catalogue (`passes_iff_solvable`). Otherwise: the plug DP with the
short side as the frontier (`thinBF_iff`).
-/

namespace ZZN

open Thin


/-- **Solvability of two-colour Zig-Zag Numberlink on rectangles is decided by `solvableB`.** -/
theorem solvableB_iff {J : Inst} (hwf : J.WellFormed) : solvableB J = true ↔ Solvable J := by
  unfold solvableB
  split_ifs with h
  · rw [← passes_iff_solvable J hwf h.1 h.2]
    unfold Passes
    simp
  · exact thinBF_iff hwf

end ZZN
