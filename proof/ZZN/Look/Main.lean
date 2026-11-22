/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Look.Complete
public import ZZN.Look.Table
public import ZZN.Timed.Construct

@[expose] public section

/-!
# The construction with lookup leaves is sound and complete

`solveZ3 (leafL thinSolveW2 tabAll)`: the block construction whose leaves with a side at most 10 go
to the plug DP and whose irreducible leaves with sides 11–16 go to the certificate lookup.
-/

namespace ZZN

open GridHam ZZN.Look

theorem solveZ3L_main (I : Inst) :
    (∀ p q, solveZ3 (leafL Thin.thinSolveW2 tabAll) I = some (p, q) → IsSolution I p q) ∧
    (I.WellFormed → Solvable I → ∃ p q, solveZ3 (leafL Thin.thinSolveW2 tabAll) I = some (p, q)) :=
  ⟨fun _ _ h => solveZ3_sound _ h,
   fun hwf hS => solveZ3_completeL (leafL_ok T.thinOK16 tabAll_ok) hwf hS⟩

end ZZN
