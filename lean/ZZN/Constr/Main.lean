-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Statement
import ZZN.Constr.Solve
import ZZN.Constr.ThinWit

/-!
# The construction

`solveZZN I` returns two paths for every solvable instance and only solutions.

* `solveZZN_sound`: every answer is a solution (standard axioms only).
* `solveZZN_complete`: for a well-formed solvable instance, it returns an answer. This rests on
  `passes_iff_solvable` (Theorem A and Theorem B).
-/

namespace ZZN

open GridHam

theorem thinOK : ThinOK Thin.thinSolveW := by
  intro J hwf hS _
  obtain ⟨⟨p, q⟩, h⟩ := Option.isSome_iff_exists.1 (Thin.thinSolveW_complete hwf hS)
  exact ⟨p, q, h, Thin.thinSolveW_sound h⟩


theorem solveZZN_sound {I : Inst} {p q : List Coord} (h : solveZZN I = some (p, q)) :
    IsSolution I p q := solveZ_sound _ h

theorem solveZZN_complete {I : Inst} (hwf : I.WellFormed) (hS : Solvable I) :
    ∃ p q, solveZZN I = some (p, q) := solveZ_complete thinOK hwf hS

end ZZN
