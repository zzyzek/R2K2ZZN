/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Constr.Main
public import ZZN.Timed.Solve
public import ZZN.Timed.ThinWitCost

@[expose] public section

/-!
# The step bound of the construction

`solveZZNT` counts the steps of `solveZ2 Thin.thinSolveW2` (`ZZN/Constr/Solve2.lean`,
`ZZN/Constr/ThinWit2.lean`): the construction of `solveZZN` with band compressions as a second
kind of reduction, no check after a lift, and duplicate DP states removed by sorting. On a `w × h` instance with `M = max w h` it takes at most
`700 (w + h) (M + 1)² + (16 M + 1)² (Kw 16 + 3) + 10` steps (`solveZZNT_time`), a polynomial of
degree 3 in `M`. Each of the at most `w + h` levels finds a reduction and lifts the smaller solution
by the one-pass band extension (`bandExtLT`, `O(M²)` steps). The thin solver runs once, on an
instance with a side at most 10 or both sides at most 16 (`leaf16`), so on an area at most `16 M`.

Completeness rests on `passes_iff_solvable`; `solveZZNT_time` and soundness do not.
-/

namespace ZZN.T

open ZZN GridHam


theorem solveZZNT_ret (I : Inst) : (solveZZNT I).ret = solveZ2 Thin.thinSolveW2 I :=
  solveZT_ret thinSolveWT_ret I

lemma thinSolveW_len (J : Inst) (x : List Coord × List Coord) (h : Thin.thinSolveW2 J = some x) :
    x.1.length + x.2.length ≤ J.w * J.h :=
  le_of_eq (solB_len (solB_complete (Thin.thinSolveW2_sound (p := x.1) (q := x.2) h)))

theorem thinOK16 : ThinOK16 Thin.thinSolveW2 := by
  intro J hwf hS _
  obtain ⟨⟨p, q⟩, h⟩ := Option.isSome_iff_exists.1 (Thin.thinSolveW2_complete hwf hS)
  exact ⟨p, q, h, Thin.thinSolveW2_sound h⟩

/-- **The step bound of the construction.** -/
theorem solveZZNT_time (I : Inst) :
    (solveZZNT I).time ≤ 700 * (I.w + I.h) * (max I.w I.h + 1) ^ 2 +
      (16 * max I.w I.h + 1) ^ 2 * (Kw 16 + 3) + 10 := by
  set M := max I.w I.h
  have h := solveZT_time thinSolveWT_ret thinSolveW_len M ((16 * M + 1) ^ 2 * Kw 16) (fun J a b c => ?_) I
    (le_max_left _ _) (le_max_right _ _)
  · show (solveZT thinSolveWT I).time ≤ _
    generalize Kw 16 = K at h ⊢
    generalize (solveZT thinSolveWT I).time = T at h ⊢
    refine le_of_le_of_eq h ?_
    ring
  · have t := thinSolveWT_time J
    have k : Kw (min J.w J.h) ≤ Kw 16 := Kw_mono (by omega)
    have area : J.w * J.h ≤ 16 * M := by
      rcases c with c | c
      · exact Nat.mul_le_mul c b
      · rw [Nat.mul_comm]; exact Nat.mul_le_mul c a
    have s : (J.w * J.h + 1) ^ 2 ≤ (16 * M + 1) ^ 2 := sq_mono (by omega)
    exact le_trans t (Nat.mul_le_mul s k)

/-- **The construction, counted.** Every answer of `solveZZNT` is a solution, it returns one for
every well-formed solvable instance, and it takes polynomially many steps. -/
theorem solveZZNT_main (I : Inst) :
    (∀ p q, (solveZZNT I).ret = some (p, q) → IsSolution I p q) ∧
    (I.WellFormed → Solvable I → ∃ p q, (solveZZNT I).ret = some (p, q)) ∧
    (solveZZNT I).time ≤ 700 * (I.w + I.h) * (max I.w I.h + 1) ^ 2 +
      (16 * max I.w I.h + 1) ^ 2 * (Kw 16 + 3) + 10 :=
  ⟨fun _ _ h => solveZ2_sound _ (by rw [← solveZZNT_ret]; exact h),
   fun hwf hS => by rw [solveZZNT_ret]; exact solveZ2_complete thinOK16 hwf hS,
   solveZZNT_time I⟩

end ZZN.T
