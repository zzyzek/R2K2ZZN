-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Constr.Main
import ZZN.Timed.Solve
import ZZN.Timed.ThinWitCost

/-!
# The step bound of the construction

`solveZZNT` counts the steps of `solveZZN`. On a `w × h` instance with `M = max w h` it takes at
most `(w + h + 1) (1100 (M + 1)⁴ + (M² + 1)² Kw 22 + 10)` steps (`solveZZNT_time`), a polynomial
of degree 5 in `M`. The constant `Kw 22` comes from the crude state count of the thin solver and
is astronomically large.

`solveZZNT_time` and `solveZZN_sound` use only the standard axioms. `solveZZN_complete` uses the
`native_decide` axioms of the finite case analyses.
-/

namespace ZZN.T

open ZZN GridHam

def solveZZNT (I : Inst) : TimeM Sol := solveZT thinSolveWT I

theorem solveZZNT_ret (I : Inst) : (solveZZNT I).ret = solveZZN I :=
  solveZT_ret thinSolveWT_ret I

lemma thinSolveW_len (J : Inst) (x : List Coord × List Coord) (h : Thin.thinSolveW J = some x) :
    x.1.length + x.2.length ≤ J.w * J.h :=
  le_of_eq (solB_len (solB_complete (Thin.thinSolveW_sound (p := x.1) (q := x.2) h)))

/-- **The step bound of the construction.** -/
theorem solveZZNT_time (I : Inst) :
    (solveZZNT I).time ≤ (I.w + I.h + 1) *
      (1100 * ((max I.w I.h + 1) ^ 2) ^ 2 + (max I.w I.h * max I.w I.h + 1) ^ 2 * Kw 22 + 10) := by
  set M := max I.w I.h
  refine solveZT_time thinSolveWT_ret thinSolveW_len M _ (fun J a b c => ?_) I
    (le_max_left _ _) (le_max_right _ _)
  have t := thinSolveWT_time J
  have k : Kw (min J.w J.h) ≤ Kw 22 := Kw_mono (by omega)
  have s : (J.w * J.h + 1) ^ 2 ≤ (M * M + 1) ^ 2 := sq_mono (by have := Nat.mul_le_mul a b; omega)
  exact le_trans t (Nat.mul_le_mul s k)

end ZZN.T
