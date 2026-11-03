/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Thin.Decide
public import ZZN.Timed.CatalogueCost
public import ZZN.Timed.ThinCost

@[expose] public section

/-!
# The decision procedure runs in polynomial time

`solvableBT` is the decision procedure `solvableB` (`ZZN/Statement.lean`; lemmas in
`ZZN/Thin/Decide.lean`) with its steps counted: the catalogue test when both sides are at least 11, the plug DP otherwise.

* `solvableBT_ret`: it returns what `solvableB` returns.
* `solvableBT_time`: it takes at most `Cdec · (R C + R + C + 1)` counted steps. This uses only
  the standard axioms. The constant `Cdec` comes from a crude count of plug DP states on a strip
  of width at most 10 (`ThinCount.lean`) and is astronomically large, but it is a constant.
* `solvableBT_main`: for a well-formed instance, the answer is `true` exactly when the instance is
  solvable, within that number of steps. Correctness rests on `solvableB_iff`.

What counts as a step is fixed by the cost table in `ZZN/Timed/TimeM.lean`. Arithmetic on
numbers is charged as constant time.
-/

namespace ZZN.T

open ZZN ZZN.Thin


@[simp] lemma solvableBT_ret (J : Inst) : (solvableBT J).ret = solvableB J := by
  unfold solvableBT solvableB
  split <;> simp

lemma Q_mono {b b' : ℕ} (h : b ≤ b') : Q b ≤ Q b' := by unfold Q; exact Nat.pow_le_pow_left (by omega) 2

lemma Nst_mono {b b' : ℕ} (h : b ≤ b') : Nst b ≤ Nst b' := by
  unfold Nst
  have hq := Q_mono h
  have : (Q b + 1) ^ Q b ≤ (Q b' + 1) ^ Q b := Nat.pow_le_pow_left (by omega) _
  have : (Q b' + 1) ^ Q b ≤ (Q b' + 1) ^ Q b' := Nat.pow_le_pow_right (by omega) hq
  omega

lemma Kst_mono {b b' : ℕ} (h : b ≤ b') : Kst b ≤ Kst b' := by
  unfold Kst
  have hq := Q_mono h
  have hn := Nst_mono h
  have : Nst b * (6 * Q b + 19) ≤ Nst b' * (6 * Q b' + 19) := Nat.mul_le_mul hn (by omega)
  have : Nst b ^ 2 ≤ Nst b' ^ 2 := Nat.pow_le_pow_left hn 2
  have : 2 * Nst b * (Q b + 2) ≤ 2 * Nst b' * (Q b' + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) (by omega)
  omega


/-- **The decision procedure takes polynomially many steps** (standard axioms only). -/
theorem solvableBT_time (J : Inst) : (solvableBT J).time ≤ Cdec * (J.w * J.h + J.w + J.h + 1) := by
  unfold solvableBT
  split
  · simp only [time_bind, time_pure]
    have h1 := fires3T_time J.w J.h J.s0 J.t0 J.s1 J.t1
    have h2 : 300000 * (J.w + J.h + 1) ≤ Cdec * (J.w * J.h + J.w + J.h + 1) :=
      Nat.mul_le_mul (by unfold Cdec; omega) (by omega)
    omega
  · rename_i h
    have hm : min J.w J.h ≤ 10 := by omega
    have h1 := thinBFT_time J
    have k := Kst_mono hm
    have n := Nst_mono hm
    generalize Kst (min J.w J.h) = k0 at *
    generalize Nst (min J.w J.h) = n0 at *
    have hC : Kst 10 + 2 + (Nst 10 + 1) ≤ Cdec := by unfold Cdec; omega
    generalize J.w * J.h = A at *
    have e1 : (A + 1) * (k0 + 2) ≤ (A + 1) * (Kst 10 + 2) := Nat.mul_le_mul_left _ (by omega)
    have e2 : n0 + 1 ≤ (A + 1) * (Nst 10 + 1) := by nlinarith
    have e3 : (A + 1) * (Kst 10 + 2) + (A + 1) * (Nst 10 + 1) ≤ (A + 1) * Cdec := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hC
    have e4 : (A + 1) * Cdec ≤ Cdec * (A + J.w + J.h + 1) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega

/-- **Main theorem with a time bound.** For a well-formed instance, the counted decision procedure
answers `true` exactly when the instance is solvable, within `Cdec · (R C + R + C + 1)` steps. -/
theorem solvableBT_main {J : Inst} (hwf : J.WellFormed) :
    ((solvableBT J).ret = true ↔ Solvable J) ∧
      (solvableBT J).time ≤ Cdec * (J.w * J.h + J.w + J.h + 1) :=
  ⟨by rw [solvableBT_ret]; exact solvableB_iff hwf, solvableBT_time J⟩

/-- **The characterization, counted.** On rectangles with both sides at least 11, a well-formed
instance is solvable exactly when the counted forbidden-pattern catalogue `fires3T` finds no
pattern. -/
theorem fires3T_iff_solvable {J : Inst} (hwf : J.WellFormed) (hw : 11 ≤ J.w) (hh : 11 ≤ J.h) :
    (fires3T J.w J.h J.s0 J.t0 J.s1 J.t1).ret = false ↔ Solvable J := by
  rw [← (solvableBT_main hwf).1]
  simp [solvableBT, hw, hh, ret_bind, ret_pure]

end ZZN.T
