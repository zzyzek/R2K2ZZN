/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.Main
public import ZZN.Timed.ThinRopeCost
public import ZZN.Timed.Construct

@[expose] public section

/-!
# The decision procedure with the tree-segment plug DP

`solvableBRT`: the forbidden-pattern catalogue when both sides are at least 11 (as `solvableBT`),
otherwise the tree-segment plug DP `thinSolveWRT` of `Timed/ThinRope.lean`, answering whether it
finds a solution. `solvableBRT_main`: on a well-formed instance it answers `true` exactly when the
instance is solvable, within `CdecR · (w h + w + h + 1)` steps, `CdecR = KwR 10 + 300000`.
-/

namespace ZZN.T

open ZZN ZZN.Thin

def solvableBRT (J : Inst) : TimeM Bool :=
  if 11 ≤ J.w ∧ 11 ≤ J.h then do
    let f ← fires3T J.w J.h J.s0 J.t0 J.s1 J.t1
    pure !f
  else do
    let o ← thinSolveWRT J
    pure o.isSome

/-- The constant of the decision procedure. -/
def CdecR : ℕ := KwR 10 + 300000

theorem solvableBRT_iff {J : Inst} (hwf : J.WellFormed) :
    (solvableBRT J).ret = true ↔ Solvable J := by
  unfold solvableBRT
  split
  · rename_i h
    have := fires3T_iff_solvable hwf h.1 h.2
    simp only [ret_bind, ret_pure, Bool.not_eq_true']
    exact this
  · simp only [ret_bind, ret_pure, thinSolveWRT_ret]
    constructor
    · intro hs
      obtain ⟨⟨p, q⟩, h⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨p, q, thinSolveW2_sound h⟩
    · exact thinSolveW2_complete hwf

theorem solvableBRT_time (J : Inst) :
    (solvableBRT J).time ≤ CdecR * (J.w * J.h + J.w + J.h + 1) := by
  unfold solvableBRT
  have hC : CdecR = KwR 10 + 300000 := rfl
  split
  · simp only [time_bind, time_pure]
    have h1 := fires3T_time J.w J.h J.s0 J.t0 J.s1 J.t1
    rw [hC]
    generalize KwR 10 = K
    generalize (fires3T J.w J.h J.s0 J.t0 J.s1 J.t1).time = F at h1 ⊢
    have h2 : 300000 * (J.w + J.h + 1) ≤ (K + 300000) * (J.w * J.h + J.w + J.h + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact le_trans (Nat.add_le_add_right h1 _) (by simpa using h2)
  · rename_i h
    simp only [time_bind, time_pure]
    have t := thinSolveWRT_time J
    have k : KwR (min J.w J.h) ≤ KwR 10 := KwR_mono (by omega)
    rw [hC]
    generalize KwR (min J.w J.h) = k0 at t k
    generalize KwR 10 = K at k ⊢
    have e1 := Nat.mul_le_mul_left (J.w * J.h + 1) k
    have e2 : (J.w * J.h + 1) * K ≤ (K + 300000) * (J.w * J.h + J.w + J.h + 1) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
    omega

/-- **Feasibility, counted.** For a well-formed instance the counted decision procedure answers
`true` exactly when the instance is solvable, within `CdecR · (w h + w + h + 1)` steps. -/
theorem solvableBRT_main {J : Inst} (hwf : J.WellFormed) :
    ((solvableBRT J).ret = true ↔ Solvable J) ∧
      (solvableBRT J).time ≤ CdecR * (J.w * J.h + J.w + J.h + 1) :=
  ⟨solvableBRT_iff hwf, solvableBRT_time J⟩

end ZZN.T
