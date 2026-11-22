/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.RoundTimeR
public import ZZN.Look.Table

@[expose] public section

/-!
# The block construction with lookup leaves, counted

`leafLT`: the tree-segment plug DP (`thinSolveWRT`) on a side at most 10, the counted certificate
lookup (`lookJT tabAll`) on other well-formed instances. `solveZ3LT_main`: the block construction
with these leaves is sound, complete, and on a `w × h` instance with `M = max w h` takes at most
`37 (80 (M + 1)² + 400) + (10 M + 1) KwR 10 + 3 (10 M + 1)² + 10 + const` steps, where the constant
is `74 · 700 · 38² + (371 KwR 10 + 28 000 000) + 3 · 593² + 10`.
-/

namespace ZZN.T

open ZZN ZZN.Thin ZZN.Look GridHam

noncomputable def leafLT (J : Inst) : TimeM Sol :=
  if J.w ≤ 10 ∨ J.h ≤ 10 then thinSolveWRT J
  else if J.WellFormed then lookJT tabAll J else pure none

theorem leafLT_ret (J : Inst) : (leafLT J).ret = leafL Thin.thinSolveW2 tabAll J := by
  unfold leafLT leafL
  split_ifs
  · exact thinSolveWRT_ret J
  · exact lookJT_ret tabAll J
  · rfl

theorem isSolution_len {I : Inst} {p q : List Coord} (hS : IsSolution I p q) :
    p.length + q.length = I.w * I.h :=
  solB_len (solB_complete hS)

theorem leafL_len (J : Inst) (x : List Coord × List Coord)
    (h : leafL Thin.thinSolveW2 tabAll J = some x) : x.1.length + x.2.length ≤ J.w * J.h := by
  unfold leafL at h
  split_ifs at h with h1 h2
  · exact thinSolveW_len J x h
  · exact le_of_eq (isSolution_len (lookJ_sound tabAll h2 h))

theorem leafLT_time (J : Inst) :
    (leafLT J).time ≤ (J.w * J.h + 1) * KwR (min J.w J.h) + 28000000 := by
  unfold leafLT
  split_ifs
  · have := thinSolveWRT_time J; omega
  · have := lookJT_time tabAll_sz J; omega
  · simp

/-- A leaf with a side at most 10. -/
theorem solveZT_thinL_time {J : Inst} (hwf : J.WellFormed) (hs : J.w ≤ 10 ∨ J.h ≤ 10) :
    (solveZT leafLT J).time ≤ (J.w * J.h + 1) * KwR 10 + 3 * (J.w * J.h + 1) ^ 2 + 10 := by
  unfold solveZT
  rw [ite_t ((wfB_iff J).2 hwf)]
  have h1 : 1 ≤ J.w := by have := hwf.1; unfold InBounds at this; omega
  obtain ⟨n, hn⟩ : ∃ n, J.w + J.h = n + 1 := ⟨J.w + J.h - 1, by omega⟩
  rw [hn]
  simp only [solveRecT, ite_t hs, time_bind]
  have e : leafLT J = thinSolveWRT J := by unfold leafLT; rw [ite_t hs]
  rw [e]
  have t := thinSolveWRT_time J
  have k : KwR (min J.w J.h) ≤ KwR 10 := KwR_mono (by omega)
  have c := checkET_time J (thinSolveWRT J).ret (J.w * J.h) (fun x hx => by
    rw [thinSolveWRT_ret] at hx; exact thinSolveW_len J x hx)
  have := Nat.mul_le_mul_left (J.w * J.h + 1) k
  omega

/-- A leaf with both sides at most 37. -/
theorem solveZT_boxL_time {J : Inst} (hw : J.w ≤ 37) (hh : J.h ≤ 37) :
    (solveZT leafLT J).time ≤
      74 * (700 * (37 + 1) ^ 2) + (((10 * 37 + 1) * KwR 10 + 28000000) + 3 * (16 * 37 + 1) ^ 2 + 10) := by
  have h := solveZT_time leafLT_ret leafL_len 37 ((10 * 37 + 1) * KwR 10 + 28000000)
    (fun J' a b _ => by
      unfold leafLT
      split_ifs with hs
      · have t := thinSolveWRT_time J'
        have k : KwR (min J'.w J'.h) ≤ KwR 10 := KwR_mono (by omega)
        have area : J'.w * J'.h ≤ 10 * 37 := by
          rcases hs with c | c
          · exact Nat.mul_le_mul c b
          · rw [Nat.mul_comm]; exact Nat.mul_le_mul c a
        have := Nat.mul_le_mul (show J'.w * J'.h + 1 ≤ 10 * 37 + 1 by omega) k
        omega
      · have := lookJT_time tabAll_sz J'; omega
      · simp) J hw hh
  exact le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)

/-- **The block construction with lookup leaves, counted.** Every answer is a solution, it returns
one for every well-formed solvable instance, and on a `w × h` instance with `M = max w h` it takes
`O(M²)` steps with the constants shown. -/
theorem solveZ3LT_main (I : Inst) :
    (∀ p q, (solveZ3T leafLT I).ret = some (p, q) → IsSolution I p q) ∧
    (I.WellFormed → Solvable I → ∃ p q, (solveZ3T leafLT I).ret = some (p, q)) ∧
    (solveZ3T leafLT I).time ≤ 37 * (80 * (max I.w I.h + 1) ^ 2 + 400) +
      ((10 * max I.w I.h + 1) * KwR 10 + 3 * (10 * max I.w I.h + 1) ^ 2 + 10) +
      (74 * (700 * (37 + 1) ^ 2) +
        (((10 * 37 + 1) * KwR 10 + 28000000) + 3 * (16 * 37 + 1) ^ 2 + 10)) := by
  refine ⟨fun p q h => solveZ3_sound _ (by rw [← solveZ3T_ret leafLT_ret]; exact h),
    fun hwf hS => by
      rw [solveZ3T_ret leafLT_ret]
      exact solveZ3_completeL (leafL_ok thinOK16 tabAll_ok) hwf hS, ?_⟩
  set M := max I.w I.h
  set B := 74 * (700 * (37 + 1) ^ 2) +
    (((10 * 37 + 1) * KwR 10 + 28000000) + 3 * (16 * 37 + 1) ^ 2 + 10)
  set T := (10 * M + 1) * KwR 10 + 3 * (10 * M + 1) ^ 2 + 10
  unfold solveZ3T
  by_cases hwf : I.WellFormed
  · rw [ite_t ((wfB_iff I).2 hwf)]
    have h := solveRT_time leafLT_ret M (T + B)
      (fun J hJ a b c => by
        rcases c with c | ⟨c1, c2⟩
        · have t := solveZT_thinL_time hJ c
          have area : J.w * J.h ≤ 10 * M := by
            rcases c with c | c
            · exact Nat.mul_le_mul c b
            · have := Nat.mul_le_mul a c; rw [Nat.mul_comm M 10] at this; exact this
          have s : (J.w * J.h + 1) ^ 2 ≤ (10 * M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have s1 := Nat.mul_le_mul_right (KwR 10) (show J.w * J.h + 1 ≤ 10 * M + 1 by omega)
          have s3 := Nat.mul_le_mul_left 3 s
          exact le_trans t (Nat.le_add_right_of_le (by omega))
        · exact le_trans (solveZT_boxL_time c1 c2) (Nat.le_add_left _ _))
      (I.w + I.h) I hwf (le_max_left _ _) (le_max_right _ _)
    have hp := phi_le I
    have : (phi I + 1) * (80 * (M + 1) ^ 2 + 400) ≤ 37 * (80 * (M + 1) ^ 2 + 400) :=
      Nat.mul_le_mul_right _ (by omega)
    clear_value T B
    generalize 80 * (M + 1) ^ 2 + 400 = C at h this ⊢
    generalize (phi I + 1) * C = X at h this
    generalize (solveRT leafLT (I.w + I.h) I).time = Y at h ⊢
    omega
  · rw [ite_f (fun h => hwf ((wfB_iff I).1 h))]
    simp

end ZZN.T
