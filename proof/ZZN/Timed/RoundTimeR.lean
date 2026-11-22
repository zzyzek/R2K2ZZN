/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.RoundTime
public import ZZN.Timed.ThinRopeCost

@[expose] public section

/-!
# The block construction with the tree-segment plug DP

`solveZ3T thinSolveWRT` is the counted block construction (`Timed/RoundT.lean`) with the plug DP
of `Timed/ThinRope.lean` at the leaves. That DP returns the same answers as `thinSolveWT`
(`thinSolveWRT_ret`), so soundness and completeness carry over; it takes `(R C + 1) KwR b` steps
(`thinSolveWRT_time`), linear in the area. A leaf with a side at most `10` then costs
`O(M KwR 10 + M²)`, and the bound becomes
`37 (80 (M + 1)² + 400) + (10 M + 1) KwR 10 + 3 (10 M + 1)² + 10 + const` (`solveZ3RT_main`).
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-- A leaf with a side at most 10: the thin solver runs once, then the answer is checked. -/
theorem solveZT_thinR_time {J : Inst} (hwf : J.WellFormed) (hs : J.w ≤ 10 ∨ J.h ≤ 10) :
    (solveZT thinSolveWRT J).time ≤ (J.w * J.h + 1) * KwR 10 + 3 * (J.w * J.h + 1) ^ 2 + 10 := by
  unfold solveZT
  rw [ite_t ((wfB_iff J).2 hwf)]
  have h1 : 1 ≤ J.w := by have := hwf.1; unfold InBounds at this; omega
  obtain ⟨n, hn⟩ : ∃ n, J.w + J.h = n + 1 := ⟨J.w + J.h - 1, by omega⟩
  rw [hn]
  simp only [solveRecT, ite_t hs, time_bind]
  have t := thinSolveWRT_time J
  have k : KwR (min J.w J.h) ≤ KwR 10 := KwR_mono (by omega)
  have c := checkET_time J (thinSolveWRT J).ret (J.w * J.h) (fun x hx => by
    rw [thinSolveWRT_ret] at hx; exact thinSolveW_len J x hx)
  have := Nat.mul_le_mul_left (J.w * J.h + 1) k
  omega

/-- A leaf with both sides at most 37: the step bound of `solveZ2` at `M = 37`. -/
theorem solveZT_boxR_time {J : Inst} (hw : J.w ≤ 37) (hh : J.h ≤ 37) :
    (solveZT thinSolveWRT J).time ≤
      74 * (700 * (37 + 1) ^ 2) + ((16 * 37 + 1) * KwR 16 + 3 * (16 * 37 + 1) ^ 2 + 10) := by
  have h := solveZT_time thinSolveWRT_ret thinSolveW_len 37 ((16 * 37 + 1) * KwR 16)
    (fun J' a b c => by
      have t := thinSolveWRT_time J'
      have k : KwR (min J'.w J'.h) ≤ KwR 16 := KwR_mono (by omega)
      have area : J'.w * J'.h ≤ 16 * 37 := by
        rcases c with c | c
        · exact Nat.mul_le_mul c b
        · rw [Nat.mul_comm]; exact Nat.mul_le_mul c a
      exact le_trans t (Nat.mul_le_mul (by omega) k)) J hw hh
  exact le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)

/-- **The block construction with the tree-segment plug DP, counted.** Every answer is a
solution, it returns one for every well-formed solvable instance, and on a `w × h` instance with
`M = max w h` it takes `O(M²)` steps. -/
theorem solveZ3RT_main (I : Inst) :
    (∀ p q, (solveZ3T thinSolveWRT I).ret = some (p, q) → IsSolution I p q) ∧
    (I.WellFormed → Solvable I → ∃ p q, (solveZ3T thinSolveWRT I).ret = some (p, q)) ∧
    (solveZ3T thinSolveWRT I).time ≤ 37 * (80 * (max I.w I.h + 1) ^ 2 + 400) +
      ((10 * max I.w I.h + 1) * KwR 10 + 3 * (10 * max I.w I.h + 1) ^ 2 + 10) +
      (74 * (700 * (37 + 1) ^ 2) + ((16 * 37 + 1) * KwR 16 + 3 * (16 * 37 + 1) ^ 2 + 10)) := by
  refine ⟨fun p q h => solveZ3_sound _ (by rw [← solveZ3T_ret thinSolveWRT_ret]; exact h),
    fun hwf hS => by rw [solveZ3T_ret thinSolveWRT_ret]; exact solveZ3_complete thinOK16 hwf hS, ?_⟩
  set M := max I.w I.h
  set B := 74 * (700 * (37 + 1) ^ 2) + ((16 * 37 + 1) * KwR 16 + 3 * (16 * 37 + 1) ^ 2 + 10)
  set T := (10 * M + 1) * KwR 10 + 3 * (10 * M + 1) ^ 2 + 10
  unfold solveZ3T
  by_cases hwf : I.WellFormed
  · rw [ite_t ((wfB_iff I).2 hwf)]
    have h := solveRT_time thinSolveWRT_ret M (T + B)
      (fun J hJ a b c => by
        rcases c with c | ⟨c1, c2⟩
        · have t := solveZT_thinR_time hJ c
          have area : J.w * J.h ≤ 10 * M := by
            rcases c with c | c
            · exact Nat.mul_le_mul c b
            · have := Nat.mul_le_mul a c; rw [Nat.mul_comm M 10] at this; exact this
          have s : (J.w * J.h + 1) ^ 2 ≤ (10 * M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have s1 := Nat.mul_le_mul_right (KwR 10) (show J.w * J.h + 1 ≤ 10 * M + 1 by omega)
          have s3 := Nat.mul_le_mul_left 3 s
          exact le_trans t (Nat.le_add_right_of_le (by omega))
        · exact le_trans (solveZT_boxR_time c1 c2) (Nat.le_add_left _ _))
      (I.w + I.h) I hwf (le_max_left _ _) (le_max_right _ _)
    have hp := phi_le I
    have : (phi I + 1) * (80 * (M + 1) ^ 2 + 400) ≤ 37 * (80 * (M + 1) ^ 2 + 400) :=
      Nat.mul_le_mul_right _ (by omega)
    clear_value T B
    generalize 80 * (M + 1) ^ 2 + 400 = C at h this ⊢
    generalize (phi I + 1) * C = X at h this
    generalize (solveRT thinSolveWRT (I.w + I.h) I).time = Y at h ⊢
    omega
  · rw [ite_f (fun h => hwf ((wfB_iff I).1 h))]
    simp

end ZZN.T
