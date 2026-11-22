/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Timed.Lift

@[expose] public section

/-!
# The counted construction

`solveRecT thinT` counts the steps of `solveRec thin`, given a counted thin solver `thinT`
with `(thinT J).ret = thin J`. If the thin solver takes at most `B` steps on every instance with
sides at most `M` and one side at most 22, then the construction takes at most
`(w + h + 1) (1100 Q² + B + 10)` steps on a `w × h` instance with `w, h ≤ M`, where
`Q = (M + 1)²` (`solveZT_time`).
-/

namespace ZZN.T

open ZZN GridHam


lemma sq_mono {a b : ℕ} (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h 2

lemma checkET_time (I : Inst) (o : Sol) (L : ℕ)
    (h : ∀ x, o = some x → x.1.length + x.2.length ≤ L) :
    (checkET I o).time ≤ 3 * (L + 1) ^ 2 + 10 := by
  cases o with
  | none => simp [checkET]
  | some x =>
    have a := solBT_time I x.1 x.2
    have b := sq_mono (by have := h x rfl; omega : x.1.length + x.2.length + 1 ≤ L + 1)
    simp only [checkET, time_bind, time_pure]
    omega


lemma swapT_ret (l : List Coord) : (swapT l).ret = l.map Prod.swap := by
  simp [swapT, lmapT]

lemma swapT_time (l : List Coord) : (swapT l).time ≤ l.length := by
  have := lmapT_time_le (fun x : Coord => (pure x.swap : TimeM Coord)) l 0 (fun _ _ => by simp)
  simpa [swapT] using this





section

variable {thinT : Inst → TimeM Sol} {thin : Inst → Sol}

theorem solveRecT_ret (hret : ∀ J, (thinT J).ret = thin J) :
    ∀ (n : ℕ) (I : Inst), (solveRecT thinT n I).ret = solveRec2 thin n I := by
  intro n
  induction n with
  | zero => intro I; rfl
  | succ n ih =>
    intro I
    simp only [solveRecT, solveRec2]
    split_ifs
    · simp [hret, checkET_ret]
    · simp only [ret_bind, findRed2T_ret]
      cases hf : findRed2 I with
      | some d =>
        simp only [ret_bind, ih]
        cases hs : solveRec2 thin n (I.deleteAt d) with
        | none => simp [stepT]
        | some pq =>
          obtain ⟨p, q⟩ := pq
          have hL := liftL_eqF (findRed2_shape hf) (solveRec2_sound thin n _ _ _ hs)
          simp [stepT, liftET_ret, hL]
      | none =>
        simp only [ret_bind, findRed2T_ret]
        cases hg : findRed2 I.transpose with
        | some d =>
          simp only [ret_bind, ih]
          cases hs : solveRec2 thin n (I.transpose.deleteAt d) with
          | none => simp [stepTT]
          | some pq =>
            obtain ⟨p, q⟩ := pq
            have hL := liftL_eqF (findRed2_shape hg) (solveRec2_sound thin n _ _ _ hs)
            simp [stepTT, liftET_ret, hL, swapT_ret]
        | none => simp [hret, checkET_ret]

theorem wfB_iff (I : Inst) : wfB I = true ↔ I.WellFormed := by
  unfold wfB Inst.WellFormed InBounds
  simp only [decide_eq_true_eq]
  tauto

theorem solveZT_ret (hret : ∀ J, (thinT J).ret = thin J) (I : Inst) :
    (solveZT thinT I).ret = solveZ2 thin I := by
  unfold solveZT solveZ2
  by_cases hwf : I.WellFormed
  · rw [ite_t ((wfB_iff I).2 hwf), ite_t hwf, solveRecT_ret hret]
  · rw [ite_f (fun h => hwf ((wfB_iff I).1 h)), ite_f hwf]; rfl

end

/-- Every answer of `solveRec2` is a solution, so it has `w h` cells. -/
theorem solveRec2_len {thin : Inst → Sol} {n : ℕ} {I : Inst} {p q : List Coord}
    (h : solveRec2 thin n I = some (p, q)) : p.length + q.length = I.w * I.h :=
  solB_len (solB_complete (solveRec2_sound thin n I p q h))

lemma stepT_time (I : Inst) (d M : ℕ) (r : Sol) (hr : FreeShape I d)
    (hs : ∀ p q, r = some (p, q) → IsSolution (I.deleteAt d) p q) (hw : I.w ≤ M) (hh : I.h ≤ M) :
    (stepT I d r).time ≤ 51 * (M + 1) ^ 2 := by
  cases r with
  | none => simp [stepT]
  | some pq =>
    obtain ⟨p, q⟩ := pq
    have hsol := hs p q rfl
    have hl := liftET_time hr hsol
    have l1 := sol_len hsol
    have a1 : (I.deleteAt d).w * (I.deleteAt d).h ≤ M * M :=
      Nat.mul_le_mul (by show I.w - 2 ≤ M; omega) (by show I.h ≤ M; omega)
    have a2 : (I.h + 1) ^ 2 ≤ (M + 1) ^ 2 := sq_mono (by omega)
    have a3 : M * M ≤ (M + 1) ^ 2 := by nlinarith
    have a4 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    simp only [stepT, time_bind, time_pure]
    omega

lemma stepTT_time (I : Inst) (d M : ℕ) (r : Sol) (hr : FreeShape I.transpose d)
    (hs : ∀ p q, r = some (p, q) → IsSolution (I.transpose.deleteAt d) p q) (hw : I.w ≤ M)
    (hh : I.h ≤ M) : (stepTT I d r).time ≤ 52 * (M + 1) ^ 2 := by
  cases r with
  | none => simp [stepTT]
  | some pq =>
    obtain ⟨p, q⟩ := pq
    have hsol := hs p q rfl
    have hl := liftET_time hr hsol
    have l1 := sol_len hsol
    have l2 := sol_len (liftE_solF hr hsol)
    have hL := liftL_eqF hr hsol
    have s1 := swapT_time (liftET I.transpose d p q).ret.1
    have s2 := swapT_time (liftET I.transpose d p q).ret.2
    rw [liftET_ret, hL] at s1 s2
    have a1 : (I.transpose.deleteAt d).w * (I.transpose.deleteAt d).h ≤ M * M :=
      Nat.mul_le_mul (by show I.h - 2 ≤ M; omega) (by show I.w ≤ M; omega)
    have a0 : I.transpose.w * I.transpose.h ≤ M * M :=
      Nat.mul_le_mul (by show I.h ≤ M; omega) (by show I.w ≤ M; omega)
    have a2 : (I.transpose.h + 1) ^ 2 ≤ (M + 1) ^ 2 := sq_mono (by show I.w + 1 ≤ M + 1; omega)
    have a3 : M * M ≤ (M + 1) ^ 2 := by nlinarith
    have a4 : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    simp only [stepTT, time_bind, time_pure, liftET_ret, hL]
    omega

theorem solveRecT_time {thinT : Inst → TimeM Sol} {thin : Inst → Sol}
    (hret : ∀ J, (thinT J).ret = thin J)
    (hlen : ∀ J x, thin J = some x → x.1.length + x.2.length ≤ J.w * J.h)
    (M B : ℕ) (hB : ∀ J : Inst, J.w ≤ M → J.h ≤ M → (J.w ≤ 16 ∨ J.h ≤ 16) → (thinT J).time ≤ B) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → I.w ≤ M → I.h ≤ M →
      (solveRecT thinT n I).time ≤ n * (700 * (M + 1) ^ 2) + (B + 3 * (16 * M + 1) ^ 2 + 10) := by
  have leaf : ∀ J : Inst, J.w ≤ M → J.h ≤ M → (J.w ≤ 16 ∨ J.h ≤ 16) →
      (thinT J >>= checkET J).time ≤ B + 3 * (16 * M + 1) ^ 2 + 10 := by
    intro J a b c
    have t := hB J a b c
    have area : J.w * J.h ≤ 16 * M := by
      rcases c with c | c
      · exact Nat.mul_le_mul c b
      · rw [Nat.mul_comm]; exact Nat.mul_le_mul c a
    have k := checkET_time J (thinT J).ret (16 * M) (fun x hx => by
      rw [hret] at hx; exact le_trans (hlen J x hx) area)
    simp only [time_bind]
    omega
  intro n
  induction n with
  | zero => intro I _ _ _; simp [solveRecT]
  | succ n ih =>
    intro I hwf hw hh
    have hn : 700 * (M + 1) ^ 2 ≤ (n + 1) * (700 * (M + 1) ^ 2) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [solveRecT]
    split_ifs with h10
    · have := leaf I hw hh (by omega)
      omega
    · have hI : InDom I := ⟨by omega, by omega, hwf⟩
      have f1 := findRed2T_time I
      have e1 : 300 * (I.w + 1) ^ 2 ≤ 300 * (M + 1) ^ 2 := by have := sq_mono (by omega : I.w + 1 ≤ M + 1); omega
      simp only [time_bind, findRed2T_ret]
      cases hf : findRed2 I with
      | some d =>
        have hI' : InDom (I.deleteAt d) := by
          rcases findRed2_some hf with hr | hr
          · exact inDom_deleteAt hI hr
          · exact inDom_deleteB hI hr
        have r := ih (I.deleteAt d) hI'.2.2 (by simp only [Inst.deleteAt]; omega) hh
        have s := stepT_time I d M (solveRecT thinT n (I.deleteAt d)).ret (findRed2_shape hf)
          (fun p q hx => by rw [solveRecT_ret hret] at hx; exact solveRec2_sound thin n _ _ _ hx) hw hh
        simp only [time_bind]
        rw [Nat.succ_mul]; omega
      | none =>
        have hIT := inDom_transpose hI
        have f2 := findRed2T_time I.transpose
        have ht : I.transpose.w = I.h := rfl
        rw [ht] at f2
        have e2 : 300 * (I.h + 1) ^ 2 ≤ 300 * (M + 1) ^ 2 := by have := sq_mono (by omega : I.h + 1 ≤ M + 1); omega
        simp only [time_bind, findRed2T_ret]
        cases hg : findRed2 I.transpose with
        | some d =>
          have hI' : InDom (I.transpose.deleteAt d) := by
            rcases findRed2_some hg with hr | hr
            · exact inDom_deleteAt hIT hr
            · exact inDom_deleteB hIT hr
          have r := ih (I.transpose.deleteAt d) hI'.2.2
            (by simp only [Inst.deleteAt, Inst.transpose]; omega)
            (by simp only [Inst.deleteAt, Inst.transpose]; omega)
          have s := stepTT_time I d M (solveRecT thinT n (I.transpose.deleteAt d)).ret (findRed2_shape hg)
            (fun p q hx => by rw [solveRecT_ret hret] at hx; exact solveRec2_sound thin n _ _ _ hx) hw hh
          simp only [time_bind]
          rw [Nat.succ_mul]; omega
        | none =>
          have hw16 : I.w ≤ 16 := leaf16 hwf hI.1 (findRed2_none hf)
          have := leaf I hw hh (Or.inl hw16)
          simp only [time_bind] at this ⊢
          omega

/-- **The step bound of the construction.** -/
theorem solveZT_time {thinT : Inst → TimeM Sol} {thin : Inst → Sol}
    (hret : ∀ J, (thinT J).ret = thin J)
    (hlen : ∀ J x, thin J = some x → x.1.length + x.2.length ≤ J.w * J.h)
    (M B : ℕ) (hB : ∀ J : Inst, J.w ≤ M → J.h ≤ M → (J.w ≤ 16 ∨ J.h ≤ 16) → (thinT J).time ≤ B)
    (I : Inst) (hw : I.w ≤ M) (hh : I.h ≤ M) :
    (solveZT thinT I).time ≤ (I.w + I.h) * (700 * (M + 1) ^ 2) + (B + 3 * (16 * M + 1) ^ 2 + 10) := by
  unfold solveZT
  by_cases hwf : I.WellFormed
  · rw [ite_t ((wfB_iff I).2 hwf)]
    exact solveRecT_time hret hlen M B hB (I.w + I.h) I hwf hw hh
  · rw [ite_f (fun h => hwf ((wfB_iff I).1 h))]
    simp

end ZZN.T
