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
    ∀ (n : ℕ) (I : Inst), (solveRecT thinT n I).ret = solveRec thin n I := by
  intro n
  induction n with
  | zero => intro I; rfl
  | succ n ih =>
    intro I
    simp only [solveRecT, solveRec]
    split_ifs
    · simp [hret, checkET_ret]
    · simp only [ret_bind, findRedT_ret]
      cases findRed I with
      | some d =>
        simp only [ret_bind, ih]
        cases solveRec thin n (I.deleteAt d) <;> simp [stepT, liftET_ret, checkET_ret]
      | none =>
        simp only [ret_bind, findRedT_ret]
        cases findRed I.transpose with
        | some d =>
          simp only [ret_bind, ih]
          cases solveRec thin n (I.transpose.deleteAt d) <;>
            simp [stepTT, liftET_ret, checkET_ret, swapT_ret]
        | none => simp [hret, checkET_ret]

theorem solveZT_ret (hret : ∀ J, (thinT J).ret = thin J) (I : Inst) :
    (solveZT thinT I).ret = solveZ thin I := by
  simp only [solveZT, solveZ, ret_bind, solveRecT_ret hret, checkET_ret]
  cases solveRec thin (I.w + I.h) I <;> rfl

end

/-- Every answer of `solveRec` passed the checker, so it has `w h` cells. -/
theorem solveRec_len {thin : Inst → Sol} {n : ℕ} {I : Inst} {p q : List Coord}
    (h : solveRec thin n I = some (p, q)) : p.length + q.length = I.w * I.h := by
  cases n with
  | zero => simp [solveRec] at h
  | succ n =>
    simp only [solveRec] at h
    split_ifs at h
    · exact checkE_len h
    · split at h
      · split at h
        · exact checkE_len h
        · cases h
      · split at h
        · split at h
          · exact checkE_len h
          · cases h
        · exact checkE_len h

lemma stepT_time (I : Inst) (d Q : ℕ) (r : Sol) (hQ : I.h + 1 ≤ Q)
    (hr : ∀ x, r = some x → x.1.length + x.2.length ≤ Q) :
    (stepT I d r).time ≤ 700 * Q ^ 2 + 10 := by
  cases r with
  | none => simp [stepT]
  | some pq =>
    obtain ⟨p, q⟩ := pq
    have hn := hr (p, q) rfl
    simp only at hn
    have hl := liftET_time I d p q
    have hlen := liftE_len I d p q
    have hc := checkET_time I (some (liftE I d p q)) (7 * Q) (fun x hx => by
      cases hx; omega)
    have m : (I.h + 1) * (p.length + q.length + I.h + 1) ≤ 2 * Q ^ 2 :=
      calc _ ≤ Q * (2 * Q) := Nat.mul_le_mul hQ (by omega)
        _ = 2 * Q ^ 2 := by ring
    have s : (7 * Q + 1) ^ 2 ≤ 64 * Q ^ 2 :=
      calc _ ≤ (8 * Q) ^ 2 := sq_mono (by omega)
        _ = 64 * Q ^ 2 := by ring
    simp only [stepT, time_bind, liftET_ret]
    omega

lemma stepTT_time (I : Inst) (d Q : ℕ) (r : Sol) (hQ : I.w + 1 ≤ Q)
    (hr : ∀ x, r = some x → x.1.length + x.2.length ≤ Q) :
    (stepTT I d r).time ≤ 700 * Q ^ 2 + 10 := by
  cases r with
  | none => simp [stepTT]
  | some pq =>
    obtain ⟨p, q⟩ := pq
    have hn := hr (p, q) rfl
    simp only at hn
    have hl := liftET_time I.transpose d p q
    have hlen := liftE_len I.transpose d p q
    have ht : I.transpose.h = I.w := rfl
    have hc := checkET_time I (some ((liftE I.transpose d p q).1.map Prod.swap, (liftE I.transpose d p q).2.map Prod.swap)) (7 * Q)
      (fun x hx => by cases hx; simp only [List.length_map]; omega)
    have s1 := swapT_time (liftE I.transpose d p q).1
    have s2 := swapT_time (liftE I.transpose d p q).2
    have m : (I.transpose.h + 1) * (p.length + q.length + I.transpose.h + 1) ≤ 2 * Q ^ 2 :=
      calc _ ≤ Q * (2 * Q) := Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * Q ^ 2 := by ring
    have s : (7 * Q + 1) ^ 2 ≤ 64 * Q ^ 2 :=
      calc _ ≤ (8 * Q) ^ 2 := sq_mono (by omega)
        _ = 64 * Q ^ 2 := by ring
    have qq : Q ≤ Q ^ 2 := by nlinarith
    simp only [stepTT, time_bind, liftET_ret, swapT_ret]
    omega

theorem solveRecT_time {thinT : Inst → TimeM Sol} {thin : Inst → Sol}
    (hret : ∀ J, (thinT J).ret = thin J)
    (hlen : ∀ J x, thin J = some x → x.1.length + x.2.length ≤ J.w * J.h)
    (M B : ℕ) (hB : ∀ J : Inst, J.w ≤ M → J.h ≤ M → (J.w ≤ 22 ∨ J.h ≤ 22) → (thinT J).time ≤ B) :
    ∀ (n : ℕ) (I : Inst), I.w ≤ M → I.h ≤ M →
      (solveRecT thinT n I).time ≤ n * (1100 * ((M + 1) ^ 2) ^ 2 + B + 10) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (M + 1) ^ 2 := ⟨_, rfl⟩
  rw [← hQ]
  have hMQ : M * M ≤ Q := by rw [hQ]; nlinarith
  have hKQ : M + 1 ≤ Q := by rw [hQ]; nlinarith
  have qq : Q ≤ Q ^ 2 := by nlinarith
  have q1 : (Q + 1) ^ 2 ≤ 4 * Q ^ 2 :=
    calc _ ≤ (2 * Q) ^ 2 := sq_mono (by omega)
      _ = 4 * Q ^ 2 := by ring
  have area : ∀ J : Inst, J.w ≤ M → J.h ≤ M → J.w * J.h ≤ Q := fun J a b =>
    le_trans (Nat.mul_le_mul a b) hMQ
  have leaf : ∀ J : Inst, J.w ≤ M → J.h ≤ M → (J.w ≤ 22 ∨ J.h ≤ 22) →
      (thinT J >>= checkET J).time ≤ B + 12 * Q ^ 2 + 10 := by
    intro J a b c
    have t := hB J a b c
    have k := checkET_time J (thinT J).ret Q (fun x hx => by
      rw [hret] at hx; exact le_trans (hlen J x hx) (area J a b))
    simp only [time_bind]
    omega
  intro n
  induction n with
  | zero => intro I _ _; simp [solveRecT]
  | succ n ih =>
    intro I hw hh
    simp only [solveRecT]
    split_ifs with h10
    · have := leaf I hw hh (by omega)
      rw [Nat.succ_mul]; nlinarith
    · have f1 := findRedT_time I
      have e1 : 200 * (I.w + 1) ^ 2 ≤ 200 * Q ^ 2 := by have := sq_mono (by omega : I.w + 1 ≤ Q); omega
      simp only [time_bind, findRedT_ret]
      cases hf : findRed I with
      | some d =>
        have r := ih (I.deleteAt d) (by simp only [Inst.deleteAt]; omega) hh
        have s := stepT_time I d Q (solveRecT thinT n (I.deleteAt d)).ret (by omega) (fun x hx => by
          rw [solveRecT_ret hret] at hx
          rw [solveRec_len hx]
          exact area _ (by simp only [Inst.deleteAt]; omega) hh)
        simp only [time_bind]
        rw [Nat.succ_mul]; omega
      | none =>
        have f2 := findRedT_time I.transpose
        have ht : I.transpose.w = I.h := rfl
        rw [ht] at f2
        have e2 : 200 * (I.h + 1) ^ 2 ≤ 200 * Q ^ 2 := by have := sq_mono (by omega : I.h + 1 ≤ Q); omega
        simp only [time_bind, findRedT_ret]
        cases hg : findRed I.transpose with
        | some d =>
          have r := ih (I.transpose.deleteAt d) (by simp only [Inst.deleteAt, Inst.transpose]; omega)
            (by simp only [Inst.deleteAt, Inst.transpose]; omega)
          have s := stepTT_time I d Q (solveRecT thinT n (I.transpose.deleteAt d)).ret (by omega)
            (fun x hx => by
              rw [solveRecT_ret hret] at hx
              rw [solveRec_len hx]
              exact area _ (by simp only [Inst.deleteAt, Inst.transpose]; omega)
                (by simp only [Inst.deleteAt, Inst.transpose]; omega))
          simp only [time_bind]
          rw [Nat.succ_mul]; omega
        | none =>
          have hw22 : I.w ≤ 22 := by
            by_contra h
            obtain ⟨d, hd⟩ := redX_of_wide I (by omega)
            exact findRed_none hf d hd
          have := leaf I hw hh (Or.inl hw22)
          simp only [time_bind] at this ⊢
          rw [Nat.succ_mul]; omega

/-- **The step bound of the construction.** -/
theorem solveZT_time {thinT : Inst → TimeM Sol} {thin : Inst → Sol}
    (hret : ∀ J, (thinT J).ret = thin J)
    (hlen : ∀ J x, thin J = some x → x.1.length + x.2.length ≤ J.w * J.h)
    (M B : ℕ) (hB : ∀ J : Inst, J.w ≤ M → J.h ≤ M → (J.w ≤ 22 ∨ J.h ≤ 22) → (thinT J).time ≤ B)
    (I : Inst) (hw : I.w ≤ M) (hh : I.h ≤ M) :
    (solveZT thinT I).time ≤ (I.w + I.h + 1) * (1100 * ((M + 1) ^ 2) ^ 2 + B + 10) := by
  have r := solveRecT_time hret hlen M B hB (I.w + I.h) I hw hh
  have hMQ : M * M ≤ (M + 1) ^ 2 := by nlinarith
  have k := checkET_time I (solveRecT thinT (I.w + I.h) I).ret ((M + 1) ^ 2) (fun x hx => by
    rw [solveRecT_ret hret] at hx
    rw [solveRec_len hx]
    exact le_trans (Nat.mul_le_mul hw hh) hMQ)
  have q1 : ((M + 1) ^ 2 + 1) ^ 2 ≤ 4 * ((M + 1) ^ 2) ^ 2 :=
    calc _ ≤ (2 * (M + 1) ^ 2) ^ 2 := sq_mono (by nlinarith)
      _ = 4 * ((M + 1) ^ 2) ^ 2 := by ring
  simp only [solveZT, time_bind]
  rw [Nat.succ_mul]; omega

end ZZN.T
