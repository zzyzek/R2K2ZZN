-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.TimedStatement
import ZZN.Timed.ThinCount

/-!
# The time of the counted plug DP

Every state list held by the counted DP is duplicate-free and its states are good (their pieces
come from the realizability invariant `W` and the exit filter), so it has at most `Nst b` states
(`ThinCount.lean`). One cell then costs at most `Kst b` steps, and `thinBFT` takes at most
`(R C + 1) (Kst b + 2) + Nst b + 1` steps, where `b` is the short side (`thinBFT_time`).
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

variable {a b : ℕ} {J : Inst}

/-! ### The states are good -/

theorem fold_W {tm : List ((ℕ × ℕ) × ℕ)}
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∀ n, n ≤ a * b → ∀ s ∈ (List.range n).foldl (stageF a b tm) [([], 0)], W a b J n s := by
  intro n
  induction n with
  | zero => intro _ s hs; rw [List.mem_singleton.mp hs]; exact W_zero
  | succ n ih =>
    intro hn s hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageF stage at hs
    rw [List.mem_filter, mem_normS, List.mem_flatMap] at hs
    obtain ⟨⟨s0, h0, h1⟩, -⟩ := hs
    exact step_W htm (by omega) (ih (by omega) s0 h0) h1

lemma endCol_val {y : Coord} {col : ℕ} (h : endCol J y = some col) : col = 0 ∨ col = 1 := by
  unfold endCol at h; split_ifs at h <;> simp_all

lemma goodEnd_of {n e : ℕ} {x : Coord} (hx : prI a b n x) (hE : EndOK a b J n e x)
    (hok : okEnd a b e = true) : GoodEnd a b e := by
  rcases hE with ⟨col, rfl, hc⟩ | ⟨y, hy, hadj, rfl⟩
  · rcases endCol_val hc with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · have := desc_lt hx hy hadj
    unfold okEnd isTerm at hok
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
    left; omega

lemma good_of_W {n : ℕ} {s : St} (hW : W a b J n s) (hx : noExit a b s = true) : Good a b s := by
  obtain ⟨sg, dp, hn, h4, hseg, -⟩ := hW
  refine ⟨hn, h4, fun z hz => ?_⟩
  obtain ⟨-, -, -, hp, u, v, hu, hv, eu, ev⟩ := hseg z hz
  have hok := List.all_eq_true.1 hx z hz
  simp only [Bool.and_eq_true] at hok
  have hum : u ∈ sg z := List.mem_of_mem_head? hu
  have hvm : v ∈ sg z := List.mem_of_mem_getLast? hv
  exact ⟨goodEnd_of (hp u hum) eu hok.1, goodEnd_of (hp v hvm) ev hok.2⟩

/-- The state list after `n` cells of the counted DP. -/
def foldT (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) : List St :=
  (List.range n).foldl (fun S i => (stageT a b tm S i).ret) [([], 0)]

lemma foldT_succ (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) :
    foldT a b tm (n + 1) = (stageT a b tm (foldT a b tm n) n).ret := by
  simp [foldT, List.range_succ, List.foldl_append]

theorem foldT_good {tm : List ((ℕ × ℕ) × ℕ)}
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) (n : ℕ) (hn : n ≤ a * b) :
    (foldT a b tm n).Nodup ∧ ∀ s ∈ foldT a b tm n, Good a b s := by
  cases n with
  | zero => exact ⟨by simp [foldT], fun s hs => by simp [foldT] at hs; subst hs; simp [Good]⟩
  | succ n =>
    refine ⟨?_, fun s hs => ?_⟩
    · rw [foldT_succ]
      simp only [stageT, ret_bind, lfilterT, ldedupT]
      exact (List.nodup_dedup _).filter _
    · have hW := fold_W (J := J) htm (n + 1) hn s ((insideT_mem a b tm (n + 1) s).1 hs)
      rw [foldT_succ, mem_stageT] at hs
      exact good_of_W hW hs.1

/-! ### Step lengths -/

lemma insSorted_length (x : ℕ) : ∀ l : List ℕ, (insSorted x l).length = l.length + 1
  | [] => rfl
  | y :: l => by unfold insSorted; split_ifs <;> simp [insSorted_length x l]

lemma restT_len (ps : List ℕ) (pu pl : Option ℕ) : (restT ps pu pl).ret.length ≤ ps.length := by
  rw [restT_ret]
  split_ifs <;>
    first
    | exact le_trans List.length_erase_le List.length_erase_le
    | exact List.length_erase_le
    | exact le_refl _

lemma stepCell_len (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) :
    (stepCell a b e r c s).length ≤ 2 ∧ ∀ s' ∈ stepCell a b e r c s, s'.1.length ≤ s.1.length + 1 := by
  rw [stepCell_eq]
  unfold stepCellFrom
  dsimp only
  generalize (if r = 0 then none else s.1.find? (hasEnd c)) = pu
  generalize (if c = 0 then none else s.1.find? (hasEnd b)) = pl
  have hrest := restT_len s.1 pu pl
  rw [restT_ret] at hrest
  generalize (if pu.isSome = true then (if pl.isSome = true then (s.1.erase (pu.getD 0)).erase (pl.getD 0)
    else s.1.erase (pu.getD 0)) else (if pl.isSome = true then s.1.erase (pl.getD 0) else s.1)) = rest at *
  generalize (if e.isSome = true then 1 else 2) = deg
  generalize (if pu.isSome = true then 1 else 0) + (if pl.isSome = true then 1 else 0) = nin
  generalize (if r + 1 < a then c else exitE b (a + (b - 1 - c))) = down
  generalize (if c + 1 < b then b else exitE b r) = right
  by_cases h1 : deg < nin
  · simp only [h1, ↓reduceIte]; simp
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (pu.isSome && pu == pl) = true
    · simp only [h2, ↓reduceIte]; simp
    · simp only [Bool.not_eq_true] at h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      constructor
      · refine le_trans (List.length_filterMap_le _ _) ?_
        split <;> simp
      · intro s' hs'
        obtain ⟨outs, -, ho⟩ := List.mem_filterMap.1 hs'
        split at ho
        · unfold closeP at ho
          split_ifs at ho <;> simp at ho <;> (try subst ho) <;> simp [insSorted_length] <;> omega
        · simp at ho

/-! ### Step times -/

lemma insSortedT_time (x : ℕ) : ∀ l : List ℕ, (insSortedT x l).time ≤ l.length + 1
  | [] => by simp [insSortedT]
  | y :: l => by
    unfold insSortedT
    split_ifs
    · simp
    · simp only [time_bind, List.length_cons]; have := insSortedT_time x l; omega

lemma restT_time (ps : List ℕ) (pu pl : Option ℕ) : (restT ps pu pl).time ≤ 2 * ps.length + 2 := by
  match pu, pl with
  | some u, some l =>
    simp only [restT, time_bind, leraseT]
    have : (ps.erase u).length ≤ ps.length := List.length_erase_le
    omega
  | some u, none => simp only [restT, leraseT]; omega
  | none, some l => simp only [restT, leraseT]; omega
  | none, none => simp [restT]

lemma lookT_time (skip : Bool) (k : ℕ) (ps : List ℕ) : (lookT skip k ps).time ≤ ps.length := by
  unfold lookT; split
  · simp
  · simpa using lfindT_time_le (fun z => (pure (hasEnd k z) : TimeM Bool)) ps 0 (fun _ _ => by simp)

lemma endsL_len (a b c : ℕ) (e pu pl : Option ℕ) : (endsL a b c e pu pl).length ≤ 3 := by
  cases pu <;> cases pl <;> cases e <;> simp [endsL]

lemma optsL_len (k down right : ℕ) : (optsL k down right).length ≤ 2 ∧
    ∀ o ∈ optsL k down right, o.length ≤ 2 := by
  unfold optsL; split <;> simp

lemma closeOptT_time (a b : ℕ) (ins outs rest : List ℕ) (dn : ℕ) :
    (closeOptT a b ins outs rest dn).time ≤ ins.length + rest.length + 3 := by
  simp only [closeOptT, time_bind, lappendT]
  split
  · unfold closePT; split
    · simp only [time_pure]; omega
    · rename_i x y _ _
      simp only [time_bind, time_pure]; have := insSortedT_time (mkP x y) rest; omega
  · simp only [time_pure]; omega
  · simp only [time_pure]; omega
  · simp only [time_pure]; omega

lemma stepCellT_time (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) :
    (stepCellT a b e r c s).time ≤ 6 * s.1.length + 16 := by
  simp only [stepCellT, time_bind]
  have h1 := lookT_time (r == 0) c s.1
  have h2 := lookT_time (c == 0) b s.1
  generalize (lookT (r == 0) c s.1).ret = pu
  generalize (lookT (c == 0) b s.1).ret = pl
  unfold stepTailT
  dsimp only
  have h3 := restT_time s.1 pu pl
  have h4 := restT_len s.1 pu pl
  have h5 := endsL_len a b c e pu pl
  generalize (if e.isSome = true then 1 else 2) = deg
  generalize (if pu.isSome = true then 1 else 0) + (if pl.isSome = true then 1 else 0) = nin
  generalize (if r + 1 < a then c else exitE b (a + (b - 1 - c))) = down
  generalize (if c + 1 < b then b else exitE b r) = right
  by_cases k1 : deg < nin
  · simp only [k1, ↓reduceIte]; simp only [time_pure]; omega
  · simp only [k1, ↓reduceIte]
    by_cases k2 : (pu.isSome && pu == pl) = true
    · simp only [k2, ↓reduceIte]; simp only [time_pure]; omega
    · simp only [Bool.not_eq_true] at k2
      simp only [k2, Bool.false_eq_true, ↓reduceIte, time_bind]
      obtain ⟨h6, -⟩ := optsL_len (deg - nin) down right
      have h7 := lfilterMapT_time_le (fun outs => closeOptT a b (endsL a b c e pu pl) outs
        (restT s.1 pu pl).ret s.2) (optsL (deg - nin) down right) (s.1.length + 6) (fun outs _ => by
          have := closeOptT_time a b (endsL a b c e pu pl) outs (restT s.1 pu pl).ret s.2; omega)
      have h8 : (optsL (deg - nin) down right).length * (s.1.length + 6 + 1) ≤ 2 * (s.1.length + 7) :=
        Nat.mul_le_mul_right _ h6
      omega

/-! ### One stage -/


lemma stageT_time (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (htm : tm.length = 4) (S : List St)
    (hS : S.length ≤ Nst b) (hg : ∀ s ∈ S, s.1.length ≤ Q b) (i : ℕ) :
    (stageT a b tm S i).time ≤ Kst b := by
  simp only [stageT, time_bind]
  have t1 := lfindT_time_le (fun q => (pure (q.1 == cell b i) : TimeM Bool)) tm 0 (fun _ _ => by simp)
  rw [htm] at t1
  generalize ((lfindT (fun q => (pure (q.1 == cell b i) : TimeM Bool)) tm).ret) = o
  generalize optSnd o = e
  have t2 := lflatMapT_time_le (stepCellT a b e (cell b i).1 (cell b i).2) S (6 * Q b + 16) 2
    (fun s hs => by have := stepCellT_time a b e (cell b i).1 (cell b i).2 s; have := hg s hs; omega)
    (fun s _ => by rw [stepCellT_ret]; exact (stepCell_len a b e _ _ s).1)
  have hl : (lflatMapT (stepCellT a b e (cell b i).1 (cell b i).2) S).ret.length ≤ 2 * Nst b := by
    simp only [lflatMapT, List.length_flatMap]
    have := lsum_le S (fun s => (stepCellT a b e (cell b i).1 (cell b i).2 s).ret.length) 2
      (fun s _ => by rw [stepCellT_ret]; exact (stepCell_len a b e _ _ s).1)
    omega
  have hlq : ∀ s' ∈ (lflatMapT (stepCellT a b e (cell b i).1 (cell b i).2) S).ret,
      s'.1.length ≤ Q b + 1 := by
    intro s' hs'
    simp only [lflatMapT, List.mem_flatMap, stepCellT_ret] at hs'
    obtain ⟨s, hs, h⟩ := hs'
    have := (stepCell_len a b e _ _ s).2 s' h
    have := hg s hs
    omega
  generalize (lflatMapT (stepCellT a b e (cell b i).1 (cell b i).2) S).ret = l at hl hlq
  have t3 := lfilterT_time_le (noExitT a b) (ldedupT l).ret (Q b + 1) (fun s hs => by
    simp only [ldedupT, List.mem_dedup] at hs
    unfold noExitT
    have := lallT_time_le (fun z => (pure (okEnd a b (lo z) && okEnd a b (hi z)) : TimeM Bool)) s.1 0
      (fun _ _ => by simp)
    have := hlq s hs
    omega)
  have hd : (ldedupT l).ret.length ≤ 2 * Nst b := by
    simp only [ldedupT]; exact le_trans (List.Sublist.length_le (List.dedup_sublist _)) hl
  have m1 : S.length * (6 * Q b + 16 + 2 + 1) ≤ Nst b * (6 * Q b + 19) := Nat.mul_le_mul_right _ hS
  have m2 : (ldedupT l).ret.length * (Q b + 1 + 1) ≤ 2 * Nst b * (Q b + 2) := by
    have := Nat.mul_le_mul_right (Q b + 1 + 1) hd; linarith
  have m3 : l.length ^ 2 ≤ (2 * Nst b) ^ 2 := Nat.pow_le_pow_left hl 2
  have e3 : (ldedupT l).time = l.length ^ 2 + 1 := rfl
  rw [e3]
  unfold Kst
  nlinarith

/-! ### The whole DP -/

lemma lfoldlT_time_append {β α : Type} (f : β → α → TimeM β) :
    ∀ (l m : List α) (b : β), (lfoldlT f b (l ++ m)).time =
      (lfoldlT f b l).time + (lfoldlT f (l.foldl (fun b x => (f b x).ret) b) m).time
  | [], m, b => by simp [lfoldlT]
  | x :: l, m, b => by
    simp only [List.cons_append, lfoldlT, List.foldl_cons]
    rw [lfoldlT_time_append f l m]
    omega

lemma insideT_time (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (htm4 : tm.length = 4)
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    (insideT a b tm).time ≤ (a * b + 1) * (Kst b + 2) ∧ (insideT a b tm).ret.length ≤ Nst b := by
  have key : ∀ n, n ≤ a * b →
      (lfoldlT (stageT a b tm) [([], 0)] (List.range n)).time ≤ n * (Kst b + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [lfoldlT]
    | succ n ih =>
      intro hn
      rw [List.range_succ, lfoldlT_time_append]
      obtain ⟨hnd, hg⟩ := foldT_good (J := J) htm n (by omega)
      have hS := card_good _ hnd hg
      have := stageT_time a b tm htm4 (foldT a b tm n) hS (fun s hs => good_len (hg s hs)) n
      simp only [lfoldlT]
      have h2 := ih (by omega)
      simp only [foldT] at this
      rw [Nat.succ_mul]
      simp only [add_zero] at *
      omega
  obtain ⟨hnd, hg⟩ := foldT_good (J := J) htm (a * b) le_rfl
  refine ⟨?_, ?_⟩
  · simp only [insideT, time_bind, rangeT]
    have := key (a * b) le_rfl
    nlinarith
  · simp only [insideT, ret_bind, rangeT, ret_lfoldlT]
    exact card_good _ hnd hg

lemma dpAcceptT_time (J : Inst) :
    (dpAcceptT J).time ≤ (J.w * J.h + 1) * (Kst J.h + 2) + Nst J.h + 1 := by
  obtain ⟨h1, h2⟩ := insideT_time J.w J.h (tmOf J) rfl (J := J) (fun y _ _ => termAt_tmOf J y)
  simp only [dpAcceptT, time_bind, lcontainsT]
  omega

/-- **The counted plug DP takes at most `(R C + 1) (Kst b + 2) + Nst b + 1` steps, where `b` is the
short side.** -/
theorem thinBFT_time (J : Inst) :
    (thinBFT J).time ≤ (J.w * J.h + 1) * (Kst (min J.w J.h) + 2) + Nst (min J.w J.h) + 1 := by
  unfold thinBFT
  split
  · rename_i h
    have := dpAcceptT_time J
    rwa [min_eq_right h]
  · rename_i h
    have := dpAcceptT_time J.transpose
    simp only [Inst.transpose] at this
    rw [min_eq_left (by omega), Nat.mul_comm J.w J.h]
    exact this

end ZZN.T
