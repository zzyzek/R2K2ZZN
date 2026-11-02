-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.TimedStatement
import ZZN.Timed.ThinWit
import ZZN.Timed.ThinCost

/-!
# The time of the counted solver

After `n` cells the witness-carrying DP holds a list whose states are distinct (`dedupKey`) and good
(they are states of `insideF`, so the realizability invariant and the exit filter apply), hence at
most `Nst b` entries (`card_good`). Each entry has at most `Q b` pieces, and every stored segment
and completed path is a duplicate-free list of grid cells, so it has at most `a b` cells
(`grid_len`). One cell then costs at most `(a b + 1) Ks b` steps, and the solver at most
`(R C + 1)² Kw b` steps, where `b` is the short side (`thinSolveWT_time`).
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-! ### Small time lemmas -/

lemma lbeqT_time : ∀ l m : List ℕ, (lbeqT l m).time ≤ l.length
  | [], [] => by simp [lbeqT]
  | [], _ :: _ => by simp [lbeqT]
  | _ :: _, [] => by simp [lbeqT]
  | x :: l, y :: m => by
    unfold lbeqT
    split
    · simp only [time_bind, List.length_cons]; have := lbeqT_time l m; omega
    · simp

lemma lbeqT_nil_time (l : List ℕ) : (lbeqT l []).time = 0 := by
  cases l <;> rfl

lemma stEqT_time (s t : St) : (stEqT s t).time ≤ s.1.length := by
  simp only [stEqT, time_bind, time_pure]; have := lbeqT_time s.1 t.1; omega

lemma dedupKeyAuxT_time (B : ℕ) : ∀ (seen : List St) (l : List (St × Wit)),
    (∀ t ∈ seen, t.1.length ≤ B) → (∀ x ∈ l, x.1.1.length ≤ B) →
    (dedupKeyAuxT seen l).time ≤ l.length * ((seen.length + l.length) * (B + 1) + 1)
  | _, [], _, _ => by simp [dedupKeyAuxT]
  | seen, x :: l, hs, hl => by
    have hx := hl x (by simp)
    have hl' : ∀ y ∈ l, y.1.1.length ≤ B := fun y hy => hl y (by simp [hy])
    have h1 := lanyT_time_le (fun t => stEqT t x.1) seen B
      (fun t ht => le_trans (stEqT_time t x.1) (hs t ht))
    unfold dedupKeyAuxT
    simp only [time_bind, List.length_cons]
    have key : seen.length * (B + 1) ≤ (seen.length + (l.length + 1)) * (B + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have e : (l.length + 1) * ((seen.length + (l.length + 1)) * (B + 1) + 1) =
        l.length * ((seen.length + (l.length + 1)) * (B + 1) + 1) +
          ((seen.length + (l.length + 1)) * (B + 1) + 1) := by ring
    split
    · have h2 := dedupKeyAuxT_time B seen l hs hl'
      have h3 : l.length * ((seen.length + l.length) * (B + 1) + 1) ≤
          l.length * ((seen.length + (l.length + 1)) * (B + 1) + 1) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      omega
    · have h2 := dedupKeyAuxT_time B (x.1 :: seen) l
        (fun t ht => by rcases List.mem_cons.mp ht with rfl | ht; exacts [hx, hs t ht]) hl'
      simp only [time_bind, time_pure, List.length_cons] at h2 ⊢
      have h3 : seen.length + 1 + l.length = seen.length + (l.length + 1) := by omega
      rw [h3] at h2
      omega

lemma lookDT_time (l : List (ℕ × List Coord)) (z : ℕ) : (lookDT l z).time ≤ l.length := by
  simp only [lookDT, time_bind, time_pure]
  have := lfindT_time_le (fun q => (pure (q.1 == z) : TimeM Bool)) l 0 (fun _ _ => by simp)
  omega

lemma orientST_time (e z : ℕ) (L : List Coord) : (orientST e z L).time ≤ L.length + 1 := by
  unfold orientST; split <;> simp [lreverseT]

lemma orientS_len (e z : ℕ) (L : List Coord) : (orientS e z L).length = L.length := by
  unfold orientS; split <;> simp

lemma closeWitT_time (J : Inst) (a b x y : ℕ) (Ln : List Coord) (sgR : List (ℕ × List Coord))
    (d : List Coord × List Coord) : (closeWitT J a b x y Ln sgR d).time ≤ Ln.length + 1 := by
  unfold closeWitT
  split
  · simp only [time_bind, time_pure, orientPT]; split <;> simp [lreverseT]
  · simp only [time_bind, time_pure, orientNT]; split <;> simp [lreverseT]

/-- The new segment: time and length, when the attached pieces' segments have at most `A` cells. -/
lemma segNewT_time (b r c : ℕ) (w : List (ℕ × List Coord)) (pu pl : Option ℕ) (A : ℕ)
    (hu : ∀ z, pu = some z → (lookD w z).length ≤ A) (hl : ∀ z, pl = some z → (lookD w z).length ≤ A) :
    (segNewT b r c w pu pl).time ≤ 2 * w.length + 5 * A + 6 ∧
      (segNewT b r c w pu pl).ret.length ≤ 2 * A + 1 := by
  rw [segNewT_ret]
  cases pu with
  | none =>
    cases pl with
    | none => simp [segNewT, segNew]
    | some zl =>
      have h1 := hl zl rfl
      simp only [segNewT, segNew, time_bind, lappendT, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        Option.map_some, Option.getD_some, List.length_append, List.length_singleton, orientS_len]
      have := lookDT_time w zl
      have := orientST_time b zl (lookDT w zl).ret
      simp only [lookDT_ret, orientST_ret, orientS_len] at *
      constructor <;> omega
  | some zu =>
    have h1 := hu zu rfl
    cases pl with
    | none =>
      simp only [segNewT, segNew, time_bind, lappendT, Option.isSome_some, ↓reduceIte,
        Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, List.reverse_nil,
        List.append_nil, List.length_append, List.length_singleton, orientS_len]
      have := lookDT_time w zu
      have := orientST_time c zu (lookDT w zu).ret
      simp only [lookDT_ret, orientST_ret, orientS_len] at *
      constructor <;> omega
    | some zl =>
      have h2 := hl zl rfl
      simp only [segNewT, segNew, time_bind, lappendT, lreverseT, Option.isSome_some, ↓reduceIte,
        Option.map_some, Option.getD_some, List.length_append, List.length_singleton, List.length_reverse,
        orientS_len]
      have := lookDT_time w zu
      have := orientST_time c zu (lookDT w zu).ret
      have := lookDT_time w zl
      have := orientST_time b zl (lookDT w zl).ret
      simp only [lookDT_ret, orientST_ret, orientS_len] at *
      constructor <;> omega

lemma optsOf_len (a b r c : ℕ) (e pu pl : Option ℕ) : (optsOf a b r c e pu pl).length ≤ 2 := by
  unfold optsOf; split <;> simp

lemma closeOptGT_time (a b : ℕ) (ins outs rest : List ℕ) (dn : ℕ) :
    (closeOptGT a b ins outs rest dn).time ≤ ins.length + rest.length + 3 := by
  simp only [closeOptGT, time_bind, lappendT]
  split
  · simp only [time_bind, time_pure]
    unfold closePT; split
    · simp only [time_pure]; omega
    · rename_i x y _ _
      simp only [time_bind, time_pure]; have := insSortedT_time (mkP x y) rest; omega
  · simp only [time_pure]; omega
  · simp only [time_pure]; omega
  · simp only [time_pure]; omega

lemma stepTailGT_time (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) (pu pl : Option ℕ) :
    (stepTailGT a b e r c s pu pl).time ≤ 4 * s.1.length + 16 := by
  unfold stepTailGT
  split
  · simp
  · split
    · simp
    · simp only [time_bind]
      have h3 := restT_time s.1 pu pl
      have h4 := restT_len s.1 pu pl
      have h5 := endsL_len a b c e pu pl
      have h6 := optsOf_len a b r c e pu pl
      have h7 := lfilterMapT_time_le (fun outs => closeOptGT a b (endsL a b c e pu pl) outs
        (restT s.1 pu pl).ret s.2) (optsOf a b r c e pu pl) (s.1.length + 6) (fun outs _ => by
          have := closeOptGT_time a b (endsL a b c e pu pl) outs (restT s.1 pu pl).ret s.2; omega)
      have h8 : (optsOf a b r c e pu pl).length * (s.1.length + 6 + 1) ≤ 2 * (s.1.length + 7) :=
        Nat.mul_le_mul_right _ h6
      omega

/-- **One cell of the witness-carrying DP**, for an entry with at most `q` pieces whose segments
have at most `A` cells. -/
lemma stepCellWT_time (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × Wit) (q A : ℕ)
    (hs : sw.1.1.length ≤ q) (hw : sw.2.1.length ≤ q) (hl : ∀ z ∈ sw.1.1, (lookD sw.2.1 z).length ≤ A) :
    (stepCellWT J a b e r c sw).time ≤ 9 * q + 9 * A + 28 := by
  simp only [stepCellWT, time_bind]
  have t1 := lookT_time (r == 0) c sw.1.1
  have t2 := lookT_time (c == 0) b sw.1.1
  have hpu := lookT_pu sw.1 r c
  have hpl : (lookT (c == 0) b sw.1.1).ret = plOf b sw.1 c := lookT_pu sw.1 c b
  rw [hpu, hpl]
  have mu : ∀ z, puOf sw.1 r c = some z → (lookD sw.2.1 z).length ≤ A := by
    intro z h; unfold puOf at h; split_ifs at h; exact hl z (List.mem_of_find?_eq_some h)
  have ml : ∀ z, plOf b sw.1 c = some z → (lookD sw.2.1 z).length ≤ A := by
    intro z h; unfold plOf at h; split_ifs at h; exact hl z (List.mem_of_find?_eq_some h)
  obtain ⟨t3, hLn⟩ := segNewT_time b r c sw.2.1 (puOf sw.1 r c) (plOf b sw.1 c) A mu ml
  have t4 := lfilterT_time_le (fun q => (pure (puOf sw.1 r c != some q.1 && plOf b sw.1 c != some q.1) :
    TimeM Bool)) sw.2.1 0 (fun _ _ => by simp)
  have t5 := stepTailGT_time a b e r c sw.1 (puOf sw.1 r c) (plOf b sw.1 c)
  have hG : (stepTailGT a b e r c sw.1 (puOf sw.1 r c) (plOf b sw.1 c)).ret.length ≤ 2 := by
    rw [stepTailGT_ret, ← List.length_map (f := Prod.snd), stepCellG_snd]
    exact (stepCell_len a b e r c sw.1).1
  generalize (segNewT b r c sw.2.1 (puOf sw.1 r c) (plOf b sw.1 c)).ret = Ln at hLn ⊢
  have t6 := lmapT_time_le (fun g => do
      let w ← closeWitT J a b g.1.1 g.1.2 Ln
        (lfilterT (fun q => pure (puOf sw.1 r c != some q.1 && plOf b sw.1 c != some q.1))
          sw.2.1).ret sw.2.2
      pure (g.2, w)) (stepTailGT a b e r c sw.1 (puOf sw.1 r c) (plOf b sw.1 c)).ret (2 * A + 2)
    (fun g _ => by
      simp only [time_bind, time_pure]
      have := closeWitT_time J a b g.1.1 g.1.2 Ln
        (lfilterT (fun q => pure (puOf sw.1 r c != some q.1 && plOf b sw.1 c != some q.1))
          sw.2.1).ret sw.2.2
      omega)
  have t7 : (stepTailGT a b e r c sw.1 (puOf sw.1 r c) (plOf b sw.1 c)).ret.length * (2 * A + 2 + 1) ≤
      2 * (2 * A + 3) := Nat.mul_le_mul_right _ hG
  omega

lemma stepCellWT_out (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × Wit) :
    (stepCellWT J a b e r c sw).ret.length ≤ 2 ∧
      ∀ sw' ∈ (stepCellWT J a b e r c sw).ret, sw'.1.1.length ≤ sw.1.1.length + 1 := by
  rw [stepCellWT_ret, ← List.length_map (f := Prod.fst), stepCellW_fst]
  refine ⟨(stepCell_len a b e r c sw.1).1, fun sw' h => ?_⟩
  have : sw'.1 ∈ (stepCellW J a b e r c sw).map Prod.fst := List.mem_map_of_mem h
  rw [stepCellW_fst] at this
  exact (stepCell_len a b e r c sw.1).2 _ this

/-! ### The entries of the DP -/

lemma grid_len {a b : ℕ} (l : List Coord) (hn : l.Nodup) (h : ∀ x ∈ l, x.1 < a ∧ x.2 < b) :
    l.length ≤ a * b := by
  have hmap : (l.map (fun x => x.1 * b + x.2)).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) hn
    obtain ⟨e1, e2⟩ := digit_inj (h x hx).2 (h y hy).2 hxy
    exact Prod.ext e1 e2
  have := nodup_len_le (a * b) _ hmap (fun v hv => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    obtain ⟨h1, h2⟩ := h x hx
    have : (x.1 + 1) * b ≤ a * b := Nat.mul_le_mul_right _ h1
    simp only [Nat.succ_mul] at this
    omega)
  simpa using this

/-- The entry list after `n` cells. -/
def foldW (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) : List (St × Wit) :=
  (List.range n).foldl (stageW J a b tm) [(([], 0), ([], ([], [])))]

lemma foldW_succ (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) :
    foldW J a b tm (n + 1) = stageW J a b tm (foldW J a b tm n) n := by
  simp [foldW, List.range_succ, List.foldl_append]

theorem dedupKeyAux_nodup : ∀ (seen : List St) (l : List (St × Wit)),
    ((dedupKeyAux seen l).map Prod.fst).Nodup ∧ ∀ x ∈ dedupKeyAux seen l, x.1 ∉ seen
  | _, [] => by simp [dedupKeyAux]
  | seen, x :: l => by
    unfold dedupKeyAux
    split_ifs with h
    · exact dedupKeyAux_nodup seen l
    · obtain ⟨h1, h2⟩ := dedupKeyAux_nodup (x.1 :: seen) l
      refine ⟨?_, fun y hy => ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, h1⟩
        obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
        exact h2 y hy (by rw [e]; exact List.mem_cons_self)
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact h
        · exact fun hm => h2 y hy (List.mem_cons_of_mem _ hm)

section Entries

variable {a b : ℕ} {J : Inst} {tm : List ((ℕ × ℕ) × ℕ)}

lemma foldW_WC (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    ∀ n, n ≤ a * b → ∀ sw ∈ foldW J a b tm n, WC a b J n sw := by
  intro n
  induction n with
  | zero => intro _ sw hs; rw [List.mem_singleton.mp hs]; exact WC_zero
  | succ n ih =>
    intro hn sw hs
    rw [foldW_succ] at hs
    unfold stageW dedupKey at hs
    have hs := dedupKeyAux_sub _ _ _ hs
    rw [List.mem_filter, List.mem_flatMap] at hs
    obtain ⟨⟨t, ht, hst⟩, -⟩ := hs
    exact stepW_WC htm (by omega) (ih (by omega) t ht) hst

lemma foldW_noExit (n : ℕ) : ∀ sw ∈ foldW J a b tm n, noExit a b sw.1 = true := by
  cases n with
  | zero =>
    intro sw hs
    simp only [foldW, List.range_zero, List.foldl_nil, List.mem_singleton] at hs
    subst hs; rfl
  | succ n =>
    intro sw hs
    rw [foldW_succ] at hs
    unfold stageW dedupKey at hs
    exact (List.mem_filter.mp (dedupKeyAux_sub _ _ _ hs)).2

lemma foldW_nodup (n : ℕ) : ((foldW J a b tm n).map Prod.fst).Nodup := by
  cases n with
  | zero => simp [foldW]
  | succ n => rw [foldW_succ]; exact (dedupKeyAux_nodup _ _).1

/-- The facts about one entry used for the time bound. -/
def EntryOK (a b : ℕ) (sw : St × Wit) : Prop :=
  sw.1.1.length ≤ Q b ∧ sw.2.1.length ≤ Q b ∧ (∀ z ∈ sw.1.1, (lookD sw.2.1 z).length ≤ a * b) ∧
    sw.2.2.1.length ≤ a * b ∧ sw.2.2.2.length ≤ a * b

lemma entryOK_of {n : ℕ} {sw : St × Wit} (hW : WC a b J n sw) (hx : noExit a b sw.1 = true) :
    EntryOK a b sw := by
  have hg := good_of_W (W_of_WF hW.1) hx
  have hq := good_len hg
  obtain ⟨⟨-, -, hseg, hdone, -, -⟩, hkeys, hemp⟩ := hW
  have hw : sw.2.1.length = sw.1.1.length := by rw [← List.length_map (f := Prod.fst)]; exact hkeys.length_eq
  have hcol : ∀ col < 2, (dpOf sw.2.2 col).length ≤ a * b := by
    intro col hc
    by_cases hd : col ∈ doneCols sw.1.2
    · obtain ⟨-, -, hn, hb, -⟩ := hdone col hd
      exact grid_len _ hn hb
    · rw [hemp col hc hd]; simp
  refine ⟨hq, by omega, fun z hz => ?_, by simpa [dpOf] using hcol 0 (by omega),
    by simpa [dpOf] using hcol 1 (by omega)⟩
  obtain ⟨hn, -, hp, -⟩ := (hseg z hz).2
  exact grid_len _ hn (fun x hx => ⟨(hp x hx).1, (hp x hx).2.1⟩)

lemma foldW_entries (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) (n : ℕ)
    (hn : n ≤ a * b) : (foldW J a b tm n).length ≤ Nst b ∧ ∀ sw ∈ foldW J a b tm n, EntryOK a b sw := by
  have hE : ∀ sw ∈ foldW J a b tm n, EntryOK a b sw :=
    fun sw hs => entryOK_of (foldW_WC htm n hn sw hs) (foldW_noExit n sw hs)
  refine ⟨?_, hE⟩
  have := card_good (a := a) (b := b) _ (foldW_nodup n) (fun s hs => by
    obtain ⟨sw, hsw, rfl⟩ := List.mem_map.1 hs
    exact good_of_W (W_of_WF (foldW_WC htm n hn sw hsw).1) (foldW_noExit n sw hsw))
  simpa using this

end Entries

/-! ### One stage -/


lemma stageWT_time (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (htm : tm.length = 4)
    (S : List (St × Wit)) (hS : S.length ≤ Nst b) (hE : ∀ sw ∈ S, EntryOK a b sw) (i : ℕ) :
    (stageWT J a b tm S i).time ≤ (a * b + 1) * Ks b := by
  simp only [stageWT, time_bind]
  have t1 := lfindT_time_le (fun q => (pure (q.1 == cell b i) : TimeM Bool)) tm 0 (fun _ _ => by simp)
  rw [htm] at t1
  generalize optSnd (lfindT (fun q => (pure (q.1 == cell b i) : TimeM Bool)) tm).ret = e
  have t2 := lflatMapT_time_le (stepCellWT J a b e (cell b i).1 (cell b i).2) S
    (9 * Q b + 9 * (a * b) + 28) 2
    (fun sw hs => by
      obtain ⟨h1, h2, h3, -⟩ := hE sw hs
      exact stepCellWT_time J a b e _ _ sw (Q b) (a * b) h1 h2 h3)
    (fun sw _ => (stepCellWT_out J a b e _ _ sw).1)
  have hl : (lflatMapT (stepCellWT J a b e (cell b i).1 (cell b i).2) S).ret.length ≤ 2 * Nst b := by
    simp only [lflatMapT, List.length_flatMap]
    have := lsum_le S (fun sw => (stepCellWT J a b e (cell b i).1 (cell b i).2 sw).ret.length) 2
      (fun sw _ => (stepCellWT_out J a b e _ _ sw).1)
    omega
  have hlq : ∀ sw' ∈ (lflatMapT (stepCellWT J a b e (cell b i).1 (cell b i).2) S).ret,
      sw'.1.1.length ≤ Q b + 1 := by
    intro sw' hs'
    simp only [lflatMapT, List.mem_flatMap] at hs'
    obtain ⟨sw, hs, h⟩ := hs'
    have := (stepCellWT_out J a b e _ _ sw).2 sw' h
    have := (hE sw hs).1
    omega
  generalize (lflatMapT (stepCellWT J a b e (cell b i).1 (cell b i).2) S).ret = l at hl hlq
  have t3 := lfilterT_time_le (fun sw => noExitT a b sw.1) l (Q b + 1) (fun sw hs => by
    unfold noExitT
    have := lallT_time_le (fun z => (pure (okEnd a b (lo z) && okEnd a b (hi z)) : TimeM Bool)) sw.1.1 0
      (fun _ _ => by simp)
    have := hlq sw hs
    omega)
  have hf : (lfilterT (fun sw => noExitT a b sw.1) l).ret.length ≤ 2 * Nst b := by
    simp only [lfilterT]; exact le_trans (List.length_filter_le _ _) hl
  have hfq : ∀ sw ∈ (lfilterT (fun sw => noExitT a b sw.1) l).ret, sw.1.1.length ≤ Q b + 1 := by
    intro sw hs; simp only [lfilterT, List.mem_filter] at hs; exact hlq sw hs.1
  generalize (lfilterT (fun sw => noExitT a b sw.1) l).ret = f at hf hfq
  have t4 := dedupKeyAuxT_time (Q b + 1) [] f (by simp) hfq
  simp only [List.length_nil, Nat.zero_add] at t4
  have m1 : S.length * (9 * Q b + 9 * (a * b) + 28 + 2 + 1) ≤
      Nst b * (9 * Q b + 31) + 9 * Nst b * (a * b) :=
    calc S.length * (9 * Q b + 9 * (a * b) + 28 + 2 + 1)
        ≤ Nst b * (9 * Q b + 9 * (a * b) + 28 + 2 + 1) := Nat.mul_le_mul_right _ hS
      _ = Nst b * (9 * Q b + 31) + 9 * Nst b * (a * b) := by ring
  have m2 : l.length * (Q b + 1 + 1) ≤ 2 * Nst b * (Q b + 2) :=
    calc l.length * (Q b + 1 + 1) ≤ 2 * Nst b * (Q b + 1 + 1) := Nat.mul_le_mul_right _ hl
      _ = 2 * Nst b * (Q b + 2) := by ring
  have m3 : f.length * (f.length * (Q b + 1 + 1) + 1) ≤ 2 * Nst b * (2 * Nst b * (Q b + 2) + 1) :=
    calc f.length * (f.length * (Q b + 1 + 1) + 1)
        ≤ 2 * Nst b * (2 * Nst b * (Q b + 1 + 1) + 1) :=
          Nat.mul_le_mul hf (Nat.add_le_add_right (Nat.mul_le_mul_right _ hf) 1)
      _ = 2 * Nst b * (2 * Nst b * (Q b + 2) + 1) := by ring
  have e1 : (dedupKeyT f).time = (dedupKeyAuxT [] f).time := rfl
  rw [e1]
  have hKs : Ks b = 4 + Nst b * (9 * Q b + 31) + 2 * Nst b * (Q b + 2) +
      2 * Nst b * (2 * Nst b * (Q b + 2) + 1) + 9 * Nst b := rfl
  have e3 : (a * b + 1) * Ks b = Ks b + a * b * Ks b := by ring
  have m4 : 9 * Nst b * (a * b) ≤ a * b * Ks b :=
    calc 9 * Nst b * (a * b) ≤ Ks b * (a * b) := Nat.mul_le_mul_right _ (by omega)
      _ = a * b * Ks b := by ring
  omega

/-! ### The whole DP -/

lemma insideWT_time (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (htm4 : tm.length = 4)
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    (insideWT J a b tm).time ≤ (a * b + 1) + a * b * ((a * b + 1) * Ks b + 1) ∧
      (insideWT J a b tm).ret.length ≤ Nst b := by
  have hf : ∀ n, (List.range n).foldl (fun S i => (stageWT J a b tm S i).ret)
      [(([], 0), ([], ([], [])))] = foldW J a b tm n := by
    intro n; unfold foldW; congr 1; funext S i; exact stageWT_ret J a b tm S i
  have key : ∀ n, n ≤ a * b →
      (lfoldlT (stageWT J a b tm) [(([], 0), ([], ([], [])))] (List.range n)).time ≤
        n * ((a * b + 1) * Ks b + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [lfoldlT]
    | succ n ih =>
      intro hn
      rw [List.range_succ, lfoldlT_time_append, hf]
      obtain ⟨hS, hE⟩ := foldW_entries htm n (by omega)
      have := stageWT_time J a b tm htm4 (foldW J a b tm n) hS hE n
      simp only [lfoldlT]
      have h2 := ih (by omega)
      rw [Nat.succ_mul]
      omega
  refine ⟨?_, ?_⟩
  · simp only [insideWT, time_bind, rangeT]
    have := key (a * b) le_rfl
    omega
  · simp only [insideWT, ret_bind, rangeT, ret_lfoldlT]
    rw [hf]
    exact (foldW_entries htm (a * b) le_rfl).1

lemma solveDPT_time (J : Inst) :
    (solveDPT J).time ≤ (J.w * J.h + 1) + J.w * J.h * ((J.w * J.h + 1) * Ks J.h + 1) + Nst J.h := by
  obtain ⟨h1, h2⟩ := insideWT_time J J.w J.h (tmOf J) rfl (fun y _ _ => termAt_tmOf J y)
  simp only [solveDPT, time_bind, time_pure]
  have := lfindT_time_le (fun sw => stEqT sw.1 ([], 3)) (insideWT J J.w J.h (tmOf J)).ret 0
    (fun sw _ => by simp only [stEqT, time_bind, time_pure, lbeqT_nil_time]; omega)
  omega

/-! ### The solver -/


lemma Q_mono {b b' : ℕ} (h : b ≤ b') : Q b ≤ Q b' := by
  unfold Q; exact Nat.pow_le_pow_left (by omega) 2

lemma Nst_le_of_le {b b' : ℕ} (h : b ≤ b') : Nst b ≤ Nst b' := by
  unfold Nst
  have hq := Q_mono h
  have : (Q b + 1) ^ Q b ≤ (Q b' + 1) ^ Q b' :=
    le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) hq)
  omega

/-- **`Kw` is monotone.** -/
theorem Kw_mono {b b' : ℕ} (h : b ≤ b') : Kw b ≤ Kw b' := by
  have hq := Q_mono h
  have hn := Nst_le_of_le h
  unfold Kw Ks
  gcongr

lemma solveDPT_le (J : Inst) : (solveDPT J).time + 2 * (J.w * J.h) ≤ (J.w * J.h + 1) ^ 2 * Kw J.h := by
  have h := solveDPT_time J
  set A := J.w * J.h
  set K := Ks J.h
  set N := Nst J.h
  have e : (A + 1) ^ 2 * Kw J.h = A * ((A + 1) * K) + (A + 1) * K + (A + 1) ^ 2 * (N + 4) := by
    unfold Kw; ring
  have m0 : (A + 1) * (N + 4) ≤ (A + 1) ^ 2 * (N + 4) := by
    rw [pow_two, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  have m1 : (A + 1) * (N + 4) = A * N + 4 * A + N + 4 := by ring
  have m2 : 0 ≤ (A + 1) * K := Nat.zero_le _
  rw [e]
  have e2 : A * ((A + 1) * K + 1) = A * ((A + 1) * K) + A := by ring
  omega

/-- **The counted solver takes at most `(R C + 1)² Kw b` steps, where `b` is the short side.** -/
theorem thinSolveWT_time (J : Inst) :
    (thinSolveWT J).time ≤ (J.w * J.h + 1) ^ 2 * Kw (min J.w J.h) := by
  unfold thinSolveWT
  split
  · rename_i h
    rw [min_eq_right h]
    have := solveDPT_le J
    omega
  · rename_i h
    rw [min_eq_left (by omega)]
    have hle := solveDPT_le J.transpose
    simp only [Inst.transpose] at hle
    rw [Nat.mul_comm J.h J.w] at hle
    simp only [time_bind]
    have hsol := solveDPT_ret J.transpose
    generalize (solveDPT J.transpose).ret = o at hsol ⊢
    cases o with
    | none => simp only [time_pure]; simp only [Inst.transpose] at hle ⊢; omega
    | some pq =>
      obtain ⟨hp, hq, -⟩ := solveDP_sound hsol.symm
      have lp := grid_len (a := J.transpose.w) (b := J.transpose.h) pq.1 hp.2.2.1 hp.2.2.2.1
      have lq := grid_len (a := J.transpose.w) (b := J.transpose.h) pq.2 hq.2.2.1 hq.2.2.2.1
      simp only [Inst.transpose] at lp lq
      simp only [time_bind, time_pure, swapPairT]
      have t1 := lmapT_time_le (fun x : Coord => (pure x.swap : TimeM Coord)) pq.1 0 (fun _ _ => by simp)
      have t2 := lmapT_time_le (fun x : Coord => (pure x.swap : TimeM Coord)) pq.2 0 (fun _ _ => by simp)
      simp only [Inst.transpose] at hle ⊢
      rw [Nat.mul_comm J.h J.w] at lp lq
      omega

end ZZN.T
