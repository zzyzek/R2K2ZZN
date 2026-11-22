/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.ThinRope
public import ZZN.Timed.ThinWordCount
public import ZZN.Timed.ThinWitCost

@[expose] public section

/-!
# The time of the plug DP with tree segments

A stage holds at most `Nw b = wcnt (b + 1) 0 0 0` entries (`card_fold`), each with at most `b + 1`
pieces (`pieces_le`: different pieces have different plug codes `lo`). One cell of one entry costs
`O(b)`: the tree segments are built in constant time. So a stage costs at most `KsR b` steps, the
whole DP `O(a b KsR b)`, and reading out the answer flattens two trees of at most `9 a b + 1` nodes
(`RS`: a tree of `m` cells has at most `9 m + 1` nodes). The solver takes at most
`(R C + 1) KwR b` steps, `b` the short side (`thinSolveWRT_time`): linear in the area.
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

/-! ### Constants -/

/-- The bound on the states of one stage. -/
def Nw (b : ℕ) : ℕ := wcnt (b + 1) 0 0 0

/-- Enough merge-sort levels for `2 Nw b` entries. -/
def LgW (b : ℕ) : ℕ := Nat.log2 (2 * Nw b) + 1

/-- The cost of one stage. -/
def KsR (b : ℕ) : ℕ := 4 + Nw b * (9 * (b + 1) + 31) + 2 * Nw b * (b + 3) +
    (2 * Nw b + 1 + ((b + 8) * (2 * Nw b) * (LgW b + 1) + 1) + 2 * Nw b * (b + 3))

/-- The cost per cell of the solver. -/
def KwR (b : ℕ) : ℕ := KsR b + 2 * Nw b + 30

/-! ### Pieces -/

lemma pieces_le {a b n : ℕ} {s : St} (h : SW a b n s) : s.1.length ≤ b + 1 := by
  have hn : (s.1.map lo).Nodup := by
    refine List.Nodup.map_on (fun z hz z' hz' he => ?_) h.good.1.1
    exact h.good.2.2.2 z hz z' hz' (lo z) (h.plug z hz) (Or.inl rfl) (Or.inl he.symm)
  have hsub : (s.1.map lo).toFinset ⊆ Finset.range (b + 1) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact Finset.mem_range.mpr (by have := h.plug z hz; omega)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, List.length_map, Finset.card_range] at this
  exact this

/-! ### One cell -/

lemma lookDRT_time (l : List (ℕ × Rp)) (z : ℕ) : (lookDRT l z).time ≤ l.length := by
  simp only [lookDRT, time_bind, time_pure]
  have := lfindT_time_le (fun q => (pure (q.1 == z) : TimeM Bool)) l 0 (fun _ _ => by simp)
  omega

lemma segNewRT_time (b r c : ℕ) (w : List (ℕ × Rp)) (pu pl : Option ℕ) :
    (segNewRT b r c w pu pl).time ≤ 2 * w.length := by
  rcases pu with _ | zu <;> rcases pl with _ | zl
  · simp [segNewRT]
  · simp only [segNewRT, time_bind, time_pure]; have := lookDRT_time w zl; omega
  · simp only [segNewRT, time_bind, time_pure]; have := lookDRT_time w zu; omega
  · simp only [segNewRT, time_bind, time_pure]
    have := lookDRT_time w zu; have := lookDRT_time w zl; omega

lemma stepCellWRT_time (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × WitR) (q : ℕ)
    (hs : sw.1.1.length ≤ q) (hw : sw.2.1.length ≤ q) :
    (stepCellWRT a b e r c sw).time ≤ 9 * q + 28 := by
  simp only [stepCellWRT, time_bind]
  have t1 := lookT_time (r == 0) c sw.1.1
  have t2 := lookT_time (c == 0) b sw.1.1
  have hpl : (lookT (c == 0) b sw.1.1).ret = plOf b sw.1 c := lookT_pu sw.1 c b
  rw [lookT_pu, hpl]
  have t3 := segNewRT_time b r c sw.2.1 (puOf sw.1 r c) (plOf b sw.1 c)
  have t4 := lfilterT_time_le (fun q => (pure (puOf sw.1 r c != some q.1 && plOf b sw.1 c != some q.1) :
    TimeM Bool)) sw.2.1 0 (fun _ _ => by simp)
  have t5 := stepTailGT_time a b e r c sw.1 (puOf sw.1 r c) (plOf b sw.1 c)
  have hG : (stepTailGT a b e r c sw.1 (puOf sw.1 r c) (plOf b sw.1 c)).ret.length ≤ 2 := by
    rw [stepTailGT_ret, ← List.length_map (f := Prod.snd), stepCellG_snd]
    exact (stepCell_len a b e r c sw.1).1
  generalize (segNewRT b r c sw.2.1 (puOf sw.1 r c) (plOf b sw.1 c)).ret = Ln
  generalize (lfilterT (fun q => (pure (puOf sw.1 r c != some q.1 && plOf b sw.1 c != some q.1) :
    TimeM Bool)) sw.2.1).ret = sgR
  have t6 := lmapT_time_le (fun g : (ℕ × ℕ) × St =>
      (pure (g.2, closeWitR a b g.1.1 g.1.2 Ln sgR sw.2.2) : TimeM (St × WitR)))
    (stepTailGT a b e r c sw.1 (puOf sw.1 r c) (plOf b sw.1 c)).ret 0 (fun _ _ => by simp)
  omega

lemma stepCellWRT_fst (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × WitR) :
    (stepCellWRT a b e r c sw).ret.map Prod.fst = stepCell a b e r c sw.1 := by
  have h := congrArg (List.map Prod.fst) (stepCellWRT_flat J a b e r c sw)
  rw [List.map_map, stepCellW_fst] at h
  exact h

lemma stepCellWRT_out (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × WitR) :
    (stepCellWRT a b e r c sw).ret.length ≤ 2 ∧
      ∀ sw' ∈ (stepCellWRT a b e r c sw).ret, sw'.1.1.length ≤ sw.1.1.length + 1 := by
  have hm := stepCellWRT_fst J a b e r c sw
  refine ⟨?_, fun sw' h => ?_⟩
  · rw [← List.length_map (f := Prod.fst), hm]; exact (stepCell_len a b e r c sw.1).1
  · have : sw'.1 ∈ (stepCellWRT a b e r c sw).ret.map Prod.fst := List.mem_map_of_mem h
    rw [hm] at this
    exact (stepCell_len a b e r c sw.1).2 _ this

/-! ### One stage -/

lemma stageWRT_time (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (htm : tm.length = 4)
    (S : List (St × WitR)) (hS : S.length ≤ Nw b)
    (hE : ∀ sw ∈ S, sw.1.1.length ≤ b + 1 ∧ sw.2.1.length ≤ b + 1) (i : ℕ) :
    (stageWRT a b tm S i).time ≤ KsR b := by
  simp only [stageWRT, time_bind]
  have t1 := lfindT_time_le (fun q => (pure (q.1 == cell b i) : TimeM Bool)) tm 0 (fun _ _ => by simp)
  rw [htm] at t1
  generalize optSnd (lfindT (fun q => (pure (q.1 == cell b i) : TimeM Bool)) tm).ret = e
  have t2 := lflatMapT_time_le (stepCellWRT a b e (cell b i).1 (cell b i).2) S
    (9 * (b + 1) + 28) 2
    (fun sw hs => stepCellWRT_time a b e _ _ sw (b + 1) (hE sw hs).1 (hE sw hs).2)
    (fun sw _ => (stepCellWRT_out J a b e _ _ sw).1)
  have hl : (lflatMapT (stepCellWRT a b e (cell b i).1 (cell b i).2) S).ret.length ≤ 2 * Nw b := by
    simp only [lflatMapT, List.length_flatMap]
    have := lsum_le S (fun sw => (stepCellWRT a b e (cell b i).1 (cell b i).2 sw).ret.length) 2
      (fun sw _ => (stepCellWRT_out J a b e _ _ sw).1)
    omega
  have hlq : ∀ sw' ∈ (lflatMapT (stepCellWRT a b e (cell b i).1 (cell b i).2) S).ret,
      sw'.1.1.length ≤ b + 1 + 1 := by
    intro sw' hs'
    simp only [lflatMapT, List.mem_flatMap] at hs'
    obtain ⟨sw, hs, h⟩ := hs'
    have := (stepCellWRT_out J a b e _ _ sw).2 sw' h
    have := (hE sw hs).1
    omega
  generalize (lflatMapT (stepCellWRT a b e (cell b i).1 (cell b i).2) S).ret = l at hl hlq
  have t3 := lfilterT_time_le (fun sw => noExitT a b sw.1) l (b + 1 + 1) (fun sw hs => by
    unfold noExitT
    have := lallT_time_le (fun z => (pure (okEnd a b (lo z) && okEnd a b (hi z)) : TimeM Bool)) sw.1.1 0
      (fun _ _ => by simp)
    have := hlq sw hs
    omega)
  have hf : (lfilterT (fun sw => noExitT a b sw.1) l).ret.length ≤ 2 * Nw b := by
    simp only [lfilterT]; exact le_trans (List.length_filter_le _ _) hl
  have hfq : ∀ sw ∈ (lfilterT (fun sw => noExitT a b sw.1) l).ret, sw.1.1.length ≤ b + 1 + 1 := by
    intro sw hs; simp only [lfilterT, List.mem_filter] at hs; exact hlq sw hs.1
  generalize (lfilterT (fun sw => noExitT a b sw.1) l).ret = f at hf hfq
  have hlg : 2 * Nw b < 2 ^ LgW b := Nat.lt_log2_self
  have t4 := dedupGT_time (b + 1 + 1) (LgW b) f (by omega) hfq
  have m1 : S.length * (9 * (b + 1) + 28 + 2 + 1) ≤ Nw b * (9 * (b + 1) + 31) :=
    Nat.mul_le_mul_right _ hS
  have m2 : l.length * (b + 1 + 1 + 1) ≤ 2 * Nw b * (b + 3) :=
    calc l.length * (b + 1 + 1 + 1) ≤ 2 * Nw b * (b + 1 + 1 + 1) := Nat.mul_le_mul_right _ hl
      _ = 2 * Nw b * (b + 3) := by ring
  have m3 : (b + 1 + 1 + 6) * f.length * (LgW b + 1) ≤ (b + 8) * (2 * Nw b) * (LgW b + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)
  have m3' : f.length * (b + 1 + 1 + 1) ≤ 2 * Nw b * (b + 3) :=
    calc f.length * (b + 1 + 1 + 1) ≤ 2 * Nw b * (b + 1 + 1 + 1) := Nat.mul_le_mul_right _ hf
      _ = 2 * Nw b * (b + 3) := by ring
  unfold KsR
  omega

/-! ### The entries of the DP -/

/-- The entry list after `n` cells. -/
def foldWR (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) : List (St × WitR) :=
  (List.range n).foldl (fun S i => (stageWRT a b tm S i).ret) [(([], 0), ([], (Rp.nil, Rp.nil)))]

lemma foldWR_succ (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (n : ℕ) :
    foldWR a b tm (n + 1) = (stageWRT a b tm (foldWR a b tm n) n).ret := by
  simp [foldWR, List.range_succ, List.foldl_append]

section Entries
variable {a b : ℕ} {J : Inst} {tm : List ((ℕ × ℕ) × ℕ)}

lemma foldWR_map (n : ℕ) : (foldWR a b tm n).map (flatE J) = foldW J a b tm n :=
  foldWR_flat J a b tm n

lemma foldWR_mem {n : ℕ} {sw : St × WitR} (h : sw ∈ foldWR a b tm n) : flatE J sw ∈ foldW J a b tm n := by
  rw [← foldWR_map]; exact List.mem_map_of_mem h

lemma foldWR_entries (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) (n : ℕ)
    (hn : n ≤ a * b) : (foldWR a b tm n).length ≤ Nw b ∧
      ∀ sw ∈ foldWR a b tm n, sw.1.1.length ≤ b + 1 ∧ sw.2.1.length ≤ b + 1 := by
  have hlen : (foldWR a b tm n).length = ((foldW J a b tm n).map Prod.fst).length := by
    rw [List.length_map, ← foldWR_map (J := J), List.length_map]
  refine ⟨?_, fun sw hs => ?_⟩
  · rw [hlen]
    exact card_fold htm hn _ (foldW_nodup n) (fun s hs => (foldW2_fst n s).mp hs)
  · have hm := foldWR_mem (J := J) hs
    have hfst : sw.1 ∈ (List.range n).foldl (stageF a b tm) [([], 0)] :=
      (foldW2_fst n sw.1).mp (List.mem_map_of_mem (f := Prod.fst) hm)
    have hkeys := (foldW_WC htm n hn _ hm).2.1
    have hk : sw.2.1.length = sw.1.1.length := by
      have := hkeys.length_eq
      simpa [flatE, flatW] using this
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have h0 : n = 0 := by simpa using hn
      subst h0
      simp only [foldWR, List.range_zero, List.foldl_nil, List.mem_singleton] at hs
      subst hs; simp
    · have := pieces_le (sw_of_fold htm hb hn hfst).1
      omega

end Entries

/-! ### Tree sizes -/

/-- A tree of `m` cells has at most `9 m + 1` nodes. -/
def RS (R : Rp) : Prop := R.size ≤ 9 * R.toL.length + 1

/-- All trees of a witness. -/
def RSw (w : WitR) : Prop := (∀ q ∈ w.1, RS q.2) ∧ RS w.2.1 ∧ RS w.2.2

lemma lookDRT_RS (l : List (ℕ × Rp)) (hl : ∀ q ∈ l, RS q.2) (z : ℕ) : RS (lookDRT l z).ret := by
  simp only [lookDRT, ret_bind, lfindT, ret_pure]
  split
  · rename_i q hq
    exact hl q (List.mem_of_find?_eq_some hq)
  · simp [RS, Rp.size, Rp.toL]

lemma orientSR_size (e z : ℕ) (R : Rp) :
    (orientSR e z R).size ≤ R.size + 1 ∧ (orientSR e z R).toL.length = R.toL.length := by
  unfold orientSR
  split
  · exact ⟨by simp only [Rp.size]; omega, by simp [Rp.toL]⟩
  · exact ⟨Nat.le_succ _, rfl⟩

lemma segNewRT_size (b r c : ℕ) (w : List (ℕ × Rp)) (hw : ∀ q ∈ w, RS q.2) (pu pl : Option ℕ) :
    (segNewRT b r c w pu pl).ret.size + 1 ≤ 9 * (segNewRT b r c w pu pl).ret.toL.length := by
  rcases pu with _ | zu <;> rcases pl with _ | zl
  · simp [segNewRT, Rp.size, Rp.toL]
  · simp only [segNewRT, ret_bind, ret_pure, Rp.size, Rp.toL, List.length_append, List.length_singleton]
    have h1 := lookDRT_RS w hw zl
    have h2 := orientSR_size b zl (lookDRT w zl).ret
    unfold RS at h1; omega
  · simp only [segNewRT, ret_bind, ret_pure, Rp.size, Rp.toL, List.length_append, List.length_singleton,
      List.length_reverse, List.length_nil]
    have h1 := lookDRT_RS w hw zu
    have h2 := orientSR_size c zu (lookDRT w zu).ret
    unfold RS at h1; omega
  · simp only [segNewRT, ret_bind, ret_pure, Rp.size, Rp.toL, List.length_append, List.length_singleton,
      List.length_reverse]
    have h1 := lookDRT_RS w hw zu
    have h2 := orientSR_size c zu (lookDRT w zu).ret
    have h3 := lookDRT_RS w hw zl
    have h4 := orientSR_size b zl (lookDRT w zl).ret
    unfold RS at h1 h3; omega

lemma stepCellWRT_RS (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × WitR) (hw : RSw sw.2) :
    ∀ sw' ∈ (stepCellWRT a b e r c sw).ret, RSw sw'.2 := by
  intro sw' hs
  simp only [stepCellWRT, ret_bind, lmapT, ret_pure, List.mem_map] at hs
  obtain ⟨g, -, rfl⟩ := hs
  have hn := segNewRT_size b r c sw.2.1 hw.1 (lookT (r == 0) c sw.1.1).ret (lookT (c == 0) b sw.1.1).ret
  generalize (segNewRT b r c sw.2.1 (lookT (r == 0) c sw.1.1).ret (lookT (c == 0) b sw.1.1).ret).ret = Ln at hn
  have hf : ∀ q ∈ (lfilterT (fun q => (pure ((lookT (r == 0) c sw.1.1).ret != some q.1 &&
      (lookT (c == 0) b sw.1.1).ret != some q.1) : TimeM Bool)) sw.2.1).ret, RS q.2 := by
    intro q hq
    simp only [lfilterT, ret_pure, List.mem_filter] at hq
    exact hw.1 q hq.1
  generalize (lfilterT (fun q => (pure ((lookT (r == 0) c sw.1.1).ret != some q.1 &&
      (lookT (c == 0) b sw.1.1).ret != some q.1) : TimeM Bool)) sw.2.1).ret = sgR at hf
  unfold closeWitR
  split
  · unfold setDpR
    split
    · exact ⟨hf, (by unfold RS; omega : RS Ln), hw.2.2⟩
    · exact ⟨hf, hw.2.1, (by unfold RS; omega : RS Ln)⟩
  · refine ⟨fun q hq => ?_, hw.2.1, hw.2.2⟩
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · unfold RS orientNR; split <;> simp [Rp.size, Rp.toL] <;> omega
    · exact hf q hq

lemma foldWR_RS (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : ∀ n, ∀ sw ∈ foldWR a b tm n, RSw sw.2 := by
  intro n
  induction n with
  | zero =>
    intro sw hs
    simp only [foldWR, List.range_zero, List.foldl_nil, List.mem_singleton] at hs
    subst hs
    simp [RSw, RS, Rp.size, Rp.toL]
  | succ n ih =>
    intro sw hs
    rw [foldWR_succ] at hs
    simp only [stageWRT, ret_bind, dedupGT_ret, lfilterT, lflatMapT] at hs
    have hs := dedupK_sub Prod.fst hs
    rw [List.mem_filter, List.mem_flatMap] at hs
    obtain ⟨⟨t, ht, hst⟩, -⟩ := hs
    exact stepCellWRT_RS a b _ _ _ t (ih t ht) sw hst

lemma flatAccT_time : ∀ (R : Rp) (rv : Bool) (acc : List Coord), (flatAccT R rv acc).time ≤ R.size
  | Rp.nil, _, _ => by simp [flatAccT, Rp.size]
  | Rp.leaf _, _, _ => by simp [flatAccT, Rp.size]
  | Rp.app l r, rv, acc => by
    cases rv
    · simp only [flatAccT, time_bind, Rp.size, Bool.false_eq_true, ↓reduceIte]
      have h1 := flatAccT_time r false acc
      have h2 := flatAccT_time l false (flatAccT r false acc).ret
      omega
    · simp only [flatAccT, time_bind, Rp.size, ↓reduceIte]
      have h1 := flatAccT_time l true acc
      have h2 := flatAccT_time r true (flatAccT l true acc).ret
      omega
  | Rp.rev r, rv, acc => by
    simp only [flatAccT, time_bind, Rp.size]
    have := flatAccT_time r (!rv) acc
    simp; omega

lemma flatT_time (R : Rp) (h : RS R) : (flatT R).time ≤ 9 * R.toL.length + 1 :=
  le_trans (flatAccT_time R false []) h

/-! ### The whole DP and the solver -/

lemma insideWRT_time (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (htm4 : tm.length = 4)
    (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) :
    (insideWRT a b tm).time ≤ (a * b + 1) + a * b * (KsR b + 1) ∧
      (insideWRT a b tm).ret = foldWR a b tm (a * b) := by
  have key : ∀ n, n ≤ a * b →
      (lfoldlT (stageWRT a b tm) [(([], 0), ([], (Rp.nil, Rp.nil)))] (List.range n)).time ≤
        n * (KsR b + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [lfoldlT]
    | succ n ih =>
      intro hn
      rw [List.range_succ, lfoldlT_time_append]
      obtain ⟨hS, hE⟩ := foldWR_entries htm n (by omega)
      have := stageWRT_time J a b tm htm4 (foldWR a b tm n) hS hE n
      simp only [lfoldlT]
      have h2 := ih (by omega)
      unfold foldWR at this
      rw [Nat.succ_mul]
      omega
  refine ⟨?_, ?_⟩
  · simp only [insideWRT, time_bind, rangeT]
    have := key (a * b) le_rfl
    omega
  · simp only [insideWRT, ret_bind, rangeT, ret_lfoldlT]
    rfl

lemma orientP_length (J : Inst) (col : ℕ) (L : List Coord) : (orientP J col L).length = L.length := by
  unfold orientP; split <;> simp

lemma orientPT_time (J : Inst) (col : ℕ) (L : List Coord) : (orientPT J col L).time ≤ L.length + 1 := by
  unfold orientPT; split <;> simp [lreverseT]

lemma solveDPRT_time (J : Inst) :
    (solveDPRT J).time ≤ (J.w * J.h + 1) + J.w * J.h * (KsR J.h + 1) + Nw J.h +
      2 * (9 * (J.w * J.h) + 1) + 2 * (J.w * J.h + 1) := by
  have htm : ∀ y : Coord, y.1 < J.w → y.2 < J.h → termAt (tmOf J) y = endCol J y :=
    fun y _ _ => termAt_tmOf J y
  obtain ⟨h1, h2⟩ := insideWRT_time J J.w J.h (tmOf J) rfl htm
  have hlen := (foldWR_entries htm (J.w * J.h) le_rfl).1
  simp only [solveDPRT, time_bind]
  have t2 := lfindT_time_le (fun sw => stEqT sw.1 ([], 3)) (insideWRT J.w J.h (tmOf J)).ret 0
    (fun sw _ => by simp only [stEqT, time_bind, time_pure, lbeqT_nil_time]; omega)
  rw [h2] at t2 ⊢
  split
  · rename_i sw hf
    have hm : sw ∈ foldWR J.w J.h (tmOf J) (J.w * J.h) := by
      simp only [lfindT] at hf; exact List.mem_of_find?_eq_some hf
    have hrs := foldWR_RS J.w J.h (tmOf J) _ sw hm
    have hmf := foldWR_mem (J := J) hm
    have hE := entryOK_of (foldW_WC htm _ le_rfl _ hmf) (foldW_noExit _ _ hmf)
    obtain ⟨-, -, -, l0, l1⟩ := hE
    simp only [flatE, flatW, orientP_length] at l0 l1
    simp only [time_bind, time_pure, flatT_ret]
    have f0 := flatT_time _ hrs.2.1
    have f1 := flatT_time _ hrs.2.2
    have o0 := orientPT_time J 0 sw.2.2.1.toL
    have o1 := orientPT_time J 1 sw.2.2.2.toL
    omega
  · simp only [time_pure]
    omega

lemma solveDPRT_le (J : Inst) : (solveDPRT J).time + 2 * (J.w * J.h) ≤ (J.w * J.h + 1) * KwR J.h := by
  have h := solveDPRT_time J
  unfold KwR
  generalize KsR J.h = K at h ⊢
  generalize Nw J.h = N at h ⊢
  generalize J.w * J.h = A at h ⊢
  have e : (A + 1) * (K + 2 * N + 30) = A * K + K + 2 * N * A + 2 * N + 30 * A + 30 := by ring
  have e2 : A * (K + 1) = A * K + A := by ring
  rw [e]
  omega

/-- **The tree-segment solver takes at most `(R C + 1) KwR b` steps, `b` the short side.** -/
theorem thinSolveWRT_time (J : Inst) :
    (thinSolveWRT J).time ≤ (J.w * J.h + 1) * KwR (min J.w J.h) := by
  unfold thinSolveWRT
  split
  · rename_i h
    rw [min_eq_right h]
    have := solveDPRT_le J
    omega
  · rename_i h
    rw [min_eq_left (by omega)]
    have hle := solveDPRT_le J.transpose
    simp only [Inst.transpose] at hle
    rw [Nat.mul_comm J.h J.w] at hle
    simp only [time_bind]
    have hsol := solveDPRT_ret J.transpose
    generalize (solveDPRT J.transpose).ret = o at hsol ⊢
    cases o with
    | none => simp only [time_pure]; simp only [Inst.transpose] at hle ⊢; omega
    | some pq =>
      obtain ⟨hp, hq, -⟩ := solveDP2_sound hsol.symm
      have lp := grid_len (a := J.transpose.w) (b := J.transpose.h) pq.1 hp.2.2.1 hp.2.2.2.1
      have lq := grid_len (a := J.transpose.w) (b := J.transpose.h) pq.2 hq.2.2.1 hq.2.2.2.1
      simp only [Inst.transpose] at lp lq
      simp only [time_bind, time_pure, swapPairT]
      have t1 := lmapT_time_le (fun x : Coord => (pure x.swap : TimeM Coord)) pq.1 0 (fun _ _ => by simp)
      have t2 := lmapT_time_le (fun x : Coord => (pure x.swap : TimeM Coord)) pq.2 0 (fun _ _ => by simp)
      simp only [Inst.transpose] at hle ⊢
      rw [Nat.mul_comm J.h J.w] at lp lq
      omega

/-! ### Monotonicity -/

lemma wcnt_le_succ (m d u v : ℕ) : wcnt m d u v ≤ wcnt (m + 1) d u v := by
  conv_rhs => unfold wcnt
  omega

lemma Nw_mono {b b' : ℕ} (h : b ≤ b') : Nw b ≤ Nw b' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (wcnt_le_succ _ 0 0 0)

lemma Nw_pos (b : ℕ) : 0 < Nw b := by
  have h : ∀ m, wcnt 0 0 0 0 ≤ wcnt m 0 0 0 := by
    intro m
    induction m with
    | zero => exact le_refl _
    | succ m ih => exact ih.trans (wcnt_le_succ m 0 0 0)
  have h0 : wcnt 0 0 0 0 = 4 := rfl
  have := h (b + 1)
  unfold Nw
  omega

lemma LgW_mono {b b' : ℕ} (h : b ≤ b') : LgW b ≤ LgW b' := by
  have hn := Nw_mono h
  have h0 : 2 * Nw b ≠ 0 := by have := Nw_pos b; omega
  unfold LgW
  have : Nat.log2 (2 * Nw b) ≤ Nat.log2 (2 * Nw b') :=
    (Nat.le_log2 (by have := Nw_pos b'; omega)).mpr (le_trans (Nat.log2_self_le h0) (by omega))
  omega

/-- **`KwR` is monotone.** -/
theorem KwR_mono {b b' : ℕ} (h : b ≤ b') : KwR b ≤ KwR b' := by
  have hn := Nw_mono h
  have hl := LgW_mono h
  unfold KwR KsR
  gcongr

end ZZN.T
