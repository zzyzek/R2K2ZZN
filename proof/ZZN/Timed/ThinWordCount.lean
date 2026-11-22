/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.ThinWord

@[expose] public section

/-!
# The word of a reached state is valid

The letters `1, 2` of a reached state are the opening and closing places of a non-crossing
matching on the places `0 .. b`, so every prefix has at most as many `2` as `1` and the whole word
equally many (`card_cl_le_range`, `card_cl_eq_range`). Letters `3 + col` name pieces ending at an
endpoint of colour `col`; their segments end at distinct endpoint cells of that colour, so there
are at most two (`tcount_le`), and none once the colour is done, since then its path holds both
endpoint cells (`dn_bit`). Hence the word lies in `wset (b + 1) 0 0 0` and a duplicate-free list
of reached states has at most `wcnt (b + 1) 0 0 0` entries (`card_sw`, `card_fold`).
-/

namespace ZZN.T

open ZZN ZZN.Thin GridHam

section Prefix
open Classical
variable {M : ℕ → ℕ → Prop}

lemma card_cl_le_range (hM : Mtch M) (k : ℕ) :
    ((Finset.range k).filter (Cl M)).card ≤ ((Finset.range k).filter (Op M)).card := by
  apply Finset.card_le_card_of_injOn (pcl M)
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
    obtain ⟨s1, s2⟩ := pcl_spec hi.2
    exact ⟨by omega, ⟨i, s1, hM.symm _ _ s2⟩⟩
  · intro i hi i' hi' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hi'
    have a1 := (pcl_spec hi.2).2
    have a2 := (pcl_spec hi'.2).2
    rw [h] at a1
    exact hM.func _ _ _ (hM.symm _ _ a1) (hM.symm _ _ a2)

lemma card_cl_eq_range (hM : Mtch M) (m : ℕ) (hb : ∀ p q, M p q → p < m) :
    ((Finset.range m).filter (Cl M)).card = ((Finset.range m).filter (Op M)).card := by
  refine le_antisymm (card_cl_le_range hM m) ?_
  apply Finset.card_le_card_of_injOn (pop M)
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
    obtain ⟨s1, s2⟩ := pop_spec hi.2
    exact ⟨hb _ _ (hM.symm _ _ s2), ⟨i, s1, hM.symm _ _ s2⟩⟩
  · intro i hi i' hi' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hi'
    have a1 := (pop_spec hi.2).2
    have a2 := (pop_spec hi'.2).2
    rw [h] at a1
    exact hM.func _ _ _ (hM.symm _ _ a1) (hM.symm _ _ a2)

end Prefix

lemma count_map_range (f : ℕ → ℕ) (v : ℕ) :
    ∀ k, ((List.range k).map f).count v = ((Finset.range k).filter (fun i => f i = v)).card
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.count_append, count_map_range f v k,
      Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; simp [h]
    · simp [h]

section Ends
variable {a b n : ℕ} {s : St} {J : Inst}

lemma ends_of_endCol {v : Coord} {col : ℕ} (h : endCol J v = some col) :
    v = (ends2 J col).1 ∨ v = (ends2 J col).2 := by
  unfold endCol at h
  unfold ends2
  split_ifs at h with h1 h2 <;> simp only [Option.some.injEq] at h
  · subst h; simpa using h1
  · subst h; simpa using h2

/-- A letter naming colour `col` comes from a piece from that plug to an endpoint of `col`. -/
lemma tpiece_of_letter (h : SW a b n s) {k col : ℕ} (hk : k ≤ b) (hcol : col < 2)
    (hl : letter a b n s.1 k = 3 + col) :
    ∃ z, pieceAt s.1 (codeAt b n k) = some z ∧ z ∈ s.1 ∧ lo z = codeAt b n k ∧
      hi z = termE a b col := by
  unfold letter at hl
  split at hl
  · omega
  · rename_i z hp
    obtain ⟨hz, hj⟩ := pieceAt_mem hp
    split_ifs at hl with ho
    · omega
    · omega
    · have hg := goodEnd_other (h.good.1.2.2 z hz) (codeAt b n k)
      have hcb := codeAt_le (n := n) h.pos hk
      have hlt := h.good.2.2.1 z hz
      have hot : otherAt z (codeAt b n k) = termE a b col := by
        unfold GoodEnd at hg; unfold colE termE at *; omega
      refine ⟨z, hp, hz, ?_⟩
      rcases otherAt_ends hj hlt with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨e1, e2.trans hot⟩
      · omega

/-- **At most two letters name each colour.** -/
lemma tcount_le (hW : W a b J n s) (h : SW a b n s) {col : ℕ} (hcol : col < 2) :
    ((Finset.range (b + 1)).filter (fun k => letter a b n s.1 k = 3 + col)).card ≤ 2 := by
  obtain ⟨sg, dp, hnd, -, hseg, -, hall, -⟩ := hW
  unfold allOf at hall
  have hflat : (s.1.flatMap sg).Nodup := (List.nodup_append.mp hall).1
  let f : ℕ → Coord := fun k => ((sg ((pieceAt s.1 (codeAt b n k)).getD 0)).getLast?).getD (0, 0)
  have key : ∀ k, k ≤ b → letter a b n s.1 k = 3 + col → ∃ z ∈ s.1, lo z = codeAt b n k ∧
      f k ∈ sg z ∧ (f k = (ends2 J col).1 ∨ f k = (ends2 J col).2) := by
    intro k hk hl
    obtain ⟨z, hp, hz, hlo, hhi⟩ := tpiece_of_letter h hk hcol hl
    obtain ⟨-, -, -, hpr, u, v, -, hv, -, ev⟩ := hseg z hz
    have hfk : f k = v := by simp only [f, hp, Option.getD_some, hv]
    rw [hhi] at ev
    have hvm := List.mem_of_mem_getLast? hv
    exact ⟨z, hz, hlo, hfk ▸ hvm, hfk ▸ ends_of_endCol (endOK_term (hpr v hvm) ev)⟩
  refine le_trans (Finset.card_le_card_of_injOn (t := {(ends2 J col).1, (ends2 J col).2}) f ?_ ?_)
    Finset.card_le_two
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hk
    obtain ⟨z, -, -, -, he⟩ := key k (by omega) hk.2
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact he
  · intro k hk k' hk' hff
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hk hk'
    obtain ⟨z, hz, hlo, hm, -⟩ := key k (by omega) hk.2
    obtain ⟨z', hz', hlo', hm', -⟩ := key k' (by omega) hk'.2
    rw [hff] at hm
    have := flatMap_unique hnd hflat hz hz' hm hm'
    subst this
    have e := congrArg (posP b n) (hlo.symm.trans hlo')
    rwa [posP_codeAt h.pos (by omega), posP_codeAt h.pos (by omega)] at e

/-- **A done colour has no letter.** -/
lemma dn_bit (hW : W a b J n s) (h : SW a b n s) {col : ℕ} (hcol : col < 2)
    (hbit : bitOf s.2 col = true) {k : ℕ} (hk : k ≤ b) : letter a b n s.1 k ≠ 3 + col := by
  intro hl
  obtain ⟨sg, dp, -, -, hseg, hdone, hall, -⟩ := hW
  unfold allOf at hall
  obtain ⟨z, -, hz, -, hhi⟩ := tpiece_of_letter h hk hcol hl
  obtain ⟨-, -, -, hpr, u, v, -, hv, -, ev⟩ := hseg z hz
  rw [hhi] at ev
  have hvm := List.mem_of_mem_getLast? hv
  have hend := ends_of_endCol (endOK_term (hpr v hvm) ev)
  have hcd : col ∈ doneCols s.2 := by unfold doneCols; simp [hcol, hbit]
  obtain ⟨h1, h2, -⟩ := hdone col hcd
  have hvd : v ∈ dp col := by
    rcases hend with rfl | rfl
    · exact List.mem_of_mem_head? h1
    · exact List.mem_of_mem_getLast? h2
  exact (List.nodup_append.mp hall).2.2 v (List.mem_flatMap.mpr ⟨z, hz, hvm⟩) v
    (List.mem_flatMap.mpr ⟨col, hcd, hvd⟩) rfl

open Classical in
/-- **The word of a reached state is valid.** -/
theorem word_mem (hW : W a b J n s) (h : SW a b n s) : wordOf a b n s ∈ wset (b + 1) 0 0 0 := by
  have hb := h.pos
  have hM := ms_mtch h
  set L := (List.range (b + 1)).map (letter a b n s.1) with hL
  have cnt : ∀ m, m ≤ b + 1 → ∀ v, ((List.range m).map (letter a b n s.1)).count v =
      ((Finset.range m).filter (fun i => letter a b n s.1 i = v)).card := fun m _ v =>
    count_map_range _ v m
  have fcl : ∀ m, m ≤ b + 1 → (Finset.range m).filter (fun i => letter a b n s.1 i = 2) =
      (Finset.range m).filter (Cl (Ms b n s.1)) := fun m hm =>
    Finset.filter_congr (fun i hi => (cl_iff h (by simp at hi; omega)).symm)
  have fop : ∀ m, m ≤ b + 1 → (Finset.range m).filter (fun i => letter a b n s.1 i = 1) =
      (Finset.range m).filter (Op (Ms b n s.1)) := fun m hm =>
    Finset.filter_congr (fun i hi => (op_iff h (by simp at hi; omega)).symm)
  have hpre : ∀ k, (L.take k).count 2 ≤ 0 + (L.take k).count 1 := by
    intro k
    rw [hL, ← List.map_take, List.take_range, cnt _ (min_le_right _ _), cnt _ (min_le_right _ _),
      fcl _ (min_le_right _ _), fop _ (min_le_right _ _), zero_add]
    exact card_cl_le_range hM _
  have htot : L.count 2 = 0 + L.count 1 := by
    rw [hL, cnt _ le_rfl, cnt _ le_rfl, fcl _ le_rfl, fop _ le_rfl, zero_add]
    exact card_cl_eq_range hM _ (fun p q hm => by have := (ms_le h hm).1; omega)
  have h3 : L.count 3 = ((Finset.range (b + 1)).filter (fun k => letter a b n s.1 k = 3 + 0)).card := by
    rw [hL, cnt _ le_rfl]
  have h4 : L.count 4 = ((Finset.range (b + 1)).filter (fun k => letter a b n s.1 k = 3 + 1)).card := by
    rw [hL, cnt _ le_rfl]
  have t0 := tcount_le hW h (col := 0) (by omega)
  have t1 := tcount_le hW h (col := 1) (by omega)
  have z0 : s.2 % 2 = 1 → L.count 3 = 0 := by
    intro hd
    rw [h3, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk
    exact dn_bit hW h (col := 0) (by omega) (by simp [bitOf, hd]) (by simp at hk; omega)
  have z1 : s.2 / 2 % 2 = 1 → L.count 4 = 0 := by
    intro hd
    rw [h4, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk
    exact dn_bit hW h (col := 1) (by omega) (by simp [bitOf, hd]) (by simp at hk; omega)
  have hw := mem_wset L 0 0 0 s.2 (wok_of L 0 0 0 s.2
    (fun x hx => by obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx; exact letter_lt h k) hpre htot
    (by omega) (by omega) h.good.1.2.1 (fun hd => by have := z0 hd; omega)
    (fun hd => by have := z1 hd; omega))
  rw [hL, List.length_map, List.length_range] at hw
  exact hw

/-- **A duplicate-free list of reached states has at most `wcnt (b + 1) 0 0 0` entries.** -/
theorem card_sw (S : List St) (hn : S.Nodup) (hs : ∀ s ∈ S, SW a b n s ∧ W a b J n s) :
    S.length ≤ wcnt (b + 1) 0 0 0 := by
  have hmap : (S.map (wordOf a b n)).Nodup :=
    List.Nodup.map_on (fun x hx y hy he => word_inj (hs x hx).1 (hs y hy).1 he) hn
  have hsub : (S.map (wordOf a b n)).toFinset ⊆ wset (b + 1) 0 0 0 := by
    intro w hw
    obtain ⟨s, hs', rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
    exact word_mem (hs s hs').2 (hs s hs').1
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hmap, List.length_map] at this
  exact this.trans (card_wset_le _ _ _ _)

end Ends

/-! ### Reached states -/

section Fold
variable {a b : ℕ} {J : Inst} {tm : List ((ℕ × ℕ) × ℕ)}

lemma fold_noExit : ∀ n, ∀ s ∈ (List.range n).foldl (stageF a b tm) [([], 0)], noExit a b s = true
  | 0, s, hs => by rw [List.mem_singleton.mp hs]; simp [noExit]
  | n + 1, s, hs => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs
    unfold stageF at hs
    exact (List.mem_filter.mp hs).2

/-- A reached state has the facts used for counting. -/
theorem sw_of_fold (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) (hb : 0 < b)
    {n : ℕ} (hn : n ≤ a * b) {s : St} (hs : s ∈ (List.range n).foldl (stageF a b tm) [([], 0)]) :
    SW a b n s ∧ W a b J n s := by
  have hW := fold_W htm n hn s hs
  have hx := fold_noExit n s hs
  have hg := good2_of_W hn hW hx (fold_SInv a b tm n s hs)
  refine ⟨⟨hg, fold_NC htm n hn s hs, fun z hz => ?_, hb⟩, hW⟩
  have ht := fold_NoTT a b tm n s hs z hz
  have hok := List.all_eq_true.1 hx z hz
  have hlt := hg.2.2.1 z hz
  simp only [Bool.and_eq_true, okEnd, isTerm, Bool.or_eq_true, decide_eq_true_eq] at hok ht
  omega

/-- **A duplicate-free list of states reached after `n` cells has at most `wcnt (b + 1) 0 0 0`
entries.** -/
theorem card_fold (htm : ∀ y : Coord, y.1 < a → y.2 < b → termAt tm y = endCol J y) {n : ℕ}
    (hn : n ≤ a * b) (S : List St) (hnd : S.Nodup)
    (hS : ∀ s ∈ S, s ∈ (List.range n).foldl (stageF a b tm) [([], 0)]) :
    S.length ≤ wcnt (b + 1) 0 0 0 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- No columns: only the start state.
    have h0 : n = 0 := by simpa using hn
    subst h0
    have hsub : ∀ s ∈ S, s = ([], 0) := fun s hs => List.mem_singleton.mp (hS s hs)
    have : S.length ≤ 1 := by
      rcases S with _ | ⟨x, _ | ⟨y, l⟩⟩
      · simp
      · simp
      · have e : x = y := (hsub x (by simp)).trans (hsub y (by simp)).symm
        exact absurd (e ▸ List.mem_cons_self) (List.nodup_cons.mp hnd).1
    exact this.trans (by decide)
  · exact card_sw S hnd (fun s hs => sw_of_fold htm hb hn (hS s hs))

end Fold

end ZZN.T
