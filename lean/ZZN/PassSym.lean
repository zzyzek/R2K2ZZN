-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PassTR

/-!
# The catalogue is symmetric under reversing a path and swapping the colors

`Passes` is unchanged by `Inst.rev0`, `Inst.rev1` and `Inst.swapColors`. Each is a reordering of
the endpoint list `[(s0, 0), (t0, 0), (s1, 1), (t1, 1)]`, after relabelling the colors `0 ↔ 1`
for the swap. So it suffices that every entry is unchanged
* by a reordering of endpoints on distinct cells (`Perm`), and
* by the relabelling `relab`, which swaps the colors 0 and 1.
-/

namespace ZZN

/-! ### Relabelling the colors -/

/-- Swap the colors 0 and 1 (and fix every other value, so that it is injective). -/
def sw01 (k : ℕ) : ℕ := if k = 0 then 1 else if k = 1 then 0 else k

theorem sw01_sw01 (k : ℕ) : sw01 (sw01 k) = k := by
  rcases k with _ | _ | k <;> simp [sw01]

theorem sw01_inj {a b : ℕ} (h : sw01 a = sw01 b) : a = b := by
  rw [← sw01_sw01 a, h, sw01_sw01]

@[simp] theorem sw01_inj_iff {a b : ℕ} : sw01 a = sw01 b ↔ a = b :=
  ⟨sw01_inj, fun h => h ▸ rfl⟩

theorem sw01_eq_iff {a b : ℕ} : sw01 a = b ↔ a = sw01 b :=
  ⟨fun h => by rw [← h, sw01_sw01], fun h => by rw [h, sw01_sw01]⟩

theorem sw01_le {a : ℕ} (h : a ≤ 1) : sw01 a = 1 - a := by
  unfold sw01; split_ifs <;> omega

theorem beq_sw01 (a b : ℕ) : (sw01 a == sw01 b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨sw01_inj, fun h => h ▸ rfl⟩

theorem bne_sw01 (a b : ℕ) : (sw01 a != sw01 b) = (a != b) := by
  simp only [bne, beq_sw01]

/-- Relabel the color of an endpoint. -/
def relab (q : Pt) : Pt := (q.1, sw01 q.2)

theorem relab_fst (q : Pt) : (relab q).1 = q.1 := rfl

/-- Finding by a test on the cell commutes with relabelling. -/
theorem find?_relab (l : List Pt) (p : ℕ × ℕ → Bool) :
    (l.map relab).find? (fun q => p q.1) = (l.find? (fun q => p q.1)).map relab := by
  rw [List.find?_map]
  rfl

/-! ### Views -/

theorem makeView_relab (R C : ℕ) (f : Frame) (l : List Pt) (r c : ℕ) :
    (makeView R C f (l.map relab)).at r c = ((makeView R C f l).at r c).map sw01 := by
  unfold View.at makeView
  simp only [List.map_map]
  rw [show ((fun q : Pt => (f.to R C q.1, q.2)) ∘ relab) =
      relab ∘ (fun q : Pt => (f.to R C q.1, q.2)) from rfl, ← List.map_map]
  rw [find?_relab _ (fun x => x == (r, c))]
  cases (List.find? (fun q => q.1 == (r, c)) (l.map fun q => (f.to R C q.1, q.2))) <;> rfl

theorem makeView_relab_H (R C : ℕ) (f : Frame) (l : List Pt) :
    (makeView R C f (l.map relab)).H = (makeView R C f l).H := rfl

theorem makeView_relab_W (R C : ℕ) (f : Frame) (l : List Pt) :
    (makeView R C f (l.map relab)).W = (makeView R C f l).W := rfl

/-- The rewrites only compare colors for equality. -/
theorem rewritesAt_relab {v v' : View} (hH : v'.H = v.H) (hW : v'.W = v.W)
    (h : ∀ r c, v'.at r c = (v.at r c).map sw01) : rewritesAt v' = rewritesAt v := by
  have he : ∀ cells, v'.empty cells = v.empty cells := by
    intro cells
    unfold View.empty
    congr 1
    funext x
    rw [h]
    cases v.at x.1 x.2 <;> rfl
  unfold rewritesAt
  simp only [h, he, hH, hW]
  generalize v.at 1 2 = o1
  generalize v.at 2 1 = o2
  generalize v.at 0 0 = o3
  generalize v.at 1 1 = o4
  generalize v.at 0 1 = o5
  cases o1 <;> cases o2 <;> cases o3 <;> cases o4 <;> cases o5 <;> simp [bne_sw01]

/-! ### The rewrite phase -/

def relabSt (st : RWState) : RWState := ⟨st.eff.map relab, st.removed, st.any⟩

theorem moveFirst_relab : ∀ (l : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)),
    moveFirst (l.map relab) m = (moveFirst l m).map relab
  | [], m => rfl
  | q :: l, m => by
    rw [List.map_cons, moveFirst_cons, moveFirst_cons, relab_fst]
    split_ifs
    · rfl
    · rw [List.map_cons, moveFirst_relab l m]

theorem foldl_moveFirst_relab : ∀ (M : List ((ℕ × ℕ) × (ℕ × ℕ))) (l : List Pt),
    M.foldl moveFirst (l.map relab) = (M.foldl moveFirst l).map relab
  | [], _ => rfl
  | m :: M, l => by
    simp only [List.foldl_cons]
    rw [moveFirst_relab, foldl_moveFirst_relab M]

theorem rwStep_relab (R C : ℕ) (st : RWState) (f : Frame) :
    rwStep R C (relabSt st) f = relabSt (rwStep R C st f) := by
  have hr : rewritesAt (makeView R C f (st.eff.map relab)) = rewritesAt (makeView R C f st.eff) :=
    rewritesAt_relab (makeView_relab_H R C f st.eff) (makeView_relab_W R C f st.eff)
      (makeView_relab R C f st.eff)
  unfold rwStep relabSt
  simp only [hr]
  cases rewritesAt (makeView R C f st.eff) with
  | none => rfl
  | some rw =>
    simp only
    split_ifs
    · rfl
    · rfl
    · simp only [foldl_moveFirst_relab]

theorem foldl_rwStep_relab (R C : ℕ) : ∀ (fs : List Frame) (st : RWState),
    fs.foldl (rwStep R C) (relabSt st) = relabSt (fs.foldl (rwStep R C) st)
  | [], _ => rfl
  | f :: fs, st => by
    simp only [List.foldl_cons]
    rw [rwStep_relab, foldl_rwStep_relab R C fs]

theorem rewriteAll_relab (R C : ℕ) (l : List Pt) :
    rewriteAll R C (l.map relab) = relabSt (rewriteAll R C l) :=
  foldl_rwStep_relab R C frames ⟨l, [], false⟩

/-! ### The alternation test -/

theorem sortByKey_map_snd (g : ℕ → ℕ) : ∀ l : List (ℕ × ℕ),
    sortByKey (l.map fun x => (x.1, g x.2)) = (sortByKey l).map fun x => (x.1, g x.2)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, sortByKey]
    rw [sortByKey_map_snd g l, List.filter_map, List.filter_map, List.map_append, List.map_append]
    rfl

theorem alternating_sw01 (l : List ℕ) : alternating (l.map sw01) = alternating l := by
  match l with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [a, b, c, d] => simp only [alternating, List.map_cons, List.map_nil, bne_sw01]
  | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem effAltFrom_relab (R C : ℕ) (st : RWState) : effAltFrom R C (relabSt st) = effAltFrom R C st := by
  unfold effAltFrom relabSt
  simp only [List.any_map, List.map_map]
  have e1 : ((fun q : Pt => st.removed.contains q.1) ∘ relab) = fun q => st.removed.contains q.1 := rfl
  have e2 : ((·.1) ∘ relab) = fun q : Pt => q.1 := rfl
  have e4 : ((fun pl : List ℕ × ℕ => pl.1.length != 1) ∘
      (fun q : Pt => (positions (walk3 R C st.removed) q.1, q.2)) ∘ relab) =
      ((fun pl : List ℕ × ℕ => pl.1.length != 1) ∘
      (fun q : Pt => (positions (walk3 R C st.removed) q.1, q.2))) := rfl
  have e3 : ((fun pl : List ℕ × ℕ => (pl.1.headD 0, pl.2)) ∘
      (fun q : Pt => (positions (walk3 R C st.removed) q.1, q.2)) ∘ relab) =
      (fun x : ℕ × ℕ => (x.1, sw01 x.2)) ∘ ((fun pl : List ℕ × ℕ => (pl.1.headD 0, pl.2)) ∘
        (fun q : Pt => (positions (walk3 R C st.removed) q.1, q.2))) := rfl
  rw [e1, e2, e4, e3, ← List.map_map (g := (fun x : ℕ × ℕ => (x.1, sw01 x.2))), sortByKey_map_snd,
    List.map_map]
  have e5 : ((fun x : ℕ × ℕ => x.2) ∘ fun x : ℕ × ℕ => (x.1, sw01 x.2)) =
      sw01 ∘ (fun x : ℕ × ℕ => x.2) := rfl
  rw [e5, ← List.map_map, alternating_sw01]

theorem effAlt3_relab (R C : ℕ) (l : List Pt) : effAlt3 R C (l.map relab) = effAlt3 R C l := by
  rw [effAlt3_eq, effAlt3_eq, rewriteAll_relab, effAltFrom_relab]

/-! ### Reordering: the R test -/

/-- Endpoints on distinct cells of the grid. -/
def GoodL (R C : ℕ) (l : List Pt) : Prop := (cellsOf l).Nodup ∧ ∀ q ∈ l, q.1.1 < R ∧ q.1.2 < C

theorem cellsOf_perm {l l' : List Pt} (hp : l.Perm l') : (cellsOf l).Perm (cellsOf l') := hp.map _

theorem GoodL.perm {R C : ℕ} {l l' : List Pt} (hg : GoodL R C l) (hp : l.Perm l') : GoodL R C l' :=
  ⟨(cellsOf_perm hp).nodup_iff.mp hg.1, fun q hq => hg.2 q (hp.mem_iff.mpr hq)⟩

theorem GoodL.map_relab {R C : ℕ} {l : List Pt} (hg : GoodL R C l) : GoodL R C (l.map relab) := by
  refine ⟨?_, fun q hq => ?_⟩
  · have : cellsOf (l.map relab) = cellsOf l := by unfold cellsOf; rw [List.map_map]; rfl
    rw [this]; exact hg.1
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hg.2 p hp

theorem effAlt3_perm {R C : ℕ} (hR : 4 ≤ R) (hC : 4 ≤ C) {l l' : List Pt} (hg : GoodL R C l)
    (hp : l.Perm l') : effAlt3 R C l' = effAlt3 R C l := by
  have hg' := hg.perm hp
  have h0 : Equiv R C ⟨l', [], false⟩ ⟨l, [], false⟩ :=
    ⟨hg', hg, fun q => hp.mem_iff.symm, fun _ => Iff.rfl, rfl⟩
  have h := equiv_foldl hR hC frames h0
  rw [effAlt3_eq, effAlt3_eq]
  exact effAltFrom_congr h.1.1 h.2.1.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-! ### Sorting by distinct keys does not depend on the order -/

theorem sortByKey_perm : ∀ l : List (ℕ × ℕ), (sortByKey l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => by
    simp only [sortByKey]
    have ih := sortByKey_perm xs
    rw [List.append_assoc, List.singleton_append]
    refine List.perm_middle.trans (List.Perm.cons x ?_)
    have e : (sortByKey xs).filter (fun y => decide ¬ y.1 < x.1) =
        (sortByKey xs).filter (fun y => !decide (y.1 < x.1)) := by
      simp only [decide_not]
    rw [e]
    exact (List.filter_append_perm _ _).trans ih

theorem sortByKey_sorted : ∀ l : List (ℕ × ℕ), (l.map (·.1)).Nodup →
    (sortByKey l).Pairwise (fun a b => a.1 < b.1)
  | [] => fun _ => List.Pairwise.nil
  | x :: xs => fun hn => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    have ih := sortByKey_sorted xs hn.2
    have hp := sortByKey_perm xs
    simp only [sortByKey]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨ih.filter _, List.pairwise_singleton _ _, ?_⟩, ih.filter _, ?_⟩
    · intro a ha b hb
      simp only [List.mem_filter, decide_eq_true_eq, List.mem_singleton] at ha hb
      rw [hb]; exact ha.2
    · intro a ha b hb
      simp only [List.mem_filter, decide_eq_true_eq, List.mem_append, List.mem_singleton] at ha hb
      have hb' : ¬ b.1 < x.1 := by simpa using hb.2
      have hne : b.1 ≠ x.1 := fun e => hn.1 b (hp.mem_iff.mp hb.1) e
      rcases ha with ⟨-, ha⟩ | rfl
      · omega
      · omega

theorem sortByKey_eq_of_perm {l l' : List (ℕ × ℕ)} (hn : (l.map (·.1)).Nodup) (hp : l.Perm l') :
    sortByKey l = sortByKey l' := by
  have hn' : (l'.map (·.1)).Nodup := (hp.map _).nodup_iff.mp hn
  apply List.Perm.eq_of_pairwise (le := fun a b => a.1 < b.1)
  · intro a b _ _ h1 h2; omega
  · exact sortByKey_sorted l hn
  · exact sortByKey_sorted l' hn'
  · exact (sortByKey_perm l).trans (hp.trans (sortByKey_perm l').symm)

/-! ### P, T1, L1, L6 -/

theorem parityOk_perm (R C : ℕ) {l l' : List Pt} (hp : l.Perm l') : parityOk R C l' = parityOk R C l := by
  unfold parityOk; rw [(hp.map _).sum_eq]

theorem parityOk_relab (R C : ℕ) (l : List Pt) : parityOk R C (l.map relab) = parityOk R C l := by
  unfold parityOk; rw [List.map_map]; rfl

theorem t1_keys (R C : ℕ) (l : List Pt) :
    ((l.map fun q => perimIndex R C q.1).map (·.getD 0)).zip (l.map (·.2)) =
      l.map fun q => ((perimIndex R C q.1).getD 0, q.2) := by
  rw [List.map_map, List.zip_map']; rfl

theorem t1Fires_relab (R C : ℕ) (l : List Pt) : t1Fires R C (l.map relab) = t1Fires R C l := by
  unfold t1Fires
  dsimp only
  rw [t1_keys, t1_keys, List.map_map, List.map_map]
  have e : ((fun q : Pt => ((perimIndex R C q.1).getD 0, q.2)) ∘ relab) =
      (fun x : ℕ × ℕ => (x.1, sw01 x.2)) ∘ (fun q : Pt => ((perimIndex R C q.1).getD 0, q.2)) := rfl
  have e2 : ((fun q : Pt => perimIndex R C q.1) ∘ relab) = (fun q : Pt => perimIndex R C q.1) := rfl
  rw [e, e2, ← List.map_map (g := (fun x : ℕ × ℕ => (x.1, sw01 x.2))), sortByKey_map_snd, List.map_map]
  have e5 : ((fun x : ℕ × ℕ => x.2) ∘ fun x : ℕ × ℕ => (x.1, sw01 x.2)) =
      sw01 ∘ (fun x : ℕ × ℕ => x.2) := rfl
  rw [e5, ← List.map_map, alternating_sw01]

theorem t1Fires_perm {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {l l' : List Pt} (hg : GoodL R C l)
    (hp : l.Perm l') : t1Fires R C l' = t1Fires R C l := by
  unfold t1Fires
  dsimp only
  rw [t1_keys, t1_keys]
  have ha : (l'.map fun q => perimIndex R C q.1).all Option.isSome =
      (l.map fun q => perimIndex R C q.1).all Option.isSome := (hp.map _).all_eq.symm
  rw [ha]
  by_cases hall : (l.map fun q => perimIndex R C q.1).all Option.isSome = true
  · rw [hall, Bool.true_and, Bool.true_and]
    have hn : ((l.map fun q => ((perimIndex R C q.1).getD 0, q.2)).map (·.1)).Nodup := by
      rw [List.map_map]
      refine List.Nodup.map_on ?_ (nodup_of_cells hg.1)
      intro x hx y hy hxy
      simp only [Function.comp] at hxy
      by_contra hne
      have hc : x.1 ≠ y.1 := fun e => hne (cell_unique hg.1 hx hy e)
      have sx := List.all_eq_true.mp hall _ (List.mem_map_of_mem (f := fun q : Pt => perimIndex R C q.1) hx)
      have sy := List.all_eq_true.mp hall _ (List.mem_map_of_mem (f := fun q : Pt => perimIndex R C q.1) hy)
      have ox := (perimIndex_isSome (hg.2 x hx).1 (hg.2 x hx).2).mp sx
      have oy := (perimIndex_isSome (hg.2 y hy).1 (hg.2 y hy).2).mp sy
      exact perimIndex_inj hR hC (hg.2 x hx).1 (hg.2 x hx).2 (hg.2 y hy).1 (hg.2 y hy).2 ox oy hc hxy
    rw [sortByKey_eq_of_perm hn (hp.map _)]
  · simp only [Bool.not_eq_true] at hall
    rw [hall, Bool.false_and, Bool.false_and]

theorem l1Prop_perm (R C : ℕ) {l l' : List Pt} (hp : l.Perm l') : L1Prop R C l' ↔ L1Prop R C l := by
  unfold L1Prop
  simp only [hp.mem_iff]

theorem l1Prop_relab (R C : ℕ) (l : List Pt) : L1Prop R C (l.map relab) ↔ L1Prop R C l := by
  unfold L1Prop
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    refine ⟨p, hp, fun n h1 h2 hadj => ?_⟩
    obtain ⟨e, he, hen, hc⟩ := h n h1 h2 hadj
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact ⟨e', he', hen, fun h => hc (by simp [relab, h])⟩
  · rintro ⟨q, hq, h⟩
    refine ⟨relab q, List.mem_map_of_mem hq, fun n h1 h2 hadj => ?_⟩
    obtain ⟨e, he, hen, hc⟩ := h n h1 h2 hadj
    exact ⟨relab e, List.mem_map_of_mem he, hen, fun h => hc (sw01_inj h)⟩

theorem l1Fires_perm (R C : ℕ) {l l' : List Pt} (hp : l.Perm l') : l1Fires R C l' = l1Fires R C l :=
  Bool.eq_iff_iff.mpr (by rw [l1Fires_iff, l1Fires_iff, l1Prop_perm R C hp])

theorem l1Fires_relab (R C : ℕ) (l : List Pt) : l1Fires R C (l.map relab) = l1Fires R C l :=
  Bool.eq_iff_iff.mpr (by rw [l1Fires_iff, l1Fires_iff, l1Prop_relab])

/-- Finding by cell, among endpoints on distinct cells, does not depend on the order. -/
theorem find_cell_perm {l l' : List Pt} (hn : (cellsOf l).Nodup) (hp : l.Perm l') (x : ℕ × ℕ) :
    l'.find? (fun q => q.1 == x) = l.find? (fun q => q.1 == x) := by
  have hn' : (cellsOf l').Nodup := (cellsOf_perm hp).nodup_iff.mp hn
  cases h : l.find? (fun q => q.1 == x) with
  | some q =>
    obtain ⟨hq, hx⟩ := (find_cell_iff hn x q).mp h
    exact (find_cell_iff hn' x q).mpr ⟨hp.mem_iff.mp hq, hx⟩
  | none =>
    rw [List.find?_eq_none] at h ⊢
    exact fun y hy => h y (hp.mem_iff.mpr hy)

theorem closureAt_perm {l l' : List Pt} (hn : (cellsOf l).Nodup) (hp : l.Perm l') (n1 n2 cor : ℕ × ℕ) :
    closureAt l' n1 n2 cor = closureAt l n1 n2 cor := by
  unfold closureAt
  rw [find_cell_perm hn hp n1, find_cell_perm hn hp n2, hp.any_eq]

theorem closureAt_relab (l : List Pt) (n1 n2 cor : ℕ × ℕ) :
    closureAt (l.map relab) n1 n2 cor = (closureAt l n1 n2 cor).map sw01 := by
  unfold closureAt
  rw [find?_relab l (· == n1), find?_relab l (· == n2), List.any_map]
  have e : ((fun q : Pt => q.1 == cor) ∘ relab) = fun q : Pt => q.1 == cor := rfl
  rw [e]
  cases l.find? (fun q => q.1 == n1) with
  | none => rfl
  | some a =>
    cases l.find? (fun q => q.1 == n2) with
    | none => rfl
    | some b =>
      simp only [Option.map_some, relab, beq_sw01]
      split_ifs <;> rfl

theorem filterMap_id_map (g : ℕ → ℕ) : ∀ os : List (Option ℕ),
    (os.map (Option.map g)).filterMap id = (os.filterMap id).map g
  | [] => rfl
  | o :: os => by
    have ih := filterMap_id_map g os
    cases o with
    | none => simpa using ih
    | some a => simpa using ih

theorem contains_sw01 (L : List ℕ) (k : ℕ) : (L.map sw01).contains k = L.contains (sw01 k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; rwa [sw01_sw01]
  · intro h; exact ⟨_, h, sw01_sw01 k⟩

theorem l6Fires_perm {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {l l' : List Pt} (hn : (cellsOf l).Nodup)
    (hp : l.Perm l') : l6Fires R C l' = l6Fires R C l := by
  unfold l6Fires
  rw [l6Closures_eq hR hC, l6Closures_eq hR hC]
  unfold l6List
  simp only [closureAt_perm hn hp]

theorem l6Fires_relab {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) (l : List Pt) :
    l6Fires R C (l.map relab) = l6Fires R C l := by
  unfold l6Fires
  rw [l6Closures_eq hR hC, l6Closures_eq hR hC]
  unfold l6List
  simp only [closureAt_relab]
  have e := filterMap_id_map sw01 [closureAt l (0, 1) (1, 0) (0, 0),
    closureAt l (0, C - 2) (1, C - 1) (0, C - 1), closureAt l (R - 1, 1) (R - 2, 0) (R - 1, 0),
    closureAt l (R - 1, C - 2) (R - 2, C - 1) (R - 1, C - 1)]
  simp only [List.map_cons, List.map_nil] at e
  rw [e, contains_sw01, contains_sw01, show sw01 0 = 1 from rfl, show sw01 1 = 0 from rfl]
  ac_rfl

/-! ### The frame entries: views -/

theorem frame_to_inj {R C : ℕ} (f : Frame) {p q : ℕ × ℕ} (hp1 : p.1 < R) (hp2 : p.2 < C) (hq1 : q.1 < R)
    (hq2 : q.2 < C) (h : f.to R C p = f.to R C q) : p = q := by
  obtain ⟨fr, fc, tr⟩ := f
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only at hp1 hp2 hq1 hq2
  unfold Frame.to at h
  cases fr <;> cases fc <;> cases tr <;> simp at h <;> simp only [Prod.mk.injEq] <;> omega

/-- The endpoints as seen in a frame. -/
def inFrame (R C : ℕ) (f : Frame) (l : List Pt) : List Pt := l.map fun q => (f.to R C q.1, q.2)

theorem inFrame_nodup {R C : ℕ} (f : Frame) {l : List Pt} (hg : GoodL R C l) :
    (cellsOf (inFrame R C f l)).Nodup := by
  unfold cellsOf inFrame
  rw [List.map_map]
  refine List.Nodup.map_on ?_ (nodup_of_cells hg.1)
  intro x hx y hy h
  exact cell_unique hg.1 hx hy (frame_to_inj f (hg.2 x hx).1 (hg.2 x hx).2 (hg.2 y hy).1 (hg.2 y hy).2 h)

theorem inFrame_relab (R C : ℕ) (f : Frame) (l : List Pt) :
    inFrame R C f (l.map relab) = (inFrame R C f l).map relab := by
  unfold inFrame; rw [List.map_map, List.map_map]; rfl

theorem view_at_perm {R C : ℕ} (f : Frame) {l l' : List Pt} (hg : GoodL R C l) (hp : l.Perm l') :
    (makeView R C f l').at = (makeView R C f l).at := by
  funext r c
  unfold View.at makeView
  exact congrArg (Option.map _) (find_cell_perm (inFrame_nodup f hg) (hp.map _) (r, c))

theorem view_at_relab (R C : ℕ) (f : Frame) (l : List Pt) :
    (makeView R C f (l.map relab)).at = fun r c => ((makeView R C f l).at r c).map sw01 := by
  funext r c; exact makeView_relab R C f l r c

theorem view_at_le {R C : ℕ} (f : Frame) {l : List Pt} (hc : ∀ q ∈ l, q.2 ≤ 1) (r c a : ℕ)
    (h : (makeView R C f l).at r c = some a) : a ≤ 1 := by
  unfold View.at makeView at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hq)
  exact hc p hp

/-- The tests that read only the view. -/
def viewTests (v : View) : Bool := testL2 v || testL3 v || testL4 v || testL5 v || edgeClosure v

theorem viewTests_congr {v v' : View} (hH : v'.H = v.H) (hW : v'.W = v.W) (hat : v'.at = v.at) :
    viewTests v' = viewTests v := by
  unfold viewTests testL2 testL3 testL4 testL5 edgeClosure View.empty
  simp only [hH, hW, hat]

theorem empty_relab {v v' : View} (hat : v'.at = fun r c => (v.at r c).map sw01)
    (cells : List (ℕ × ℕ)) : v'.empty cells = v.empty cells := by
  unfold View.empty
  rw [hat]
  congr 1
  funext x
  dsimp only
  cases v.at x.1 x.2 <;> rfl

theorem opt_cases {o : Option ℕ} (h : ∀ a, o = some a → a ≤ 1) : o = none ∨ o = some 0 ∨ o = some 1 := by
  rcases o with _ | a
  · exact Or.inl rfl
  · have := h a rfl
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem viewTests_relab {v v' : View} (hH : v'.H = v.H) (hW : v'.W = v.W)
    (hat : v'.at = fun r c => (v.at r c).map sw01) (hb : ∀ r c a, v.at r c = some a → a ≤ 1) :
    viewTests v' = viewTests v := by
  unfold viewTests
  have he := empty_relab hat
  have t2 : testL2 v' = testL2 v := by
    unfold testL2
    rw [he, hat]
    dsimp only
    rcases opt_cases (hb 0 1) with h1 | h1 | h1 <;> rcases opt_cases (hb 1 0) with h2 | h2 | h2 <;>
      simp [h1, h2, sw01]
  have t3 : testL3 v' = testL3 v := by
    unfold testL3
    rw [he, hat]
    dsimp only
    rcases opt_cases (hb 0 2) with h1 | h1 | h1 <;> rcases opt_cases (hb 1 1) with h2 | h2 | h2 <;>
      rcases opt_cases (hb 1 0) with h3 | h3 | h3 <;> simp [h1, h2, h3, sw01]
  have t4 : testL4 v' = testL4 v := by
    unfold testL4
    rw [he, hat, hH]
    dsimp only
    rcases opt_cases (hb 0 0) with h1 | h1 | h1 <;> rcases opt_cases (hb 1 1) with h2 | h2 | h2 <;>
      rcases opt_cases (hb 0 2) with h3 | h3 | h3 <;> simp [h1, h2, h3, sw01]
  have t5 : testL5 v' = testL5 v := by
    unfold testL5
    rw [he, hat]
    dsimp only
    rcases opt_cases (hb 0 0) with h1 | h1 | h1 <;> rcases opt_cases (hb 0 2) with h2 | h2 | h2 <;>
      rcases opt_cases (hb 2 0) with h3 | h3 | h3 <;> simp [h1, h2, h3, sw01]
  have t6 : edgeClosure v' = edgeClosure v := by
    unfold edgeClosure
    rw [hat, hW]
    dsimp only
    congr 1
    funext k
    rcases opt_cases (hb 0 k) with h1 | h1 | h1 <;> rcases opt_cases (hb 1 (k + 1)) with h2 | h2 | h2 <;>
      rcases opt_cases (hb 0 (k + 3)) with h3 | h3 | h3 <;>
      rcases opt_cases (hb 1 (k + 2)) with h4 | h4 | h4 <;> simp [h1, h2, h3, h4, sw01]
  rw [t2, t3, t4, t5, t6]

/-! ### The frame entries: B and C4 -/

/-- At most two endpoints of each color. -/
def Two (l : List Pt) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, ∀ z ∈ l, x.2 = y.2 → y.2 = z.2 → x = y ∨ y = z ∨ x = z

theorem find?_perm_unique {L L' : List Pt} (hp : L.Perm L') (P : Pt → Bool)
    (hu : ∀ x ∈ L, ∀ y ∈ L, P x = true → P y = true → x = y) : L'.find? P = L.find? P := by
  cases h : L.find? P with
  | none =>
    rw [List.find?_eq_none] at h ⊢
    exact fun y hy => h y (hp.mem_iff.mpr hy)
  | some z =>
    have hz := List.mem_of_find?_eq_some h
    have pz := List.find?_some h
    cases h' : L'.find? P with
    | none =>
      rw [List.find?_eq_none] at h'
      exact absurd pz (h' z (hp.mem_iff.mp hz))
    | some z' =>
      have hz' := hp.mem_iff.mpr (List.mem_of_find?_eq_some h')
      rw [hu z' hz' z hz (List.find?_some h') pz]

theorem find?_isSome_perm {L L' : List Pt} (hp : L.Perm L') (P : Pt → Bool) :
    (L'.find? P).isSome = (L.find? P).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.find?_isSome]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hp.mem_iff.mpr hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hp.mem_iff.mp hx, h⟩⟩

theorem two_inFrame (R C : ℕ) (f : Frame) {l : List Pt} (h2 : Two l) :
    Two (inFrame R C f l) := by
  intro x hx y hy z hz hxy hyz
  unfold inFrame at hx hy hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
  rcases h2 p hp q hq r hr hxy hyz with e | e | e <;> rw [e] <;> simp

theorem two_relab {l : List Pt} (h2 : Two l) : Two (l.map relab) := by
  intro x hx y hy z hz hxy hyz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
  rcases h2 p hp q hq r hr (sw01_inj hxy) (sw01_inj hyz) with e | e | e <;> rw [e] <;> simp

theorem boundaryOnly_perm {R C : ℕ} (f : Frame) {l l' : List Pt} (hg : GoodL R C l) (h2 : Two l)
    (hp : l.Perm l') : boundaryOnly R C f l' = boundaryOnly R C f l := by
  unfold boundaryOnly
  dsimp only
  have hL := hp.map (fun q : Pt => (f.to R C q.1, q.2))
  have hn := inFrame_nodup f hg
  have ht := two_inFrame R C f h2
  unfold inFrame at hn ht
  generalize l.map (fun q : Pt => (f.to R C q.1, q.2)) = L at hL hn ht ⊢
  generalize l'.map (fun q : Pt => (f.to R C q.1, q.2)) = L' at hL ⊢
  congr 1
  funext t
  obtain ⟨a1, a2, b⟩ := t
  dsimp only
  congr 1
  funext A
  have k1 := find?_isSome_perm hL (fun q => q.2 == 1 - A && q.1 == b)
  cases h1 : L.find? (fun q => q.2 == 1 - A && q.1 == b) with
  | none =>
    rw [h1] at k1
    cases h1' : L'.find? (fun q => q.2 == 1 - A && q.1 == b) with
    | none => rfl
    | some _ => rw [h1'] at k1; exact absurd k1 (by simp)
  | some z =>
    rw [h1] at k1
    obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.mp (by rw [k1]; rfl :
      (L'.find? (fun q => q.2 == 1 - A && q.1 == b)).isSome = true)
    rw [hz']
    dsimp only
    rw [hL.any_eq, hL.any_eq]
    have hz := List.mem_of_find?_eq_some h1
    have pz := List.find?_some h1
    rw [find?_perm_unique hL _ ?_]
    intro x hx y hy px py
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at px py pz
    rcases ht x hx y hy z hz (px.1.trans py.1.symm) (py.1.trans pz.1.symm) with e | e | e
    · exact e
    · exact absurd (e ▸ pz.2) py.2
    · exact absurd (e ▸ pz.2) px.2

theorem beq_sw01_left (a k : ℕ) : (sw01 a == k) = (a == sw01 k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact sw01_eq_iff

theorem any01 (g h : ℕ → Bool) (hk : ∀ A, A ≤ 1 → g A = h (sw01 A)) :
    [0, 1].any g = [0, 1].any h := by
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [hk 0 (by omega), hk 1 (by omega), show sw01 0 = 1 from rfl, show sw01 1 = 0 from rfl]
  exact Bool.or_comm _ _

theorem boundaryOnly_relab (R C : ℕ) (f : Frame) (l : List Pt) :
    boundaryOnly R C f (l.map relab) = boundaryOnly R C f l := by
  unfold boundaryOnly
  dsimp only
  have e0 := inFrame_relab R C f l
  unfold inFrame at e0
  rw [e0]
  generalize l.map (fun q : Pt => (f.to R C q.1, q.2)) = L
  congr 1
  funext t
  obtain ⟨a1, a2, b⟩ := t
  dsimp only
  -- branch `A` of the relabelled list is branch `sw01 A` of the original
  apply any01
  intro A hA
  have c1 : ∀ q : Pt, (sw01 q.2 == 1 - A) = (q.2 == 1 - sw01 A) := by
    intro q; rw [beq_sw01_left, sw01_le hA, sw01_le (by omega : 1 - A ≤ 1)]
  have c2 : ∀ q : Pt, (sw01 q.2 == A) = (q.2 == sw01 A) := fun q => beq_sw01_left _ _
  rw [List.find?_map, List.find?_map, List.any_map, List.any_map]
  simp only [Function.comp_def, relab, c1, c2]
  cases L.find? (fun q => q.2 == 1 - sw01 A && q.1 == b) with
  | none => rfl
  | some _ =>
    dsimp only
    cases L.find? (fun q => q.2 == 1 - sw01 A && q.1 != b) with
    | none => rfl
    | some _ => rfl

theorem sameSet_perm (A : List (ℕ × ℕ)) {X X' : List (ℕ × ℕ)} (hp : X.Perm X') :
    sameSet A X' = sameSet A X := by
  unfold sameSet
  rw [hp.length_eq]
  congr 1
  apply List.all_congr rfl
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, hp.mem_iff]

theorem corner4_perm (R C : ℕ) (f : Frame) {l l' : List Pt} (hp : l.Perm l') :
    corner4 R C f l' = corner4 R C f l := by
  unfold corner4
  dsimp only
  simp only [sameSet_perm _ ((hp.filter _).map _)]

theorem corner4_relab (R C : ℕ) (f : Frame) (l : List Pt) :
    corner4 R C f (l.map relab) = corner4 R C f l := by
  unfold corner4
  dsimp only
  have e : ∀ k : ℕ, ((l.map relab).filter (·.2 == k)).map (fun q => f.to R C q.1) =
      (l.filter (·.2 == sw01 k)).map (fun q => f.to R C q.1) := by
    intro k
    rw [List.filter_map, List.map_map]
    congr 1
    congr 1
    funext q
    exact beq_sw01_left _ _
  rw [e 0, e 1]
  simp only [show sw01 0 = 1 from rfl, show sw01 1 = 0 from rfl]
  congr 1
  funext t
  exact Bool.or_comm _ _

/-! ### The frame entries together -/

theorem frameFires_perm {R C : ℕ} (f : Frame) {l l' : List Pt} (hg : GoodL R C l) (h2 : Two l)
    (hp : l.Perm l') : frameFires R C l' f = frameFires R C l f := by
  show (viewTests (makeView R C f l') || boundaryOnly R C f l' ||
      (decide (R ≥ 10) && decide (C ≥ 10) && corner4 R C f l')) =
    (viewTests (makeView R C f l) || boundaryOnly R C f l ||
      (decide (R ≥ 10) && decide (C ≥ 10) && corner4 R C f l))
  rw [viewTests_congr (v := makeView R C f l) (v' := makeView R C f l') rfl rfl (view_at_perm f hg hp), boundaryOnly_perm f hg h2 hp,
    corner4_perm R C f hp]

theorem frameFires_relab {R C : ℕ} (f : Frame) {l : List Pt} (hc : ∀ q ∈ l, q.2 ≤ 1) :
    frameFires R C (l.map relab) f = frameFires R C l f := by
  show (viewTests (makeView R C f (l.map relab)) || boundaryOnly R C f (l.map relab) ||
      (decide (R ≥ 10) && decide (C ≥ 10) && corner4 R C f (l.map relab))) =
    (viewTests (makeView R C f l) || boundaryOnly R C f l ||
      (decide (R ≥ 10) && decide (C ≥ 10) && corner4 R C f l))
  rw [viewTests_relab (v := makeView R C f l) (v' := makeView R C f (l.map relab)) rfl rfl (view_at_relab R C f l) (view_at_le f hc), boundaryOnly_relab,
    corner4_relab]

theorem frames_any_perm {R C : ℕ} {l l' : List Pt} (hg : GoodL R C l) (h2 : Two l) (hp : l.Perm l') :
    frames.any (frameFires R C l') = frames.any (frameFires R C l) := by
  congr 1; funext f; exact frameFires_perm f hg h2 hp

theorem frames_any_relab {R C : ℕ} {l : List Pt} (hc : ∀ q ∈ l, q.2 ≤ 1) :
    frames.any (frameFires R C (l.map relab)) = frames.any (frameFires R C l) := by
  congr 1; funext f; exact frameFires_relab f hc

/-! ### T2 -/

theorem t2_norm (a b c e : ℕ × ℕ) : t2Fires [a, b, c, e] =
    (max (max (max a.1 b.1) c.1) e.1 - min (min (min a.1 b.1) c.1) e.1 == 1 &&
      max (max (max a.2 b.2) c.2) e.2 - min (min (min a.2 b.2) c.2) e.2 == 1 &&
      min (min (min a.1 b.1) c.1) e.1 + 1 == max (max (max a.1 b.1) c.1) e.1 &&
      min (min (min a.2 b.2) c.2) e.2 + 1 == max (max (max a.2 b.2) c.2) e.2 &&
      a.1 != b.1 && a.2 != b.2) := by
  unfold t2Fires
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.headD_cons,
    List.getElem!_cons_zero, List.getElem!_cons_succ, Nat.zero_max, min_self]

theorem t2_swap01 (a b c e : ℕ × ℕ) : t2Fires [b, a, c, e] = t2Fires [a, b, c, e] := by
  have h1 : (b.1 != a.1) = (a.1 != b.1) := bne_comm
  have h2 : (b.2 != a.2) = (a.2 != b.2) := bne_comm
  rw [t2_norm, t2_norm, max_comm b.1 a.1, max_comm b.2 a.2, min_comm b.1 a.1, min_comm b.2 a.2, h1, h2]

theorem t2_swap23 (a b c e : ℕ × ℕ) : t2Fires [a, b, e, c] = t2Fires [a, b, c, e] := by
  rw [t2_norm, t2_norm, max_assoc _ e.1, max_comm e.1 c.1, ← max_assoc, max_assoc _ e.2,
    max_comm e.2 c.2, ← max_assoc, min_assoc _ e.1, min_comm e.1 c.1, ← min_assoc, min_assoc _ e.2,
    min_comm e.2 c.2, ← min_assoc]

/-- Four distinct cells in a 2 × 2 square: `a, b` are diagonal exactly when `c, e` are. -/
theorem sq4 {m1 m2 a1 a2 b1 b2 c1 c2 e1 e2 : ℕ}
    (ha1 : m1 ≤ a1 ∧ a1 ≤ m1 + 1) (hb1 : m1 ≤ b1 ∧ b1 ≤ m1 + 1) (hc1 : m1 ≤ c1 ∧ c1 ≤ m1 + 1)
    (he1 : m1 ≤ e1 ∧ e1 ≤ m1 + 1) (ha2 : m2 ≤ a2 ∧ a2 ≤ m2 + 1) (hb2 : m2 ≤ b2 ∧ b2 ≤ m2 + 1)
    (hc2 : m2 ≤ c2 ∧ c2 ≤ m2 + 1) (he2 : m2 ≤ e2 ∧ e2 ≤ m2 + 1)
    (d1 : ¬(a1 = b1 ∧ a2 = b2)) (d2 : ¬(a1 = c1 ∧ a2 = c2)) (d3 : ¬(a1 = e1 ∧ a2 = e2))
    (d4 : ¬(b1 = c1 ∧ b2 = c2)) (d5 : ¬(b1 = e1 ∧ b2 = e2)) (d6 : ¬(c1 = e1 ∧ c2 = e2)) :
    (c1 ≠ e1 ∧ c2 ≠ e2) ↔ (a1 ≠ b1 ∧ a2 ≠ b2) := by
  have k : ∀ x m : ℕ, m ≤ x ∧ x ≤ m + 1 → x = m ∨ x = m + 1 := fun x m h => by omega
  rcases k _ _ ha1 with rfl | rfl <;> rcases k _ _ hb1 with h1 | h1 <;> rcases k _ _ hc1 with h2 | h2 <;>
    rcases k _ _ he1 with h3 | h3 <;> rcases k _ _ ha2 with rfl | rfl <;> rcases k _ _ hb2 with h4 | h4 <;>
    rcases k _ _ hc2 with h5 | h5 <;> rcases k _ _ he2 with h6 | h6 <;> subst_vars <;> omega

theorem min4_le (a b c e : ℕ) : min (min (min a b) c) e ≤ a ∧ min (min (min a b) c) e ≤ b ∧
    min (min (min a b) c) e ≤ c ∧ min (min (min a b) c) e ≤ e := by omega

theorem le_max4 (a b c e : ℕ) : a ≤ max (max (max a b) c) e ∧ b ≤ max (max (max a b) c) e ∧
    c ≤ max (max (max a b) c) e ∧ e ≤ max (max (max a b) c) e := by omega

theorem t2_pairs {a b c e : ℕ × ℕ} (hd : a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e) :
    t2Fires [c, e, a, b] = t2Fires [a, b, c, e] := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  obtain ⟨e1, e2⟩ := e
  simp only [ne_eq, Prod.mk.injEq] at hd
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  rw [t2_norm, t2_norm]
  dsimp only
  have x1 : max (max (max c1 e1) a1) b1 = max (max (max a1 b1) c1) e1 := by ac_rfl
  have x2 : max (max (max c2 e2) a2) b2 = max (max (max a2 b2) c2) e2 := by ac_rfl
  have n1 : min (min (min c1 e1) a1) b1 = min (min (min a1 b1) c1) e1 := by ac_rfl
  have n2 : min (min (min c2 e2) a2) b2 = min (min (min a2 b2) c2) e2 := by ac_rfl
  rw [x1, x2, n1, n2]
  have bm1 := min4_le a1 b1 c1 e1
  have bm2 := min4_le a2 b2 c2 e2
  have bM1 := le_max4 a1 b1 c1 e1
  have bM2 := le_max4 a2 b2 c2 e2
  generalize max (max (max a1 b1) c1) e1 = M1 at bM1 ⊢
  generalize max (max (max a2 b2) c2) e2 = M2 at bM2 ⊢
  generalize min (min (min a1 b1) c1) e1 = m1 at bm1 ⊢
  generalize min (min (min a2 b2) c2) e2 = m2 at bm2 ⊢
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, and_assoc]
  constructor
  · rintro ⟨p1, p2, p3, p4, y1, y2⟩
    refine ⟨p1, p2, p3, p4, ?_⟩
    exact (sq4 ⟨bm1.1, by rw [p3]; exact bM1.1⟩ ⟨bm1.2.1, by rw [p3]; exact bM1.2.1⟩
      ⟨bm1.2.2.1, by rw [p3]; exact bM1.2.2.1⟩ ⟨bm1.2.2.2, by rw [p3]; exact bM1.2.2.2⟩
      ⟨bm2.1, by rw [p4]; exact bM2.1⟩ ⟨bm2.2.1, by rw [p4]; exact bM2.2.1⟩
      ⟨bm2.2.2.1, by rw [p4]; exact bM2.2.2.1⟩ ⟨bm2.2.2.2, by rw [p4]; exact bM2.2.2.2⟩
      d1 d2 d3 d4 d5 d6).mp ⟨y1, y2⟩
  · rintro ⟨p1, p2, p3, p4, y1, y2⟩
    refine ⟨p1, p2, p3, p4, ?_⟩
    exact (sq4 ⟨bm1.1, by rw [p3]; exact bM1.1⟩ ⟨bm1.2.1, by rw [p3]; exact bM1.2.1⟩
      ⟨bm1.2.2.1, by rw [p3]; exact bM1.2.2.1⟩ ⟨bm1.2.2.2, by rw [p3]; exact bM1.2.2.2⟩
      ⟨bm2.1, by rw [p4]; exact bM2.1⟩ ⟨bm2.2.1, by rw [p4]; exact bM2.2.1⟩
      ⟨bm2.2.2.1, by rw [p4]; exact bM2.2.2.1⟩ ⟨bm2.2.2.2, by rw [p4]; exact bM2.2.2.2⟩
      d1 d2 d3 d4 d5 d6).mpr ⟨y1, y2⟩

/-! ### Assembly -/

theorem four_good {R C : ℕ} {a b c e : ℕ × ℕ} (h4 : Four R C a b c e) :
    GoodL R C [(a, 0), (b, 0), (c, 1), (e, 1)] := by
  obtain ⟨⟨a1, a2, b1, b2, c1, c2, e1, e2⟩, ⟨dab, dac, dae, dbc, dbe, dce⟩⟩ := h4
  refine ⟨?_, ?_⟩
  · simp only [cellsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨⟨dab, dac, dae⟩, ⟨dbc, dbe⟩, dce, by simp, List.nodup_nil⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨a1, a2⟩
    · exact ⟨b1, b2⟩
    · exact ⟨c1, c2⟩
    · exact ⟨e1, e2⟩

theorem four_two (a b c e : ℕ × ℕ) : Two [(a, 0), (b, 0), (c, 1), (e, 1)] := by
  intro x hx y hy z hz hxy hyz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all

theorem four_col (a b c e : ℕ × ℕ) : ∀ q ∈ [((a, 0) : Pt), (b, 0), (c, 1), (e, 1)], q.2 ≤ 1 := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> simp

/-- The entries other than T2, for a reordering. -/
theorem fires3_perm {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {a b c e a' b' c' e' : ℕ × ℕ}
    (h4 : Four R C a b c e)
    (hp : [((a, 0) : Pt), (b, 0), (c, 1), (e, 1)].Perm [(a', 0), (b', 0), (c', 1), (e', 1)])
    (ht : t2Fires [a', b', c', e'] = t2Fires [a, b, c, e]) :
    fires3 R C a' b' c' e' = fires3 R C a b c e := by
  have hg := four_good h4
  have h2 := four_two a b c e
  unfold fires3
  dsimp only
  rw [parityOk_perm R C hp, t1Fires_perm (by omega) (by omega) hg hp, ht, l1Fires_perm R C hp,
    l6Fires_perm (by omega) (by omega) hg.1 hp, frames_any_perm hg h2 hp,
    effAlt3_perm (by omega) (by omega) hg hp]

theorem fires3_rev0 {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {a b c e : ℕ × ℕ} (h4 : Four R C a b c e) :
    fires3 R C b a c e = fires3 R C a b c e :=
  fires3_perm hR hC h4 (List.Perm.swap _ _ _) (t2_swap01 a b c e)

theorem fires3_rev1 {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {a b c e : ℕ × ℕ} (h4 : Four R C a b c e) :
    fires3 R C a b e c = fires3 R C a b c e :=
  fires3_perm hR hC h4 ((List.Perm.swap _ _ _).cons _ |>.cons _) (t2_swap23 a b c e)

theorem fires3_swap {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {a b c e : ℕ × ℕ} (h4 : Four R C a b c e) :
    fires3 R C c e a b = fires3 R C a b c e := by
  have hg := four_good h4
  set l : List Pt := [(a, 0), (b, 0), (c, 1), (e, 1)] with hl
  have hm : l.map relab = [(a, 1), (b, 1), (c, 0), (e, 0)] := rfl
  have hp : (l.map relab).Perm [(c, 0), (e, 0), (a, 1), (b, 1)] := by
    rw [hm]; exact List.perm_append_comm (l₁ := [(a, 1), (b, 1)]) (l₂ := [(c, 0), (e, 0)])
  have hg' := hg.map_relab
  have h2' := two_relab (four_two a b c e)
  have hc := four_col a b c e
  unfold fires3
  dsimp only
  rw [parityOk_perm R C hp, t1Fires_perm (by omega) (by omega) hg' hp, t2_pairs h4.2,
    l1Fires_perm R C hp, l6Fires_perm (by omega) (by omega) hg'.1 hp, frames_any_perm hg' h2' hp,
    effAlt3_perm (by omega) (by omega) hg' hp]
  rw [parityOk_relab, t1Fires_relab, l1Fires_relab, l6Fires_relab (by omega) (by omega),
    frames_any_relab hc, effAlt3_relab]

theorem four_of_inDom {I : Inst} (hI : InDom I) : Four I.w I.h I.s0 I.t0 I.s1 I.t1 := by
  obtain ⟨-, -, b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hI
  exact ⟨⟨b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩

/-- **Reversing path 0 does not change passing.** -/
theorem passes_rev0 {I : Inst} (hI : InDom I) : Passes I.rev0 ↔ Passes I := by
  unfold Passes Inst.rev0
  rw [fires3_rev0 hI.1 hI.2.1 (four_of_inDom hI)]

/-- **Reversing path 1 does not change passing.** -/
theorem passes_rev1 {I : Inst} (hI : InDom I) : Passes I.rev1 ↔ Passes I := by
  unfold Passes Inst.rev1
  rw [fires3_rev1 hI.1 hI.2.1 (four_of_inDom hI)]

/-- **Swapping the colors does not change passing.** -/
theorem passes_swapColors {I : Inst} (hI : InDom I) : Passes I.swapColors ↔ Passes I := by
  unfold Passes Inst.swapColors
  rw [fires3_swap hI.1 hI.2.1 (four_of_inDom hI)]

end ZZN
