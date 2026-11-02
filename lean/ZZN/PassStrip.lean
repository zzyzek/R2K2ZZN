-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.TheoremA

/-!
# `passStrip`: strips preserve passing

A strip deletes two endpoint-free lines at an edge (`d = 0` with lines 0–3 free, or `d = w − 2`
with the last four lines free). In the frames at the strip's corners (*near* frames) every
endpoint is at least 2 lines from the corner line, so no corner-local entry can fire there
(*locality*); in the other frames (*far* frames) the endpoints keep their frame coordinates.
-/

namespace ZZN

open GridHam

/-! ### Locality in near frames -/

/-- Every endpoint is at least 2 from the frame's corner, along the frame's rows (if not
transposed) or columns (if transposed). -/
def NearP (R C : ℕ) (f : Frame) (pts : List Pt) : Prop :=
  ∀ q ∈ pts, 2 ≤ (if f.tr then (f.to R C q.1).2 else (f.to R C q.1).1)

theorem at_none_of_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) {r c : ℕ}
    (hrc : if f.tr then c ≤ 1 else r ≤ 1) : (makeView R C f pts).at r c = none := by
  unfold View.at makeView
  simp only [Option.map_eq_none_iff, List.find?_eq_none, List.mem_map, beq_iff_eq]
  rintro _ ⟨q, hq, rfl⟩ he
  have := h q hq
  simp only at he
  rw [he] at this
  split_ifs at this hrc <;> simp only at this <;> omega

theorem testL2_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) :
    testL2 (makeView R C f pts) = false := by
  unfold testL2
  cases htr : f.tr
  · rw [at_none_of_near h (r := 0) (c := 1) (by simp [htr])]
  · rw [at_none_of_near h (r := 1) (c := 0) (by simp [htr])]
    cases (makeView R C f pts).at 0 1 <;> rfl

theorem testL3_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) :
    testL3 (makeView R C f pts) = false := by
  unfold testL3
  cases htr : f.tr
  · rw [at_none_of_near h (r := 0) (c := 2) (by simp [htr])]
  · have := at_none_of_near h (r := 1) (c := 0) (by simp [htr])
    cases (makeView R C f pts).at 0 2 <;> simp [this]

theorem testL4_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) :
    testL4 (makeView R C f pts) = false := by
  unfold testL4
  rw [at_none_of_near h (r := 0) (c := 0) (by split_ifs <;> simp)]

theorem testL5_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) :
    testL5 (makeView R C f pts) = false := by
  unfold testL5
  rw [at_none_of_near h (r := 0) (c := 0) (by split_ifs <;> simp)]

theorem rewritesAt_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) :
    rewritesAt (makeView R C f pts) = none := by
  unfold rewritesAt
  dsimp only
  have n00 := at_none_of_near h (r := 0) (c := 0) (by split_ifs <;> simp)
  cases htr : f.tr
  · have n01 := at_none_of_near h (r := 0) (c := 1) (by simp [htr])
    have n12 := at_none_of_near h (r := 1) (c := 2) (by simp [htr])
    simp [n00, n01, n12]
  · have n10 := at_none_of_near h (r := 1) (c := 0) (by simp [htr])
    have n21 := at_none_of_near h (r := 2) (c := 1) (by simp [htr])
    have n01 := at_none_of_near h (r := 0) (c := 1) (by simp [htr])
    simp [n00, n01, n21]

theorem boundary_lists_local :
    (∀ e ∈ BOUNDARY3_EVEN, (e.1.1 ≤ 1 ∨ e.2.1.1 ≤ 1 ∨ e.2.2.1 ≤ 1) ∧
      (e.1.2 ≤ 1 ∨ e.2.1.2 ≤ 1 ∨ e.2.2.2 ≤ 1)) ∧
    (∀ e ∈ BOUNDARY3_ODD, (e.1.1 ≤ 1 ∨ e.2.1.1 ≤ 1 ∨ e.2.2.1 ≤ 1) ∧
      (e.1.2 ≤ 1 ∨ e.2.1.2 ≤ 1 ∨ e.2.2.2 ≤ 1)) := by
  decide

theorem corner4_lists_local :
    (∀ e ∈ CORNER4, (∃ x ∈ e.1 ++ e.2, x.1 ≤ 1) ∧ (∃ x ∈ e.1 ++ e.2, x.2 ≤ 1)) ∧
    (∀ e ∈ CORNER4_ODD, (∃ x ∈ e.1 ++ e.2, x.1 ≤ 1) ∧ (∃ x ∈ e.1 ++ e.2, x.2 ≤ 1)) := by
  decide

/-- A frame cell that holds an endpoint is not within 1 of the corner (in the near direction). -/
theorem near_cell {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) {q : Pt}
    (hq : q ∈ pts) {x : ℕ × ℕ} (hx : f.to R C q.1 = x) : 2 ≤ (if f.tr then x.2 else x.1) := by
  have := h q hq
  rw [hx] at this
  exact this

theorem boundaryOnly_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) :
    boundaryOnly R C f pts = false := by
  by_contra hb
  rw [Bool.not_eq_false] at hb
  unfold boundaryOnly at hb
  simp only [List.any_eq_true] at hb
  obtain ⟨⟨a1, a2, b⟩, he, A, -, hm⟩ := hb
  have hloc : (a1.1 ≤ 1 ∨ a2.1 ≤ 1 ∨ b.1 ≤ 1) ∧ (a1.2 ≤ 1 ∨ a2.2 ≤ 1 ∨ b.2 ≤ 1) := by
    split_ifs at he
    · exact boundary_lists_local.2 _ he
    · exact boundary_lists_local.1 _ he
  -- the three pattern cells hold endpoints
  have occ : ∀ x : ℕ × ℕ, ((pts.map fun q => (f.to R C q.1, q.2)).any
      fun u => u.2 == A && u.1 == x) = true → 2 ≤ (if f.tr then x.2 else x.1) := by
    intro x hx
    simp only [List.any_eq_true, List.mem_map, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨_, ⟨q, hq, rfl⟩, -, hqx⟩ := hx
    exact near_cell h hq hqx
  revert hm
  cases hfind : (pts.map fun q => (f.to R C q.1, q.2)).find? (fun u => u.2 == 1 - A && u.1 == b) with
  | none => simp
  | some u =>
    intro hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨⟨h1, h2⟩, -⟩ := hm
    have hb' := List.find?_some hfind
    have hbm := List.mem_of_find?_eq_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hb'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hbm
    have c3 := near_cell h hq hb'.2
    have c1 := occ a1 h1
    have c2 := occ a2 h2
    split_ifs at c1 c2 c3 <;> omega

theorem corner4_near {R C : ℕ} {f : Frame} {pts : List Pt} (h : NearP R C f pts) :
    corner4 R C f pts = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  unfold corner4 at hc
  simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hc
  obtain ⟨e, he, hm⟩ := hc
  have hloc : (∃ x ∈ e.1 ++ e.2, x.1 ≤ 1) ∧ (∃ x ∈ e.1 ++ e.2, x.2 ≤ 1) := by
    split_ifs at he
    · exact corner4_lists_local.1 e he
    · exact corner4_lists_local.2 e he
  -- every pattern cell is an endpoint's frame cell
  have inA : ∀ (col : ℕ) (L : List (ℕ × ℕ)), sameSet L ((pts.filter (·.2 == col)).map
      (fun q => f.to R C q.1)) = true → ∀ x ∈ L, 2 ≤ (if f.tr then x.2 else x.1) := by
    intro col L hs x hx
    unfold sameSet at hs
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hs
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp (hs.2 x hx)
    exact near_cell h (List.mem_of_mem_filter hq) hqx
  have all : ∀ x ∈ e.1 ++ e.2, 2 ≤ (if f.tr then x.2 else x.1) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx <;> rcases hm with ⟨a, b⟩ | ⟨a, b⟩
    · exact inA 0 _ a x hx
    · exact inA 1 _ a x hx
    · exact inA 1 _ b x hx
    · exact inA 0 _ b x hx
  obtain ⟨⟨x, hx, hx1⟩, ⟨y, hy, hy2⟩⟩ := hloc
  have := all x hx
  have := all y hy
  split_ifs at * <;> omega

/-! ### E1 under reflecting a transposed frame -/

theorem find?_congr_mem {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons, h x List.mem_cons_self,
      find?_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem view_flip {R C : ℕ} (fr fc : Bool) {pts : List Pt} (hb : ∀ q ∈ pts, q.1.1 < R)
    (r : ℕ) {c : ℕ} (hc : c < R) :
    (makeView R C ⟨!fr, fc, true⟩ pts).at r c = (makeView R C ⟨fr, fc, true⟩ pts).at r (R - 1 - c) := by
  unfold makeView View.at
  simp only [List.find?_map, Option.map_map]
  have e : ∀ fr' : Bool, ((fun x : (ℕ × ℕ) × ℕ => x.2) ∘
      fun q : Pt => (Frame.to R C ⟨fr', fc, true⟩ q.1, q.2)) = fun q => q.2 := fun _ => rfl
  rw [e, e]
  congr 1
  apply find?_congr_mem
  intro q hq
  have hx := hb q hq
  obtain ⟨⟨x, y⟩, col⟩ := q
  simp only [Function.comp, Frame.to, ↓reduceIte] at hx ⊢
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Prod.mk.injEq]
  cases fr <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem at_color_le {R C : ℕ} {f : Frame} {pts : List Pt} (hc : ∀ q ∈ pts, q.2 ≤ 1) {r c col : ℕ}
    (h : (makeView R C f pts).at r c = some col) : col ≤ 1 := by
  unfold makeView View.at at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hu
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  exact hc q hq

/-- E1 in a transposed frame implies E1 in the reflected frame (colors swapped). -/
theorem edgeClosure_flip {R C : ℕ} (fr fc : Bool) {pts : List Pt} (hb : ∀ q ∈ pts, q.1.1 < R)
    (hc : ∀ q ∈ pts, q.2 ≤ 1)
    (h : edgeClosure (makeView R C ⟨!fr, fc, true⟩ pts) = true) :
    edgeClosure (makeView R C ⟨fr, fc, true⟩ pts) = true := by
  have hW : ∀ fr' : Bool, (makeView R C ⟨fr', fc, true⟩ pts).W = R := by
    intro fr'; simp [makeView, Frame.W]
  unfold edgeClosure at h ⊢
  rw [hW] at h ⊢
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨k, hkR, hk3, hm⟩ := h
  revert hm
  cases h0 : (makeView R C ⟨!fr, fc, true⟩ pts).at 0 k with
  | none => simp
  | some a =>
    intro hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨h1, h3⟩, h2⟩ := hm
    have ha := at_color_le hc h0
    rw [view_flip fr fc hb 0 (by omega)] at h0
    rw [view_flip fr fc hb 1 (by omega)] at h1 h2
    rw [view_flip fr fc hb 0 (by omega)] at h3
    refine ⟨R - 4 - k, by omega, by omega, ?_⟩
    have e0 : R - 4 - k = R - 1 - (k + 3) := by omega
    have e1 : R - 1 - (k + 3) + 1 = R - 1 - (k + 2) := by omega
    have e2 : R - 1 - (k + 3) + 3 = R - 1 - k := by omega
    have e3 : R - 1 - (k + 3) + 2 = R - 1 - (k + 1) := by omega
    have e4 : 1 - (1 - a) = a := by omega
    rw [e0, h3]
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [e1, e2, e3, h0, h1, h2, e4]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-! ### All frame-based entries, for strips -/

/-- In a far frame, every endpoint keeps its frame cell. -/
def SameCells (R R' C : ℕ) (f : Frame) (pts pts' : List Pt) : Prop :=
  List.Forall₂ (fun q q' => q'.2 = q.2 ∧ f.to R' C q'.1 = f.to R C q.1) pts pts'

theorem forall2_map_self' {R R' C : ℕ} {f : Frame} {pts : List Pt}
    (h : ∀ q ∈ pts, f.to R' C q.1 = f.to R C q.1) : SameCells R R' C f pts pts := by
  induction pts with
  | nil => exact List.Forall₂.nil
  | cons q qs ih =>
    exact List.Forall₂.cons ⟨rfl, h q List.mem_cons_self⟩
      (ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')))

theorem view_at_same {R R' C : ℕ} {f : Frame} {pts pts' : List Pt} (h : SameCells R R' C f pts pts')
    (r c : ℕ) : (makeView R' C f pts').at r c = (makeView R C f pts).at r c := by
  induction h with
  | nil => rfl
  | @cons q q' qs qs' hq _ ih =>
    obtain ⟨hcol, hto⟩ := hq
    simp only [makeView, View.at, List.map_cons, List.find?_cons] at ih ⊢
    rw [hto]
    cases (f.to R C q.1 == (r, c))
    · exact ih
    · simp [hcol]

theorem mem_frames (f : Frame) : f ∈ frames := by
  obtain ⟨a, b, c⟩ := f
  cases a <;> cases b <;> cases c <;> simp [frames]

/-- Strip version of `frames_any_of`: in near frames nothing fires except E1 in transposed frames,
which reflects to a far frame; in far frames the endpoints keep their cells. -/
theorem frames_any_strip {R R' C : ℕ} {pts pts' : List Pt} (hR : R' ≤ R) (nearFr : Bool)
    (hnear : ∀ f : Frame, f.fr = nearFr → NearP R' C f pts')
    (hfar : ∀ f : Frame, f.fr = !nearFr → List.Forall₂ (WinRel R R' C f) pts pts' ∧
      SameCells R R' C f pts pts')
    (hb' : ∀ q ∈ pts', q.1.1 < R') (hc' : ∀ q ∈ pts', q.2 ≤ 1) (hpar : R' % 2 = R % 2)
    (h : frames.any (frameFires R' C pts') = true) : frames.any (frameFires R C pts) = true := by
  have hpar2 : (R' * C) % 2 = (R * C) % 2 := by rw [Nat.mul_mod, hpar, ← Nat.mul_mod]
  -- the far-frame step
  have farStep : ∀ f : Frame, f.fr = !nearFr → frameFires R' C pts' f = true →
      frameFires R C pts f = true := by
    intro f hf hfire
    obtain ⟨hrel, hsame⟩ := hfar f hf
    have hs := sameCorner_of_winRel hrel
    have hH : (makeView R' C f pts').H ≤ (makeView R C f pts).H := by
      simp only [makeView, Frame.H]; split_ifs <;> omega
    unfold frameFires at hfire ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfire ⊢
    rcases hfire with (((((h2 | h3) | h4) | h5) | hE) | hB) | ⟨⟨h10, h10'⟩, hC⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (testL2_of hs h2))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (testL3_of hs h3))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (testL4_of hs hH h4)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (testL5_of hs h5))))
    · refine Or.inl (Or.inl (Or.inr ?_))
      have hW : (makeView R' C f pts').W ≤ (makeView R C f pts).W := by
        simp only [makeView, Frame.W]; split_ifs <;> omega
      unfold edgeClosure at hE ⊢
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hE ⊢
      obtain ⟨k, hk, hk3, hm⟩ := hE
      refine ⟨k, by omega, by omega, ?_⟩
      simp only [view_at_same hsame] at hm
      exact hm
    · exact Or.inl (Or.inr (boundaryOnly_of hrel hpar hB))
    · exact Or.inr ⟨⟨by omega, h10'⟩, corner4_of (goodIn_of_winRel hrel) hpar2 hC⟩
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨f, hf, hfire⟩ := h
  by_cases hfn : f.fr = nearFr
  · -- near frame: only E1 in a transposed frame can fire
    have hn := hnear f hfn
    unfold frameFires at hfire
    simp only [testL2_near hn, testL3_near hn, testL4_near hn, testL5_near hn,
      boundaryOnly_near hn, corner4_near hn, Bool.false_or, Bool.or_false, Bool.and_false] at hfire
    obtain ⟨frN, fc, tr⟩ := f
    simp only at hfn
    subst hfn
    cases tr
    · -- not transposed: E1 needs frame rows 0 and 1, which are empty
      exfalso
      unfold edgeClosure at hfire
      simp only [List.any_eq_true] at hfire
      obtain ⟨k, -, hk⟩ := hfire
      rw [at_none_of_near hn (r := 0) (c := k) (by simp)] at hk
      simp at hk
    · have hE := edgeClosure_flip (!frN) fc hb' hc' (by simpa using hfire)
      refine ⟨⟨!frN, fc, true⟩, mem_frames _, farStep _ rfl ?_⟩
      unfold frameFires
      simp [hE]
  · have hf' : f.fr = !nearFr := by cases h1 : f.fr <;> cases nearFr <;> simp_all
    exact ⟨f, hf, farStep f hf' hfire⟩

/-! ### Right strip: the rewrite phase is unchanged -/

/-- All cells of a rewrite state are at least 5 lines from the far edge `R - 1`. -/
def LowSt (R : ℕ) (st : RWState) : Prop := ∀ q ∈ st.eff, q.1.1 + 5 ≤ R

theorem nearP_low {R R' C : ℕ} (hR' : R' ≤ R) (hRR : R ≤ R' + 2) {pts : List Pt}
    (h : ∀ q ∈ pts, q.1.1 + 5 ≤ R) (f : Frame) (hf : f.fr = true) : NearP R' C f pts := by
  intro q hq
  have := h q hq
  obtain ⟨fr, fc, tr⟩ := f
  simp only at hf
  subst hf
  cases tr <;> simp only [Frame.to, ↓reduceIte, Bool.false_eq_true] <;> omega

theorem back_same_low {R R' C : ℕ} (f : Frame) (hf : f.fr = false) (a : ℕ × ℕ) :
    f.back R' C a = f.back R C a := by
  unfold Frame.back
  simp [hf]

theorem mem_foldl_moveFirst : ∀ {moves : List ((ℕ × ℕ) × (ℕ × ℕ))} {e : List Pt} {q : Pt},
    q ∈ moves.foldl moveFirst e → q ∈ e ∨ ∃ m ∈ moves, q.1 = m.2
  | [], _, _, h => Or.inl h
  | m :: ms, e, q, h => by
    simp only [List.foldl_cons] at h
    rcases mem_foldl_moveFirst h with h' | ⟨m', hm', hq⟩
    · rcases mem_moveFirst h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨m, List.mem_cons_self, h''⟩
    · exact Or.inr ⟨m', List.mem_cons_of_mem _ hm', hq⟩

theorem rwStep_rstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 4 ≤ C) {st : RWState} (hst : LowSt R st)
    (f : Frame) : rwStep (R - 2) C st f = rwStep R C st f ∧ LowSt R (rwStep R C st f) := by
  cases hfr : f.fr
  · -- far frame: identical views and cells
    have hv : rewritesAt (makeView (R - 2) C f st.eff) = rewritesAt (makeView R C f st.eff) := by
      have hsame : ∀ q ∈ st.eff, f.to (R - 2) C q.1 = f.to R C q.1 := by
        intro q hq
        rw [frame_to_eq, frame_to_eq]
        unfold xf
        simp [hfr]
      apply rewritesAt_congr
      · intro r c _ _
        exact view_at_same (forall2_map_self' hsame) r c
      all_goals (simp only [makeView, Frame.H, Frame.W]; split_ifs <;> omega)
    have hbk : Frame.back (R - 2) C f = Frame.back R C f := funext (back_same_low f hfr)
    unfold rwStep
    rw [hv, hbk]
    refine ⟨rfl, ?_⟩
    cases hrw : rewritesAt (makeView R C f st.eff) with
    | none => exact hst
    | some rw =>
      simp only
      split_ifs
      · exact hst
      · exact hst
      · intro q hq
        simp only at hq
        rcases mem_foldl_moveFirst hq with h | ⟨m, hm, hqm⟩
        · exact hst q h
        · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
          have := (rewritesAt_small hrw).2 m0 hm0
          rw [hqm]
          simp only [Frame.back, hfr, Bool.false_eq_true, ↓reduceIte]
          split_ifs <;> omega
  · -- near frame: no rewrite in either instance
    have n1 := rewritesAt_near (nearP_low (R' := R - 2) (C := C) (by omega) (by omega) hst f hfr)
    have n2 := rewritesAt_near (nearP_low (R' := R) (C := C) le_rfl (by omega) hst f hfr)
    unfold rwStep
    rw [n1, n2]
    exact ⟨rfl, hst⟩

/-- Removed cells stay near the top edge. -/
def TopSt (R : ℕ) (st : RWState) : Prop := LowSt R st ∧ ∀ c ∈ st.removed, c.1 ≤ 3

theorem rwStep_rstrip' {R C : ℕ} (hR : 13 ≤ R) (hC : 4 ≤ C) {st : RWState} (hst : TopSt R st)
    (f : Frame) : rwStep (R - 2) C st f = rwStep R C st f ∧ TopSt R (rwStep R C st f) := by
  obtain ⟨e1, e2⟩ := rwStep_rstrip hR hC hst.1 f
  refine ⟨e1, e2, ?_⟩
  cases hfr : f.fr
  · unfold rwStep
    cases hrw : rewritesAt (makeView R C f st.eff) with
    | none => exact hst.2
    | some rw =>
      simp only
      split_ifs
      · exact hst.2
      · exact hst.2
      · intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hst.2 c h
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
          have := (rewritesAt_small hrw).1 a ha
          simp only [Frame.back, hfr, Bool.false_eq_true, ↓reduceIte]
          split_ifs <;> omega
  · have n2 := rewritesAt_near (nearP_low (R' := R) (C := C) le_rfl (by omega) hst.1 f hfr)
    unfold rwStep
    rw [n2]
    exact hst.2

theorem rewriteAll_rstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 4 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, q.1.1 + 5 ≤ R) :
    rewriteAll (R - 2) C pts = rewriteAll R C pts ∧ TopSt R (rewriteAll R C pts) := by
  have key : ∀ (fs : List Frame) (st : RWState), TopSt R st →
      fs.foldl (rwStep (R - 2) C) st = fs.foldl (rwStep R C) st ∧ TopSt R (fs.foldl (rwStep R C) st) := by
    intro fs
    induction fs with
    | nil => intro st h; exact ⟨rfl, h⟩
    | cons f fs ih =>
      intro st h
      obtain ⟨e1, e2⟩ := rwStep_rstrip' hR hC h f
      simp only [List.foldl_cons]
      rw [e1]
      exact ih _ e2
  exact key frames ⟨pts, [], false⟩ ⟨hp, by simp⟩

/-! ### Right strip: the walk, restricted to lines `≤ R - 4`, is unchanged -/

def lowP (R : ℕ) (c : ℕ × ℕ) : Bool := decide (c.1 + 4 ≤ R)

theorem notchLen_bottom_zero {R C : ℕ} (hR : 9 ≤ R) {rem : List (ℕ × ℕ)}
    (hrem : ∀ c ∈ rem, c.1 ≤ 3) {f : Frame} (hf : f.fr = true) (htr : f.tr = false) {i : ℕ}
    (hi : i ≤ 4) : notchLen R C f rem i = 0 := by
  unfold notchLen
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro j hj hc
  simp only [List.contains_iff_mem] at hc
  have := hrem _ hc
  simp only [Frame.back, hf, htr, Bool.false_eq_true, ↓reduceIte] at this
  omega

theorem staircase_zero : staircase (fun _ => 0) = [(0, 0)] := by decide

theorem side_rstrip (R a : ℕ) (hR : 13 ≤ R) (g : ℕ → ℕ × ℕ) (hg : ∀ x, (g x).1 = x) :
    (((List.range R).filter fun x => decide (a < x ∧ x + 1 + 0 < R)).map g).filter (lowP R) =
      (((List.range (R - 2)).filter fun x => decide (a < x ∧ x + 1 + 0 < R - 2)).map g).filter
        (lowP R) := by
  rw [List.filter_map, List.filter_map, List.filter_filter, List.filter_filter]
  congr 1
  apply eq_of_sorted_mem (sorted_range_filter _ _) (sorted_range_filter _ _)
  intro x
  simp only [List.mem_filter, List.mem_range, Function.comp, lowP, hg, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem walk_rstrip {R C : ℕ} (hR : 13 ≤ R) {rem : List (ℕ × ℕ)} (hrem : ∀ c ∈ rem, c.1 ≤ 3) :
    (walk3 R C rem).filter (lowP R) = (walk3 (R - 2) C rem).filter (lowP R) := by
  rw [walk3_eq, walk3_eq]
  -- top staircases and notch lengths are the same
  have bTL : Frame.back (R - 2) C frameTL = Frame.back R C frameTL :=
    funext (back_same_low frameTL rfl)
  have bTR : Frame.back (R - 2) C frameTR = Frame.back R C frameTR :=
    funext (back_same_low frameTR rfl)
  have tTL : notchLen (R - 2) C frameTL rem = notchLen R C frameTL rem := by
    funext i; unfold notchLen; rw [bTL]
  have tTR : notchLen (R - 2) C frameTR rem = notchLen R C frameTR rem := by
    funext i; unfold notchLen; rw [bTR]
  have sTL : stairOf (R - 2) C frameTL rem = stairOf R C frameTL rem := by
    unfold stairOf; rw [tTL, bTL]
  have sTR : stairOf (R - 2) C frameTR rem = stairOf R C frameTR rem := by
    unfold stairOf; rw [tTR, bTR]
  have kTL : kOf (R - 2) C frameTL rem = kOf R C frameTL rem := by unfold kOf; rw [tTL]
  have kTR : kOf (R - 2) C frameTR rem = kOf R C frameTR rem := by unfold kOf; rw [tTR]
  -- bottom notches are empty
  have zero : ∀ R', 9 ≤ R' → ∀ f : Frame, f.fr = true → f.tr = false →
      staircase (notchLen R' C f rem) = [(0, 0)] ∧ notchLen R' C f rem 0 = 0 ∧ kOf R' C f rem = 0 := by
    intro R' h f hf htr
    have z : ∀ i, i ≤ 4 → notchLen R' C f rem i = 0 := fun i hi => notchLen_bottom_zero h hrem hf htr hi
    refine ⟨(staircase_congr (lam := fun _ => 0) z).trans staircase_zero, z 0 (by omega), ?_⟩
    unfold kOf
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro i hi
    simp at hi
    simp [z i (by omega)]
  obtain ⟨zBR, zBR0, kBR⟩ := zero R (by omega) frameBR rfl rfl
  obtain ⟨zBR', zBR0', kBR'⟩ := zero (R - 2) (by omega) frameBR rfl rfl
  obtain ⟨zBL, zBL0, kBL⟩ := zero R (by omega) frameBL rfl rfl
  obtain ⟨zBL', zBL0', kBL'⟩ := zero (R - 2) (by omega) frameBL rfl rfl
  have sBR : stairOf R C frameBR rem = [(R - 1, C - 1)] := by
    unfold stairOf; rw [zBR]; simp [Frame.back, frameBR]
  have sBR' : stairOf (R - 2) C frameBR rem = [(R - 2 - 1, C - 1)] := by
    unfold stairOf; rw [zBR']; simp [Frame.back, frameBR]
  have sBL : stairOf R C frameBL rem = [(R - 1, 0)] := by
    unfold stairOf; rw [zBL]; simp [Frame.back, frameBL]
  have sBL' : stairOf (R - 2) C frameBL rem = [(R - 2 - 1, 0)] := by
    unfold stairOf; rw [zBL']; simp [Frame.back, frameBL]
  rw [sTL, sTR, tTL, tTR, kTL, kTR, sBR, sBR', sBL, sBL', zBR0, zBR0', zBL0, zBL0', kBR, kBR',
    kBL, kBL']
  -- the top staircases are kept by the filter
  have keepTop : ∀ f : Frame, f.fr = false → f.tr = false →
      (stairOf R C f rem).filter (lowP R) = stairOf R C f rem := by
    intro f hf htr
    rw [List.filter_eq_self]
    intro c hc
    unfold stairOf at hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    have := staircase_small (notchLen_le R C f rem) a ha
    simp only [lowP, Frame.back, hf, htr, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    omega
  unfold walk3Core
  simp only [List.filter_append, List.filter_reverse, keepTop frameTL rfl rfl,
    keepTop frameTR rfl rfl]
  rw [side_rstrip R _ hR (fun x => (x, C - 1)) (fun x => rfl),
    side_rstrip R _ hR (fun x => (x, 0)) (fun x => rfl)]
  have e1 : ([(R - 1, C - 1)] : List (ℕ × ℕ)).filter (lowP R) = [] := by simp [lowP]; omega
  have e2 : ([(R - 2 - 1, C - 1)] : List (ℕ × ℕ)).filter (lowP R) = [] := by simp [lowP]; omega
  have e3 : ([(R - 1, 0)] : List (ℕ × ℕ)).filter (lowP R) = [] := by simp [lowP]; omega
  have e4 : ([(R - 2 - 1, 0)] : List (ℕ × ℕ)).filter (lowP R) = [] := by simp [lowP]; omega
  have e5 : ∀ (L : List ℕ) (x : ℕ), R < x + 4 → (L.map (fun y => (x, y))).filter (lowP R) = [] := by
    intro L x hx
    rw [List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
    simp only [lowP, decide_eq_true_eq]
    omega
  have ktop : ∀ L : List ℕ, (L.map (fun y => ((0 : ℕ), y))).filter (lowP R) =
      L.map (fun y => ((0 : ℕ), y)) := by
    intro L
    rw [List.filter_eq_self]
    intro c hc
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
    simp only [lowP, decide_eq_true_eq]
    omega
  rw [e1, e2, e3, e4, e5 _ (R - 1) (by omega), e5 _ (R - 2 - 1) (by omega), ktop]

/-- **Right strip: the R test gives the same answer.** -/
theorem effAltFrom_rstrip {R C : ℕ} (hR : 13 ≤ R) {st : RWState} (hst : TopSt R st) :
    effAltFrom (R - 2) C st = effAltFrom R C st := by
  unfold effAltFrom
  simp only
  have hwalk := walk_rstrip (C := C) hR hst.2
  generalize walk3 R C st.removed = W at hwalk ⊢
  generalize walk3 (R - 2) C st.removed = W' at hwalk ⊢
  have keep : ∀ q ∈ st.eff, lowP R q.1 = true := by
    intro q hq; have := hst.1 q hq; simp [lowP]; omega
  have hcount : ∀ q ∈ st.eff, W'.count q.1 = W.count q.1 := by
    intro q hq
    rw [← count_filter_keep (keep q hq) W, ← count_filter_keep (keep q hq) W', hwalk]
  have t3 : (st.eff.map fun q => (positions W' q.1, q.2)).any (fun pl => pl.1.length != 1) =
      (st.eff.map fun q => (positions W q.1, q.2)).any (fun pl => pl.1.length != 1) := by
    rw [List.any_map, List.any_map]
    exact any_congr' (fun q hq => by simp only [Function.comp, positions_length, hcount q hq])
  rw [t3]
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · rfl
  · rfl
  · have hin : ∀ q ∈ st.eff, q.1 ∈ W := by
      intro q hq
      have : (positions W q.1).length = 1 := by
        by_contra hne
        apply h4
        rw [List.any_eq_true]
        exact ⟨(positions W q.1, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, by simpa using hne⟩
      rw [positions_length] at this
      exact List.count_pos_iff.mp (by omega)
    have hin' : ∀ q ∈ st.eff, q.1 ∈ W' := fun q hq =>
      List.count_pos_iff.mp (by rw [hcount q hq]; exact List.count_pos_iff.mpr (hin q hq))
    have e1 : (st.eff.map fun q => (positions W' q.1, q.2)).map (fun pl => (pl.1.headD 0, pl.2)) =
        (st.eff.map fun q => (W.idxOf q.1, W'.idxOf q.1, q.2)).map (fun t => (t.2.1, t.2.2)) := by
      simp only [List.map_map]
      exact List.map_congr_left (fun q hq => by
        show ((positions W' q.1).headD 0, q.2) = (W'.idxOf q.1, q.2)
        rw [positions_head (hin' q hq)])
    have e2 : (st.eff.map fun q => (positions W q.1, q.2)).map (fun pl => (pl.1.headD 0, pl.2)) =
        (st.eff.map fun q => (W.idxOf q.1, W'.idxOf q.1, q.2)).map (fun t => (t.1, t.2.2)) := by
      simp only [List.map_map]
      exact List.map_congr_left (fun q hq => by
        show ((positions W q.1).headD 0, q.2) = (W.idxOf q.1, q.2)
        rw [positions_head (hin q hq)])
    rw [e1, e2]
    congr 1
    refine (sortByKey_colors _ ?_).symm
    intro t ht u hu
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hu
    simp only
    rw [idxOf_filter_lt (keep q hq) (keep q' hq') W (hin q hq) (hin q' hq'),
      idxOf_filter_lt (keep q hq) (keep q' hq') W' (hin' q hq) (hin' q' hq'), hwalk]

theorem effAlt3_rstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 4 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, q.1.1 + 5 ≤ R) : effAlt3 (R - 2) C pts = effAlt3 R C pts := by
  obtain ⟨e, h⟩ := rewriteAll_rstrip (C := C) hR hC hp
  rw [effAlt3_eq, effAlt3_eq, e]
  exact effAltFrom_rstrip hR h

/-! ### Right strip: T1, L1, L6 -/

set_option maxHeartbeats 4000000 in
theorem perim_order_rstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 2 ≤ C) {e f : ℕ × ℕ}
    (he : e.1 + 5 ≤ R ∧ e.2 < C) (hf : f.1 + 5 ≤ R ∧ f.2 < C) :
    (perimIndex R C e).getD 0 < (perimIndex R C f).getD 0 ↔
      (perimIndex (R - 2) C e).getD 0 < (perimIndex (R - 2) C f).getD 0 := by
  obtain ⟨ex, ey⟩ := e
  obtain ⟨fx, fy⟩ := f
  obtain ⟨a1, a2⟩ := he
  obtain ⟨b1, b2⟩ := hf
  simp only at *
  unfold perimIndex
  simp only [beq_iff_eq]
  split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega

theorem onPerim_rstrip {R C : ℕ} {e : ℕ × ℕ} (he : e.1 + 5 ≤ R) :
    OnPerim (R - 2) C e ↔ OnPerim R C e := by
  unfold OnPerim; omega

theorem zip_map_self {α β γ : Type} (a : α → β) (b : α → γ) :
    ∀ l : List α, (l.map a).zip (l.map b) = l.map fun x => (a x, b x)
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_map_self a b l]

theorem t1_rstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 2 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, q.1.1 + 5 ≤ R ∧ q.1.2 < C) (h : t1Fires (R - 2) C pts = true) :
    t1Fires R C pts = true := by
  unfold t1Fires at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hall, halt⟩ := h
  have some : ∀ q ∈ pts, (perimIndex (R - 2) C q.1).isSome = (perimIndex R C q.1).isSome := by
    intro q hq
    have := hp q hq
    apply Bool.eq_iff_iff.mpr
    rw [perimIndex_isSome (by omega) this.2, perimIndex_isSome (by omega) this.2,
      onPerim_rstrip this.1]
  refine ⟨?_, ?_⟩
  · rw [List.all_map] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro q hq
    have := hall q hq
    simp only [Function.comp] at this ⊢
    rw [← some q hq]
    exact this
  · let items : List (ℕ × ℕ × ℕ) := pts.map fun q =>
      ((perimIndex R C q.1).getD 0, (perimIndex (R - 2) C q.1).getD 0, q.2)
    have hord : ∀ t ∈ items, ∀ u ∈ items, t.1 < u.1 ↔ t.2.1 < u.2.1 := by
      intro t ht u hu
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hu
      exact perim_order_rstrip hR hC (hp q hq) (hp q' hq')
    have := sortByKey_colors items hord
    have z1 : ((pts.map fun q => perimIndex R C q.1).map (·.getD 0)).zip (pts.map (·.2)) =
        items.map fun t => (t.1, t.2.2) := by
      simp only [items, List.map_map]
      exact zip_map_self _ _ pts
    have z2 : ((pts.map fun q => perimIndex (R - 2) C q.1).map (·.getD 0)).zip (pts.map (·.2)) =
        items.map fun t => (t.2.1, t.2.2) := by
      simp only [items, List.map_map]
      exact zip_map_self _ _ pts
    rw [z1, this, ← z2]
    exact halt

theorem l1_rstrip {R C : ℕ} {pts : List Pt} (hp : ∀ q ∈ pts, q.1.1 + 5 ≤ R)
    (h : L1Prop (R - 2) C pts) : L1Prop R C pts := by
  obtain ⟨q, hq, hall⟩ := h
  refine ⟨q, hq, fun n h1 h2 hadj => hall n ?_ h2 hadj⟩
  have := hp q hq
  unfold Adjacent at hadj
  omega

theorem closureAt_none {pts : List Pt} {n1 n2 cor : ℕ × ℕ} (h : ∀ q ∈ pts, q.1 ≠ n1) :
    closureAt pts n1 n2 cor = none := by
  unfold closureAt
  have : pts.find? (·.1 == n1) = none := by
    rw [List.find?_eq_none]
    intro q hq
    simpa using h q hq
  rw [this]

theorem l6_rstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 2 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, q.1.1 + 5 ≤ R) (h : l6Fires (R - 2) C pts = true) : l6Fires R C pts = true := by
  unfold l6Fires at h ⊢
  rw [l6Closures_eq (by omega) hC] at h
  rw [l6Closures_eq (by omega) hC]
  have far : ∀ x, R ≤ x + 4 → ∀ y, ∀ q ∈ pts, q.1 ≠ (x, y) := by
    intro x hx y q hq he
    have := hp q hq
    rw [he] at this
    simp only at this
    omega
  unfold l6List at h ⊢
  rw [closureAt_none (n1 := (R - 2 - 1, 1)) (far _ (by omega) _),
    closureAt_none (n1 := (R - 2 - 1, C - 2)) (far _ (by omega) _)] at h
  rw [closureAt_none (n1 := (R - 1, 1)) (far _ (by omega) _),
    closureAt_none (n1 := (R - 1, C - 2)) (far _ (by omega) _)]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, Nat.lt_of_lt_of_le h.2 (Nat.mul_le_mul_right _ (by omega))⟩

/-! ### Right strip: assembly -/

theorem forall2_self {α : Type} {P : α → α → Prop} : ∀ {l : List α}, (∀ x ∈ l, P x x) →
    List.Forall₂ P l l
  | [], _ => List.Forall₂.nil
  | x :: _l, h => List.Forall₂.cons (h x List.mem_cons_self)
      (forall2_self (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem passStrip_right {I : Inst} {d : ℕ} (hI : InDom I) (hw : 13 ≤ I.w) (hd : d + 2 = I.w)
    (hfree : ∀ k, I.w ≤ k + 4 → k < I.w → I.FreeLine k) (hP : Passes I) :
    Passes (I.deleteAt d) := by
  have hC := hI.2.1
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := id hI
  have low : ∀ e ∈ I.ends, e.1 + 5 ≤ I.w ∧ e.2 < I.h := by
    intro e he
    have hb : e.1 < I.w ∧ e.2 < I.h := by
      simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact b0
      · exact b1
      · exact b2
      · exact b3
    refine ⟨?_, hb.2⟩
    by_contra hc
    exact hfree e.1 (by omega) hb.1 e he rfl
  have same : ∀ e ∈ I.ends, delAt d e = e := by
    intro e he
    have := (low e he).1
    unfold delAt
    rw [ite_eq_left (by omega)]
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at same low
  have hdel : I.deleteAt d = ⟨I.w - 2, I.h, I.s0, I.t0, I.s1, I.t1⟩ := by
    simp only [Inst.deleteAt, same.1, same.2.1, same.2.2.1, same.2.2.2]
  have f0 : I.FreeLine d := hfree d (by omega) (by omega)
  have f1 : I.FreeLine (d + 1) := hfree (d + 1) (by omega) (by omega)
  have par := parityOk_deleteAt (I := I) (by omega) f0 f1
  rw [hdel]
  set pts : List Pt := [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] with hpts
  have hp : ∀ q ∈ pts, q.1.1 + 5 ≤ I.w ∧ q.1.2 < I.h := by
    intro q hq
    simp only [hpts, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact low.1
    · exact low.2.1
    · exact low.2.2.1
    · exact low.2.2.2
  unfold Passes at hP ⊢
  by_contra hf
  apply absurd hP
  rw [Bool.not_eq_false] at hf ⊢
  unfold fires3 at hf ⊢
  simp only [Bool.or_eq_true] at hf ⊢
  rcases hf with (((((hpar | ht1) | ht2) | hl1) | hl6) | hfr) | hea
  · left; left; left; left; left; left
    simp only [Inst.deleteAt, same.1, same.2.1, same.2.2.1, same.2.2.2] at par
    rw [← par]; exact hpar
  · left; left; left; left; left; right
    exact t1_rstrip hw (by omega) hp ht1
  · left; left; left; left; right; exact ht2
  · left; left; left; right
    rw [l1Fires_iff] at hl1 ⊢
    exact l1_rstrip (fun q hq => (hp q hq).1) hl1
  · left; left; right
    exact l6_rstrip hw (by omega) (fun q hq => (hp q hq).1) hl6
  · left; right
    refine frames_any_strip (by omega) true (fun f hf => nearP_low (by omega) (by omega)
      (fun q hq => (hp q hq).1) f hf) (fun f hf => ⟨?_, ?_⟩) ?_ ?_ (by omega) hfr
    · simp only [Bool.not_true] at hf
      apply forall2_self
      intro q hq
      have h1 := hp q hq
      refine ⟨rfl, ⟨rfl, Or.inl (by simp [xf, hf])⟩, (onPerim_rstrip h1.1).mp, by omega, h1.2,
        by omega, h1.2, ?_, ?_⟩
      · simp only [Frame.H]; split_ifs <;> omega
      · simp only [Frame.W]; split_ifs <;> omega
    · simp only [Bool.not_true] at hf
      apply forall2_map_self'
      intro q hq
      rw [frame_to_eq, frame_to_eq]
      unfold xf
      simp [hf]
    · intro q hq; have := (hp q hq).1; omega
    · intro q hq
      simp only [hpts, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp
  · right
    rw [effAlt3_rstrip hw (by omega) (fun q hq => (hp q hq).1)] at hea
    exact hea

/-! ### Left strip: the rewrite phase -/

/-- `rwStep_map` with its two frame facts as hypotheses: the views agree and the corner-window
cells map through the deletion. -/
theorem rwStep_map_gen {R C d : ℕ} {st : RWState} (hav : StAv d R st) (f : Frame)
    (hv : rewritesAt (makeView (R - 2) C f (delPts d st.eff)) = rewritesAt (makeView R C f st.eff))
    (hb : ∀ a : ℕ × ℕ, a.1 ≤ 3 → a.2 ≤ 3 →
      f.back (R - 2) C a = delAt d (f.back R C a) ∧ Av d R (f.back R C a)) :
    rwStep (R - 2) C (mapSt d st) f = mapSt d (rwStep R C st f) ∧ StAv d R (rwStep R C st f) := by
  unfold rwStep mapSt
  simp only
  rw [hv]
  cases hrw : rewritesAt (makeView R C f st.eff) with
  | none => exact ⟨rfl, hav⟩
  | some rw =>
    obtain ⟨hsm1, hsm2⟩ := rewritesAt_small hrw
    have bc : ∀ a ∈ rw.removed, f.back (R - 2) C a = delAt d (f.back R C a) ∧
        Av d R (f.back R C a) := fun a ha => hb a (hsm1 a ha).1 (hsm1 a ha).2
    have bm : ∀ m ∈ rw.moves, f.back (R - 2) C m.1 = delAt d (f.back R C m.1) ∧
        f.back (R - 2) C m.2 = delAt d (f.back R C m.2) ∧ Av d R (f.back R C m.1) ∧
        Av d R (f.back R C m.2) := by
      intro m hm
      obtain ⟨h1, h2, h3, h4⟩ := hsm2 m hm
      obtain ⟨a1, a2⟩ := hb m.1 h1 h2
      obtain ⟨b1, b2⟩ := hb m.2 h3 h4
      exact ⟨a1, b1, a2, b2⟩
    have ecells : rw.removed.map (f.back (R - 2) C) = (rw.removed.map (f.back R C)).map (delAt d) := by
      rw [List.map_map]
      exact List.map_congr_left (fun a ha => (bc a ha).1)
    have emoves : (rw.moves.map fun m => (f.back (R - 2) C m.1, f.back (R - 2) C m.2)) =
        (rw.moves.map fun m => (f.back R C m.1, f.back R C m.2)).map
          (fun m => (delAt d m.1, delAt d m.2)) := by
      rw [List.map_map]
      exact List.map_congr_left (fun m hm => by simp only [Function.comp, (bm m hm).1, (bm m hm).2.1])
    have cav : ∀ c ∈ rw.removed.map (f.back R C), Av d R c := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      exact (bc a ha).2
    have mav : ∀ m ∈ rw.moves.map (fun m => (f.back R C m.1, f.back R C m.2)),
        Av d R m.1 ∧ Av d R m.2 := by
      intro m hm
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
      exact ⟨(bm m0 hm0).2.2.1, (bm m0 hm0).2.2.2⟩
    have c1 : ((rw.removed.map (f.back R C)).map (delAt d)).any
        (fun x => (st.removed.map (delAt d)).contains x) =
        (rw.removed.map (f.back R C)).any (fun x => st.removed.contains x) := by
      rw [List.any_map]
      exact any_congr' (fun x hx => contains_map_delAt hav.2 (cav x hx))
    have c2 : ((rw.moves.map fun m => (f.back R C m.1, f.back R C m.2)).map
        (fun m => (delAt d m.1, delAt d m.2))).any (fun m => (st.removed.map (delAt d)).contains m.2) =
        (rw.moves.map fun m => (f.back R C m.1, f.back R C m.2)).any
          (fun m => st.removed.contains m.2) := by
      rw [List.any_map]
      exact any_congr' (fun m hm => contains_map_delAt hav.2 (mav m hm).2)
    obtain ⟨fm1, fm2⟩ := foldl_moveFirst_map _ st.eff hav.1 mav
    simp only
    rw [ecells, emoves, c1, c2]
    split_ifs with h1 h2
    · exact ⟨rfl, hav⟩
    · exact ⟨rfl, hav⟩
    · refine ⟨?_, fm2, ?_⟩
      · simp only [fm1, List.map_append]
      · intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hav.2 c h
        · exact cav c h

/-- Invariant: endpoints at least 4 lines in from the near edge, removed cells within 4 lines of
the far edge. -/
def LSt (R : ℕ) (st : RWState) : Prop :=
  (∀ q ∈ st.eff, 4 ≤ q.1.1 ∧ q.1.1 < R) ∧ (∀ c ∈ st.removed, R ≤ c.1 + 4 ∧ c.1 < R)

theorem lst_av {R : ℕ} (hR : 6 ≤ R) {st : RWState} (h : LSt R st) : StAv 0 R st :=
  ⟨fun q hq => by have := h.1 q hq; exact ⟨by omega, by omega, this.2⟩,
   fun c hc => by have := h.2 c hc; exact ⟨by omega, by omega, this.2⟩⟩

theorem delAt0 {c : ℕ × ℕ} (h : 2 ≤ c.1) : delAt 0 c = (c.1 - 2, c.2) := by
  unfold delAt; rw [ite_eq_right (by omega)]

theorem back_far_lstrip {R C : ℕ} (hR : 13 ≤ R) (f : Frame) (hf : f.fr = true) {a : ℕ × ℕ}
    (ha1 : a.1 ≤ 3) (ha2 : a.2 ≤ 3) :
    f.back (R - 2) C a = delAt 0 (f.back R C a) ∧ Av 0 R (f.back R C a) ∧
      R ≤ (f.back R C a).1 + 4 := by
  obtain ⟨fr, fc, tr⟩ := f
  simp only at hf
  subst hf
  unfold Av
  cases tr
  · simp only [Frame.back, ↓reduceIte, Bool.false_eq_true]
    rw [delAt0 (by simp only; omega)]
    simp only [Prod.mk.injEq, and_true]
    omega
  · simp only [Frame.back, ↓reduceIte]
    rw [delAt0 (by simp only; omega)]
    simp only [Prod.mk.injEq, and_true]
    omega

theorem rwStep_lstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 4 ≤ C) {st : RWState} (hst : LSt R st)
    (f : Frame) :
    rwStep (R - 2) C (mapSt 0 st) f = mapSt 0 (rwStep R C st f) ∧ LSt R (rwStep R C st f) := by
  have hav := lst_av (by omega) hst
  cases hfr : f.fr
  · -- near frame: no rewrite in either instance
    have nR : NearP R C f st.eff := by
      intro q hq
      have := (hst.1 q hq).1
      obtain ⟨fr, fc, tr⟩ := f
      simp only at hfr
      subst hfr
      cases tr <;> simp only [Frame.to, ↓reduceIte, Bool.false_eq_true] <;> omega
    have nR' : NearP (R - 2) C f (delPts 0 st.eff) := by
      intro q hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      have := (hst.1 q0 hq0).1
      obtain ⟨fr, fc, tr⟩ := f
      simp only at hfr
      subst hfr
      rw [delAt0 (by omega)]
      cases tr <;> simp only [Frame.to, ↓reduceIte, Bool.false_eq_true] <;> omega
    unfold rwStep mapSt
    simp only
    rw [rewritesAt_near nR', rewritesAt_near nR]
    exact ⟨rfl, hst⟩
  · -- far frame: the same view, cells shifted by the deletion
    have hsame : SameCells R (R - 2) C f st.eff (delPts 0 st.eff) := by
      unfold delPts
      apply forall2_map_self
      intro q hq
      have := hst.1 q hq
      refine ⟨rfl, ?_⟩
      rw [delAt0 (by omega), frame_to_eq, frame_to_eq]
      unfold xf
      simp only [hfr, ↓reduceIte]
      have e : R - 2 - 1 - (q.1.1 - 2) = R - 1 - q.1.1 := by omega
      rw [e]
    have hv : rewritesAt (makeView (R - 2) C f (delPts 0 st.eff)) =
        rewritesAt (makeView R C f st.eff) := by
      apply rewritesAt_congr
      · intro r c _ _
        exact view_at_same hsame r c
      all_goals (simp only [makeView, Frame.H, Frame.W]; split_ifs <;> omega)
    obtain ⟨e1, e2⟩ := rwStep_map_gen hav f hv
      (fun a h1 h2 => ⟨(back_far_lstrip hR f hfr h1 h2).1, (back_far_lstrip hR f hfr h1 h2).2.1⟩)
    refine ⟨e1, ?_, ?_⟩
    · -- endpoints: unmoved, or moved to a far-frame cell
      unfold rwStep
      cases hrw : rewritesAt (makeView R C f st.eff) with
      | none => exact hst.1
      | some rw =>
        simp only
        split_ifs
        · exact hst.1
        · exact hst.1
        · intro q hq
          simp only at hq
          rcases mem_foldl_moveFirst hq with h | ⟨m, hm, hqm⟩
          · exact hst.1 q h
          · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
            obtain ⟨-, -, h3, h4⟩ := (rewritesAt_small hrw).2 m0 hm0
            obtain ⟨-, ⟨-, -, hlt⟩, hge⟩ := back_far_lstrip (C := C) hR f hfr h3 h4
            rw [hqm]
            simp only
            exact ⟨by omega, hlt⟩
    · unfold rwStep
      cases hrw : rewritesAt (makeView R C f st.eff) with
      | none => exact hst.2
      | some rw =>
        simp only
        split_ifs
        · exact hst.2
        · exact hst.2
        · intro c hc
          rcases List.mem_append.mp hc with h | h
          · exact hst.2 c h
          · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
            obtain ⟨h1, h2⟩ := (rewritesAt_small hrw).1 a ha
            obtain ⟨-, ⟨-, -, hlt⟩, hge⟩ := back_far_lstrip (C := C) hR f hfr h1 h2
            exact ⟨hge, hlt⟩

theorem rewriteAll_lstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 4 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, 4 ≤ q.1.1 ∧ q.1.1 < R) :
    rewriteAll (R - 2) C (delPts 0 pts) = mapSt 0 (rewriteAll R C pts) ∧
      LSt R (rewriteAll R C pts) := by
  have key : ∀ (fs : List Frame) (st : RWState), LSt R st →
      fs.foldl (rwStep (R - 2) C) (mapSt 0 st) = mapSt 0 (fs.foldl (rwStep R C) st) ∧
        LSt R (fs.foldl (rwStep R C) st) := by
    intro fs
    induction fs with
    | nil => intro st h; exact ⟨rfl, h⟩
    | cons f fs ih =>
      intro st h
      obtain ⟨e1, e2⟩ := rwStep_lstrip hR hC h f
      simp only [List.foldl_cons]
      rw [e1]
      exact ih _ e2
  exact key frames ⟨pts, [], false⟩ ⟨hp, by simp⟩

/-! ### The R test from a walk relation -/

set_option maxHeartbeats 1000000 in
/-- `effAltFrom_map` with the walk relation as a hypothesis: the larger walk, filtered by `P`, is
the smaller walk, filtered by `P'`, mapped by the injective `g`. -/
theorem effAltFrom_gen {R R' C d : ℕ} {st : RWState} (hav : StAv d R st) (P P' : ℕ × ℕ → Bool)
    (g : ℕ × ℕ → ℕ × ℕ) (hg : Function.Injective g) (hP : ∀ q ∈ st.eff, P q.1 = true)
    (hP' : ∀ q ∈ st.eff, P' (delAt d q.1) = true) (hgd : ∀ q ∈ st.eff, g (delAt d q.1) = q.1)
    (hwalk : (walk3 R C st.removed).filter P =
      ((walk3 R' C (st.removed.map (delAt d))).filter P').map g) :
    effAltFrom R' C (mapSt d st) = effAltFrom R C st := by
  unfold effAltFrom mapSt
  simp only
  generalize walk3 R C st.removed = W at hwalk ⊢
  generalize walk3 R' C (st.removed.map (delAt d)) = W' at hwalk ⊢
  have hcount : ∀ q ∈ st.eff, W'.count (delAt d q.1) = W.count q.1 := by
    intro q hq
    have h1 := count_filter_keep (hP q hq) W
    rw [hwalk] at h1
    have e := List.count_map_of_injective (W'.filter P') g hg (delAt d q.1)
    rw [hgd q hq] at e
    rw [← count_filter_keep (hP' q hq) W', ← e, h1]
  have hord : ∀ q ∈ st.eff, ∀ q' ∈ st.eff, q.1 ∈ W → q'.1 ∈ W →
      (W.idxOf q.1 < W.idxOf q'.1 ↔ W'.idxOf (delAt d q.1) < W'.idxOf (delAt d q'.1)) := by
    intro q hq q' hq' hm hm'
    have mem' : ∀ q ∈ st.eff, q.1 ∈ W → delAt d q.1 ∈ W' := fun q hq hm =>
      List.count_pos_iff.mp (by rw [hcount q hq]; exact List.count_pos_iff.mpr hm)
    rw [idxOf_filter_lt (hP q hq) (hP q' hq') W hm hm', hwalk,
      idxOf_filter_lt (hP' q hq) (hP' q' hq') W' (mem' q hq hm) (mem' q' hq' hm'),
      ← idxOf_map_inj hg (delAt d q.1) (W'.filter P'),
      ← idxOf_map_inj hg (delAt d q'.1) (W'.filter P'), hgd q hq, hgd q' hq']
  -- the four tests
  have t1 : (delPts d st.eff).any (fun q => (st.removed.map (delAt d)).contains q.1) =
      st.eff.any (fun q => st.removed.contains q.1) := by
    unfold delPts
    rw [List.any_map]
    exact any_congr' (fun q hq => contains_map_delAt hav.2 (hav.1 q hq))
  have t2 : ((delPts d st.eff).map (·.1)).dedup.length = (st.eff.map (·.1)).dedup.length := by
    unfold delPts
    rw [List.map_map]
    have : ((fun q : Pt => q.1) ∘ fun q : Pt => (delAt d q.1, q.2)) = (delAt d) ∘ (fun q : Pt => q.1) := rfl
    rw [this, ← List.map_map]
    apply dedup_length_map_inj
    intro x hx y hy h
    obtain ⟨qx, hqx, rfl⟩ := List.mem_map.mp hx
    obtain ⟨qy, hqy, rfl⟩ := List.mem_map.mp hy
    exact (delAt_inj' (hav.1 qx hqx) (hav.1 qy hqy)).mp h
  have t3 : ((delPts d st.eff).map fun q => (positions W' q.1, q.2)).any
        (fun pl => pl.1.length != 1) =
      (st.eff.map fun q => (positions W q.1, q.2)).any (fun pl => pl.1.length != 1) := by
    unfold delPts
    rw [List.map_map, List.any_map, List.any_map]
    exact any_congr' (fun q hq => by
      simp only [Function.comp, positions_length, hcount q hq])
  rw [t1, t2, t3]
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · rfl
  · rfl
  · have hin : ∀ q ∈ st.eff, q.1 ∈ W := by
      intro q hq
      have : (positions W q.1).length = 1 := by
        by_contra hne
        apply h4
        rw [List.any_eq_true]
        exact ⟨(positions W q.1, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, by simpa using hne⟩
      rw [positions_length] at this
      exact List.count_pos_iff.mp (by omega)
    have e1 : ((delPts d st.eff).map fun q => (positions W' q.1, q.2)).map
          (fun pl => (pl.1.headD 0, pl.2)) =
        (st.eff.map fun q => (W.idxOf q.1, W'.idxOf (delAt d q.1), q.2)).map
          (fun t => (t.2.1, t.2.2)) := by
      unfold delPts
      simp only [List.map_map]
      refine List.map_congr_left (fun q hq => ?_)
      have : delAt d q.1 ∈ W' :=
        List.count_pos_iff.mp (by rw [hcount q hq]; exact List.count_pos_iff.mpr (hin q hq))
      show ((positions W' (delAt d q.1)).headD 0, q.2) = (W'.idxOf (delAt d q.1), q.2)
      rw [positions_head this]
    have e2 : (st.eff.map fun q => (positions W q.1, q.2)).map (fun pl => (pl.1.headD 0, pl.2)) =
        (st.eff.map fun q => (W.idxOf q.1, W'.idxOf (delAt d q.1), q.2)).map
          (fun t => (t.1, t.2.2)) := by
      simp only [List.map_map]
      exact List.map_congr_left (fun q hq => by
        show ((positions W q.1).headD 0, q.2) = (W.idxOf q.1, q.2)
        rw [positions_head (hin q hq)])
    rw [e1, e2]
    congr 1
    refine (sortByKey_colors _ ?_).symm
    intro t ht u hu
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hu
    exact hord q hq q' hq' (hin q hq) (hin q' hq')

/-! ### Left strip: the walk, away from the strip, is shifted -/

def ge4 (c : ℕ × ℕ) : Bool := decide (4 ≤ c.1)
def ge2 (c : ℕ × ℕ) : Bool := decide (2 ≤ c.1)

theorem liftR0 (c : ℕ × ℕ) : liftR 0 c = (c.1 + 2, c.2) := by
  simp [liftR, liftN]

theorem back_bot {R C : ℕ} (hR : 13 ≤ R) (f : Frame) (hf : f.fr = true) {a : ℕ × ℕ}
    (ha1 : a.1 ≤ 4) (ha2 : a.2 ≤ 4) :
    f.back (R - 2) C a = delAt 0 (f.back R C a) ∧ Av 0 R (f.back R C a) ∧
      R ≤ (f.back R C a).1 + 5 := by
  obtain ⟨fr, fc, tr⟩ := f
  simp only at hf
  subst hf
  unfold Av
  cases tr
  · simp only [Frame.back, ↓reduceIte, Bool.false_eq_true]
    rw [delAt0 (by simp only; omega)]
    simp only [Prod.mk.injEq, and_true]
    omega
  · simp only [Frame.back, ↓reduceIte]
    rw [delAt0 (by simp only; omega)]
    simp only [Prod.mk.injEq, and_true]
    omega

theorem notchLen_bot {R C : ℕ} (hR : 13 ≤ R) (f : Frame) (hf : f.fr = true)
    {rem : List (ℕ × ℕ)} (hrem : ∀ c ∈ rem, Av 0 R c) {i : ℕ} (hi : i ≤ 4) :
    notchLen (R - 2) C f (rem.map (delAt 0)) i = notchLen R C f rem i := by
  unfold notchLen
  congr 1
  apply List.filter_congr
  intro j hj
  have hj4 : j ≤ 4 := by simp at hj; omega
  obtain ⟨e1, e2, -⟩ := back_bot (C := C) hR f hf (a := (i, j)) hi hj4
  rw [e1, contains_map_delAt hrem e2]

theorem stairOf_bot {R C : ℕ} (hR : 13 ≤ R) (f : Frame) (hf : f.fr = true)
    {rem : List (ℕ × ℕ)} (hrem : ∀ c ∈ rem, Av 0 R c) :
    stairOf (R - 2) C f (rem.map (delAt 0)) = (stairOf R C f rem).map (delAt 0) ∧
      ∀ c ∈ stairOf R C f rem, Av 0 R c ∧ R ≤ c.1 + 5 := by
  have hl : staircase (notchLen (R - 2) C f (rem.map (delAt 0))) =
      staircase (notchLen R C f rem) :=
    staircase_congr (fun i hi => notchLen_bot hR f hf hrem hi)
  unfold stairOf
  rw [hl, List.map_map]
  refine ⟨List.map_congr_left (fun a ha => ?_), fun c hc => ?_⟩
  · have := staircase_small (notchLen_le R C f rem) a ha
    exact (back_bot (C := C) hR f hf this.1 this.2).1
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    have := staircase_small (notchLen_le R C f rem) a ha
    exact (back_bot (C := C) hR f hf this.1 this.2).2

theorem kOf_bot {R C : ℕ} (hR : 13 ≤ R) (f : Frame) (hf : f.fr = true) {rem : List (ℕ × ℕ)}
    (hrem : ∀ c ∈ rem, Av 0 R c) : kOf (R - 2) C f (rem.map (delAt 0)) = kOf R C f rem := by
  unfold kOf
  congr 1
  apply List.filter_congr
  intro i hi
  simp at hi
  rw [notchLen_bot hR f hf hrem (by omega)]

/-- Top corners have empty notches when every removed cell is at line `≥ 5`. -/
theorem top_zero {R C : ℕ} {rem : List (ℕ × ℕ)} (hrem : ∀ c ∈ rem, 5 ≤ c.1) (f : Frame)
    (hf : f.fr = false) (htr : f.tr = false) :
    stairOf R C f rem = [f.back R C (0, 0)] ∧ notchLen R C f rem 0 = 0 ∧ kOf R C f rem = 0 := by
  have z : ∀ i, i ≤ 4 → notchLen R C f rem i = 0 := by
    intro i hi
    unfold notchLen
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro j hj hc
    simp only [List.contains_iff_mem] at hc
    have := hrem _ hc
    simp only [Frame.back, hf, htr, Bool.false_eq_true, ↓reduceIte] at this
    omega
  refine ⟨?_, z 0 (by omega), ?_⟩
  · unfold stairOf
    rw [(staircase_congr (lam := fun _ => 0) z).trans staircase_zero]
    rfl
  · unfold kOf
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro i hi
    simp at hi
    simp [z i (by omega)]

theorem side_lstrip (R b c : ℕ) (hR : 13 ≤ R) :
    (((List.range R).filter fun x => decide (0 < x ∧ x + 1 + b < R)).map (fun x => (x, c))).filter
        ge4 =
      ((((List.range (R - 2)).filter fun x => decide (0 < x ∧ x + 1 + b < R - 2)).map
        (fun x => (x, c))).filter ge2).map (liftR 0) := by
  rw [List.filter_map, List.filter_map, List.filter_filter, List.filter_filter, List.map_map]
  have key : (List.range R).filter (fun x => (ge4 ∘ fun x => (x, c)) x &&
        decide (0 < x ∧ x + 1 + b < R)) =
      ((List.range (R - 2)).filter (fun x => (ge2 ∘ fun x => (x, c)) x &&
        decide (0 < x ∧ x + 1 + b < R - 2))).map (· + 2) := by
    apply eq_of_sorted_mem (sorted_range_filter _ _)
      ((sorted_range_filter _ _).map _ (fun x y h => by omega))
    intro x
    simp only [List.mem_filter, List.mem_range, List.mem_map, Function.comp, ge4, ge2,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hx, h1, h2, h3⟩
      exact ⟨x - 2, ⟨by omega, by omega, by omega, by omega⟩, by omega⟩
    · rintro ⟨y, ⟨hy, h1, h2, h3⟩, rfl⟩
      exact ⟨by omega, by omega, by omega, by omega⟩
  rw [key, List.map_map]
  apply List.map_congr_left
  intro x _
  simp [liftR0]

theorem stair_lstrip {R : ℕ} (hR : 13 ≤ R) {br : List (ℕ × ℕ)}
    (hb : ∀ c ∈ br, Av 0 R c ∧ R ≤ c.1 + 5) :
    br.filter ge4 = ((br.map (delAt 0)).filter ge2).map (liftR 0) := by
  have e1 : br.filter ge4 = br := by
    rw [List.filter_eq_self]
    intro c hc; have := hb c hc; simp [ge4]; omega
  have e2 : (br.map (delAt 0)).filter ge2 = br.map (delAt 0) := by
    rw [List.filter_eq_self]
    intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    have := hb c0 hc0
    rw [delAt0 (by omega)]
    simp [ge2]; omega
  rw [e1, e2, map_liftR_of_av (fun c hc => (hb c hc).1)]

theorem row_lstrip {R : ℕ} (hR : 13 ≤ R) (L : List ℕ) :
    (L.map fun y => (R - 1, y)).filter ge4 =
      ((L.map fun y => (R - 2 - 1, y)).filter ge2).map (liftR 0) := by
  have e1 : (L.map fun y => (R - 1, y)).filter ge4 = L.map fun y => (R - 1, y) := by
    rw [List.filter_eq_self]; intro c hc; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc; simp [ge4]; omega
  have e2 : (L.map fun y => (R - 2 - 1, y)).filter ge2 = L.map fun y => (R - 2 - 1, y) := by
    rw [List.filter_eq_self]; intro c hc; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc; simp [ge2]; omega
  rw [e1, e2, List.map_map]
  apply List.map_congr_left
  intro y _
  simp only [Function.comp, liftR0, Prod.mk.injEq, and_true]
  omega

theorem top_lstrip (p : ℕ × ℕ → Bool) (hp : ∀ y, p (0, y) = false) (L : List ℕ) :
    (L.map fun y => ((0 : ℕ), y)).filter p = [] := by
  rw [List.filter_eq_nil_iff]
  intro c hc
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
  simp [hp]

/-- **The walk relation for the left strip.** -/
theorem walk3_lstrip {R C : ℕ} (hR : 13 ≤ R) {rem : List (ℕ × ℕ)}
    (hrem : ∀ c ∈ rem, R ≤ c.1 + 4 ∧ c.1 < R) :
    (walk3 R C rem).filter ge4 = ((walk3 (R - 2) C (rem.map (delAt 0))).filter ge2).map (liftR 0) := by
  have hav : ∀ c ∈ rem, Av 0 R c := fun c hc => by
    have := hrem c hc; exact ⟨by omega, by omega, this.2⟩
  have h5 : ∀ c ∈ rem, 5 ≤ c.1 := fun c hc => by have := hrem c hc; omega
  have h5' : ∀ c ∈ rem.map (delAt 0), 5 ≤ c.1 := by
    intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    have := hrem c0 hc0
    rw [delAt0 (by omega)]; simp only; omega
  rw [walk3_eq, walk3_eq]
  obtain ⟨tTL, nTL, kTL⟩ := top_zero (R := R) (C := C) h5 frameTL rfl rfl
  obtain ⟨tTR, nTR, kTR⟩ := top_zero (R := R) (C := C) h5 frameTR rfl rfl
  obtain ⟨tTL', nTL', kTL'⟩ := top_zero (R := R - 2) (C := C) h5' frameTL rfl rfl
  obtain ⟨tTR', nTR', kTR'⟩ := top_zero (R := R - 2) (C := C) h5' frameTR rfl rfl
  obtain ⟨sBR, aBR⟩ := stairOf_bot (C := C) hR frameBR rfl hav
  obtain ⟨sBL, aBL⟩ := stairOf_bot (C := C) hR frameBL rfl hav
  rw [tTL, tTR, tTL', tTR', nTL, nTR, nTL', nTR', kTL, kTR, kTL', kTR', sBR, sBL,
    notchLen_bot hR frameBR rfl hav (by omega), notchLen_bot hR frameBL rfl hav (by omega),
    kOf_bot hR frameBR rfl hav, kOf_bot hR frameBL rfl hav]
  unfold walk3Core
  simp only [List.filter_append, List.map_append, List.filter_reverse, List.map_reverse]
  have f1 : ∀ (R' : ℕ) (f : Frame) (p : ℕ × ℕ → Bool), f.fr = false → f.tr = false →
      p (0, (f.back R' C (0, 0)).2) = false → [f.back R' C (0, 0)].filter p = [] := by
    intro R' f p hf htr hp
    have : f.back R' C (0, 0) = (0, (f.back R' C (0, 0)).2) := by
      simp [Frame.back, hf, htr]
    rw [this]
    simp [hp]
  rw [f1 R frameTL ge4 rfl rfl (by simp [ge4]), f1 R frameTR ge4 rfl rfl (by simp [ge4]),
    f1 (R - 2) frameTL ge2 rfl rfl (by simp [ge2]), f1 (R - 2) frameTR ge2 rfl rfl (by simp [ge2]),
    top_lstrip ge4 (by simp [ge4]), top_lstrip ge2 (by simp [ge2]),
    side_lstrip R _ (C - 1) hR, side_lstrip R _ 0 hR, row_lstrip hR,
    stair_lstrip hR aBR, stair_lstrip hR aBL]
  simp

/-- **Left strip: the R test gives the same answer.** -/
theorem effAlt3_lstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 4 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, 4 ≤ q.1.1 ∧ q.1.1 < R) : effAlt3 (R - 2) C (delPts 0 pts) = effAlt3 R C pts := by
  obtain ⟨e, h⟩ := rewriteAll_lstrip (C := C) hR hC hp
  rw [effAlt3_eq, effAlt3_eq, e]
  have hav := lst_av (by omega) h
  refine effAltFrom_gen hav ge4 ge2 (liftR 0) (liftR_injective 0) (fun q hq => ?_) (fun q hq => ?_)
    (fun q hq => liftR_delAt (hav.1 q hq)) (walk3_lstrip hR h.2)
  · have := h.1 q hq; simp [ge4]; omega
  · have := h.1 q hq; rw [delAt0 (by omega)]; simp [ge2]; omega

/-! ### Left strip: T1, T2, L1, L6 -/

/-- Endpoints of a left-strip instance: at line `≥ 4`, inside the grid. -/
def LIn (R C : ℕ) (pts : List Pt) : Prop := ∀ q ∈ pts, 4 ≤ q.1.1 ∧ q.1.1 < R ∧ q.1.2 < C

set_option maxHeartbeats 4000000 in
theorem perim_order_lstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 2 ≤ C) {e f : ℕ × ℕ}
    (he : 4 ≤ e.1 ∧ e.1 < R ∧ e.2 < C) (hf : 4 ≤ f.1 ∧ f.1 < R ∧ f.2 < C) :
    (perimIndex R C e).getD 0 < (perimIndex R C f).getD 0 ↔
      (perimIndex (R - 2) C (delAt 0 e)).getD 0 < (perimIndex (R - 2) C (delAt 0 f)).getD 0 := by
  rw [delAt0 (by omega), delAt0 (by omega)]
  obtain ⟨ex, ey⟩ := e
  obtain ⟨fx, fy⟩ := f
  obtain ⟨a1, a2, a3⟩ := he
  obtain ⟨b1, b2, b3⟩ := hf
  simp only at *
  unfold perimIndex
  simp only [beq_iff_eq]
  split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega

theorem onPerim_lstrip {R C : ℕ} {e : ℕ × ℕ} (he : 4 ≤ e.1) :
    OnPerim (R - 2) C (delAt 0 e) ↔ OnPerim R C e := by
  rw [delAt0 (by omega)]; unfold OnPerim; simp only; omega

theorem t1_lstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 2 ≤ C) {pts : List Pt} (hp : LIn R C pts)
    (h : t1Fires (R - 2) C (delPts 0 pts) = true) : t1Fires R C pts = true := by
  unfold t1Fires at h ⊢
  unfold delPts at h
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hall, halt⟩ := h
  have some : ∀ q ∈ pts,
      (perimIndex (R - 2) C (delAt 0 q.1)).isSome = (perimIndex R C q.1).isSome := by
    intro q hq
    have := hp q hq
    apply Bool.eq_iff_iff.mpr
    have hx : (delAt 0 q.1).1 < R - 2 ∧ (delAt 0 q.1).2 < C := by
      rw [delAt0 (by omega)]; simp only; omega
    rw [perimIndex_isSome hx.1 hx.2, perimIndex_isSome this.2.1 this.2.2, onPerim_lstrip this.1]
  refine ⟨?_, ?_⟩
  · rw [List.map_map, List.all_map] at hall
    rw [List.all_map]
    rw [List.all_eq_true] at hall ⊢
    intro q hq
    have := hall q hq
    simp only [Function.comp] at this ⊢
    rw [← some q hq]
    exact this
  · let items : List (ℕ × ℕ × ℕ) := pts.map fun q =>
      ((perimIndex R C q.1).getD 0, (perimIndex (R - 2) C (delAt 0 q.1)).getD 0, q.2)
    have hord : ∀ t ∈ items, ∀ u ∈ items, t.1 < u.1 ↔ t.2.1 < u.2.1 := by
      intro t ht u hu
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hu
      exact perim_order_lstrip hR hC (hp q hq) (hp q' hq')
    have := sortByKey_colors items hord
    have z1 : ((pts.map fun q => perimIndex R C q.1).map (·.getD 0)).zip (pts.map (·.2)) =
        items.map fun t => (t.1, t.2.2) := by
      simp only [items, List.map_map]
      exact zip_map_self _ _ pts
    have z2 : (((pts.map fun q => (delAt 0 q.1, q.2)).map fun q => perimIndex (R - 2) C q.1).map
          (·.getD 0)).zip ((pts.map fun q => (delAt 0 q.1, q.2)).map (·.2)) =
        items.map fun t => (t.2.1, t.2.2) := by
      simp only [items, List.map_map]
      exact zip_map_self _ _ pts
    rw [z1, this, ← z2]
    exact halt

theorem t2_lstrip {a b c e : ℕ × ℕ} (ha : 2 ≤ a.1) (hb : 2 ≤ b.1) (hc : 2 ≤ c.1) (he : 2 ≤ e.1) :
    t2Fires [delAt 0 a, delAt 0 b, delAt 0 c, delAt 0 e] = t2Fires [a, b, c, e] := by
  rw [delAt0 ha, delAt0 hb, delAt0 hc, delAt0 he]
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  obtain ⟨e1, e2⟩ := e
  simp only at ha hb hc he
  unfold t2Fires
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.headD_cons,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  have hM : max (max (max (max 0 (a1 - 2)) (b1 - 2)) (c1 - 2)) (e1 - 2) =
      max (max (max (max 0 a1) b1) c1) e1 - 2 := by omega
  have hm : min (min (min (min (a1 - 2) (a1 - 2)) (b1 - 2)) (c1 - 2)) (e1 - 2) =
      min (min (min (min a1 a1) b1) c1) e1 - 2 := by omega
  have hm2 : 2 ≤ min (min (min (min a1 a1) b1) c1) e1 := by omega
  have hMm : min (min (min (min a1 a1) b1) c1) e1 ≤ max (max (max (max 0 a1) b1) c1) e1 := by
    omega
  rw [hM, hm]
  generalize max (max (max (max 0 a1) b1) c1) e1 = M at *
  generalize min (min (min (min a1 a1) b1) c1) e1 = m at *
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  constructor <;> intro h <;> omega

theorem l1_lstrip {R C : ℕ} {pts : List Pt} (hp : LIn R C pts)
    (h : L1Prop (R - 2) C (delPts 0 pts)) : L1Prop R C pts := by
  obtain ⟨q', hq', hall⟩ := h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
  have hq4 := hp q hq
  refine ⟨q, hq, fun n h1 h2 hadj => ?_⟩
  have hn : 3 ≤ n.1 := by unfold Adjacent at hadj; omega
  have hadj' : Adjacent (delAt 0 q.1) (n.1 - 2, n.2) := by
    rw [delAt0 (by omega)]; unfold Adjacent at hadj ⊢; simp only; omega
  obtain ⟨e', he', hne, hcol⟩ := hall (n.1 - 2, n.2) (by simp only; omega) h2 hadj'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
  have he4 := hp e he
  refine ⟨e, he, ?_, hcol⟩
  rw [delAt0 (by omega)] at hne
  simp only [Prod.mk.injEq] at hne
  exact Prod.ext (by omega) hne.2

theorem l6_lstrip {R C : ℕ} (hR : 13 ≤ R) (hC : 2 ≤ C) {pts : List Pt} (hp : LIn R C pts)
    (h : l6Fires (R - 2) C (delPts 0 pts) = true) : l6Fires R C pts = true := by
  have rel : ∀ (n1 n2 cor : ℕ × ℕ), (n1.1 ≤ 1 ∨ R ≤ n1.1 + 2) → (n2.1 ≤ 1 ∨ R ≤ n2.1 + 2) →
      (cor.1 ≤ 1 ∨ R ≤ cor.1 + 2) →
      let g := fun n : ℕ × ℕ => if n.1 ≤ 1 then n else (n.1 - 2, n.2)
      closureAt (delPts 0 pts) (g n1) (g n2) (g cor) = closureAt pts n1 n2 cor := by
    intro n1 n2 cor c1 c2 c3 g
    apply closureAt_rel
    have one : ∀ q ∈ pts, ∀ n : ℕ × ℕ, (n.1 ≤ 1 ∨ R ≤ n.1 + 2) → (delAt 0 q.1 = g n ↔ q.1 = n) := by
      intro q hq n hn
      have := hp q hq
      rw [delAt0 (by omega)]
      simp only [g]
      split_ifs with hn1
      · constructor
        · intro e; rw [← e] at hn1; simp only at hn1; omega
        · intro e; rw [e] at this; omega
      · constructor
        · intro e
          simp only [Prod.mk.injEq] at e
          exact Prod.ext (by omega) e.2
        · intro e; rw [e]
    unfold delPts
    exact forall2_map_self (fun q hq => ⟨rfl, one q hq n1 c1, one q hq n2 c2, one q hq cor c3⟩)
  unfold l6Fires at h ⊢
  rw [l6Closures_eq (by omega) hC] at h
  rw [l6Closures_eq (by omega) hC]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨h0, h1⟩, h6⟩ := h
  have e1 := rel (0, 1) (1, 0) (0, 0) (by simp) (by simp) (by simp)
  have e2 := rel (0, C - 2) (1, C - 1) (0, C - 1) (by simp) (by simp) (by simp)
  have e3 := rel (R - 1, 1) (R - 2, 0) (R - 1, 0) (Or.inr (by simp; omega))
    (Or.inr (by simp; omega)) (Or.inr (by simp; omega))
  have e4 := rel (R - 1, C - 2) (R - 2, C - 1) (R - 1, C - 1) (Or.inr (by simp; omega))
    (Or.inr (by simp; omega)) (Or.inr (by simp; omega))
  simp only [show ¬ (R - 1 ≤ 1) by omega, show ¬ (R - 2 ≤ 1) by omega, ↓reduceIte,
    show (0 : ℕ) ≤ 1 by omega, show (1 : ℕ) ≤ 1 by omega] at e1 e2 e3 e4
  have w1 : R - 1 - 2 = R - 2 - 1 := by omega
  unfold l6List at h0 h1 ⊢
  rw [w1] at e3 e4
  rw [e1, e2, e3, e4] at h0 h1
  exact ⟨⟨h0, h1⟩, Nat.lt_of_lt_of_le h6 (Nat.mul_le_mul_right _ (by omega))⟩

/-! ### Left strip: assembly -/

theorem nearP_lstrip {R C : ℕ} {pts : List Pt} (hp : ∀ q ∈ pts, 4 ≤ q.1.1) (f : Frame)
    (hf : f.fr = false) : NearP (R - 2) C f (delPts 0 pts) := by
  intro q hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have := hp q0 hq0
  obtain ⟨fr, fc, tr⟩ := f
  simp only at hf
  subst hf
  rw [delAt0 (by omega)]
  cases tr <;> simp only [Frame.to, ↓reduceIte, Bool.false_eq_true] <;> omega

theorem far_lstrip {R C : ℕ} (hR : 13 ≤ R) {pts : List Pt} (hp : LIn R C pts) (f : Frame)
    (hf : f.fr = true) :
    List.Forall₂ (WinRel R (R - 2) C f) pts (delPts 0 pts) ∧ SameCells R (R - 2) C f pts (delPts 0 pts) := by
  have hx : ∀ q ∈ pts, xf (R - 2) f (delAt 0 q.1) = xf R f q.1 := by
    intro q hq
    have := hp q hq
    rw [delAt0 (by omega)]
    unfold xf
    simp only [hf, ↓reduceIte]
    omega
  refine ⟨forall2_map_self (fun q hq => ?_), forall2_map_self (fun q hq => ?_)⟩
  · have h1 := hp q hq
    have hy : (delAt 0 q.1).2 = q.1.2 := by rw [delAt0 (by omega)]
    have hb : (delAt 0 q.1).1 < R - 2 := by rw [delAt0 (by omega)]; simp only; omega
    refine ⟨rfl, ⟨hy, Or.inl (hx q hq)⟩, (onPerim_lstrip h1.1).mp, h1.2.1, h1.2.2, hb,
      by rw [hy]; exact h1.2.2, ?_, ?_⟩
    · simp only [Frame.H]; split_ifs <;> omega
    · simp only [Frame.W]; split_ifs <;> omega
  · refine ⟨rfl, ?_⟩
    have := hp q hq
    rw [frame_to_eq, frame_to_eq, hx q hq]
    have hy : (delAt 0 q.1).2 = q.1.2 := by rw [delAt0 (by omega)]
    simp only [hy]

theorem passStrip_left {I : Inst} (hI : InDom I) (hw : 13 ≤ I.w)
    (hfree : ∀ k, k ≤ 3 → I.FreeLine k) (hP : Passes I) : Passes (I.deleteAt 0) := by
  have hC := hI.2.1
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := id hI
  have hi : ∀ e ∈ I.ends, 4 ≤ e.1 := by
    intro e he
    by_contra hc
    exact hfree e.1 (by omega) e he rfl
  have par := parityOk_deleteAt (I := I) (d := 0) (by omega) (hfree 0 (by omega))
    (hfree 1 (by omega))
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hi
  set pts : List Pt := [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] with hpts
  have hp : LIn I.w I.h pts := by
    intro q hq
    simp only [hpts, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨hi.1, b0⟩
    · exact ⟨hi.2.1, b1⟩
    · exact ⟨hi.2.2.1, b2⟩
    · exact ⟨hi.2.2.2, b3⟩
  have hd : delPts 0 pts = [(delAt 0 I.s0, 0), (delAt 0 I.t0, 0), (delAt 0 I.s1, 1),
      (delAt 0 I.t1, 1)] := rfl
  unfold Passes at hP ⊢
  simp only [Inst.deleteAt] at par ⊢
  rw [← hd] at par
  by_contra hf
  apply absurd hP
  rw [Bool.not_eq_false] at hf ⊢
  unfold fires3 at hf ⊢
  rw [← hd] at hf
  simp only [Bool.or_eq_true] at hf ⊢
  rcases hf with (((((hpar | ht1) | ht2) | hl1) | hl6) | hfr) | hea
  · left; left; left; left; left; left
    rw [par] at hpar; exact hpar
  · left; left; left; left; left; right
    exact t1_lstrip hw (by omega) hp ht1
  · left; left; left; left; right
    rw [t2_lstrip (by omega) (by omega) (by omega) (by omega)] at ht2
    exact ht2
  · left; left; left; right
    rw [l1Fires_iff] at hl1 ⊢
    exact l1_lstrip hp hl1
  · left; left; right
    exact l6_lstrip hw (by omega) hp hl6
  · left; right
    refine frames_any_strip (by omega) false
      (fun f hf => nearP_lstrip (fun q hq => (hp q hq).1) f hf)
      (fun f hf => far_lstrip hw hp f (by simpa using hf)) ?_ ?_ (by omega) hfr
    · intro q hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      have := hp q0 hq0
      rw [delAt0 (by omega)]; simp only; omega
    · intro q hq
      rw [hd] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp
  · right
    rw [effAlt3_lstrip hw (by omega) (fun q hq => ⟨(hp q hq).1, (hp q hq).2.1⟩)] at hea
    exact hea

/-- **Strips preserve passing.** -/
theorem passStrip {I : Inst} {d : ℕ} (hI : InDom I) (hw : 13 ≤ I.w) (h : StripClause I d)
    (hP : Passes I) : Passes (I.deleteAt d) := by
  rcases h with ⟨rfl, hf⟩ | ⟨hd, hf⟩
  · exact passStrip_left hI hw hf hP
  · exact passStrip_right hI hw hd hf hP

/-- What Theorem A still assumes: transposition symmetry of the catalogue, and the computation. -/
structure Facts'' : Prop where
  passT  : ∀ I, InDom I → Passes I → Passes I.transpose
  finite : ∀ I, InDom I → I.w ≤ 22 → I.h ≤ 22 → Passes I → ¬ Reducible I →
    MoveOK I ∨ Solvable I

/-- **Theorem A**, assuming only `Facts''`. -/
theorem theoremA'' (F : Facts'') (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h)
    (hP : Passes I) : Solvable I :=
  theoremA' ⟨fun _ _ hI hw h hP => passStrip hI hw h hP, F.passT, F.finite⟩ I hwf hw hh hP

end ZZN
