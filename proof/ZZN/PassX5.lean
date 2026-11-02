/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.PassX

@[expose] public section

/-!
# Window entries at band 5

With every endpoint at least 5 lines from the edge it approaches (`FarK 5`), the views of the two
instances agree on frame coordinates `≤ 4`. Every frame-based entry that fires on the smaller
instance fires on the larger one, except a window-8 C entry (`BigHit`) or a B entry with a cell
at coordinate 5 (`B5Hit`), which are reported (`frames_any_of5`). The frame coordinate along the
deleted axis does not increase (`winRel5_core`), so a fourth B endpoint outside the window stays
outside.
-/

namespace ZZN

open GridHam

/-- The window-6 C and D entries use coordinates `≤ 4` only. -/
theorem small6_le4 : ∀ e ∈ CORNER4 ++ CORNER4_ODD, small6 e = true →
    ∀ x ∈ e.1 ++ e.2, x.1 ≤ 4 ∧ x.2 ≤ 4 := by
  decide

/-- With band 5, a C/D match carries over unless it is a big (window-8) C entry. -/
theorem corner4_of5 {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (fun q q' => GoodInK 5 R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts')
    (hpar : (R' * C) % 2 = (R * C) % 2) (hb : ¬ BigHit R' C f pts')
    (hc : corner4 R' C f pts' = true) : corner4 R C f pts = true := by
  unfold corner4 at *
  have r0 := frameList_relK (C := C) h 0
  have r1 := frameList_relK (C := C) h 1
  simp only [List.any_eq_true] at hc ⊢
  obtain ⟨e, he, hm⟩ := hc
  have hsm : small6 e = true := by
    by_contra hs
    apply hb
    split_ifs at he with hp
    · exact ⟨by simpa using hp, e, he, by simpa using hs, hm⟩
    · exact (hs (corner4_odd_small e he)).elim
  have hall : e ∈ CORNER4 ++ CORNER4_ODD := by
    split_ifs at he
    · exact List.mem_append_left _ he
    · exact List.mem_append_right _ he
  rw [hpar] at he
  refine ⟨e, he, ?_⟩
  have hw : ∀ x ∈ e.1 ++ e.2, x.1 < 5 ∧ x.2 < 5 := by
    intro x hx
    have := small6_le4 e hall hsm x hx
    omega
  have w1 : ∀ x ∈ e.1, x.1 < 5 ∧ x.2 < 5 := fun x hx => hw x (List.mem_append_left _ hx)
  have w2 : ∀ x ∈ e.2, x.1 < 5 ∧ x.2 < 5 := fun x hx => hw x (List.mem_append_right _ hx)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hm ⊢
  rcases hm with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨sameSet_ofP w1 r0 a, sameSet_ofP w2 r1 b⟩
  · exact Or.inr ⟨sameSet_ofP w1 r1 a, sameSet_ofP w2 r0 b⟩

/-- B entries with every cell at coordinates `≤ 4`. -/
def small5B (e : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (e.1.1 ≤ 4) && decide (e.1.2 ≤ 4) && decide (e.2.1.1 ≤ 4) && decide (e.2.1.2 ≤ 4) &&
    decide (e.2.2.1 ≤ 4) && decide (e.2.2.2 ≤ 4)

/-- The match of one B entry, as in `boundaryOnly`. -/
def bMatch (R C : ℕ) (f : Frame) (pts : List Pt) (e : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  let fp := pts.map fun q => (f.to R C q.1, q.2)
  let H := f.H R C
  let W := f.W R C
  [0, 1].any fun A =>
    let isA := fun (x : ℕ × ℕ) => fp.any (fun q => q.2 == A && q.1 == x)
    match fp.find? (fun q => q.2 == 1 - A && q.1 == e.2.2) with
    | none => false
    | some _ =>
      isA e.1 && isA e.2.1 &&
      match fp.find? (fun q => q.2 == 1 - A && q.1 != e.2.2) with
      | none => false
      | some (fourth, _) =>
        let onPerim := fourth.1 == 0 || fourth.2 == 0 || fourth.1 == H - 1 || fourth.2 == W - 1
        let inWin := decide (fourth.1 < 6) && decide (fourth.2 < 6)
        onPerim && !inWin

theorem boundaryOnly_eq (R C : ℕ) (f : Frame) (pts : List Pt) :
    boundaryOnly R C f pts =
      (if R % 2 == 1 && C % 2 == 1 then BOUNDARY3_ODD else BOUNDARY3_EVEN).any (bMatch R C f pts) := by
  rfl

/-- A B match on an entry with a cell at coordinate 5. -/
def B5Hit (R C : ℕ) (f : Frame) (pts : List Pt) : Prop :=
  ∃ e ∈ (if R % 2 == 1 && C % 2 == 1 then BOUNDARY3_ODD else BOUNDARY3_EVEN),
    small5B e = false ∧ bMatch R C f pts e = true

/-- The endpoint relation at band 5, with the frame coordinate along the deleted axis not
increasing. -/
def WinRel5 (R R' C : ℕ) (f : Frame) (q q' : Pt) : Prop :=
  WinRelK 5 R R' C f q q' ∧ xf R' f q'.1 ≤ xf R f q.1

theorem frame_map_relG {R R' C : ℕ} {f : Frame} {Rel : Pt → Pt → Prop} {pts pts' : List Pt}
    (h : List.Forall₂ Rel pts pts') :
    List.Forall₂ (fun (u : (ℕ × ℕ) × ℕ) (u' : (ℕ × ℕ) × ℕ) =>
      ∃ q q', Rel q q' ∧ u = (f.to R C q.1, q.2) ∧ u' = (f.to R' C q'.1, q'.2))
      (pts.map fun q => (f.to R C q.1, q.2)) (pts'.map fun q => (f.to R' C q.1, q.2)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons q q' _ _ hq _ ih => exact List.Forall₂.cons ⟨q, q', hq, rfl, rfl⟩ ih

/-- **B at band 5**: a B match carries over unless the entry has a cell at coordinate 5. -/
theorem boundaryOnly_of5 {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (WinRel5 R R' C f) pts pts') (hpar : R' % 2 = R % 2)
    (hb : boundaryOnly R' C f pts' = true) : boundaryOnly R C f pts = true ∨ B5Hit R' C f pts' := by
  by_cases h5 : B5Hit R' C f pts'
  · exact Or.inr h5
  left
  have hk := h.imp (fun {_ _} hr => hr.1)
  unfold boundaryOnly at *
  simp only [List.any_eq_true] at hb ⊢
  obtain ⟨e, he, A, hA, hm⟩ := hb
  have hs : small5B e = true := by
    by_contra hs
    exact h5 ⟨e, he, by simpa using hs, List.any_eq_true.mpr ⟨A, hA, hm⟩⟩
  rw [hpar] at he
  refine ⟨e, he, A, hA, ?_⟩
  obtain ⟨a1, a2, b⟩ := e
  simp only [small5B, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩ := hs
  have key : ∀ q q', WinRelK 5 R R' C f q q' → ∀ x : ℕ × ℕ, x.1 ≤ 4 → x.2 ≤ 4 →
      ((f.to R' C q'.1 == x) = (f.to R C q.1 == x)) := by
    intro q q' hr x h1 h2
    have := to_eq_iffK (C := C) hr.2.1 (by omega : x.1 < 5) (by omega : x.2 < 5)
    obtain ⟨x1, x2⟩ := x
    by_cases hq : f.to R C q.1 = (x1, x2)
    · simp [hq, this.mpr hq]
    · have : ¬ f.to R' C q'.1 = (x1, x2) := fun e => hq (this.mp e)
      simp [hq, this]
  have hmap5 := frame_map_relG (R := R) (R' := R') (C := C) (f := f) h
  have isA_eq : ∀ x : ℕ × ℕ, x.1 ≤ 4 → x.2 ≤ 4 →
      ((pts'.map fun q => (f.to R' C q.1, q.2)).any fun u => u.2 == A && u.1 == x) =
      ((pts.map fun q => (f.to R C q.1, q.2)).any fun u => u.2 == A && u.1 == x) := by
    intro x h1 h2
    refine any_rel (fun u u' hr => ?_) hmap5
    obtain ⟨q, q', hr, rfl, rfl⟩ := hr
    simp only [hr.1.1, key q q' hr.1 x h1 h2]
  rcases find?_rel (P := fun u : (ℕ × ℕ) × ℕ => u.2 == 1 - A && u.1 == b)
      (P' := fun u => u.2 == 1 - A && u.1 == b) (fun u u' hr => by
        obtain ⟨q, q', hr, rfl, rfl⟩ := hr
        simp only [hr.1.1, key q q' hr.1 b (by omega) (by omega)]) hmap5 with
      ⟨h1, h2⟩ | ⟨u, u', h1, h2, -⟩
  · rw [h1] at hm; simp at hm
  rw [h2] at hm
  rw [h1]
  simp only [isA_eq a1 (by omega) (by omega), isA_eq a2 (by omega) (by omega)] at hm
  simp only [Bool.and_eq_true] at hm ⊢
  obtain ⟨⟨hA1, hA2⟩, hfour⟩ := hm
  refine ⟨⟨hA1, hA2⟩, ?_⟩
  rcases find?_rel (P := fun u : (ℕ × ℕ) × ℕ => u.2 == 1 - A && u.1 != b)
      (P' := fun u => u.2 == 1 - A && u.1 != b) (fun u u' hr => by
        obtain ⟨q, q', hr, rfl, rfl⟩ := hr
        simp only [hr.1.1, bne, key q q' hr.1 b (by omega) (by omega)]) hmap5 with
      ⟨g1, g2⟩ | ⟨v, v', g1, g2, ⟨q, q', hr, rfl, rfl⟩⟩
  · rw [g1] at hfour; simp at hfour
  rw [g2] at hfour
  rw [g1]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfour ⊢
  obtain ⟨hper, hwin⟩ := hfour
  obtain ⟨⟨-, hg, hperim, b1, b2, b3, b4, hH, hW⟩, hmono⟩ := hr
  refine ⟨(onPerim_frame f b1 b2).mpr (hperim ((onPerim_frame f b3 b4).mp hper)), ?_⟩
  -- outside the 6 × 6 window stays outside: the deleted axis does not grow
  obtain ⟨hy, -⟩ := hg
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hwin ⊢
  rw [frame_to_eq] at hwin ⊢
  rw [hy] at hwin
  split_ifs at hwin ⊢ <;> simp only at hwin ⊢ <;> omega

/-- **Band 5**: every frame-based entry carries over, except a big C entry or a B entry with a
cell at coordinate 5, which are reported. -/
theorem frames_any_of5 {R R' C : ℕ} {pts pts' : List Pt} (hR : R' ≤ R)
    (hrel : ∀ f, List.Forall₂ (WinRel5 R R' C f) pts pts')
    (hpar : R' % 2 = R % 2)
    (hE1 : ∀ f : Frame, f.tr = true → edgeClosure (makeView R' C f pts') = false)
    (h : frames.any (frameFires R' C pts') = true) :
    frames.any (frameFires R C pts) = true ∨ (∃ f, BigHit R' C f pts') ∨ (∃ f, B5Hit R' C f pts') := by
  simp only [List.any_eq_true] at h
  obtain ⟨f, hf, hfire⟩ := h
  by_cases hbig : BigHit R' C f pts'
  · exact Or.inr (Or.inl ⟨f, hbig⟩)
  by_cases hb5 : B5Hit R' C f pts'
  · exact Or.inr (Or.inr ⟨f, hb5⟩)
  left
  simp only [List.any_eq_true]
  refine ⟨f, hf, ?_⟩
  have hk : List.Forall₂ (WinRelK 5 R R' C f) pts pts' := (hrel f).imp (fun {_ _} hr => hr.1)
  have hs := sameCorner_of_winRel (le_refl 5) hk
  have hH : (makeView R' C f pts').H ≤ (makeView R C f pts).H := by
    simp only [makeView, Frame.H]; split_ifs <;> omega
  have hpar2 : (R' * C) % 2 = (R * C) % 2 := by
    rw [Nat.mul_mod, hpar, ← Nat.mul_mod]
  unfold frameFires at hfire ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfire ⊢
  rcases hfire with (((((h2 | h3) | h4) | h5) | hE) | hB) | ⟨⟨h10, h10'⟩, hC⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (testL2_of hs h2))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (testL3_of hs h3))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (testL4_of hs hH h4)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (testL5_of hs h5))))
  · cases htr : f.tr
    · exact Or.inl (Or.inl (Or.inr (edgeClosure_of_rows (by norm_num) htr (goodIn_of_winRel hk) hE)))
    · rw [hE1 f htr] at hE; exact absurd hE (by simp)
  · rcases boundaryOnly_of5 (hrel f) hpar hB with g | g
    · exact Or.inl (Or.inr g)
    · exact absurd g hb5
  · exact Or.inr ⟨⟨by omega, h10'⟩, corner4_of5 (goodIn_of_winRel hk) hpar2 hbig hC⟩

/-- The endpoint relation in every frame at band 5, for a compression core. -/
theorem winRel5_core {I : Inst} {d : ℕ} (hI : InDom I) (h : CompCore I d) (f : Frame) :
    List.Forall₂ (WinRel5 I.w (I.w - 2) I.h f)
      [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]
      [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)] := by
  have hk := winRel_core hI h f
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := hI
  have mono : ∀ e : ℕ × ℕ, e.1 < I.w → xf (I.w - 2) f (delAt d e) ≤ xf I.w f e := by
    intro e he
    obtain ⟨fr, fc, tr⟩ := f
    cases fr
    · simp only [xf, delAt, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega
    · simp only [xf, delAt, ↓reduceIte]
      split_ifs <;> omega
  simp only [List.forall₂_cons] at hk ⊢
  obtain ⟨r0, r1, r2, r3, -⟩ := hk
  exact ⟨⟨r0, mono _ b0.1⟩, ⟨r1, mono _ b1.1⟩, ⟨r2, mono _ b2.1⟩, ⟨r3, mono _ b3.1⟩,
    List.Forall₂.nil⟩

end ZZN
