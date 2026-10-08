-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Skeleton

/-!
# Toward `Facts.passX`: reductions preserve passing

`passX` says: if `RedX I d` and `I` passes, so does `I.deleteAt d`. Equivalently, every entry
that fires on `I.deleteAt d` fires on `I`. This file proves it entry by entry:

* P (parity): unchanged by deleting two lines (`parityOk_deleteAt`).
* Corner views: if every endpoint either keeps its distance to a frame's corner line or is at
  distance ≥ 8 in both instances (`GoodIn`), the 8 × 8 corner windows of that frame look the same
  (`view_at_eq`), and the corner tests L2–L5 carry over (`testL*_of`).
* The other frame-based entries: C and D, B, E1.
* For compressions: T2, L6, L1, T1.

R is in `PassXR.lean`; `PassXAssemble.lean` combines the entries (`passX_comp`).
-/

namespace ZZN

open GridHam

theorem sgn_delAt {d : ℕ} {v : Coord} (h : v.1 ≠ d) (h1 : v.1 ≠ d + 1) :
    sgn (delAt d v) = sgn v := by
  obtain ⟨x, y⟩ := v
  simp only at h h1
  unfold delAt sgn
  split_ifs with hx h2 h3 h3 <;> simp_all <;> omega

/-- Deleting two endpoint-free lines changes neither the endpoints' colors nor the parity of the
area, so the parity entry fires on one instance iff it fires on the other. -/
theorem parityOk_deleteAt {I : Inst} {d : ℕ} (hw : 2 ≤ I.w) (f0 : I.FreeLine d)
    (f1 : I.FreeLine (d + 1)) :
    parityOk (I.deleteAt d).w (I.deleteAt d).h
        [((I.deleteAt d).s0, 0), ((I.deleteAt d).t0, 0), ((I.deleteAt d).s1, 1),
          ((I.deleteAt d).t1, 1)] =
      parityOk I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] := by
  have g : ∀ e ∈ I.ends, sgn (delAt d e) = sgn e := fun e he => sgn_delAt (f0 e he) (f1 e he)
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g
  obtain ⟨g0, g1, g2, g3⟩ := g
  have harea : ((I.w - 2) * I.h) % 2 = (I.w * I.h) % 2 := by
    obtain ⟨k, hk⟩ : ∃ k, I.w = k + 2 := ⟨I.w - 2, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.add_mul, Nat.add_mul_mod_self_left]
  unfold parityOk
  simp only [Inst.deleteAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, g0, g1, g2,
    g3, harea]

/-! ### Corner views -/

/-- Distance of a cell from the frame's corner line, along the deleted axis. -/
def xf (R : ℕ) (f : Frame) (p : ℕ × ℕ) : ℕ := if f.fr then R - 1 - p.1 else p.1

theorem frame_to_eq (R C : ℕ) (f : Frame) (p : ℕ × ℕ) :
    f.to R C p = if f.tr then ((if f.fc then C - 1 - p.2 else p.2), xf R f p)
      else (xf R f p, (if f.fc then C - 1 - p.2 else p.2)) := by
  unfold Frame.to xf; rfl

/-- The endpoint keeps its corner distance, or is at distance ≥ 8 in both instances. -/
def GoodIn (R R' : ℕ) (f : Frame) (p p' : ℕ × ℕ) : Prop :=
  p'.2 = p.2 ∧ (xf R' f p' = xf R f p ∨ (8 ≤ xf R' f p' ∧ 8 ≤ xf R f p))

theorem to_eq_iff {R R' C : ℕ} {f : Frame} {p p' : ℕ × ℕ} (hg : GoodIn R R' f p p')
    {r c : ℕ} (hr : r ≤ 7) (hc : c ≤ 7) :
    (f.to R' C p' = (r, c)) ↔ (f.to R C p = (r, c)) := by
  obtain ⟨h2, h | ⟨h1, h1'⟩⟩ := hg
  · rw [frame_to_eq, frame_to_eq, h2, h]
  · rw [frame_to_eq, frame_to_eq, h2]
    split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- Corner windows agree. -/
theorem view_at_eq {R R' C : ℕ} {f : Frame} {r c : ℕ} (hr : r ≤ 7) (hc : c ≤ 7)
    {pts pts' : List Pt}
    (h : List.Forall₂ (fun q q' => GoodIn R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts') :
    (makeView R' C f pts').at r c = (makeView R C f pts).at r c := by
  induction h with
  | nil => rfl
  | @cons q q' qs qs' hq hrest ih =>
    obtain ⟨hg, hcol⟩ := hq
    simp only [makeView, View.at, List.map_cons, List.find?_cons] at ih ⊢
    have key := to_eq_iff (C := C) hg hr hc
    by_cases h : f.to R C q.1 = (r, c)
    · have h' : f.to R' C q'.1 = (r, c) := key.mpr h
      simp [h, h', hcol]
    · have h' : ¬ f.to R' C q'.1 = (r, c) := fun e => h (key.mp e)
      have e1 : (f.to R C q.1 == (r, c)) = false := by simpa using h
      have e2 : (f.to R' C q'.1 == (r, c)) = false := by simpa using h'
      rw [e1, e2]
      exact ih

/-! ### The corner tests carry over -/

/-- Two views agreeing on the 8 × 8 corner window. -/
def SameCorner (v v' : View) : Prop := ∀ r c, r ≤ 7 → c ≤ 7 → v'.at r c = v.at r c

theorem testL2_of {v v' : View} (hs : SameCorner v v') (h : testL2 v' = true) :
    testL2 v = true := by
  unfold testL2 View.empty at *
  simp only [List.all_cons, List.all_nil, Bool.and_true] at *
  rw [hs 0 1 (by omega) (by omega), hs 1 0 (by omega) (by omega),
    hs 0 0 (by omega) (by omega)] at h
  exact h

theorem testL3_of {v v' : View} (hs : SameCorner v v') (h : testL3 v' = true) :
    testL3 v = true := by
  unfold testL3 View.empty at *
  simp only [List.all_cons, List.all_nil, Bool.and_true] at *
  rw [hs 0 2 (by omega) (by omega), hs 1 1 (by omega) (by omega), hs 1 0 (by omega) (by omega),
    hs 0 0 (by omega) (by omega), hs 0 1 (by omega) (by omega)] at h
  exact h

theorem testL4_of {v v' : View} (hs : SameCorner v v') (hH : v'.H ≤ v.H)
    (h : testL4 v' = true) : testL4 v = true := by
  unfold testL4 View.empty at *
  simp only [List.all_cons, List.all_nil, Bool.and_true] at *
  rw [hs 0 0 (by omega) (by omega), hs 1 1 (by omega) (by omega), hs 0 2 (by omega) (by omega),
    hs 0 1 (by omega) (by omega), hs 1 0 (by omega) (by omega)] at h
  revert h
  cases v.at 0 0 with
  | none => simp
  | some a =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_imp]
    intro h1 h2 h3 h4 h5
    exact ⟨⟨⟨h1, h2⟩, by omega⟩, h4, h5⟩

theorem testL5_of {v v' : View} (hs : SameCorner v v') (h : testL5 v' = true) :
    testL5 v = true := by
  unfold testL5 View.empty at *
  simp only [List.all_cons, List.all_nil, Bool.and_true] at *
  rw [hs 0 0 (by omega) (by omega), hs 0 2 (by omega) (by omega), hs 2 0 (by omega) (by omega),
    hs 0 1 (by omega) (by omega), hs 1 0 (by omega) (by omega),
    hs 1 1 (by omega) (by omega)] at h
  exact h

/-! ### Compressions keep corner windows -/

/-- An endpoint is far from the corners across the deletion: below it, at least 11 lines from the
far edge; above it, at least at line 10. -/
def Far (d R : ℕ) (p : ℕ × ℕ) : Prop := (p.1 < d → p.1 + 11 ≤ R) ∧ (d + 2 ≤ p.1 → 10 ≤ p.1)

theorem goodIn_delAt {d R : ℕ} {p : ℕ × ℕ} (f : Frame) (hR : p.1 < R) (h0 : p.1 ≠ d)
    (h1 : p.1 ≠ d + 1) (hfar : Far d R p) : GoodIn R (R - 2) f p (delAt d p) := by
  obtain ⟨x, y⟩ := p
  simp only at hR h0 h1
  obtain ⟨fa, fb⟩ := hfar
  simp only at fa fb
  refine ⟨by unfold delAt; split_ifs <;> rfl, ?_⟩
  unfold xf delAt
  by_cases hx : x < d
  · have := fa hx
    cases f.fr <;> simp [hx]; omega
  · have := fb (by omega)
    cases f.fr <;> simp [hx] <;> omega

/-- In a compression or an interior compression, every endpoint is `Far`. -/
theorem far_of_redX {I : Inst} {d : ℕ} (hb : ∀ e ∈ I.ends, e.1 < I.w)
    (hr : (∃ lo, lo ≤ d ∧ d + 1 ≤ lo + 9 ∧ lo + 10 ≤ I.w ∧
            (∀ k, lo ≤ k → k ≤ lo + 9 → I.FreeLine k) ∧ EndBelow I lo ∧ EndAbove I (lo + 9)) ∨
          (8 ≤ d ∧ d + 10 ≤ I.w)) :
    ∀ e ∈ I.ends, Far d I.w e := by
  intro e he
  have heb := hb e he
  rcases hr with ⟨lo, hl, hh, hw, hf, -, -⟩ | ⟨h8, hw⟩
  · have notin : ¬ (lo ≤ e.1 ∧ e.1 ≤ lo + 9) := fun ⟨a, b⟩ => hf e.1 a b e he rfl
    exact ⟨fun h => by omega, fun h => by omega⟩
  · exact ⟨fun h => by omega, fun h => by omega⟩

/-! ### C and D (whole-configuration corner patterns) -/

/-- Moving the endpoints, as `I.deleteAt d` does. -/
def delPts (d : ℕ) (pts : List Pt) : List Pt := pts.map fun q => (delAt d q.1, q.2)

/-- Frame cells in the 8 × 8 corner window. -/
def InWin8 (x : ℕ × ℕ) : Prop := x.1 ≤ 7 ∧ x.2 ≤ 7

theorem corner4_lists_inWin :
    (∀ e ∈ CORNER4, ∀ x ∈ e.1 ++ e.2, x.1 ≤ 7 ∧ x.2 ≤ 7) ∧
    (∀ e ∈ CORNER4_ODD, ∀ x ∈ e.1 ++ e.2, x.1 ≤ 7 ∧ x.2 ≤ 7) := by
  decide

/-- If a window-only pattern `A` matches `L'`, it matches `L`, when the two lists agree wherever
`L'` is in the window. -/
theorem sameSet_of {A L L' : List (ℕ × ℕ)} (hA : ∀ x ∈ A, x.1 ≤ 7 ∧ x.2 ≤ 7)
    (h : List.Forall₂ (fun x x' => x'.1 ≤ 7 → x'.2 ≤ 7 → x = x') L L')
    (hs : sameSet A L' = true) : sameSet A L = true := by
  unfold sameSet at *
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hs ⊢
  refine ⟨hs.1.trans h.length_eq.symm, fun a ha => ?_⟩
  have hin := hs.2 a ha
  have hw := hA a ha
  clear hs
  induction h with
  | nil => simp at hin
  | @cons x x' l l' hx _ ih =>
    rcases List.mem_cons.mp hin with rfl | hin'
    · exact List.mem_cons.mpr (Or.inl (hx hw.1 hw.2).symm)
    · exact List.mem_cons_of_mem _ (ih hin')

theorem frameList_rel {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (fun q q' => GoodIn R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts') (col : ℕ) :
    List.Forall₂ (fun x x' => x'.1 ≤ 7 → x'.2 ≤ 7 → x = x')
      ((pts.filter (·.2 == col)).map (fun q => f.to R C q.1))
      ((pts'.filter (·.2 == col)).map (fun q => f.to R' C q.1)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons q q' qs qs' hq _ ih =>
    obtain ⟨hg, hc⟩ := hq
    by_cases hcol : q.2 = col
    · have hcol' : q'.2 = col := hc.trans hcol
      simp only [List.filter_cons, hcol, hcol', beq_self_eq_true, ↓reduceIte, List.map_cons]
      refine List.Forall₂.cons (fun h1 h2 => ?_) ih
      exact (to_eq_iff (C := C) hg h1 h2).mp rfl
    · have hcol' : ¬ q'.2 = col := fun e => hcol (hc ▸ e)
      have e1 : (q.2 == col) = false := by simpa using hcol
      have e2 : (q'.2 == col) = false := by simpa using hcol'
      simp only [List.filter_cons, e1, e2]
      exact ih

theorem corner4_of {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (fun q q' => GoodIn R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts')
    (hpar : (R' * C) % 2 = (R * C) % 2) (hc : corner4 R' C f pts' = true) :
    corner4 R C f pts = true := by
  unfold corner4 at *
  have r0 := frameList_rel (C := C) h 0
  have r1 := frameList_rel (C := C) h 1
  rw [hpar] at hc
  simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hc ⊢
  obtain ⟨e, he, hm⟩ := hc
  refine ⟨e, he, ?_⟩
  have hw : ∀ x ∈ e.1 ++ e.2, x.1 ≤ 7 ∧ x.2 ≤ 7 := by
    split_ifs at he
    · exact corner4_lists_inWin.1 e he
    · exact corner4_lists_inWin.2 e he
  have w1 : ∀ x ∈ e.1, x.1 ≤ 7 ∧ x.2 ≤ 7 := fun x hx => hw x (List.mem_append_left _ hx)
  have w2 : ∀ x ∈ e.2, x.1 ≤ 7 ∧ x.2 ≤ 7 := fun x hx => hw x (List.mem_append_right _ hx)
  rcases hm with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨sameSet_of w1 r0 a, sameSet_of w2 r1 b⟩
  · exact Or.inr ⟨sameSet_of w1 r1 a, sameSet_of w2 r0 b⟩

/-! ### B (boundary-only corner patterns) -/

/-- `find?` on related lists, with predicates that agree on related elements. -/
theorem find?_rel {α β : Type} {Rel : α → β → Prop} {P : α → Bool} {P' : β → Bool}
    (hP : ∀ a b, Rel a b → P' b = P a) {L : List α} {L' : List β} (h : List.Forall₂ Rel L L') :
    (L'.find? P' = none ∧ L.find? P = none) ∨
      (∃ a b, L.find? P = some a ∧ L'.find? P' = some b ∧ Rel a b) := by
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons a b l l' hab _ ih =>
    simp only [List.find?_cons]
    rw [hP a b hab]
    cases P a with
    | true => exact Or.inr ⟨a, b, rfl, rfl, hab⟩
    | false => simpa using ih

/-- `any` on related lists, with predicates that agree on related elements. -/
theorem any_rel {α β : Type} {Rel : α → β → Prop} {P : α → Bool} {P' : β → Bool}
    (hP : ∀ a b, Rel a b → P' b = P a) {L : List α} {L' : List β} (h : List.Forall₂ Rel L L') :
    L'.any P' = L.any P := by
  induction h with
  | nil => rfl
  | @cons a b l l' hab _ ih => simp only [List.any_cons, hP a b hab, ih]

/-- The cell lies on the grid's perimeter. -/
def OnPerim (R C : ℕ) (p : ℕ × ℕ) : Prop := p.1 = 0 ∨ p.1 = R - 1 ∨ p.2 = 0 ∨ p.2 = C - 1

theorem onPerim_frame {R C : ℕ} (f : Frame) {p : ℕ × ℕ} (hp : p.1 < R) (hq : p.2 < C) :
    ((f.to R C p).1 == 0 || (f.to R C p).2 == 0 || (f.to R C p).1 == f.H R C - 1 ||
      (f.to R C p).2 == f.W R C - 1) = true ↔ OnPerim R C p := by
  obtain ⟨x, y⟩ := p
  simp only at hp hq
  unfold OnPerim Frame.to Frame.H Frame.W
  cases f.fr <;> cases f.fc <;> cases f.tr <;> simp <;> omega

/-- The relation between an endpoint of `I` and its image in `I.deleteAt d`, seen in frame `f`. -/
def WinRel (R R' C : ℕ) (f : Frame) (q q' : Pt) : Prop :=
  q'.2 = q.2 ∧ GoodIn R R' f q.1 q'.1 ∧ (OnPerim R' C q'.1 → OnPerim R C q.1) ∧
    q.1.1 < R ∧ q.1.2 < C ∧ q'.1.1 < R' ∧ q'.1.2 < C ∧ f.H R' C ≤ f.H R C ∧ f.W R' C ≤ f.W R C

theorem boundary_lists_inWin :
    (∀ e ∈ BOUNDARY3_EVEN, e.1.1 ≤ 5 ∧ e.1.2 ≤ 5 ∧ e.2.1.1 ≤ 5 ∧ e.2.1.2 ≤ 5 ∧ e.2.2.1 ≤ 5 ∧
      e.2.2.2 ≤ 5) ∧
    (∀ e ∈ BOUNDARY3_ODD, e.1.1 ≤ 5 ∧ e.1.2 ≤ 5 ∧ e.2.1.1 ≤ 5 ∧ e.2.1.2 ≤ 5 ∧ e.2.2.1 ≤ 5 ∧
      e.2.2.2 ≤ 5) := by
  decide

theorem frame_map_rel {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (WinRel R R' C f) pts pts') :
    List.Forall₂ (fun (u : (ℕ × ℕ) × ℕ) (u' : (ℕ × ℕ) × ℕ) =>
      ∃ q q', WinRel R R' C f q q' ∧ u = (f.to R C q.1, q.2) ∧ u' = (f.to R' C q'.1, q'.2))
      (pts.map fun q => (f.to R C q.1, q.2)) (pts'.map fun q => (f.to R' C q.1, q.2)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons q q' _ _ hq _ ih => exact List.Forall₂.cons ⟨q, q', hq, rfl, rfl⟩ ih

theorem boundaryOnly_of {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (WinRel R R' C f) pts pts') (hpar : R' % 2 = R % 2)
    (hb : boundaryOnly R' C f pts' = true) : boundaryOnly R C f pts = true := by
  unfold boundaryOnly at *
  rw [hpar] at hb
  simp only [List.any_eq_true] at hb ⊢
  obtain ⟨e, he, A, hA, hm⟩ := hb
  refine ⟨e, he, A, hA, ?_⟩
  obtain ⟨a1, a2, b⟩ := e
  -- the pattern cells are in the 6 × 6 window
  have hw : a1.1 ≤ 5 ∧ a1.2 ≤ 5 ∧ a2.1 ≤ 5 ∧ a2.2 ≤ 5 ∧ b.1 ≤ 5 ∧ b.2 ≤ 5 := by
    split_ifs at he
    · exact boundary_lists_inWin.2 _ he
    · exact boundary_lists_inWin.1 _ he
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw
  -- frame coordinates in the window agree
  have key : ∀ q q', WinRel R R' C f q q' → ∀ x : ℕ × ℕ, x.1 ≤ 7 → x.2 ≤ 7 →
      ((f.to R' C q'.1 == x) = (f.to R C q.1 == x)) := by
    intro q q' hr x h1 h2
    have := to_eq_iff (C := C) hr.2.1 h1 h2
    obtain ⟨x1, x2⟩ := x
    by_cases hq : f.to R C q.1 = (x1, x2)
    · simp [hq, this.mpr hq]
    · have : ¬ f.to R' C q'.1 = (x1, x2) := fun e => hq (this.mp e)
      simp [hq, this]
  have hmap := frame_map_rel h
  have isA_eq : ∀ x : ℕ × ℕ, x.1 ≤ 7 → x.2 ≤ 7 →
      ((pts'.map fun q => (f.to R' C q.1, q.2)).any fun u => u.2 == A && u.1 == x) =
      ((pts.map fun q => (f.to R C q.1, q.2)).any fun u => u.2 == A && u.1 == x) := by
    intro x h1 h2
    refine any_rel (fun u u' hr => ?_) hmap
    obtain ⟨q, q', hr, rfl, rfl⟩ := hr
    simp only [hr.1, key q q' hr x h1 h2]
  rcases find?_rel (P := fun u : (ℕ × ℕ) × ℕ => u.2 == 1 - A && u.1 == b)
      (P' := fun u => u.2 == 1 - A && u.1 == b) (fun u u' hr => by
        obtain ⟨q, q', hr, rfl, rfl⟩ := hr
        simp only [hr.1, key q q' hr b (by omega) (by omega)]) hmap with ⟨h1, h2⟩ | ⟨u, u', h1, h2, -⟩
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
        simp only [hr.1, bne, key q q' hr b (by omega) (by omega)]) hmap with
      ⟨g1, g2⟩ | ⟨v, v', g1, g2, ⟨q, q', hr, rfl, rfl⟩⟩
  · rw [g1] at hfour; simp at hfour
  rw [g2] at hfour
  rw [g1]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfour ⊢
  obtain ⟨hper, hwin⟩ := hfour
  obtain ⟨-, hg, hperim, b1, b2, b3, b4, hH, hW⟩ := hr
  refine ⟨(onPerim_frame f b1 b2).mpr (hperim ((onPerim_frame f b3 b4).mp hper)), ?_⟩
  -- outside the 6 × 6 window stays outside
  obtain ⟨hy, hx⟩ := hg
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hwin ⊢
  rw [frame_to_eq] at hwin ⊢
  rw [hy] at hwin
  split_ifs at hwin ⊢ <;> simp only at hwin ⊢ <;> omega

/-! ### E1 (edge closure) -/

/-- In a frame along the deleted axis (not transposed), rows `≤ 7` of the view agree in every
column. -/
theorem to_eq_iff_rows {R R' C : ℕ} {f : Frame} (htr : f.tr = false) {p p' : ℕ × ℕ}
    (hg : GoodIn R R' f p p') {r c : ℕ} (hr : r ≤ 7) :
    (f.to R' C p' = (r, c)) ↔ (f.to R C p = (r, c)) := by
  obtain ⟨h2, h | ⟨h1, h1'⟩⟩ := hg
  · rw [frame_to_eq, frame_to_eq, h2, h]
  · rw [frame_to_eq, frame_to_eq, h2, htr]
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    omega

theorem view_at_eq_rows {R R' C : ℕ} {f : Frame} (htr : f.tr = false) {r : ℕ} (hr : r ≤ 7)
    (c : ℕ) {pts pts' : List Pt}
    (h : List.Forall₂ (fun q q' => GoodIn R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts') :
    (makeView R' C f pts').at r c = (makeView R C f pts).at r c := by
  induction h with
  | nil => rfl
  | @cons q q' qs qs' hq hrest ih =>
    obtain ⟨hg, hcol⟩ := hq
    simp only [makeView, View.at, List.map_cons, List.find?_cons] at ih ⊢
    have key := to_eq_iff_rows (C := C) htr hg (c := c) hr
    by_cases h : f.to R C q.1 = (r, c)
    · have h' : f.to R' C q'.1 = (r, c) := key.mpr h
      simp [h, h', hcol]
    · have h' : ¬ f.to R' C q'.1 = (r, c) := fun e => h (key.mp e)
      have e1 : (f.to R C q.1 == (r, c)) = false := by simpa using h
      have e2 : (f.to R' C q'.1 == (r, c)) = false := by simpa using h'
      rw [e1, e2]
      exact ih

/-- E1 in a frame along the deleted axis carries over (it only reads frame rows 0 and 1). -/
theorem edgeClosure_of_rows {R R' C : ℕ} {f : Frame} (htr : f.tr = false) {pts pts' : List Pt}
    (h : List.Forall₂ (fun q q' => GoodIn R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts')
    (he : edgeClosure (makeView R' C f pts') = true) :
    edgeClosure (makeView R C f pts) = true := by
  have hW : (makeView R' C f pts').W = (makeView R C f pts).W := by
    simp [makeView, Frame.W, htr]
  unfold edgeClosure at *
  rw [hW] at he
  simp only [view_at_eq_rows htr (by omega : (0 : ℕ) ≤ 7) _ h,
    view_at_eq_rows htr (by omega : (1 : ℕ) ≤ 7) _ h] at he
  exact he

/-- The view of four endpoints: what `at` can return. -/
theorem at_four {R C : ℕ} {f : Frame} {a b c e : ℕ × ℕ} {r k col : ℕ}
    (h : (makeView R C f [(a, 0), (b, 0), (c, 1), (e, 1)]).at r k = some col) :
    (f.to R C a = (r, k) ∧ col = 0) ∨ (f.to R C b = (r, k) ∧ col = 0) ∨
      (f.to R C c = (r, k) ∧ col = 1) ∨ (f.to R C e = (r, k) ∧ col = 1) := by
  simp only [makeView, View.at, List.map_cons, List.map_nil, List.find?_cons, List.find?_nil] at h
  by_cases ha : Frame.to R C f a = (r, k)
  · simp [ha] at h; exact Or.inl ⟨ha, h.symm⟩
  have ea : (Frame.to R C f a == (r, k)) = false := by simpa using ha
  rw [ea] at h
  by_cases hb : Frame.to R C f b = (r, k)
  · simp [hb] at h; exact Or.inr (Or.inl ⟨hb, h.symm⟩)
  have eb : (Frame.to R C f b == (r, k)) = false := by simpa using hb
  rw [eb] at h
  by_cases hc : Frame.to R C f c = (r, k)
  · simp [hc] at h; exact Or.inr (Or.inr (Or.inl ⟨hc, h.symm⟩))
  have ec : (Frame.to R C f c == (r, k)) = false := by simpa using hc
  rw [ec] at h
  by_cases he : Frame.to R C f e = (r, k)
  · simp [he] at h; exact Or.inr (Or.inr (Or.inr ⟨he, h.symm⟩))
  have ee : (Frame.to R C f e == (r, k)) = false := by simpa using he
  rw [ee] at h
  simp at h

/-- An endpoint of one color in the view is one of that color's two endpoints. -/
theorem at_four_col {R C : ℕ} {f : Frame} {a b c e : ℕ × ℕ} {r k col : ℕ}
    (h : (makeView R C f [(a, 0), (b, 0), (c, 1), (e, 1)]).at r k = some col) :
    (col = 0 ∧ (f.to R C a = (r, k) ∨ f.to R C b = (r, k))) ∨
      (col = 1 ∧ (f.to R C c = (r, k) ∨ f.to R C e = (r, k))) := by
  rcases at_four h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, Or.inl h1⟩
  · exact Or.inl ⟨h2, Or.inr h1⟩
  · exact Or.inr ⟨h2, Or.inl h1⟩
  · exact Or.inr ⟨h2, Or.inr h1⟩

/-- Column and row of a cell in a transposed frame. -/
theorem to_tr {R C : ℕ} {fr fc : Bool} {p : ℕ × ℕ} {r k : ℕ}
    (h : Frame.to R C ⟨fr, fc, true⟩ p = (r, k)) :
    (if fr then R - 1 - p.1 else p.1) = k ∧ (if fc then C - 1 - p.2 else p.2) = r := by
  simp only [Frame.to, ↓reduceIte, Prod.mk.injEq] at h
  exact ⟨h.2, h.1⟩

/-- The two endpoints of one color fill frame cells `(0, k)` and `(1, k+1)` (or the other two
pattern cells): their columns are `k` and `k+1`, in some order. -/
theorem pair_cols {R C : ℕ} {fr fc : Bool} {u v : ℕ × ℕ} {k₁ k₂ : ℕ}
    (h1 : Frame.to R C ⟨fr, fc, true⟩ u = (0, k₁) ∨ Frame.to R C ⟨fr, fc, true⟩ v = (0, k₁))
    (h2 : Frame.to R C ⟨fr, fc, true⟩ u = (1, k₂) ∨ Frame.to R C ⟨fr, fc, true⟩ v = (1, k₂)) :
    ((if fr then R - 1 - u.1 else u.1) = k₁ ∧ (if fr then R - 1 - v.1 else v.1) = k₂) ∨
    ((if fr then R - 1 - v.1 else v.1) = k₁ ∧ (if fr then R - 1 - u.1 else u.1) = k₂) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have a := to_tr h1; have b := to_tr h2; omega
  · exact Or.inl ⟨(to_tr h1).1, (to_tr h2).1⟩
  · exact Or.inr ⟨(to_tr h1).1, (to_tr h2).1⟩
  · have a := to_tr h1; have b := to_tr h2; omega

/-- In a transposed frame, E1 needs all four endpoints on four consecutive lines across the deleted
axis, each line holding one. It cannot fire if some free line has endpoints on both sides. -/
theorem edgeClosure_tr_false {R C : ℕ} {f : Frame} (htr : f.tr = true) {a b c e : ℕ × ℕ}
    (hb : a.1 < R ∧ b.1 < R ∧ c.1 < R ∧ e.1 < R) {L : ℕ}
    (hfree : a.1 ≠ L ∧ b.1 ≠ L ∧ c.1 ≠ L ∧ e.1 ≠ L)
    (hlo : a.1 < L ∨ b.1 < L ∨ c.1 < L ∨ e.1 < L) (hhi : L < a.1 ∨ L < b.1 ∨ L < c.1 ∨ L < e.1) :
    edgeClosure (makeView R C f [(a, 0), (b, 0), (c, 1), (e, 1)]) = false := by
  obtain ⟨fr, fc, tr⟩ := f
  simp only at htr
  subst htr
  by_contra hcon
  simp only [Bool.not_eq_false, edgeClosure, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq] at hcon
  obtain ⟨k, -, hk, hm⟩ := hcon
  revert hm
  cases h0 : (makeView R C ⟨fr, fc, true⟩ [(a, 0), (b, 0), (c, 1), (e, 1)]).at 0 k with
  | none => simp
  | some col =>
    intro hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨h1, h3⟩, h2⟩ := hm
    rcases at_four_col h0 with ⟨rfl, x0⟩ | ⟨rfl, x0⟩
    · rcases at_four_col h1 with ⟨-, x1⟩ | ⟨hc, -⟩
      swap; · omega
      rcases at_four_col h3 with ⟨hc, -⟩ | ⟨-, x3⟩
      · omega
      rcases at_four_col h2 with ⟨hc, -⟩ | ⟨-, x2⟩
      · omega
      have p1 := pair_cols x0 x1
      have p2 := pair_cols x3 x2
      cases fr <;> simp only [Bool.false_eq_true, ↓reduceIte] at p1 p2 <;> omega
    · rcases at_four_col h1 with ⟨hc, -⟩ | ⟨-, x1⟩
      · omega
      rcases at_four_col h3 with ⟨-, x3⟩ | ⟨hc, -⟩
      swap; · omega
      rcases at_four_col h2 with ⟨-, x2⟩ | ⟨hc, -⟩
      swap; · omega
      have p1 := pair_cols x0 x1
      have p2 := pair_cols x3 x2
      cases fr <;> simp only [Bool.false_eq_true, ↓reduceIte] at p1 p2 <;> omega

/-! ### All frame-based entries -/

theorem goodIn_of_winRel {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (WinRel R R' C f) pts pts') :
    List.Forall₂ (fun q q' => GoodIn R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts' :=
  h.imp (fun {_ _} hr => ⟨hr.2.1, hr.1⟩)

theorem sameCorner_of_winRel {R R' C : ℕ} {f : Frame} {pts pts' : List Pt}
    (h : List.Forall₂ (WinRel R R' C f) pts pts') :
    SameCorner (makeView R C f pts) (makeView R' C f pts') :=
  fun _ _ hr hc => view_at_eq hr hc (goodIn_of_winRel h)

/-- Every frame-based entry that fires on the smaller instance fires on the larger one, provided
the endpoints are related in every frame (`WinRel`) and E1 cannot fire in transposed frames. -/
theorem frames_any_of {R R' C : ℕ} {pts pts' : List Pt} (hR : R' ≤ R)
    (hrel : ∀ f, List.Forall₂ (WinRel R R' C f) pts pts')
    (hpar : R' % 2 = R % 2)
    (hE1 : ∀ f : Frame, f.tr = true → edgeClosure (makeView R' C f pts') = false)
    (h : frames.any (frameFires R' C pts') = true) : frames.any (frameFires R C pts) = true := by
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨f, hf, hfire⟩ := h
  refine ⟨f, hf, ?_⟩
  have hs := sameCorner_of_winRel (hrel f)
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
    · exact Or.inl (Or.inl (Or.inr (edgeClosure_of_rows htr (goodIn_of_winRel (hrel f)) hE)))
    · rw [hE1 f htr] at hE; exact absurd hE (by simp)
  · exact Or.inl (Or.inr (boundaryOnly_of (hrel f) hpar hB))
  · exact Or.inr ⟨⟨by omega, h10'⟩, corner4_of (goodIn_of_winRel (hrel f)) hpar2 hC⟩

/-! ### Compressions: the setup -/

/-- The compression and interior-compression clauses of `RedX`. -/
def CompClause (I : Inst) (d : ℕ) : Prop :=
  (∃ lo, lo ≤ d ∧ d + 1 ≤ lo + 9 ∧ lo + 10 ≤ I.w ∧ (∀ k, lo ≤ k → k ≤ lo + 9 → I.FreeLine k) ∧
      EndBelow I lo ∧ EndAbove I (lo + 9)) ∨
  (8 ≤ d ∧ d + 10 ≤ I.w ∧ I.FreeLine d ∧ I.FreeLine (d + 1) ∧
      ((1 ≤ d ∧ I.FreeLine (d - 1)) ∨ I.FreeLine (d + 2)) ∧ EndBelow I d ∧ EndAbove I (d + 1))

theorem compClause_free {I : Inst} {d : ℕ} (h : CompClause I d) :
    I.FreeLine d ∧ I.FreeLine (d + 1) ∧ d + 2 ≤ I.w := by
  rcases h with ⟨lo, hl, hh, hw, hf, -, -⟩ | ⟨-, hw, f0, f1, -, -, -⟩
  · exact ⟨hf d hl (by omega), hf (d + 1) (by omega) hh, by omega⟩
  · exact ⟨f0, f1, by omega⟩

/-- A free line other than `d, d+1`, with endpoints on both sides of it and of the deletion. -/
theorem compClause_line {I : Inst} {d : ℕ} (h : CompClause I d) :
    ∃ k, I.FreeLine k ∧ k ≠ d ∧ k ≠ d + 1 ∧
      (∃ e ∈ I.ends, e.1 < k ∧ e.1 < d) ∧ (∃ e ∈ I.ends, k < e.1 ∧ d + 1 < e.1) := by
  rcases h with ⟨lo, hl, hh, hw, hf, ⟨e1, he1, h1⟩, ⟨e2, he2, h2⟩⟩ |
      ⟨h8, hw, f0, f1, (⟨hd, fm⟩ | fp), ⟨e1, he1, h1⟩, ⟨e2, he2, h2⟩⟩
  · by_cases hd : lo < d
    · exact ⟨lo, hf lo le_rfl (by omega), by omega, by omega, ⟨e1, he1, h1, by omega⟩,
        ⟨e2, he2, by omega, by omega⟩⟩
    · exact ⟨lo + 9, hf (lo + 9) (by omega) le_rfl, by omega, by omega, ⟨e1, he1, by omega, by omega⟩,
        ⟨e2, he2, h2, by omega⟩⟩
  · have : e1.1 ≠ d - 1 := fm e1 he1
    exact ⟨d - 1, fm, by omega, by omega, ⟨e1, he1, by omega, h1⟩, ⟨e2, he2, by omega, h2⟩⟩
  · have : e2.1 ≠ d + 2 := fp e2 he2
    exact ⟨d + 2, fp, by omega, by omega, ⟨e1, he1, by omega, h1⟩, ⟨e2, he2, by omega, by omega⟩⟩

theorem far_of_compClause {I : Inst} {d : ℕ} (hb : ∀ e ∈ I.ends, e.1 < I.w)
    (h : CompClause I d) : ∀ e ∈ I.ends, Far d I.w e := by
  apply far_of_redX hb
  rcases h with ⟨lo, hl, hh, hw, hf, hb1, ha1⟩ | ⟨h8, hw, -⟩
  · exact Or.inl ⟨lo, hl, hh, hw, hf, hb1, ha1⟩
  · exact Or.inr ⟨h8, hw⟩

theorem onPerim_delAt {d R C : ℕ} {p : ℕ × ℕ} (h0 : p.1 ≠ d) (h1 : p.1 ≠ d + 1)
    (hfar : Far d R p) (h : OnPerim (R - 2) C (delAt d p)) : OnPerim R C p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨fa, fb⟩ := hfar
  simp only at h0 h1 fa fb
  unfold OnPerim delAt at *
  split_ifs at h with hx
  · have := fa hx; simp only at h ⊢; omega
  · have := fb (by omega); simp only at h ⊢; omega

/-- The endpoint relation in every frame, for a compression. -/
theorem winRel_comp {I : Inst} {d : ℕ} (hI : InDom I) (h : CompClause I d) (f : Frame) :
    List.Forall₂ (WinRel I.w (I.w - 2) I.h f)
      [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)]
      [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)] := by
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := hI
  have hb : ∀ e ∈ I.ends, e.1 < I.w ∧ e.2 < I.h := by
    intro e he
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact b0
    · exact b1
    · exact b2
    · exact b3
  obtain ⟨f0, f1, hdw⟩ := compClause_free h
  have far := far_of_compClause (fun e he => (hb e he).1) h
  have one : ∀ e ∈ I.ends, ∀ col, WinRel I.w (I.w - 2) I.h f (e, col) (delAt d e, col) := by
    intro e he col
    have he0 := f0 e he
    have he1 := f1 e he
    obtain ⟨hx, hy⟩ := hb e he
    refine ⟨rfl, goodIn_delAt f hx he0 he1 (far e he), onPerim_delAt he0 he1 (far e he), hx, hy,
      ?_, ?_, ?_, ?_⟩
    · unfold delAt; split_ifs <;> simp <;> omega
    · unfold delAt; split_ifs <;> simpa using hy
    · simp only [Frame.H]; split_ifs <;> omega
    · simp only [Frame.W]; split_ifs <;> omega
  exact List.Forall₂.cons (one _ (by simp [Inst.ends]) 0) (List.Forall₂.cons
    (one _ (by simp [Inst.ends]) 0) (List.Forall₂.cons (one _ (by simp [Inst.ends]) 1)
    (List.Forall₂.cons (one _ (by simp [Inst.ends]) 1) List.Forall₂.nil)))

/-- After a compression, the deleted instance has a free line with endpoints on both sides. -/
theorem comp_line_after {I : Inst} {d : ℕ} (_hI : InDom I) (h : CompClause I d) :
    ∃ L, (∀ e ∈ I.ends, (delAt d e).1 ≠ L) ∧ (∃ e ∈ I.ends, (delAt d e).1 < L) ∧
      (∃ e ∈ I.ends, L < (delAt d e).1) := by
  obtain ⟨k, hk, hkd, hkd1, ⟨e1, he1, a1, a2⟩, ⟨e2, he2, b1, b2⟩⟩ := compClause_line h
  obtain ⟨f0, f1, -⟩ := compClause_free h
  refine ⟨if k < d then k else k - 2, ?_, ⟨e1, he1, ?_⟩, ⟨e2, he2, ?_⟩⟩
  · intro e he
    have := hk e he; have := f0 e he; have := f1 e he
    unfold delAt; split_ifs <;> (try simp only) <;> omega
  · unfold delAt; split_ifs <;> omega
  · unfold delAt; split_ifs <;> (try simp only) <;> omega

theorem e1_comp {I : Inst} {d : ℕ} (hI : InDom I) (h : CompClause I d) (f : Frame)
    (htr : f.tr = true) :
    edgeClosure (makeView (I.w - 2) I.h f
      [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)]) = false := by
  obtain ⟨L, hfree, ⟨e1, he1, hl⟩, ⟨e2, he2, hh⟩⟩ := comp_line_after hI h
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := hI
  obtain ⟨f0, f1, hdw⟩ := compClause_free h
  have inb : ∀ e ∈ I.ends, e.1 < I.w → (delAt d e).1 < I.w - 2 := by
    intro e he hx
    have := f0 e he; have := f1 e he
    unfold delAt; split_ifs <;> simp <;> omega
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hfree inb
  refine edgeClosure_tr_false htr ⟨inb.1 b0.1, inb.2.1 b1.1, inb.2.2.1 b2.1, inb.2.2.2 b3.1⟩
    hfree ?_ ?_
  · simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he1
    rcases he1 with rfl | rfl | rfl | rfl <;> simp [hl]
  · simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he2
    rcases he2 with rfl | rfl | rfl | rfl <;> simp [hh]

/-! ### T2 -/

/-- T2 needs all four endpoints within two adjacent lines. -/
theorem t2Fires_close {a b c e : ℕ × ℕ} (h : t2Fires [a, b, c, e] = true) :
    ∀ x ∈ [a.1, b.1, c.1, e.1], ∀ y ∈ [a.1, b.1, c.1, e.1], x ≤ y + 1 := by
  unfold t2Fires at h
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.headD_cons,
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have m1 := Nat.le_max_left (max (max (max 0 a.1) b.1) c.1) e.1
  have m2 := Nat.le_max_right (max (max (max 0 a.1) b.1) c.1) e.1
  have m3 := Nat.le_max_right (max (max 0 a.1) b.1) c.1
  have m4 := Nat.le_max_right (max 0 a.1) b.1
  have m5 := Nat.le_max_right 0 a.1
  have m6 := Nat.le_max_left (max 0 a.1) b.1
  have m7 := Nat.le_max_left (max (max 0 a.1) b.1) c.1
  have n1 := Nat.min_le_left (min (min (min a.1 a.1) b.1) c.1) e.1
  have n2 := Nat.min_le_right (min (min (min a.1 a.1) b.1) c.1) e.1
  have n3 := Nat.min_le_right (min (min a.1 a.1) b.1) c.1
  have n4 := Nat.min_le_right (min a.1 a.1) b.1
  have n5 := Nat.min_le_left a.1 a.1
  have n6 := Nat.min_le_left (min a.1 a.1) b.1
  have n7 := Nat.min_le_left (min (min a.1 a.1) b.1) c.1
  rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl) <;> omega

/-- After a compression, T2 cannot fire. -/
theorem t2_comp {I : Inst} {d : ℕ} (hI : InDom I) (h : CompClause I d) :
    t2Fires [delAt d I.s0, delAt d I.t0, delAt d I.s1, delAt d I.t1] = false := by
  obtain ⟨L, hfree, ⟨e1, he1, hl⟩, ⟨e2, he2, hh⟩⟩ := comp_line_after hI h
  by_contra hc
  have := t2Fires_close (Bool.not_eq_false _ ▸ hc)
  have m1 : (delAt d e1).1 ∈ [(delAt d I.s0).1, (delAt d I.t0).1, (delAt d I.s1).1,
      (delAt d I.t1).1] := by
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he1
    rcases he1 with rfl | rfl | rfl | rfl <;> simp
  have m2 : (delAt d e2).1 ∈ [(delAt d I.s0).1, (delAt d I.t0).1, (delAt d I.s1).1,
      (delAt d I.t1).1] := by
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he2
    rcases he2 with rfl | rfl | rfl | rfl <;> simp
  have := this _ m2 _ m1
  omega

/-! ### L6 -/

/-- The closure at one corner: the two neighbors of an empty corner cell hold one color's
endpoints. -/
def closureAt (pts : List Pt) (n1 n2 cor : ℕ × ℕ) : Option ℕ :=
  match pts.find? (·.1 == n1), pts.find? (·.1 == n2) with
  | some a, some b => if a.2 == b.2 && !(pts.any (·.1 == cor)) then some a.2 else none
  | _, _ => none

def l6List (R C : ℕ) (pts : List Pt) : List ℕ :=
  [closureAt pts (0, 1) (1, 0) (0, 0), closureAt pts (0, C - 2) (1, C - 1) (0, C - 1),
    closureAt pts (R - 1, 1) (R - 2, 0) (R - 1, 0),
    closureAt pts (R - 1, C - 2) (R - 2, C - 1) (R - 1, C - 1)].filterMap id

theorem l6Closures_eq {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) (pts : List Pt) :
    l6Closures R C pts = l6List R C pts := by
  have a1 : ((R : ℤ) - 1).toNat = R - 1 := by omega
  have a2 : ((R : ℤ) - 1 + -1).toNat = R - 2 := by omega
  have b1 : ((C : ℤ) - 1).toNat = C - 1 := by omega
  have b2 : ((C : ℤ) - 1 + -1).toNat = C - 2 := by omega
  unfold l6Closures l6List closureAt
  simp only [List.filterMap_cons, List.filterMap_nil, a1, a2, b1, b2]
  norm_num
  rfl

/-- Per-endpoint behaviour near the two edges across the deleted axis. -/
theorem delAt_near_low {d R : ℕ} {q n : ℕ × ℕ} (h0 : q.1 ≠ d) (h1 : q.1 ≠ d + 1) (hfar : Far d R q)
    (hn : n.1 ≤ 1) : (delAt d q = n) ↔ (q = n) := by
  obtain ⟨x, y⟩ := q
  obtain ⟨a, b⟩ := n
  obtain ⟨fa, fb⟩ := hfar
  simp only at h0 h1 fa fb hn
  unfold delAt
  split_ifs with hx <;> simp only [Prod.mk.injEq]
  have := fb (by omega)
  omega

theorem delAt_near_high {d R : ℕ} {q n : ℕ × ℕ} (h0 : q.1 ≠ d) (h1 : q.1 ≠ d + 1)
    (hfar : Far d R q) (hq : q.1 < R) (hn : R ≤ n.1 + 2) (hn' : n.1 < R) (hR : 13 ≤ R) :
    (delAt d q = (n.1 - 2, n.2)) ↔ (q = n) := by
  obtain ⟨x, y⟩ := q
  obtain ⟨a, b⟩ := n
  obtain ⟨fa, fb⟩ := hfar
  simp only at h0 h1 fa fb hn hn' hq
  unfold delAt
  split_ifs with hx
  · have := fa hx; simp only [Prod.mk.injEq]; omega
  · simp only [Prod.mk.injEq]; omega

theorem closureAt_rel {pts pts' : List Pt} {n1 n2 cor n1' n2' cor' : ℕ × ℕ}
    (h : List.Forall₂ (fun q q' => q'.2 = q.2 ∧ (q'.1 = n1' ↔ q.1 = n1) ∧ (q'.1 = n2' ↔ q.1 = n2) ∧
      (q'.1 = cor' ↔ q.1 = cor)) pts pts') :
    closureAt pts' n1' n2' cor' = closureAt pts n1 n2 cor := by
  have k1 := find?_rel (P := fun q : Pt => q.1 == n1) (P' := fun q => q.1 == n1')
    (fun a b hr => Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact hr.2.1)) h
  have k2 := find?_rel (P := fun q : Pt => q.1 == n2) (P' := fun q => q.1 == n2')
    (fun a b hr => Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact hr.2.2.1)) h
  have k3 := any_rel (P := fun q : Pt => q.1 == cor) (P' := fun q => q.1 == cor')
    (fun a b hr => Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact hr.2.2.2)) h
  unfold closureAt
  rw [k3]
  rcases k1 with ⟨e1, e1'⟩ | ⟨a, a', e1, e1', ha⟩ <;>
    rcases k2 with ⟨e2, e2'⟩ | ⟨b, b', e2, e2', hb⟩
  · rw [e1, e1']
  · rw [e1, e1']
  · rw [e1, e1', e2, e2']
  · rw [e1, e1', e2, e2']; simp only [ha.1, hb.1]

/-- After a compression, the corner closures are the same, so L6 carries over. -/
theorem l6_comp {I : Inst} {d : ℕ} (hI : InDom I) (h : CompClause I d) (hR : 13 ≤ I.w)
    (hf : l6Fires (I.w - 2) I.h
      [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)] = true) :
    l6Fires I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] = true := by
  obtain ⟨hw, hh, b0, b1, b2, b3, -⟩ := hI
  obtain ⟨f0, f1, -⟩ := compClause_free h
  have far := far_of_compClause (fun e he => by
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact b0.1
    · exact b1.1
    · exact b2.1
    · exact b3.1) h
  have rel : ∀ (n1 n2 cor : ℕ × ℕ), (n1.1 ≤ 1 ∨ (I.w ≤ n1.1 + 2 ∧ n1.1 < I.w)) →
      (n2.1 ≤ 1 ∨ (I.w ≤ n2.1 + 2 ∧ n2.1 < I.w)) → (cor.1 ≤ 1 ∨ (I.w ≤ cor.1 + 2 ∧ cor.1 < I.w)) →
      let g := fun n : ℕ × ℕ => if n.1 ≤ 1 then n else (n.1 - 2, n.2)
      closureAt [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)]
          (g n1) (g n2) (g cor) =
        closureAt [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] n1 n2 cor := by
    intro n1 n2 cor c1 c2 c3 g
    apply closureAt_rel
    have one : ∀ e ∈ I.ends, e.1 < I.w → ∀ n : ℕ × ℕ, (n.1 ≤ 1 ∨ (I.w ≤ n.1 + 2 ∧ n.1 < I.w)) →
        (delAt d e = g n ↔ e = n) := by
      intro e he hx n hn
      simp only [g]
      split_ifs with hn1
      · exact delAt_near_low (f0 e he) (f1 e he) (far e he) hn1
      · exact delAt_near_high (f0 e he) (f1 e he) (far e he) hx (by omega) (by omega) hR
    have m : ∀ e ∈ I.ends, ∀ col, (fun q q' : Pt => q'.2 = q.2 ∧ (q'.1 = g n1 ↔ q.1 = n1) ∧
        (q'.1 = g n2 ↔ q.1 = n2) ∧ (q'.1 = g cor ↔ q.1 = cor)) (e, col) (delAt d e, col) := by
      intro e he col
      have hx : e.1 < I.w := by
        simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact b0.1
        · exact b1.1
        · exact b2.1
        · exact b3.1
      exact ⟨rfl, one e he hx n1 c1, one e he hx n2 c2, one e he hx cor c3⟩
    exact List.Forall₂.cons (m _ (by simp [Inst.ends]) 0) (List.Forall₂.cons
      (m _ (by simp [Inst.ends]) 0) (List.Forall₂.cons (m _ (by simp [Inst.ends]) 1)
      (List.Forall₂.cons (m _ (by simp [Inst.ends]) 1) List.Forall₂.nil)))
  unfold l6Fires at hf ⊢
  rw [l6Closures_eq (by omega) (by omega)] at hf
  rw [l6Closures_eq (by omega) (by omega)]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
  obtain ⟨⟨h0, h1⟩, h6⟩ := hf
  have e1 := rel (0, 1) (1, 0) (0, 0) (by simp) (by simp) (by simp)
  have e2 := rel (0, I.h - 2) (1, I.h - 1) (0, I.h - 1) (by simp) (by simp) (by simp)
  have e3 := rel (I.w - 1, 1) (I.w - 2, 0) (I.w - 1, 0) (Or.inr ⟨by simp; omega, by simp; omega⟩)
    (Or.inr ⟨by simp; omega, by simp; omega⟩) (Or.inr ⟨by simp; omega, by simp; omega⟩)
  have e4 := rel (I.w - 1, I.h - 2) (I.w - 2, I.h - 1) (I.w - 1, I.h - 1)
    (Or.inr ⟨by simp; omega, by simp; omega⟩) (Or.inr ⟨by simp; omega, by simp; omega⟩)
    (Or.inr ⟨by simp; omega, by simp; omega⟩)
  simp only [show ¬ (I.w - 1 ≤ 1) by omega, show ¬ (I.w - 2 ≤ 1) by omega, ↓reduceIte,
    show (0 : ℕ) ≤ 1 by omega, show (1 : ℕ) ≤ 1 by omega] at e1 e2 e3 e4
  have w1 : I.w - 1 - 2 = I.w - 2 - 1 := by omega
  have w2 : I.w - 2 - 2 = I.w - 2 - 2 := rfl
  unfold l6List at h0 h1 ⊢
  rw [w1] at e3 e4
  rw [e1, e2, e3, e4] at h0 h1
  exact ⟨⟨h0, h1⟩, Nat.lt_of_lt_of_le h6 (Nat.mul_le_mul_right _ (by omega))⟩

/-! ### L1 -/

/-- What `l1Fires` computes: some endpoint has every in-grid neighbor occupied by an endpoint of
the other color. -/
def L1Prop (R C : ℕ) (pts : List Pt) : Prop :=
  ∃ q ∈ pts, ∀ n : ℕ × ℕ, n.1 < R → n.2 < C → Adjacent q.1 n → ∃ e ∈ pts, e.1 = n ∧ e.2 ≠ q.2

theorem nb_all_iff (R C : ℕ) (p : ℕ × ℕ) (P : ℕ × ℕ → Bool) :
    ((([((p.1 : ℤ) - 1, (p.2 : ℤ)), ((p.1 : ℤ) + 1, (p.2 : ℤ)), ((p.1 : ℤ), (p.2 : ℤ) - 1),
        ((p.1 : ℤ), (p.2 : ℤ) + 1)] : List (ℤ × ℤ)).filter fun q => decide (0 ≤ q.1) &&
        decide (q.1 < (R : ℤ)) && decide (0 ≤ q.2) && decide (q.2 < (C : ℤ))).all
      fun q => P (q.1.toNat, q.2.toNat)) = true ↔
    ∀ n : ℕ × ℕ, n.1 < R → n.2 < C → Adjacent p n → P n = true := by
  obtain ⟨x, y⟩ := p
  constructor
  · intro h n h1 h2 hadj
    simp only [List.filter_cons, List.filter_nil, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨a, b⟩ := n
    unfold Adjacent at hadj
    simp only at hadj h1 h2
    rcases hadj with ⟨rfl, hb | hb⟩ | ⟨rfl, ha | ha⟩
    · subst hb
      split_ifs at h <;> simp_all <;> omega
    · subst hb
      split_ifs at h <;> simp_all
    · subst ha
      split_ifs at h <;> simp_all <;> omega
    · subst ha
      split_ifs at h <;> simp_all
  · intro h
    rw [List.all_eq_true]
    intro q hq
    rw [List.mem_filter] at hq
    obtain ⟨hmem, hb⟩ := hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    apply h
    · simp only; omega
    · simp only; omega
    · unfold Adjacent
      rcases hmem with rfl | rfl | rfl | rfl <;> simp only <;> omega

theorem l1Fires_iff (R C : ℕ) (pts : List Pt) : l1Fires R C pts = true ↔ L1Prop R C pts := by
  unfold l1Fires L1Prop
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨p, col⟩, hq, h⟩
    refine ⟨(p, col), hq, fun n h1 h2 hadj => ?_⟩
    have := (nb_all_iff R C p (fun n => pts.any fun pc' => pc'.1 == n && pc'.2 != col)).mp h n h1 h2
      hadj
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    obtain ⟨e, he, h3, h4⟩ := this
    exact ⟨e, he, h3, h4⟩
  · rintro ⟨⟨p, col⟩, hq, h⟩
    refine ⟨(p, col), hq, ?_⟩
    refine (nb_all_iff R C p (fun n => pts.any fun pc' => pc'.1 == n && pc'.2 != col)).mpr ?_
    intro n h1 h2 hadj
    obtain ⟨e, he, h3, h4⟩ := h n h1 h2 hadj
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨e, he, h3, h4⟩

/-- Next to the seam, the line across is free. -/
theorem seam_free {I : Inst} {d : ℕ} (h : CompClause I d) {e : Coord} (he : e ∈ I.ends) :
    (e.1 + 1 = d → I.FreeLine (d + 2)) ∧ (e.1 = d + 2 → 1 ≤ d ∧ I.FreeLine (d - 1)) := by
  rcases h with ⟨lo, hl, hh, hw, hf, -, -⟩ | ⟨h8, hw, f0, f1, (⟨hd, fm⟩ | fp), -, -⟩
  · have nin : ¬ (lo ≤ e.1 ∧ e.1 ≤ lo + 9) := fun ⟨a, b⟩ => hf e.1 a b e he rfl
    exact ⟨fun h1 => hf (d + 2) (by omega) (by omega),
      fun h2 => ⟨by omega, hf (d - 1) (by omega) (by omega)⟩⟩
  · exact ⟨fun h1 => (fm e he (by omega)).elim, fun h2 => ⟨hd, fm⟩⟩
  · exact ⟨fun _ => fp, fun h2 => (fp e he (by omega)).elim⟩

theorem delAt_adj {d : ℕ} {u v : Coord} (hu : u.1 ≠ d) (hu1 : u.1 ≠ d + 1) (hv : v.1 ≠ d)
    (hv1 : v.1 ≠ d + 1) (hadj : Adjacent u v) (hside : (u.1 < d ↔ v.1 < d)) :
    Adjacent (delAt d u) (delAt d v) := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  unfold Adjacent at hadj ⊢
  unfold delAt
  simp only at *
  split_ifs <;> simp only <;> omega

/-- After a compression, L1 carries over. -/
theorem l1_comp {I : Inst} {d : ℕ} (hI : InDom I) (h : CompClause I d)
    (hf : L1Prop (I.w - 2) I.h
      [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)]) :
    L1Prop I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] := by
  obtain ⟨-, -, b0, b1, b2, b3, -⟩ := hI
  obtain ⟨f0, f1, hdw⟩ := compClause_free h
  have hb : ∀ e ∈ I.ends, e.1 < I.w ∧ e.2 < I.h := by
    intro e he
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact b0
    · exact b1
    · exact b2
    · exact b3
  -- the endpoint list as images
  have hmem : ∀ q' ∈ [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)],
      ∃ e ∈ I.ends, ∃ col, q' = (delAt d e, col) ∧ (e, col) ∈
        [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] := by
    intro q' hq'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl
    · exact ⟨I.s0, by simp [Inst.ends], 0, rfl, by simp⟩
    · exact ⟨I.t0, by simp [Inst.ends], 0, rfl, by simp⟩
    · exact ⟨I.s1, by simp [Inst.ends], 1, rfl, by simp⟩
    · exact ⟨I.t1, by simp [Inst.ends], 1, rfl, by simp⟩
  obtain ⟨q', hq', hall⟩ := hf
  obtain ⟨e, he, col, rfl, hecol⟩ := hmem q' hq'
  refine ⟨(e, col), hecol, fun n hn1 hn2 hadj => ?_⟩
  obtain ⟨ex, ey⟩ := e
  obtain ⟨nx, ny⟩ := n
  have ef0 := f0 _ he
  have ef1 := f1 _ he
  simp only at ef0 ef1 hn1 hn2
  have hadj' := hadj
  unfold Adjacent at hadj'
  simp only at hadj'
  have sf := seam_free h he
  simp only at sf
  have heb := hb _ he
  simp only at heb
  have hd3 : d + 3 ≤ I.w := by
    obtain ⟨k, -, -, -, -, ⟨e3, he3, h3a, h3b⟩⟩ := compClause_line h
    have := (hb e3 he3).1
    omega
  -- the neighbor is on a deleted line: impossible
  by_cases hnd : nx = d ∨ nx = d + 1
  · exfalso
    rcases hnd with hn | hn
    · have hex : ex + 1 = d := by omega
      have hny : ny = ey := by omega
      have free2 := sf.1 hex
      have img : delAt d (ex, ey) = (ex, ey) := by
        unfold delAt; rw [ite_eq_left (by simp only; omega)]
      obtain ⟨e2, he2, h2a, -⟩ := hall (d, ey) (by show d < I.w - 2; omega) (by show ey < I.h; omega)
        (by rw [img]; exact Or.inr ⟨rfl, Or.inl hex⟩)
      obtain ⟨e2', he2', c2, rfl, -⟩ := hmem e2 he2
      have g0 := f0 _ he2'; have g1 := f1 _ he2'; have g2 := free2 _ he2'
      obtain ⟨x2, y2⟩ := e2'
      simp only at g0 g1 g2 h2a
      unfold delAt at h2a
      split_ifs at h2a with hlt <;> simp only [Prod.mk.injEq] at h2a hlt <;> omega
    · have hex : ex = d + 2 := by omega
      have hny : ny = ey := by omega
      obtain ⟨hd1, free1⟩ := sf.2 hex
      have img : delAt d (ex, ey) = (d, ey) := by
        unfold delAt; rw [ite_eq_right (by simp only; omega)]; simp only [Prod.mk.injEq]; exact ⟨by omega, trivial⟩
      obtain ⟨e2, he2, h2a, -⟩ := hall (d - 1, ey) (by show d - 1 < I.w - 2; omega)
        (by show ey < I.h; omega)
        (by rw [img]; exact Or.inr ⟨rfl, Or.inr (by dsimp only; omega)⟩)
      obtain ⟨e2', he2', c2, rfl, -⟩ := hmem e2 he2
      have g0 := f0 _ he2'; have g1 := f1 _ he2'; have g2 := free1 _ he2'
      obtain ⟨x2, y2⟩ := e2'
      simp only at g0 g1 g2 h2a
      unfold delAt at h2a
      split_ifs at h2a with hlt <;> simp only [Prod.mk.injEq] at h2a hlt <;> omega
  push Not at hnd
  have side : (ex < d ↔ nx < d) := by omega
  obtain ⟨e2, he2, h2a, h2b⟩ := hall (delAt d (nx, ny))
    (by unfold delAt; split_ifs <;> simp only <;> omega)
    (by unfold delAt; split_ifs <;> simpa using hn2)
    (delAt_adj ef0 ef1 hnd.1 hnd.2 hadj side)
  obtain ⟨e2', he2', c2, rfl, hc2⟩ := hmem e2 he2
  exact ⟨(e2', c2), hc2, delAt_inj (f0 _ he2') (f1 _ he2') hnd.1 hnd.2 h2a, h2b⟩

/-! ### T1 -/

/-- Insertion sort by a key, the same algorithm as `sortByKey`. -/
def sortBy {α : Type} (key : α → ℕ) : List α → List α
  | [] => []
  | x :: xs =>
    let s := sortBy key xs
    (s.filter (fun y => key y < key x)) ++ [x] ++ (s.filter (fun y => ¬ (key y < key x)))

theorem mem_sortBy {α : Type} (key : α → ℕ) : ∀ {l : List α} {y : α}, y ∈ sortBy key l → y ∈ l
  | [], _, h => by simp [sortBy] at h
  | x :: xs, y, h => by
    simp only [sortBy, List.mem_append, List.mem_filter, List.mem_singleton] at h
    rcases h with (⟨h, -⟩ | h) | ⟨h, -⟩
    · exact List.mem_cons_of_mem _ (mem_sortBy key h)
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_sortBy key h)

theorem sortByKey_eq (l : List (ℕ × ℕ)) : sortByKey l = sortBy (·.1) l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [sortByKey, sortBy, ih]

/-- Sorting commutes with relabelling the items, when the key is read through the relabelling. -/
theorem sortBy_map {α β : Type} (key : β → ℕ) (π : α → β) :
    ∀ l : List α, sortBy key (l.map π) = (sortBy (key ∘ π) l).map π
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, sortBy, sortBy_map key π xs, List.map_append, List.filter_map,
      List.map_cons, List.map_nil]
    rfl

/-- Sorting depends only on how the keys compare. -/
theorem sortBy_congr {α : Type} (k1 k2 : α → ℕ) :
    ∀ l : List α, (∀ t ∈ l, ∀ u ∈ l, k1 t < k1 u ↔ k2 t < k2 u) → sortBy k1 l = sortBy k2 l
  | [] => fun _ => rfl
  | x :: xs => by
    intro h
    have ih := sortBy_congr k1 k2 xs (fun t ht u hu => h t (List.mem_cons_of_mem _ ht) u
      (List.mem_cons_of_mem _ hu))
    simp only [sortBy, ih]
    have e1 : (sortBy k2 xs).filter (fun y => decide (k1 y < k1 x)) =
        (sortBy k2 xs).filter (fun y => decide (k2 y < k2 x)) := by
      apply List.filter_congr
      intro y hy
      have := h y (List.mem_cons_of_mem _ (mem_sortBy k2 hy)) x List.mem_cons_self
      simp only [this]
    have e2 : (sortBy k2 xs).filter (fun y => decide ¬(k1 y < k1 x)) =
        (sortBy k2 xs).filter (fun y => decide ¬(k2 y < k2 x)) := by
      apply List.filter_congr
      intro y hy
      have := h y (List.mem_cons_of_mem _ (mem_sortBy k2 hy)) x List.mem_cons_self
      simp only [this]
    rw [e1, e2]

/-- Two keyings of the same colored items that order the items the same way give the same sorted
color sequence. -/
theorem sortByKey_colors (items : List (ℕ × ℕ × ℕ))
    (h : ∀ t ∈ items, ∀ u ∈ items, t.1 < u.1 ↔ t.2.1 < u.2.1) :
    (sortByKey (items.map fun t => (t.1, t.2.2))).map (·.2) =
      (sortByKey (items.map fun t => (t.2.1, t.2.2))).map (·.2) := by
  rw [sortByKey_eq, sortByKey_eq, sortBy_map, sortBy_map, List.map_map, List.map_map]
  have := sortBy_congr ((fun x : ℕ × ℕ => x.1) ∘ fun t : ℕ × ℕ × ℕ => (t.1, t.2.2))
    ((fun x : ℕ × ℕ => x.1) ∘ fun t : ℕ × ℕ × ℕ => (t.2.1, t.2.2)) items (by simpa using h)
  rw [this]
  rfl

theorem perimIndex_isSome {R C : ℕ} {p : ℕ × ℕ} (hx : p.1 < R) (hy : p.2 < C) :
    (perimIndex R C p).isSome = true ↔ OnPerim R C p := by
  obtain ⟨x, y⟩ := p
  unfold perimIndex OnPerim
  simp only [beq_iff_eq] at hx hy ⊢
  split_ifs <;> simp_all

set_option maxHeartbeats 4000000 in
/-- Deleting two lines keeps the perimeter order of endpoints that stay on the perimeter. -/
theorem perim_order {R C d : ℕ} (hR : 13 ≤ R) (hC : 2 ≤ C) {e f : ℕ × ℕ}
    (he : e.1 < R ∧ e.2 < C ∧ e.1 ≠ d ∧ e.1 ≠ d + 1 ∧ Far d R e ∧ OnPerim R C e)
    (hf : f.1 < R ∧ f.2 < C ∧ f.1 ≠ d ∧ f.1 ≠ d + 1 ∧ Far d R f ∧ OnPerim R C f) :
    (perimIndex R C e).getD 0 < (perimIndex R C f).getD 0 ↔
      (perimIndex (R - 2) C (delAt d e)).getD 0 < (perimIndex (R - 2) C (delAt d f)).getD 0 := by
  obtain ⟨ex, ey⟩ := e
  obtain ⟨fx, fy⟩ := f
  obtain ⟨a1, a2, a3, a4, ⟨a5, a6⟩, a7⟩ := he
  obtain ⟨b1, b2, b3, b4, ⟨b5, b6⟩, b7⟩ := hf
  unfold OnPerim at a7 b7
  simp only at *
  unfold delAt perimIndex
  simp only [beq_iff_eq]
  by_cases hex : ex < d <;> by_cases hfx : fx < d
  · have := a5 hex; have := b5 hfx
    simp only [hex, hfx, ↓reduceIte]
    split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega
  · have := a5 hex; have := b6 (by omega)
    simp only [hex, hfx, ↓reduceIte]
    split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega
  · have := a6 (by omega); have := b5 hfx
    simp only [hex, hfx, ↓reduceIte]
    split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega
  · have := a6 (by omega); have := b6 (by omega)
    simp only [hex, hfx, ↓reduceIte]
    split_ifs <;> simp only [Option.getD_some, Option.getD_none] <;> omega

/-- After a compression, T1 carries over. -/
theorem t1_comp {I : Inst} {d : ℕ} (hI : InDom I) (h : CompClause I d) (hR : 13 ≤ I.w)
    (hf : t1Fires (I.w - 2) I.h
      [(delAt d I.s0, 0), (delAt d I.t0, 0), (delAt d I.s1, 1), (delAt d I.t1, 1)] = true) :
    t1Fires I.w I.h [(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] = true := by
  obtain ⟨hw, hh, b0, b1, b2, b3, -⟩ := hI
  obtain ⟨f0, f1, hdw⟩ := compClause_free h
  have hb : ∀ e ∈ I.ends, e.1 < I.w ∧ e.2 < I.h := by
    intro e he
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact b0
    · exact b1
    · exact b2
    · exact b3
  have far := far_of_compClause (fun e he => (hb e he).1) h
  have inb' : ∀ e ∈ I.ends, (delAt d e).1 < I.w - 2 ∧ (delAt d e).2 < I.h := by
    intro e he
    have := f0 e he; have := f1 e he; have := hb e he
    unfold delAt; split_ifs <;> (try simp only) <;> omega
  -- every endpoint is on the perimeter (in both instances)
  unfold t1Fires at hf ⊢
  rw [Bool.and_eq_true] at hf ⊢
  obtain ⟨hall, halt⟩ := hf
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hall
  obtain ⟨p0, p1, p2, p3⟩ := hall
  have per : ∀ e ∈ I.ends, (perimIndex (I.w - 2) I.h (delAt d e)).isSome = true →
      OnPerim I.w I.h e := by
    intro e he hs
    exact onPerim_delAt (f0 e he) (f1 e he) (far e he)
      ((perimIndex_isSome (inb' e he).1 (inb' e he).2).mp hs)
  have q0 := per _ (by simp [Inst.ends]) p0
  have q1 := per _ (by simp [Inst.ends]) p1
  have q2 := per _ (by simp [Inst.ends]) p2
  have q3 := per _ (by simp [Inst.ends]) p3
  have s : ∀ e ∈ I.ends, OnPerim I.w I.h e → (perimIndex I.w I.h e).isSome = true :=
    fun e he hp => (perimIndex_isSome (hb e he).1 (hb e he).2).mpr hp
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨s _ (by simp [Inst.ends]) q0, s _ (by simp [Inst.ends]) q1,
      s _ (by simp [Inst.ends]) q2, s _ (by simp [Inst.ends]) q3⟩
  -- the sorted color sequences agree
  have full : ∀ e ∈ I.ends, OnPerim I.w I.h e →
      e.1 < I.w ∧ e.2 < I.h ∧ e.1 ≠ d ∧ e.1 ≠ d + 1 ∧ Far d I.w e ∧ OnPerim I.w I.h e :=
    fun e he hp => ⟨(hb e he).1, (hb e he).2, f0 e he, f1 e he, far e he, hp⟩
  let items : List (ℕ × ℕ × ℕ) :=
    [((perimIndex I.w I.h I.s0).getD 0, (perimIndex (I.w - 2) I.h (delAt d I.s0)).getD 0, 0),
     ((perimIndex I.w I.h I.t0).getD 0, (perimIndex (I.w - 2) I.h (delAt d I.t0)).getD 0, 0),
     ((perimIndex I.w I.h I.s1).getD 0, (perimIndex (I.w - 2) I.h (delAt d I.s1)).getD 0, 1),
     ((perimIndex I.w I.h I.t1).getD 0, (perimIndex (I.w - 2) I.h (delAt d I.t1)).getD 0, 1)]
  have hord : ∀ t ∈ items, ∀ u ∈ items, t.1 < u.1 ↔ t.2.1 < u.2.1 := by
    have F0 := full _ (by simp [Inst.ends]) q0
    have F1 := full _ (by simp [Inst.ends]) q1
    have F2 := full _ (by simp [Inst.ends]) q2
    have F3 := full _ (by simp [Inst.ends]) q3
    intro t ht u hu
    simp only [items, List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl | rfl <;>
      exact perim_order hR (by omega) ‹_› ‹_›
  have := sortByKey_colors items hord
  simp only [items, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right] at this ⊢
  rw [this]
  exact halt

end ZZN
