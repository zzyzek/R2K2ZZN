-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PassX

/-!
# `passX` for the R test (effective alternation), compressions

With the deleted lines `d, d+1` at least 4 lines from both edges (`4 ≤ d`, `d + 6 ≤ R`), the
rewrite phase, the corner staircases and the outer walk of the two instances correspond.
-/

namespace ZZN

open GridHam

/-- Deleting two lines anywhere inside a free window of lines gives the same instance. -/
theorem deleteAt_window {I : Inst} {lo d d' : ℕ} (hf : ∀ k, lo ≤ k → k ≤ lo + 9 → I.FreeLine k)
    (hd : lo ≤ d ∧ d + 1 ≤ lo + 9) (hd' : lo ≤ d' ∧ d' + 1 ≤ lo + 9) :
    I.deleteAt d = I.deleteAt d' := by
  have key : ∀ e ∈ I.ends, delAt d e = delAt d' e := by
    intro e he
    have nin : ¬ (lo ≤ e.1 ∧ e.1 ≤ lo + 9) := fun ⟨a, b⟩ => hf e.1 a b e he rfl
    unfold delAt
    split_ifs <;> first | rfl | omega
  simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at key
  obtain ⟨k0, k1, k2, k3⟩ := key
  simp only [Inst.deleteAt, k0, k1, k2, k3]

/-! ### Frame cells near the corners avoid the deletion -/

theorem back_eq (R C : ℕ) (f : Frame) (a : ℕ × ℕ) :
    f.back R C a = ((if f.fr then R - 1 - (if f.tr then a.2 else a.1) else (if f.tr then a.2 else a.1)),
      (if f.fc then C - 1 - (if f.tr then a.1 else a.2) else (if f.tr then a.1 else a.2))) := by
  unfold Frame.back; rfl

/-- A cell of the 4 × 4 corner window of a frame, mapped to the grid, and its image under the
deletion. -/
theorem back_delAt {R C d : ℕ} (hd : 4 ≤ d) (hdR : d + 6 ≤ R) (f : Frame) {a : ℕ × ℕ}
    (ha1 : a.1 ≤ 3) (ha2 : a.2 ≤ 3) :
    f.back (R - 2) C a = delAt d (f.back R C a) ∧ (f.back R C a).1 ≠ d ∧
      (f.back R C a).1 ≠ d + 1 ∧ ((f.back R C a).1 ≤ 3 ∨ R ≤ (f.back R C a).1 + 4) ∧
      (f.back R C a).1 < R := by
  rw [back_eq, back_eq]
  generalize hr : (if f.tr then a.2 else a.1) = r
  generalize hy : (if f.fc then C - 1 - (if f.tr then a.1 else a.2) else (if f.tr then a.1 else a.2)) = y
  have hr3 : r ≤ 3 := by rw [← hr]; split_ifs <;> omega
  unfold delAt
  cases hfr : f.fr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_left (show r < d by omega)]
    exact ⟨rfl, by omega, by omega, Or.inl hr3, by omega⟩
  · simp only [↓reduceIte]
    rw [ite_eq_right (show ¬ (R - 1 - r < d) by omega)]
    refine ⟨?_, by omega, by omega, Or.inr (by omega), by omega⟩
    simp only [Prod.mk.injEq, and_true]
    omega

/-! ### The rewrite choice depends only on the 4 × 4 corner view -/

theorem rewritesAt_congr {v v' : View} (hs : ∀ r c, r ≤ 3 → c ≤ 3 → v'.at r c = v.at r c)
    (hH : 4 ≤ v.H) (hH' : 4 ≤ v'.H) (hW : 4 ≤ v.W) (hW' : 4 ≤ v'.W) :
    rewritesAt v' = rewritesAt v := by
  unfold rewritesAt View.empty
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [hs 1 2 (by omega) (by omega), hs 2 1 (by omega) (by omega), hs 0 0 (by omega) (by omega),
    hs 0 1 (by omega) (by omega), hs 0 2 (by omega) (by omega), hs 0 3 (by omega) (by omega),
    hs 1 0 (by omega) (by omega), hs 1 1 (by omega) (by omega), hs 2 0 (by omega) (by omega),
    hs 3 0 (by omega) (by omega)]
  have e1 : decide (v'.H ≥ 4) = decide (v.H ≥ 4) := by simp [hH, hH']
  have e2 : decide (v'.W ≥ 4) = decide (v.W ≥ 4) := by simp [hW, hW']
  have e3 : decide (v'.H ≥ 3) = decide (v.H ≥ 3) := by simp; omega
  have e4 : decide (v'.W ≥ 3) = decide (v.W ≥ 3) := by simp; omega
  have e5 : decide (v'.H ≥ 2) = decide (v.H ≥ 2) := by simp; omega
  rw [e1, e2, e3, e4, e5]

/-- `GoodIn` with threshold 4: the cell keeps its corner distance, or is at distance ≥ 4 in both
instances. -/
def GoodIn4 (R R' : ℕ) (f : Frame) (p p' : ℕ × ℕ) : Prop :=
  p'.2 = p.2 ∧ (xf R' f p' = xf R f p ∨ (4 ≤ xf R' f p' ∧ 4 ≤ xf R f p))

/-- Every cell off the deleted lines satisfies `GoodIn4`, when `4 ≤ d` and `d + 6 ≤ R`. -/
theorem goodIn4_delAt {R d : ℕ} (hd : 4 ≤ d) (hdR : d + 6 ≤ R) (f : Frame) {p : ℕ × ℕ}
    (hR : p.1 < R) (h0 : p.1 ≠ d) (h1 : p.1 ≠ d + 1) : GoodIn4 R (R - 2) f p (delAt d p) := by
  obtain ⟨x, y⟩ := p
  simp only at hR h0 h1
  refine ⟨by unfold delAt; split_ifs <;> rfl, ?_⟩
  unfold xf delAt
  by_cases hx : x < d
  · cases f.fr <;> simp [hx]; omega
  · cases f.fr <;> simp [hx] <;> omega

theorem view_at_eq4 {R R' C : ℕ} {f : Frame} {r c : ℕ} (hr : r ≤ 3) (hc : c ≤ 3)
    {pts pts' : List Pt}
    (h : List.Forall₂ (fun q q' => GoodIn4 R R' f q.1 q'.1 ∧ q'.2 = q.2) pts pts') :
    (makeView R' C f pts').at r c = (makeView R C f pts).at r c := by
  have key : ∀ {p p' : ℕ × ℕ}, GoodIn4 R R' f p p' →
      ((f.to R' C p' = (r, c)) ↔ (f.to R C p = (r, c))) := by
    intro p p' hg
    obtain ⟨h2, h | ⟨h1, h1'⟩⟩ := hg
    · rw [frame_to_eq, frame_to_eq, h2, h]
    · rw [frame_to_eq, frame_to_eq, h2]
      split_ifs <;> simp only [Prod.mk.injEq] <;> omega
  induction h with
  | nil => rfl
  | @cons q q' qs qs' hq hrest ih =>
    obtain ⟨hg, hcol⟩ := hq
    simp only [makeView, View.at, List.map_cons, List.find?_cons] at ih ⊢
    by_cases hh : f.to R C q.1 = (r, c)
    · have h' : f.to R' C q'.1 = (r, c) := (key hg).mpr hh
      simp [hh, h', hcol]
    · have h' : ¬ f.to R' C q'.1 = (r, c) := fun e => hh ((key hg).mp e)
      have e1 : (f.to R C q.1 == (r, c)) = false := by simpa using hh
      have e2 : (f.to R' C q'.1 == (r, c)) = false := by simpa using h'
      rw [e1, e2]
      exact ih

/-! ### The rewrite phase commutes with the deletion -/

/-- Rewrite cells and moves lie in the 4 × 4 corner window. -/
theorem rewritesAt_small {v : View} {rw : Rewrite} (h : rewritesAt v = some rw) :
    (∀ a ∈ rw.removed, a.1 ≤ 3 ∧ a.2 ≤ 3) ∧ (∀ m ∈ rw.moves, m.1.1 ≤ 3 ∧ m.1.2 ≤ 3 ∧ m.2.1 ≤ 3 ∧
      m.2.2 ≤ 3) := by
  unfold rewritesAt at h
  dsimp only at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> decide

/-- A cell avoids the deleted lines and is in the grid. -/
def Av (d R : ℕ) (c : ℕ × ℕ) : Prop := c.1 ≠ d ∧ c.1 ≠ d + 1 ∧ c.1 < R

theorem delAt_inj' {d R : ℕ} {u v : ℕ × ℕ} (hu : Av d R u) (hv : Av d R v) :
    delAt d u = delAt d v ↔ u = v :=
  ⟨delAt_inj hu.1 hu.2.1 hv.1 hv.2.1, fun h => h ▸ rfl⟩

theorem contains_map_delAt {d R : ℕ} {l : List (ℕ × ℕ)} {x : ℕ × ℕ} (hl : ∀ c ∈ l, Av d R c)
    (hx : Av d R x) : (l.map (delAt d)).contains (delAt d x) = l.contains x := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, List.contains_cons, ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))]
    have := delAt_inj' (hl y List.mem_cons_self) hx
    by_cases hyx : y = x
    · subst hyx; simp
    · have : ¬ delAt d y = delAt d x := fun e => hyx (this.mp e)
      have a1 : (delAt d x == delAt d y) = false := by
        rw [beq_eq_false_iff_ne]; exact fun e => hyx ((delAt_inj' (hl y List.mem_cons_self) hx).mp e.symm)
      have a2 : (x == y) = false := by
        rw [beq_eq_false_iff_ne]; exact fun e => hyx e.symm
      rw [a1, a2]

theorem findIdx_map_delAt {d R : ℕ} {a : ℕ × ℕ} (ha : Av d R a) :
    ∀ {l : List Pt}, (∀ q ∈ l, Av d R q.1) →
      (delPts d l).findIdx? (fun q => q.1 == delAt d a) = l.findIdx? (fun q => q.1 == a)
  | [], _ => rfl
  | q :: l, hl => by
    have ih := findIdx_map_delAt ha (l := l) (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    simp only [delPts, List.map_cons, List.findIdx?_cons] at ih ⊢
    have e : (delAt d q.1 == delAt d a) = (q.1 == a) := by
      have := delAt_inj' (hl q List.mem_cons_self) ha
      by_cases h : q.1 = a
      · simp [h]
      · have h' : ¬ delAt d q.1 = delAt d a := fun e => h (this.mp e)
        simp [h, h']
    rw [e, ih]

theorem map_modify {α β : Type} (g : α → β) (f : α → α) (f' : β → β) (hfg : ∀ x, g (f x) = f' (g x)) :
    ∀ (l : List α) (i : ℕ), (l.modify i f).map g = (l.map g).modify i f'
  | [], _ => by simp
  | x :: l, 0 => by simp [List.modify, hfg]
  | x :: l, i + 1 => by
    simp only [List.modify_succ_cons, List.map_cons]
    rw [map_modify g f f' hfg l i]

theorem moveFirst_map {d R : ℕ} {e : List Pt} {a b : ℕ × ℕ} (he : ∀ q ∈ e, Av d R q.1)
    (ha : Av d R a) : moveFirst (delPts d e) (delAt d a, delAt d b) = delPts d (moveFirst e (a, b)) := by
  unfold moveFirst
  simp only
  rw [findIdx_map_delAt ha he]
  cases e.findIdx? (fun q => q.1 == a) with
  | none => rfl
  | some i =>
    simp only [delPts]
    exact (map_modify (fun q : Pt => (delAt d q.1, q.2)) (fun q => (b, q.2))
      (fun q => (delAt d b, q.2)) (fun x => rfl) e i).symm

theorem mem_modify_aux {α : Type} (f : α → α) : ∀ (l : List α) (i : ℕ) {q : α},
    q ∈ l.modify i f → q ∈ l ∨ ∃ x ∈ l, q = f x
  | [], _, _, h => by simp at h
  | x :: l, 0, q, h => by
    simp only [List.modify_zero_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr ⟨x, List.mem_cons_self, rfl⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
  | x :: l, i + 1, q, h => by
    simp only [List.modify_succ_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases mem_modify_aux f l i h with h' | ⟨y, hy, rfl⟩
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

theorem mem_moveFirst {e : List Pt} {m : (ℕ × ℕ) × (ℕ × ℕ)} {q : Pt} (hq : q ∈ moveFirst e m) :
    q ∈ e ∨ q.1 = m.2 := by
  unfold moveFirst at hq
  split at hq
  · rename_i i _
    rcases mem_modify_aux (fun q => (m.2, q.2)) e i hq with h | ⟨x, -, rfl⟩
    · exact Or.inl h
    · exact Or.inr rfl
  · exact Or.inl hq

/-- The rewrite state carried to the smaller instance. -/
def mapSt (d : ℕ) (st : RWState) : RWState := ⟨delPts d st.eff, st.removed.map (delAt d), st.any⟩

/-- All cells of the state avoid the deleted lines. -/
def StAv (d R : ℕ) (st : RWState) : Prop :=
  (∀ q ∈ st.eff, Av d R q.1) ∧ (∀ c ∈ st.removed, Av d R c)

theorem forall2_map_self {α β : Type} {P : α → β → Prop} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, P x (g x)) → List.Forall₂ P l (l.map g)
  | [], _ => List.Forall₂.nil
  | x :: _l, h => List.Forall₂.cons (h x List.mem_cons_self)
      (forall2_map_self (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem foldl_moveFirst_map {d R : ℕ} :
    ∀ (moves : List ((ℕ × ℕ) × (ℕ × ℕ))) (e : List Pt), (∀ q ∈ e, Av d R q.1) →
      (∀ m ∈ moves, Av d R m.1 ∧ Av d R m.2) →
      (moves.map fun m => (delAt d m.1, delAt d m.2)).foldl moveFirst (delPts d e) =
        delPts d (moves.foldl moveFirst e) ∧ (∀ q ∈ moves.foldl moveFirst e, Av d R q.1)
  | [], e, he, _ => ⟨rfl, he⟩
  | m :: ms, e, he, hm => by
    have hm0 := hm m List.mem_cons_self
    have he' : ∀ q ∈ moveFirst e m, Av d R q.1 := by
      intro q hq
      rcases mem_moveFirst hq with h | h
      · exact he q h
      · rw [h]; exact hm0.2
    obtain ⟨ih1, ih2⟩ := foldl_moveFirst_map ms (moveFirst e m) he'
      (fun m' hm' => hm m' (List.mem_cons_of_mem _ hm'))
    simp only [List.map_cons, List.foldl_cons]
    have : moveFirst (delPts d e) (delAt d m.1, delAt d m.2) = delPts d (moveFirst e m) := by
      obtain ⟨a, b⟩ := m
      exact moveFirst_map he hm0.1
    rw [this]
    exact ⟨ih1, ih2⟩

theorem any_congr' {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.any p = l.any q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.any_cons, h x List.mem_cons_self,
      any_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem rwStep_map {R C d : ℕ} (hd : 4 ≤ d) (hdR : d + 6 ≤ R) (hC : 4 ≤ C) {st : RWState}
    (hav : StAv d R st) (f : Frame) :
    rwStep (R - 2) C (mapSt d st) f = mapSt d (rwStep R C st f) ∧ StAv d R (rwStep R C st f) := by
  have hrel : List.Forall₂ (fun q q' => GoodIn4 R (R - 2) f q.1 q'.1 ∧ q'.2 = q.2) st.eff
      (delPts d st.eff) :=
    forall2_map_self (fun q hq => ⟨goodIn4_delAt hd hdR f (hav.1 q hq).2.2 (hav.1 q hq).1
      (hav.1 q hq).2.1, rfl⟩)
  have hv : rewritesAt (makeView (R - 2) C f (delPts d st.eff)) =
      rewritesAt (makeView R C f st.eff) := by
    apply rewritesAt_congr (fun r c hr hc => view_at_eq4 hr hc hrel)
    all_goals (simp only [makeView, Frame.H, Frame.W]; split_ifs <;> omega)
  unfold rwStep mapSt
  simp only
  rw [hv]
  cases hrw : rewritesAt (makeView R C f st.eff) with
  | none => exact ⟨rfl, hav⟩
  | some rw =>
    obtain ⟨hsm1, hsm2⟩ := rewritesAt_small hrw
    have bc : ∀ a ∈ rw.removed, f.back (R - 2) C a = delAt d (f.back R C a) ∧
        Av d R (f.back R C a) := by
      intro a ha
      obtain ⟨e1, e2, e3, -, e5⟩ := back_delAt (C := C) hd hdR f (hsm1 a ha).1 (hsm1 a ha).2
      exact ⟨e1, e2, e3, e5⟩
    have bm : ∀ m ∈ rw.moves, f.back (R - 2) C m.1 = delAt d (f.back R C m.1) ∧
        f.back (R - 2) C m.2 = delAt d (f.back R C m.2) ∧ Av d R (f.back R C m.1) ∧
        Av d R (f.back R C m.2) := by
      intro m hm
      obtain ⟨h1, h2, h3, h4⟩ := hsm2 m hm
      obtain ⟨a1, a2, a3, -, a5⟩ := back_delAt (C := C) hd hdR f h1 h2
      obtain ⟨b1, b2, b3, -, b5⟩ := back_delAt (C := C) hd hdR f h3 h4
      exact ⟨a1, b1, ⟨a2, a3, a5⟩, ⟨b2, b3, b5⟩⟩
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

theorem foldl_rwStep_map {R C d : ℕ} (hd : 4 ≤ d) (hdR : d + 6 ≤ R) (hC : 4 ≤ C) :
    ∀ (fs : List Frame) (st : RWState), StAv d R st →
      fs.foldl (rwStep (R - 2) C) (mapSt d st) = mapSt d (fs.foldl (rwStep R C) st) ∧
        StAv d R (fs.foldl (rwStep R C) st)
  | [], _, h => ⟨rfl, h⟩
  | f :: fs, st, h => by
    obtain ⟨e1, e2⟩ := rwStep_map hd hdR hC h f
    simp only [List.foldl_cons]
    rw [e1]
    exact foldl_rwStep_map hd hdR hC fs _ e2

/-- **The rewrite phase commutes with the deletion.** -/
theorem rewriteAll_map {R C d : ℕ} (hd : 4 ≤ d) (hdR : d + 6 ≤ R) (hC : 4 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, Av d R q.1) :
    rewriteAll (R - 2) C (delPts d pts) = mapSt d (rewriteAll R C pts) ∧
      StAv d R (rewriteAll R C pts) := by
  have := foldl_rwStep_map hd hdR hC frames ⟨pts, [], false⟩ ⟨hp, by simp⟩
  exact this

/-! ### The corner staircases correspond -/

/-- Frame cells with coordinates `≤ 4` avoid the deletion when `5 ≤ d` and `d + 7 ≤ R`. -/
theorem back_delAt5 {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R) (f : Frame) {a : ℕ × ℕ}
    (ha1 : a.1 ≤ 4) (ha2 : a.2 ≤ 4) :
    f.back (R - 2) C a = delAt d (f.back R C a) ∧ Av d R (f.back R C a) := by
  rw [back_eq, back_eq]
  generalize hr : (if f.tr then a.2 else a.1) = r
  generalize hy : (if f.fc then C - 1 - (if f.tr then a.1 else a.2) else (if f.tr then a.1 else a.2)) = y
  have hr4 : r ≤ 4 := by rw [← hr]; split_ifs <;> omega
  unfold delAt Av
  cases hfr : f.fr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_left (show r < d by omega)]
    exact ⟨rfl, by omega, by omega, by omega⟩
  · simp only [↓reduceIte]
    rw [ite_eq_right (show ¬ (R - 1 - r < d) by omega)]
    refine ⟨?_, by omega, by omega, by omega⟩
    simp only [Prod.mk.injEq, and_true]
    omega

theorem notchLen_map {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R) (f : Frame)
    {rem : List (ℕ × ℕ)} (hrem : ∀ c ∈ rem, Av d R c) {i : ℕ} (hi : i ≤ 4) :
    notchLen (R - 2) C f (rem.map (delAt d)) i = notchLen R C f rem i := by
  unfold notchLen
  congr 1
  apply List.filter_congr
  intro j hj
  have hj4 : j ≤ 4 := by simp at hj; omega
  obtain ⟨e1, e2⟩ := back_delAt5 (C := C) hd hdR f (a := (i, j)) hi hj4
  rw [e1, contains_map_delAt hrem e2]

theorem notchLen_le (R C : ℕ) (f : Frame) (rem : List (ℕ × ℕ)) (i : ℕ) :
    notchLen R C f rem i ≤ 4 := by
  unfold notchLen
  exact (List.length_filter_le _ _).trans (by simp)

/-- The staircase lives in frame cells with coordinates `≤ 4` when the row lengths are `≤ 4`. -/
theorem staircase_small {lam : ℕ → ℕ} (hl : ∀ i, lam i ≤ 4) :
    ∀ a ∈ staircase lam, a.1 ≤ 4 ∧ a.2 ≤ 4 := by
  intro a ha
  unfold staircase at ha
  simp only [List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_reverse,
    List.mem_range, List.mem_map] at ha
  have hk : ((List.range 4).filter fun i => lam i > 0).length ≤ 4 :=
    (List.length_filter_le _ _).trans (by simp)
  rcases ha with rfl | ⟨i, hi, h⟩
  · exact ⟨hk, by simp⟩
  · rcases h with ⟨j, hj, rfl⟩ | rfl
    · have := hl i; have := hl (i + 1); simp only; omega
    · have := hl i; simp only; omega

/-- The staircase reads the row lengths of rows `0 … 4` only. -/
theorem staircase_congr {lam lam' : ℕ → ℕ} (h : ∀ i, i ≤ 4 → lam' i = lam i) :
    staircase lam' = staircase lam := by
  unfold staircase
  have hk : ((List.range 4).filter fun i => decide (lam' i > 0)) =
      ((List.range 4).filter fun i => decide (lam i > 0)) := by
    apply List.filter_congr
    intro i hi
    simp at hi
    rw [h i (by omega)]
  simp only [hk]
  congr 1
  apply List.flatMap_congr
  intro i hi
  have hk4 : ((List.range 4).filter fun i => decide (lam i > 0)).length ≤ 4 :=
    (List.length_filter_le _ _).trans (by simp)
  simp only [List.mem_reverse, List.mem_range] at hi
  rw [h i (by omega), h (i + 1) (by omega)]

theorem stairOf_map {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R) (f : Frame)
    {rem : List (ℕ × ℕ)} (hrem : ∀ c ∈ rem, Av d R c) :
    stairOf (R - 2) C f (rem.map (delAt d)) = (stairOf R C f rem).map (delAt d) ∧
      ∀ c ∈ stairOf R C f rem, Av d R c := by
  have hl : staircase (notchLen (R - 2) C f (rem.map (delAt d))) =
      staircase (notchLen R C f rem) :=
    staircase_congr (fun i hi => notchLen_map hd hdR f hrem hi)
  unfold stairOf
  rw [hl, List.map_map]
  refine ⟨List.map_congr_left (fun a ha => ?_), fun c hc => ?_⟩
  · have := staircase_small (notchLen_le R C f rem) a ha
    exact (back_delAt5 (C := C) hd hdR f this.1 this.2).1
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    have := staircase_small (notchLen_le R C f rem) a ha
    exact (back_delAt5 (C := C) hd hdR f this.1 this.2).2

/-! ### The sides: the larger column with lines `d, d+1` removed is the smaller column -/

/-- Line numbers of the smaller instance, back in the larger one. -/
def liftN (d x : ℕ) : ℕ := if x < d then x else x + 2

theorem liftN_strictMono (d : ℕ) : StrictMono (liftN d) := by
  intro x y h
  unfold liftN
  split_ifs <;> omega

theorem sorted_range_filter (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

/-- Two strictly increasing lists of naturals with the same members are equal. -/
theorem eq_of_sorted_mem {l l' : List ℕ} (h : l.Pairwise (· < ·)) (h' : l'.Pairwise (· < ·))
    (hm : ∀ x, x ∈ l ↔ x ∈ l') : l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y l' => exact absurd ((hm y).mpr List.mem_cons_self) (by simp)
  | cons x l ih =>
    cases l' with
    | nil => exact absurd ((hm x).mp List.mem_cons_self) (by simp)
    | cons y l' =>
      rw [List.pairwise_cons] at h h'
      have hxy : x = y := by
        have hx := (hm x).mp List.mem_cons_self
        have hy := (hm y).mpr List.mem_cons_self
        rcases List.mem_cons.mp hx with e | hx
        · exact e
        rcases List.mem_cons.mp hy with e | hy
        · exact e.symm
        have := h'.1 x hx
        have := h.1 y hy
        omega
      subst hxy
      congr 1
      apply ih h.2 h'.2
      intro z
      constructor
      · intro hz
        have := (hm z).mp (List.mem_cons_of_mem _ hz)
        rcases List.mem_cons.mp this with e | e
        · have := h.1 z hz; omega
        · exact e
      · intro hz
        have := (hm z).mpr (List.mem_cons_of_mem _ hz)
        rcases List.mem_cons.mp this with e | e
        · have := h'.1 z hz; omega
        · exact e

/-- The gap identity for one side. -/
theorem range_gap {R a b d : ℕ} (had : a < d) (hdR : d + 3 + b ≤ R) :
    (List.range R).filter (fun x => decide (a < x ∧ x + 1 + b < R) && !(x == d || x == d + 1)) =
      ((List.range (R - 2)).filter fun x => decide (a < x ∧ x + 1 + b < R - 2)).map (liftN d) := by
  apply eq_of_sorted_mem (sorted_range_filter _ _)
    ((sorted_range_filter _ _).map _ (fun x y h => liftN_strictMono d h))
  intro x
  simp only [List.mem_filter, List.mem_range, List.mem_map, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  constructor
  · rintro ⟨hx, ⟨h1, h2⟩, h3, h4⟩
    by_cases hxd : x < d
    · exact ⟨x, ⟨by omega, h1, by omega⟩, by simp [liftN, hxd]⟩
    · exact ⟨x - 2, ⟨by omega, by omega, by omega⟩, by simp only [liftN]; split_ifs <;> omega⟩
  · rintro ⟨y, ⟨hy, h1, h2⟩, rfl⟩
    unfold liftN
    split_ifs <;> refine ⟨by omega, ⟨by omega, by omega⟩, by omega, by omega⟩

/-! ### The walk with the deleted lines filtered out -/

def walk3Core (R C : ℕ) (tl tr br bl : List (ℕ × ℕ)) (lTL lTR lBR lBL kTL kTR kBR kBL : ℕ) :
    List (ℕ × ℕ) :=
  tl ++ ((List.range C).filter fun y => decide (lTL < y ∧ y + 1 + lTR < C)).map (fun y => (0, y)) ++
    tr.reverse ++
    ((List.range R).filter fun x => decide (kTR < x ∧ x + 1 + kBR < R)).map (fun x => (x, C - 1)) ++
    br ++
    (((List.range C).filter fun y => decide (lBL < y ∧ y + 1 + lBR < C)).map
      (fun y => (R - 1, y))).reverse ++
    bl.reverse ++
    (((List.range R).filter fun x => decide (kTL < x ∧ x + 1 + kBL < R)).map (fun x => (x, 0))).reverse

def kOf (R C : ℕ) (f : Frame) (rem : List (ℕ × ℕ)) : ℕ :=
  ((List.range 4).filter fun i => notchLen R C f rem i > 0).length

theorem walk3_eq (R C : ℕ) (rem : List (ℕ × ℕ)) :
    walk3 R C rem = walk3Core R C (stairOf R C frameTL rem) (stairOf R C frameTR rem)
      (stairOf R C frameBR rem) (stairOf R C frameBL rem) (notchLen R C frameTL rem 0)
      (notchLen R C frameTR rem 0) (notchLen R C frameBR rem 0) (notchLen R C frameBL rem 0)
      (kOf R C frameTL rem) (kOf R C frameTR rem) (kOf R C frameBR rem) (kOf R C frameBL rem) := rfl

def liftR (d : ℕ) (c : ℕ × ℕ) : ℕ × ℕ := (liftN d c.1, c.2)

theorem liftR_delAt {d R : ℕ} {c : ℕ × ℕ} (h : Av d R c) : liftR d (delAt d c) = c := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h0, h1, -⟩ := h
  simp only at h0 h1
  unfold liftR liftN delAt
  by_cases hx : x < d
  · simp only [hx, ↓reduceIte]
  · simp only [hx, ↓reduceIte]
    rw [ite_eq_right (by omega)]
    simp only [Prod.mk.injEq, and_true]
    omega

/-- The filter that drops the deleted lines. -/
def keepD (d : ℕ) (c : ℕ × ℕ) : Bool := !(c.1 == d || c.1 == d + 1)

theorem filter_keep_of_av {d R : ℕ} {l : List (ℕ × ℕ)} (h : ∀ c ∈ l, Av d R c) :
    l.filter (keepD d) = l := by
  rw [List.filter_eq_self]
  intro c hc
  obtain ⟨h0, h1, -⟩ := h c hc
  simp [keepD, h0, h1]

theorem map_liftR_of_av {d R : ℕ} {l : List (ℕ × ℕ)} (h : ∀ c ∈ l, Av d R c) :
    (l.map (delAt d)).map (liftR d) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left (fun c hc => liftR_delAt (h c hc))

/-- **The walk relation.** -/
theorem walk3Core_filter {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R)
    {tl tr br bl : List (ℕ × ℕ)} (htl : ∀ c ∈ tl, Av d R c) (htr : ∀ c ∈ tr, Av d R c)
    (hbr : ∀ c ∈ br, Av d R c) (hbl : ∀ c ∈ bl, Av d R c) {lTL lTR lBR lBL kTL kTR kBR kBL : ℕ}
    (hk1 : kTR ≤ 4) (hk2 : kBR ≤ 4) (hk3 : kTL ≤ 4) (hk4 : kBL ≤ 4) :
    (walk3Core R C tl tr br bl lTL lTR lBR lBL kTL kTR kBR kBL).filter (keepD d) =
      (walk3Core (R - 2) C (tl.map (delAt d)) (tr.map (delAt d)) (br.map (delAt d))
        (bl.map (delAt d)) lTL lTR lBR lBL kTL kTR kBR kBL).map (liftR d) := by
  unfold walk3Core
  simp only [List.filter_append, List.map_append, List.filter_reverse, List.map_reverse]
  rw [filter_keep_of_av htl, map_liftR_of_av htl, filter_keep_of_av htr, map_liftR_of_av htr,
    filter_keep_of_av hbr, map_liftR_of_av hbr, filter_keep_of_av hbl, map_liftR_of_av hbl]
  -- top row
  have htop : (((List.range C).filter fun y => decide (lTL < y ∧ y + 1 + lTR < C)).map
      (fun y => ((0 : ℕ), y))).filter (keepD d) =
      ((List.range C).filter fun y => decide (lTL < y ∧ y + 1 + lTR < C)).map (fun y => ((0 : ℕ), y)) := by
    rw [List.filter_eq_self]
    intro c hc
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
    simp [keepD]; omega
  have htop' : (((List.range C).filter fun y => decide (lTL < y ∧ y + 1 + lTR < C)).map
      (fun y => ((0 : ℕ), y))).map (liftR d) =
      ((List.range C).filter fun y => decide (lTL < y ∧ y + 1 + lTR < C)).map (fun y => ((0 : ℕ), y)) := by
    rw [List.map_map]
    exact List.map_congr_left (fun y _ => by
      simp only [Function.comp, liftR, liftN]; rw [ite_eq_left (by omega)])
  -- bottom row
  have hbot : (((List.range C).filter fun y => decide (lBL < y ∧ y + 1 + lBR < C)).map
      (fun y => (R - 1, y))).filter (keepD d) =
      ((List.range C).filter fun y => decide (lBL < y ∧ y + 1 + lBR < C)).map (fun y => (R - 1, y)) := by
    rw [List.filter_eq_self]
    intro c hc
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
    simp [keepD]; omega
  have hbot' : (((List.range C).filter fun y => decide (lBL < y ∧ y + 1 + lBR < C)).map
      (fun y => (R - 2 - 1, y))).map (liftR d) =
      ((List.range C).filter fun y => decide (lBL < y ∧ y + 1 + lBR < C)).map (fun y => (R - 1, y)) := by
    rw [List.map_map]
    exact List.map_congr_left (fun y _ => by
      simp only [Function.comp, liftR, liftN]
      rw [ite_eq_right (show ¬ (R - 2 - 1 < d) by omega)]
      simp only [Prod.mk.injEq, and_true]
      omega)
  -- right and left columns
  have hside : ∀ (a b : ℕ) (g : ℕ → ℕ × ℕ), (∀ x, (g x).1 = x) → (∀ x, liftR d (g x) = g (liftN d x)) →
      a < d → d + 3 + b ≤ R →
      (((List.range R).filter fun x => decide (a < x ∧ x + 1 + b < R)).map g).filter (keepD d) =
        (((List.range (R - 2)).filter fun x => decide (a < x ∧ x + 1 + b < R - 2)).map g).map
          (liftR d) := by
    intro a b g hg1 hg2 had hdR'
    rw [List.filter_map, List.filter_filter]
    have e : ∀ x, ((keepD d ∘ g) x && decide (a < x ∧ x + 1 + b < R)) =
        (decide (a < x ∧ x + 1 + b < R) && !(x == d || x == d + 1)) := by
      intro x
      simp only [keepD, Function.comp, hg1, Bool.and_comm]
    have e2 : ((List.range R).filter fun x => (keepD d ∘ g) x && decide (a < x ∧ x + 1 + b < R)) =
        (List.range R).filter (fun x => decide (a < x ∧ x + 1 + b < R) && !(x == d || x == d + 1)) :=
      List.filter_congr (fun x _ => e x)
    rw [e2, range_gap had hdR', List.map_map, List.map_map]
    exact List.map_congr_left (fun x _ => (hg2 x).symm)
  have hright := hside kTR kBR (fun x => (x, C - 1)) (fun x => rfl) (fun x => rfl) (by omega)
    (by omega)
  have hleft := hside kTL kBL (fun x => (x, 0)) (fun x => rfl) (fun x => rfl) (by omega)
    (by omega)
  rw [htop, htop', hbot, hbot', hright, hleft]

/-! ### Positions along the walk -/

def positionsFrom (l : List (ℕ × ℕ)) (x : ℕ × ℕ) (n : ℕ) : List ℕ :=
  ((l.zipIdx n).filter (·.1 == x)).map (·.2)

theorem positions_eq (l : List (ℕ × ℕ)) (x : ℕ × ℕ) : positions l x = positionsFrom l x 0 := rfl

theorem positionsFrom_length (x : ℕ × ℕ) :
    ∀ (l : List (ℕ × ℕ)) (n : ℕ), (positionsFrom l x n).length = l.count x
  | [], _ => rfl
  | a :: l, n => by
    have ih := positionsFrom_length x l (n + 1)
    unfold positionsFrom at ih ⊢
    rw [List.zipIdx_cons, List.filter_cons, List.count_cons]
    by_cases h : a = x
    · simp only [h, beq_self_eq_true, ↓reduceIte, List.map_cons, List.length_cons, ih]
    · have h' : (a == x) = false := by simpa using h
      simp only [h', Bool.false_eq_true, ↓reduceIte, ih]
      simp []

theorem positionsFrom_head (x : ℕ × ℕ) :
    ∀ (l : List (ℕ × ℕ)) (n : ℕ), x ∈ l → (positionsFrom l x n).headD 0 = n + l.idxOf x
  | [], _, h => by simp at h
  | a :: l, n, hx => by
    unfold positionsFrom
    rw [List.zipIdx_cons, List.filter_cons, List.idxOf_cons]
    by_cases h : a = x
    · simp [h]
    · have h' : (a == x) = false := by simpa using h
      have hx' : x ∈ l := by
        rcases List.mem_cons.mp hx with e | e
        · exact absurd e.symm h
        · exact e
      have ih := positionsFrom_head x l (n + 1) hx'
      unfold positionsFrom at ih
      simp only [h', Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      omega

theorem positions_length (l : List (ℕ × ℕ)) (x : ℕ × ℕ) : (positions l x).length = l.count x :=
  positionsFrom_length x l 0

theorem positions_head {l : List (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ l) :
    (positions l x).headD 0 = l.idxOf x := by
  rw [positions_eq, positionsFrom_head x l 0 hx]
  omega

theorem count_filter_keep {p : ℕ × ℕ → Bool} {x : ℕ × ℕ} (hp : p x = true) :
    ∀ l : List (ℕ × ℕ), (l.filter p).count x = l.count x
  | [] => rfl
  | a :: l => by
    have ih := count_filter_keep hp l
    by_cases ha : p a = true
    · simp only [List.filter_cons, ha, ↓reduceIte, List.count_cons, ih]
    · have ha' : p a = false := by simpa using ha
      simp only [List.filter_cons, ha', Bool.false_eq_true, ↓reduceIte, List.count_cons, ih]
      have : a ≠ x := fun e => by rw [e] at ha'; rw [hp] at ha'; exact absurd ha' (by simp)
      simp [this]

theorem idxOf_filter_lt {p : ℕ × ℕ → Bool} {x y : ℕ × ℕ} (hx : p x = true) (hy : p y = true) :
    ∀ l : List (ℕ × ℕ), x ∈ l → y ∈ l →
      (l.idxOf x < l.idxOf y ↔ (l.filter p).idxOf x < (l.filter p).idxOf y)
  | [], h, _ => by simp at h
  | a :: l, hxl, hyl => by
    by_cases hax : a = x <;> by_cases hay : a = y
    · subst hax; subst hay; simp
    · subst hax
      simp [hx, hay]
    · subst hay
      simp [hy, hax]
    · have hx' : x ∈ l := by rcases List.mem_cons.mp hxl with e | e; exact absurd e.symm hax; exact e
      have hy' : y ∈ l := by rcases List.mem_cons.mp hyl with e | e; exact absurd e.symm hay; exact e
      have ih := idxOf_filter_lt hx hy l hx' hy'
      have e1 : (a :: l).idxOf x = l.idxOf x + 1 := by simp [hax]
      have e2 : (a :: l).idxOf y = l.idxOf y + 1 := by simp [hay]
      rw [e1, e2]
      by_cases hpa : p a = true
      · simp only [List.filter_cons, hpa, ↓reduceIte]
        have f1 : (a :: l.filter p).idxOf x = (l.filter p).idxOf x + 1 := by simp [hax]
        have f2 : (a :: l.filter p).idxOf y = (l.filter p).idxOf y + 1 := by simp [hay]
        rw [f1, f2]
        omega
      · have hpa' : p a = false := by simpa using hpa
        simp only [List.filter_cons, hpa', Bool.false_eq_true, ↓reduceIte]
        omega

theorem idxOf_map_inj {g : ℕ × ℕ → ℕ × ℕ} (hg : Function.Injective g) (a : ℕ × ℕ) :
    ∀ l : List (ℕ × ℕ), (l.map g).idxOf (g a) = l.idxOf a
  | [] => rfl
  | b :: l => by
    simp only [List.map_cons, List.idxOf_cons, idxOf_map_inj hg a l]
    by_cases h : b = a
    · simp [h]
    · have : g b ≠ g a := fun e => h (hg e)
      simp [h, this]

theorem liftR_injective (d : ℕ) : Function.Injective (liftR d) := by
  intro u v h
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only [liftR, Prod.mk.injEq] at h
  exact Prod.ext ((liftN_strictMono d).injective h.1) h.2

theorem dedup_length_map_inj {g : ℕ × ℕ → ℕ × ℕ} {l : List (ℕ × ℕ)}
    (hg : ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y) : (l.map g).dedup.length = l.dedup.length := by
  have e : (l.map g).toFinset = l.toFinset.image g := by ext x; simp
  rw [← List.card_toFinset, ← List.card_toFinset, e]
  exact Finset.card_image_of_injOn (fun x hx y hy h => hg x (by simpa using hx) y (by simpa using hy) h)

theorem kOf_map {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R) (f : Frame) {rem : List (ℕ × ℕ)}
    (hrem : ∀ c ∈ rem, Av d R c) : kOf (R - 2) C f (rem.map (delAt d)) = kOf R C f rem := by
  unfold kOf
  congr 1
  apply List.filter_congr
  intro i hi
  simp at hi
  rw [notchLen_map hd hdR f hrem (by omega)]

theorem kOf_le (R C : ℕ) (f : Frame) (rem : List (ℕ × ℕ)) : kOf R C f rem ≤ 4 :=
  (List.length_filter_le _ _).trans (by simp)

/-- The walk relation for `walk3` itself. -/
theorem walk3_filter {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R) {rem : List (ℕ × ℕ)}
    (hrem : ∀ c ∈ rem, Av d R c) :
    (walk3 R C rem).filter (keepD d) = (walk3 (R - 2) C (rem.map (delAt d))).map (liftR d) := by
  rw [walk3_eq, walk3_eq]
  obtain ⟨s1, a1⟩ := stairOf_map (C := C) hd hdR frameTL hrem
  obtain ⟨s2, a2⟩ := stairOf_map (C := C) hd hdR frameTR hrem
  obtain ⟨s3, a3⟩ := stairOf_map (C := C) hd hdR frameBR hrem
  obtain ⟨s4, a4⟩ := stairOf_map (C := C) hd hdR frameBL hrem
  rw [s1, s2, s3, s4, notchLen_map hd hdR frameTL hrem (by omega),
    notchLen_map hd hdR frameTR hrem (by omega), notchLen_map hd hdR frameBR hrem (by omega),
    notchLen_map hd hdR frameBL hrem (by omega), kOf_map hd hdR frameTL hrem,
    kOf_map hd hdR frameTR hrem, kOf_map hd hdR frameBR hrem, kOf_map hd hdR frameBL hrem]
  exact walk3Core_filter hd hdR a1 a2 a3 a4 (kOf_le _ _ _ _) (kOf_le _ _ _ _) (kOf_le _ _ _ _)
    (kOf_le _ _ _ _)

theorem keepD_of_av {d R : ℕ} {c : ℕ × ℕ} (h : Av d R c) : keepD d c = true := by
  obtain ⟨h0, h1, -⟩ := h
  simp [keepD, h0, h1]

/-- The R test after the rewrite phase. -/
def effAltFrom (R C : ℕ) (st : RWState) : Bool :=
  if !st.any then false
  else if st.eff.any (fun q => st.removed.contains q.1) then false
  else if (st.eff.map (·.1)).dedup.length != 4 then false
  else
    let walk := walk3 R C st.removed
    let places := st.eff.map fun q => (positions walk q.1, q.2)
    if places.any (fun pl => pl.1.length != 1) then false
    else alternating ((sortByKey (places.map fun pl => (pl.1.headD 0, pl.2))).map (·.2))

theorem effAlt3_eq (R C : ℕ) (pts : List Pt) : effAlt3 R C pts = effAltFrom R C (rewriteAll R C pts) :=
  rfl

set_option maxHeartbeats 1000000 in
theorem effAltFrom_map {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R) {st : RWState}
    (hav : StAv d R st) : effAltFrom (R - 2) C (mapSt d st) = effAltFrom R C st := by
  unfold effAltFrom mapSt
  simp only
  have hwalk : (walk3 R C st.removed).filter (keepD d) =
      (walk3 (R - 2) C (st.removed.map (delAt d))).map (liftR d) := walk3_filter hd hdR hav.2
  generalize walk3 R C st.removed = W at hwalk ⊢
  generalize walk3 (R - 2) C (st.removed.map (delAt d)) = W' at hwalk ⊢
  have hcount : ∀ q ∈ st.eff, W'.count (delAt d q.1) = W.count q.1 := by
    intro q hq
    have h1 := count_filter_keep (keepD_of_av (hav.1 q hq)) W
    rw [hwalk] at h1
    have e := List.count_map_of_injective W' (liftR d) (liftR_injective d) (delAt d q.1)
    rw [liftR_delAt (hav.1 q hq)] at e
    exact e.symm.trans h1
  have hord : ∀ q ∈ st.eff, ∀ q' ∈ st.eff, q.1 ∈ W → q'.1 ∈ W →
      (W.idxOf q.1 < W.idxOf q'.1 ↔ W'.idxOf (delAt d q.1) < W'.idxOf (delAt d q'.1)) := by
    intro q hq q' hq' hm hm'
    rw [idxOf_filter_lt (keepD_of_av (hav.1 q hq)) (keepD_of_av (hav.1 q' hq')) W hm hm', hwalk]
    rw [← idxOf_map_inj (liftR_injective d) (delAt d q.1) W',
      ← idxOf_map_inj (liftR_injective d) (delAt d q'.1) W', liftR_delAt (hav.1 q hq),
      liftR_delAt (hav.1 q' hq')]
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
  · -- every effective endpoint is on the walk exactly once
    have hin : ∀ q ∈ st.eff, q.1 ∈ W := by
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


/-- **The R test gives the same answer on both instances.** -/
theorem effAlt3_comp {R C d : ℕ} (hd : 5 ≤ d) (hdR : d + 7 ≤ R) (hC : 4 ≤ C) {pts : List Pt}
    (hp : ∀ q ∈ pts, Av d R q.1) : effAlt3 (R - 2) C (delPts d pts) = effAlt3 R C pts := by
  obtain ⟨hst, hav⟩ := rewriteAll_map (C := C) (by omega) (by omega) hC hp
  rw [effAlt3_eq, effAlt3_eq, hst]
  exact effAltFrom_map hd hdR hav

end ZZN
