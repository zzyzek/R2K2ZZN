-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.SoundT1
import ZZN.PassTR

/-!
# Soundness of the local entries (Theorem B)

Every frame entry is reduced to the identity frame by moving the instance (`frameFires_id`); then
each entry is a short case check on path neighbours (`PROOF.md` §4.7).
-/

namespace ZZN

open GridHam

/-! ### Moving an instance into a frame -/

def idF : Frame := ⟨false, false, false⟩

def Inst.frameMap (I : Inst) (f : Frame) : Inst :=
  ⟨f.H I.w I.h, f.W I.w I.h, f.to I.w I.h I.s0, f.to I.w I.h I.t0, f.to I.w I.h I.s1,
    f.to I.w I.h I.t1⟩

theorem solvable_frameMap {I : Inst} (f : Frame) (hS : Solvable I) : Solvable (I.frameMap f) := by
  obtain ⟨fr, fc, tr⟩ := f
  refine solvable_map (Frame.to I.w I.h ⟨fr, fc, tr⟩) ?_ ?_ ?_ ?_ rfl rfl rfl rfl hS
  · intro u v hu hv h
    obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
    unfold InBounds at hu hv
    simp only at hu hv
    cases fr <;> cases fc <;> cases tr <;> simp [Frame.to] at h <;> simp only [Prod.mk.injEq] <;> omega
  · intro v hv
    obtain ⟨v1, v2⟩ := v
    unfold InBounds at hv ⊢
    simp only [Inst.frameMap] at hv ⊢
    cases fr <;> cases fc <;> cases tr <;> simp [Frame.to, Frame.H, Frame.W] <;> omega
  · intro v hv
    obtain ⟨v1, v2⟩ := v
    unfold InBounds at hv
    simp only [Inst.frameMap] at hv
    refine ⟨Frame.back I.w I.h ⟨fr, fc, tr⟩ (v1, v2), ?_, ?_⟩
    · unfold InBounds
      cases fr <;> cases fc <;> cases tr <;> simp [Frame.back, Frame.H, Frame.W] at hv ⊢ <;> omega
    · cases fr <;> cases fc <;> cases tr <;> simp [Frame.back, Frame.to, Frame.H, Frame.W] at hv ⊢ <;>
        omega
  · intro u v h hu hv
    obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
    unfold InBounds at hu hv
    unfold Adjacent at h ⊢
    simp only at hu hv h
    cases fr <;> cases fc <;> cases tr <;> simp [Frame.to] <;> omega

theorem wellFormed_frameMap {I : Inst} (f : Frame) (hI : I.WellFormed) : (I.frameMap f).WellFormed := by
  obtain ⟨b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hI
  have inj : ∀ {u v : Coord}, InBounds I.w I.h u → InBounds I.w I.h v → u ≠ v →
      f.to I.w I.h u ≠ f.to I.w I.h v := by
    intro u v hu hv hne h
    obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
    obtain ⟨fr, fc, tr⟩ := f
    unfold InBounds at hu hv
    simp only at hu hv
    apply hne
    cases fr <;> cases fc <;> cases tr <;> simp [Frame.to] at h <;> simp only [Prod.mk.injEq] <;> omega
  have bnd : ∀ {v : Coord}, InBounds I.w I.h v → InBounds (I.frameMap f).w (I.frameMap f).h (f.to I.w I.h v) := by
    intro v hv
    obtain ⟨v1, v2⟩ := v
    obtain ⟨fr, fc, tr⟩ := f
    unfold InBounds at hv ⊢
    simp only [Inst.frameMap] at hv ⊢
    cases fr <;> cases fc <;> cases tr <;> simp [Frame.to, Frame.H, Frame.W] <;> omega
  exact ⟨bnd b0, bnd b1, bnd b2, bnd b3, inj b0 b1 d1, inj b0 b2 d2, inj b0 b3 d3, inj b1 b2 d4,
    inj b1 b3 d5, inj b2 b3 d6⟩

theorem idF_to (R C : ℕ) (p : ℕ × ℕ) : idF.to R C p = p := by simp [idF, Frame.to]

theorem map_idF (R C : ℕ) (pts : List Pt) : pts.map (fun q => (idF.to R C q.1, q.2)) = pts := by
  conv_rhs => rw [← List.map_id pts]
  exact List.map_congr_left (fun q _ => by simp [idF_to])

theorem makeView_idF (f : Frame) (R C : ℕ) (pts : List Pt) :
    makeView (f.H R C) (f.W R C) idF (pts.map fun q => (f.to R C q.1, q.2)) = makeView R C f pts := by
  unfold makeView
  rw [map_idF]
  simp [idF, Frame.H, Frame.W]

theorem frameFires_id (R C : ℕ) (pts : List Pt) (f : Frame) :
    frameFires R C pts f =
      frameFires (f.H R C) (f.W R C) (pts.map fun q => (f.to R C q.1, q.2)) idF := by
  unfold frameFires
  rw [makeView_idF]
  have hb : boundaryOnly (f.H R C) (f.W R C) idF (pts.map fun q => (f.to R C q.1, q.2)) =
      boundaryOnly R C f pts := by
    unfold boundaryOnly
    rw [map_idF]
    have h1 : idF.H (f.H R C) (f.W R C) = f.H R C := rfl
    have h2 : idF.W (f.H R C) (f.W R C) = f.W R C := rfl
    rw [h1, h2]
    have hl : (f.H R C % 2 == 1 && f.W R C % 2 == 1) = (R % 2 == 1 && C % 2 == 1) := by
      unfold Frame.H Frame.W; split_ifs <;> simp [Bool.and_comm]
    rw [hl]
  have hc : corner4 (f.H R C) (f.W R C) idF (pts.map fun q => (f.to R C q.1, q.2)) = corner4 R C f pts := by
    unfold corner4
    have hm : f.H R C * f.W R C = R * C := by unfold Frame.H Frame.W; split_ifs <;> ring
    rw [hm, List.filter_map, List.filter_map, List.map_map, List.map_map]
    simp only [Function.comp_def, idF_to]
  rw [hb, hc]
  have hd : (decide (f.H R C ≥ 10) && decide (f.W R C ≥ 10)) = (decide (R ≥ 10) && decide (C ≥ 10)) := by
    unfold Frame.H Frame.W; split_ifs <;> simp [Bool.and_comm]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hd ⊢
  rw [show ((decide (R ≥ 10) = true ∧ decide (C ≥ 10) = true) ↔
      (decide (f.H R C ≥ 10) = true ∧ decide (f.W R C ≥ 10) = true)) by
    rw [← Bool.and_eq_true, ← Bool.and_eq_true, hd]]

/-- The endpoints of the moved instance. -/
theorem pts_frameMap (I : Inst) (f : Frame) :
    ([(I.s0, 0), (I.t0, 0), (I.s1, 1), (I.t1, 1)] : List Pt).map (fun q => (f.to I.w I.h q.1, q.2)) =
      [((I.frameMap f).s0, 0), ((I.frameMap f).t0, 0), ((I.frameMap f).s1, 1), ((I.frameMap f).t1, 1)] :=
  rfl

/-! ### Path neighbours in a solution -/

section Sol

variable {J : Inst} {p q : List Coord}

def IsEnd (J : Inst) (v : Coord) : Prop := v = J.s0 ∨ v = J.t0 ∨ v = J.s1 ∨ v = J.t1

def pathOf (p q : List Coord) (v : Coord) : List Coord := if v ∈ p then p else q

def colOf (p : List Coord) (v : Coord) : ℕ := if v ∈ p then 0 else 1

/-- `u` is next to `v` along `v`'s path. -/
def Nb (p q : List Coord) (v u : Coord) : Prop := Used (pathOf p q v) v u

theorem pathOf_isPath (hS : IsSolution J p q) (v : Coord) :
    ∃ s t, IsPath J.w J.h s t (pathOf p q v) ∧
      ((pathOf p q v = p ∧ s = J.s0 ∧ t = J.t0) ∨ (pathOf p q v = q ∧ s = J.s1 ∧ t = J.t1)) := by
  unfold pathOf
  split_ifs
  · exact ⟨_, _, hS.1, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨_, _, hS.2.1, Or.inr ⟨rfl, rfl, rfl⟩⟩

theorem nb_adj (hS : IsSolution J p q) {v u : Coord} (h : Nb p q v u) : Adjacent v u := by
  obtain ⟨s, t, hP, -⟩ := pathOf_isPath hS v
  exact Used.adjacent hP.2.2.2.2 h

theorem nb_mem (_hS : IsSolution J p q) {v u : Coord} (h : Nb p q v u) :
    u ∈ pathOf p q v ∧ v ∈ pathOf p q v :=
  ⟨Used.mem_right h, Used.mem_left h⟩

theorem nb_col (hS : IsSolution J p q) {v u : Coord} (h : Nb p q v u) : colOf p u = colOf p v := by
  obtain ⟨hu, hv⟩ := nb_mem hS h
  unfold colOf
  unfold pathOf at hu hv
  by_cases h1 : v ∈ p
  · simp only [h1, ↓reduceIte] at hu ⊢; simp [hu]
  · simp only [h1, ↓reduceIte] at hu ⊢
    have : u ∉ p := fun hup => hS.2.2.1 u hup hu
    simp [this]

theorem nb_symm (hS : IsSolution J p q) {v u : Coord} (h : Nb p q v u) : Nb p q u v := by
  obtain ⟨hu, hv⟩ := nb_mem hS h
  have e : pathOf p q u = pathOf p q v := by
    unfold pathOf at hu ⊢
    by_cases hvp : v ∈ p
    · simp only [hvp, ↓reduceIte] at hu ⊢; simp [hu]
    · simp only [hvp, ↓reduceIte] at hu ⊢
      have : u ∉ p := fun hup => hS.2.2.1 u hup hu
      simp [this]
  unfold Nb
  rw [e]
  exact Used.symm h

theorem nb_inb (hS : IsSolution J p q) {v u : Coord} (h : Nb p q v u) : InBounds J.w J.h u := by
  obtain ⟨s, t, hP, -⟩ := pathOf_isPath hS v
  exact hP.2.2.2.1 u (nb_mem hS h).1

theorem head_no_pred {l : List Coord} {h u : Coord} (hn : l.Nodup) (hh : l.head? = some h) :
    ¬ [u, h] <:+: l := by
  intro hi
  obtain ⟨s, t, rfl⟩ := infix_pair_iff.mp hi
  cases s with
  | nil =>
    simp at hh
    subst hh
    simp at hn
  | cons a s =>
    simp at hh
    subst hh
    simp at hn

theorem last_no_succ {l : List Coord} {h u : Coord} (hn : l.Nodup) (hl : l.getLast? = some h) :
    ¬ [h, u] <:+: l := by
  intro hi
  have h1 := head_no_pred (u := u) (List.nodup_reverse.mpr hn) (by rw [List.head?_reverse, hl])
  apply h1
  have := List.reverse_infix.mpr hi
  simpa using this

theorem end_unique (hS : IsSolution J p q) {v u x : Coord} (he : IsEnd J v) (hu : Nb p q v u)
    (hx : Nb p q v x) : u = x := by
  obtain ⟨s, t, hP, hst⟩ := pathOf_isPath hS v
  obtain ⟨hh, hl, hn, -, -⟩ := hP
  have hvs : v = s ∨ v = t := by
    unfold IsEnd at he
    have hv := (nb_mem hS hu).2
    rcases hst with ⟨hpq, rfl, rfl⟩ | ⟨hpq, rfl, rfl⟩
    · rw [hpq] at hv
      rcases he with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hv) (fun hm => hS.2.2.1 _ hm (List.mem_of_mem_head? hS.2.1.1))
      · exact absurd (h ▸ hv) (fun hm => hS.2.2.1 _ hm (List.mem_of_getLast? hS.2.1.2.1))
    · rw [hpq] at hv
      rcases he with h | h | h | h
      · exact absurd (h ▸ List.mem_of_mem_head? hS.1.1) (fun hm => hS.2.2.1 _ hm hv)
      · exact absurd (h ▸ List.mem_of_getLast? hS.1.2.1) (fun hm => hS.2.2.1 _ hm hv)
      · exact Or.inl h
      · exact Or.inr h
  unfold Nb Used at hu hx
  rcases hvs with rfl | rfl
  · have np := fun w => head_no_pred (u := w) hn hh
    rcases hu with hu | hu
    · rcases hx with hx | hx
      · exact succ_unique hn hu hx
      · exact absurd hx (np x)
    · exact absurd hu (np u)
  · have ns := fun w => last_no_succ (u := w) hn hl
    rcases hu with hu | hu
    · exact absurd hu (ns u)
    · rcases hx with hx | hx
      · exact absurd hx (ns x)
      · exact pred_unique hn hu hx

theorem ends_mem (hS : IsSolution J p q) :
    J.s0 ∈ p ∧ J.t0 ∈ p ∧ J.s1 ∈ q ∧ J.t1 ∈ q ∧ J.s1 ∉ p ∧ J.t1 ∉ p :=
  ⟨List.mem_of_mem_head? hS.1.1, List.mem_of_getLast? hS.1.2.1, List.mem_of_mem_head? hS.2.1.1,
    List.mem_of_getLast? hS.2.1.2.1, fun h => hS.2.2.1 _ h (List.mem_of_mem_head? hS.2.1.1),
    fun h => hS.2.2.1 _ h (List.mem_of_getLast? hS.2.1.2.1)⟩

theorem interior (hS : IsSolution J p q) {v : Coord} (hv : InBounds J.w J.h v) (hne : ¬ IsEnd J v) :
    ∃ u x, u ≠ x ∧ Nb p q v u ∧ Nb p q v x := by
  have hmem : v ∈ pathOf p q v := by
    unfold pathOf
    split_ifs with h
    · exact h
    · rcases hS.2.2.2 v hv with h' | h'
      · exact absurd h' h
      · exact h'
  obtain ⟨s, t, hP, hst⟩ := pathOf_isPath hS v
  obtain ⟨hh, hl, hn, -, -⟩ := hP
  have hs : v ≠ s := by
    rcases hst with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> intro e <;> apply hne <;> unfold IsEnd <;> simp [e]
  have ht : v ≠ t := by
    rcases hst with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> intro e <;> apply hne <;> unfold IsEnd <;> simp [e]
  exact interior_two hn hmem (by rw [hh]; simpa using hs.symm) (by rw [hl]; simpa using ht.symm)

theorem end_exists (hS : IsSolution J p q) (hwf : J.WellFormed) {v : Coord} (he : IsEnd J v) :
    ∃ u, Nb p q v u := by
  obtain ⟨-, -, -, -, d1, -, -, -, -, d6⟩ := hwf
  obtain ⟨m0, m1, m2, m3, n2, n3⟩ := ends_mem hS
  unfold Nb pathOf
  unfold IsEnd at he
  rcases he with rfl | rfl | rfl | rfl
  · simp only [m0, ↓reduceIte]
    obtain ⟨u, hu⟩ := exists_succ m0 (by rw [hS.1.2.1]; simpa using Ne.symm d1)
    exact ⟨u, Or.inl hu⟩
  · simp only [m1, ↓reduceIte]
    obtain ⟨u, hu⟩ := exists_pred m1 (by rw [hS.1.1]; simpa using d1)
    exact ⟨u, Or.inr hu⟩
  · simp only [n2, ↓reduceIte]
    obtain ⟨u, hu⟩ := exists_succ m2 (by rw [hS.2.1.2.1]; simpa using Ne.symm d6)
    exact ⟨u, Or.inl hu⟩
  · simp only [n3, ↓reduceIte]
    obtain ⟨u, hu⟩ := exists_pred m3 (by rw [hS.2.1.1]; simpa using d6)
    exact ⟨u, Or.inr hu⟩

theorem le_two (hS : IsSolution J p q) {v a b c : Coord} (ha : Nb p q v a) (hb : Nb p q v b)
    (hc : Nb p q v c) : a = b ∨ a = c ∨ b = c := by
  obtain ⟨s, t, hP, -⟩ := pathOf_isPath hS v
  exact used_le_two hP.2.2.1 ha hb hc

/-! ### The view in the identity frame -/

def ptsOf (J : Inst) : List Pt := [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]

theorem vat_eq (J : Inst) (r c : ℕ) :
    (makeView J.w J.h idF (ptsOf J)).at r c =
      if J.s0 = (r, c) then some 0 else if J.t0 = (r, c) then some 0 else
      if J.s1 = (r, c) then some 1 else if J.t1 = (r, c) then some 1 else none := by
  unfold View.at makeView
  rw [map_idF]
  unfold ptsOf
  by_cases e0 : J.s0 = (r, c) <;> by_cases e1 : J.t0 = (r, c) <;> by_cases e2 : J.s1 = (r, c) <;>
    by_cases e3 : J.t1 = (r, c) <;> simp [e0, e1, e2, e3]

theorem vat_some (hS : IsSolution J p q) {r c a : ℕ}
    (h : (makeView J.w J.h idF (ptsOf J)).at r c = some a) : IsEnd J (r, c) ∧ colOf p (r, c) = a := by
  rw [vat_eq] at h
  obtain ⟨m0, m1, -, -, n2, n3⟩ := ends_mem hS
  unfold IsEnd colOf
  split_ifs at h with h0 h1 h2 h3 <;> simp at h
  · rw [← h0]; exact ⟨Or.inl rfl, by simp [m0, h]⟩
  · rw [← h1]; exact ⟨Or.inr (Or.inl rfl), by simp [m1, h]⟩
  · rw [← h2]; exact ⟨Or.inr (Or.inr (Or.inl rfl)), by simp [n2, h]⟩
  · rw [← h3]; exact ⟨Or.inr (Or.inr (Or.inr rfl)), by simp [n3, h]⟩

theorem vat_none {r c : ℕ} (h : (makeView J.w J.h idF (ptsOf J)).at r c = none) : ¬ IsEnd J (r, c) := by
  rw [vat_eq] at h
  unfold IsEnd
  split_ifs at h with h0 h1 h2 h3; simp at h
  intro he
  rcases he with e | e | e | e
  · exact h0 e.symm
  · exact h1 e.symm
  · exact h2 e.symm
  · exact h3 e.symm

/-! ### L2–L5 in the identity frame -/

theorem adj_nbrs {v u : Coord} (h : Adjacent v u) :
    u = (v.1 + 1, v.2) ∨ (u = (v.1 - 1, v.2) ∧ 1 ≤ v.1) ∨ u = (v.1, v.2 + 1) ∨
      (u = (v.1, v.2 - 1) ∧ 1 ≤ v.2) := by
  obtain ⟨a, b⟩ := v; obtain ⟨c, d⟩ := u
  unfold Adjacent at h
  simp only [Prod.mk.injEq] at h ⊢
  omega

def nbrList (v : Coord) : List Coord :=
  [(v.1 + 1, v.2), (v.1, v.2 + 1)] ++ (if 1 ≤ v.1 then [(v.1 - 1, v.2)] else []) ++
    (if 1 ≤ v.2 then [(v.1, v.2 - 1)] else [])

theorem adj_mem {v u : Coord} (h : Adjacent v u) : u ∈ nbrList v := by
  obtain ⟨a, b⟩ := v; obtain ⟨c, d⟩ := u
  unfold Adjacent at h
  unfold nbrList
  simp only at h
  split_ifs <;> simp only [List.mem_append, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] <;> omega

theorem col_le (p : List Coord) (v : Coord) : colOf p v ≤ 1 := by unfold colOf; split_ifs <;> omega

/-- The colours of the endpoints read in the view. -/
theorem vat_col (hS : IsSolution J p q) {r c a : ℕ} (h : (makeView J.w J.h idF (ptsOf J)).at r c = some a) :
    colOf p (r, c) = a ∧ a ≤ 1 :=
  ⟨(vat_some hS h).2, (vat_some hS h).2 ▸ col_le p _⟩

theorem vat_inb (hwf : J.WellFormed) (hS : IsSolution J p q) {r c a : ℕ}
    (h : (makeView J.w J.h idF (ptsOf J)).at r c = some a) : InBounds J.w J.h (r, c) := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hwf
  rcases (vat_some hS h).1 with e | e | e | e <;> rw [e] <;> assumption

theorem testL2_sound (hwf : J.WellFormed) (hS : IsSolution J p q) :
    testL2 (makeView J.w J.h idF (ptsOf J)) = false := by
  unfold testL2
  set v := makeView J.w J.h idF (ptsOf J)
  cases ha : v.at 0 1 with
  | none => rfl
  | some a =>
    cases hb : v.at 1 0 with
    | none => rfl
    | some b =>
      simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq]
      by_contra hc
      push Not at hc
      obtain ⟨hab, he⟩ := hc
      rw [ne_eq, Bool.not_eq_false, empty_iff] at he
      have h00 := he (0, 0) (by simp)
      obtain ⟨ca, -⟩ := vat_col hS ha
      obtain ⟨cb, -⟩ := vat_col hS hb
      have i01 := vat_inb hwf hS ha
      have i10 := vat_inb hwf hS hb
      obtain ⟨u, x, hux, hu, hx⟩ := interior hS (v := (0, 0)) (by unfold InBounds at i01 i10 ⊢; simp at *; omega)
        (vat_none h00)
      have cu := nb_col hS hu
      have cx := nb_col hS hx
      have mu := adj_mem (nb_adj hS hu)
      have mx := adj_mem (nb_adj hS hx)
      simp [nbrList] at mu mx
      rcases mu with rfl | rfl <;> rcases mx with rfl | rfl <;> simp_all

/-- Extract the hypotheses of a fired `match`-and-`&&` test. -/
theorem beq_some {o : Option ℕ} {a : ℕ} (h : (o == some a) = true) : o = some a := by simpa using h

theorem inb_of {_hwf : J.WellFormed} {r c : ℕ} (hr : r < J.w) (hc : c < J.h) : InBounds J.w J.h (r, c) :=
  ⟨hr, hc⟩

theorem testL3_sound (hwf : J.WellFormed) (hS : IsSolution J p q) :
    testL3 (makeView J.w J.h idF (ptsOf J)) = false := by
  unfold testL3
  set v := makeView J.w J.h idF (ptsOf J)
  cases ha : v.at 0 2 with
  | none => rfl
  | some a =>
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true] at hc
    obtain ⟨⟨h11, h10⟩, he⟩ := hc
    have h11 := beq_some h11
    have h10 := beq_some h10
    rw [empty_iff] at he
    have h00 := he (0, 0) (by simp)
    have h01 := he (0, 1) (by simp)
    obtain ⟨c02, ha1⟩ := vat_col hS ha
    obtain ⟨c11, -⟩ := vat_col hS h11
    obtain ⟨c10, -⟩ := vat_col hS h10
    have i02 := vat_inb hwf hS ha
    have i10 := vat_inb hwf hS h10
    unfold InBounds at i02 i10
    simp only at i02 i10
    obtain ⟨u, x, hux, hu, hx⟩ := interior hS (v := (0, 0)) ⟨by omega, by omega⟩ (vat_none h00)
    obtain ⟨y, z, hyz, hy, hz⟩ := interior hS (v := (0, 1)) ⟨by omega, by omega⟩ (vat_none h01)
    have cu := nb_col hS hu; have cx := nb_col hS hx; have cy := nb_col hS hy; have cz := nb_col hS hz
    have mu := adj_mem (nb_adj hS hu); have mx := adj_mem (nb_adj hS hx)
    have my := adj_mem (nb_adj hS hy); have mz := adj_mem (nb_adj hS hz)
    simp [nbrList] at mu mx my mz
    rcases mu with rfl | rfl <;> rcases mx with rfl | rfl <;> rcases my with rfl | rfl | rfl <;>
      rcases mz with rfl | rfl | rfl <;> simp only [ne_eq, not_true_eq_false] at hux hyz <;> omega

theorem testL4_sound (hwf : J.WellFormed) (hS : IsSolution J p q) :
    testL4 (makeView J.w J.h idF (ptsOf J)) = false := by
  unfold testL4
  set v := makeView J.w J.h idF (ptsOf J)
  cases ha : v.at 0 0 with
  | none => rfl
  | some a =>
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h11, h02⟩, hH⟩, he⟩ := hc
    have h11 := beq_some h11
    have h02 := beq_some h02
    rw [empty_iff] at he
    have h01 := he (0, 1) (by simp)
    have h10 := he (1, 0) (by simp)
    obtain ⟨c00, ha1⟩ := vat_col hS ha
    obtain ⟨c11, -⟩ := vat_col hS h11
    obtain ⟨c02, -⟩ := vat_col hS h02
    have e00 := (vat_some hS ha).1
    have e11 := (vat_some hS h11).1
    have i02 := vat_inb hwf hS h02
    have i11 := vat_inb hwf hS h11
    unfold InBounds at i02 i11
    simp only at i02 i11
    obtain ⟨y, z, hyz, hy, hz⟩ := interior hS (v := (0, 1)) ⟨by omega, by omega⟩ (vat_none h01)
    have cy := nb_col hS hy; have cz := nb_col hS hz
    have my := adj_mem (nb_adj hS hy); have mz := adj_mem (nb_adj hS hz)
    simp [nbrList] at my mz
    -- (0,1) joins the two A endpoints
    have key : Nb p q (0, 0) (0, 1) ∧ Nb p q (1, 1) (0, 1) := by
      rcases my with rfl | rfl | rfl <;> rcases mz with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at hyz <;>
        first
          | omega
          | exact ⟨nb_symm hS hz, nb_symm hS hy⟩
          | exact ⟨nb_symm hS hy, nb_symm hS hz⟩
    -- so (1,0) can only use (2,0)
    have only : ∀ w, Nb p q (1, 0) w → w = (2, 0) := by
      intro w hw
      have mw := adj_mem (nb_adj hS hw)
      simp [nbrList] at mw
      rcases mw with rfl | rfl | rfl
      · rfl
      · have := end_unique hS e11 (nb_symm hS hw) key.2
        simp at this
      · have := end_unique hS e00 (nb_symm hS hw) key.1
        simp at this
    obtain ⟨u, x, hux, hu, hx⟩ := interior hS (v := (1, 0)) ⟨by simp [] at hH; omega,
      by omega⟩ (vat_none h10)
    exact hux ((only u hu).trans (only x hx).symm)

theorem testL5_sound (hwf : J.WellFormed) (hS : IsSolution J p q) :
    testL5 (makeView J.w J.h idF (ptsOf J)) = false := by
  unfold testL5
  set v := makeView J.w J.h idF (ptsOf J)
  cases hb : v.at 0 0 with
  | none => rfl
  | some b =>
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true] at hc
    obtain ⟨⟨h02, h20⟩, he⟩ := hc
    have h02 := beq_some h02
    have h20 := beq_some h20
    rw [empty_iff] at he
    have h01 := he (0, 1) (by simp)
    have h10 := he (1, 0) (by simp)
    have h11 := he (1, 1) (by simp)
    obtain ⟨c00, hb1⟩ := vat_col hS hb
    obtain ⟨c02, -⟩ := vat_col hS h02
    obtain ⟨c20, -⟩ := vat_col hS h20
    have e00 := (vat_some hS hb).1
    have i02 := vat_inb hwf hS h02
    have i20 := vat_inb hwf hS h20
    unfold InBounds at i02 i20
    simp only at i02 i20
    obtain ⟨u, hu⟩ := end_exists hS hwf e00
    have cu := nb_col hS hu
    have mu := adj_mem (nb_adj hS hu)
    simp [nbrList] at mu
    obtain ⟨y, z, hyz, hy, hz⟩ := interior hS (v := (0, 1)) ⟨by omega, by omega⟩ (vat_none h01)
    obtain ⟨y', z', hyz', hy', hz'⟩ := interior hS (v := (1, 0)) ⟨by omega, by omega⟩ (vat_none h10)
    have cy := nb_col hS hy; have cz := nb_col hS hz
    have cy' := nb_col hS hy'; have cz' := nb_col hS hz'
    have my := adj_mem (nb_adj hS hy); have mz := adj_mem (nb_adj hS hz)
    have my' := adj_mem (nb_adj hS hy'); have mz' := adj_mem (nb_adj hS hz')
    simp [nbrList] at my mz my' mz'
    -- a neighbour of `(0,1)` or `(1,0)` equal to `(0,0)` must be `(0,0)`'s only neighbour
    have u1 : ∀ w, Nb p q w (0, 0) → w = u := fun w hw => (end_unique hS e00 hu (nb_symm hS hw)).symm
    rcases mu with rfl | rfl
    · -- (0,0) leaves through (1,0)
      have no01 : ¬ Nb p q (0, 1) (0, 0) := fun h => by have := u1 _ h; simp at this
      rcases my with rfl | rfl | rfl <;> rcases mz with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at hyz <;>
        first | omega | exact absurd hy no01 | exact absurd hz no01 | skip
      all_goals
        rcases my' with rfl | rfl | rfl <;> rcases mz' with rfl | rfl | rfl <;>
          simp only [ne_eq, not_true_eq_false] at hyz' <;> omega
    · -- (0,0) leaves through (0,1)
      have no10 : ¬ Nb p q (1, 0) (0, 0) := fun h => by have := u1 _ h; simp at this
      rcases my' with rfl | rfl | rfl <;> rcases mz' with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at hyz' <;>
        first | omega | exact absurd hy' no10 | exact absurd hz' no10 | skip
      all_goals
        rcases my with rfl | rfl | rfl <;> rcases mz with rfl | rfl | rfl <;>
          simp only [ne_eq, not_true_eq_false] at hyz <;> omega

/-! ### Closed paths of three cells -/

theorem path3 {w h : ℕ} {L : List Coord} {s t c : Coord} (hP : IsPath w h s t L) (h1 : Used L c s)
    (h2 : Used L c t) : L = [s, c, t] := by
  obtain ⟨hh, hl, hn, -, -⟩ := hP
  have i1 : [s, c] <:+: L := by
    rcases h1 with h | h
    · exact absurd h (head_no_pred hn hh)
    · exact h
  have i2 : [c, t] <:+: L := by
    rcases h2 with h | h
    · exact h
    · exact absurd h (last_no_succ hn hl)
  obtain ⟨A, B, rfl⟩ := infix_pair_iff.mp i1
  have hA : A = [] := by
    cases A with
    | nil => rfl
    | cons a A =>
      simp at hh
      subst hh
      simp at hn
  subst hA
  obtain ⟨A', B', he⟩ := infix_pair_iff.mp i2
  have e : [s] ++ c :: B = A' ++ c :: (t :: B') := by simpa using he
  obtain ⟨rfl, rfl⟩ := nodup_split_unique (by simpa using hn) e
  cases B' with
  | nil => rfl
  | cons b B' =>
    exfalso
    simp only [List.nil_append, List.getLast?_cons_cons] at hl
    have ht : t ∈ b :: B' := List.mem_of_getLast? hl
    simp at hn
    rcases List.mem_cons.mp ht with e | e
    · exact hn.2.2.1.1 e
    · exact hn.2.2.1.2 e

/-- A cell between the two endpoints of its own path closes that path after three cells. -/
theorem closure3 (hS : IsSolution J p q) {x e1 e2 : Coord} (h1 : IsEnd J e1) (h2 : IsEnd J e2)
    (h12 : e1 ≠ e2) (n1 : Nb p q x e1) (n2 : Nb p q x e2) : (pathOf p q x).length = 3 := by
  obtain ⟨s, t, hP, hst⟩ := pathOf_isPath hS x
  have m1 := (nb_mem hS n1).1
  have m2 := (nb_mem hS n2).1
  obtain ⟨m0, mt0, ms1, mt1, n2', n3'⟩ := ends_mem hS
  -- the endpoints on the path of `x` are its two ends
  have ends : ∀ e, IsEnd J e → e ∈ pathOf p q x → e = s ∨ e = t := by
    intro e he hm
    unfold IsEnd at he
    rcases hst with ⟨hpq, rfl, rfl⟩ | ⟨hpq, rfl, rfl⟩ <;> rw [hpq] at hm
    · rcases he with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hm n2'
      · exact absurd hm n3'
    · rcases he with rfl | rfl | rfl | rfl
      · exact absurd hm (hS.2.2.1 _ m0)
      · exact absurd hm (hS.2.2.1 _ mt0)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hu : Used (pathOf p q x) x s ∧ Used (pathOf p q x) x t := by
    rcases ends e1 h1 m1 with rfl | rfl <;> rcases ends e2 h2 m2 with rfl | rfl
    · exact absurd rfl h12
    · exact ⟨n1, n2⟩
    · exact ⟨n2, n1⟩
    · exact absurd rfl h12
  rw [path3 hP hu.1 hu.2]
  rfl

theorem cover_le (hS : IsSolution J p q) : J.w * J.h ≤ p.length + q.length := by
  have hsub : Finset.range J.w ×ˢ Finset.range J.h ⊆ (p ++ q).toFinset := by
    intro v hv
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hv
    rw [List.mem_toFinset, List.mem_append]
    exact hS.2.2.2 v ⟨hv.1, hv.2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at this
  have h2 := List.toFinset_card_le (p ++ q)
  rw [List.length_append] at h2
  omega

theorem both3 (hS : IsSolution J p q) {x y : Coord} (hc : colOf p x ≠ colOf p y)
    (hx : (pathOf p q x).length = 3) (hy : (pathOf p q y).length = 3) : J.w * J.h ≤ 6 := by
  have := cover_le hS
  unfold colOf at hc
  unfold pathOf at hx hy
  by_cases h1 : x ∈ p <;> by_cases h2 : y ∈ p <;> simp only [h1, h2, ↓reduceIte] at hc hx hy <;> omega

theorem five_ends {a b c d e : Coord} (ha : IsEnd J a) (hb : IsEnd J b) (hc : IsEnd J c) (hd : IsEnd J d)
    (he : IsEnd J e) (hn : [a, b, c, d, e].Nodup) : False := by
  have hsub : [a, b, c, d, e].toFinset ⊆ [J.s0, J.t0, J.s1, J.t1].toFinset := by
    intro z hz
    rw [List.mem_toFinset] at hz ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    unfold IsEnd at ha hb hc hd he
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at h1
  have h2 := List.toFinset_card_le [J.s0, J.t0, J.s1, J.t1]
  simp at h1 h2
  omega

/-! ### E1 -/

theorem edgeClosure_sound (hwf : J.WellFormed) (hS : IsSolution J p q) :
    edgeClosure (makeView J.w J.h idF (ptsOf J)) = false := by
  unfold edgeClosure
  set v := makeView J.w J.h idF (ptsOf J)
  rw [List.any_eq_false]
  intro k _ hfire
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfire
  obtain ⟨hk, hm⟩ := hfire
  cases ha : v.at 0 k with
  | none => rw [ha] at hm; simp at hm
  | some a =>
    rw [ha] at hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨⟨h2, h3⟩, h4⟩ := hm
    have h2 := beq_some h2; have h3 := beq_some h3; have h4 := beq_some h4
    obtain ⟨c1, ha1⟩ := vat_col hS ha
    obtain ⟨c2, -⟩ := vat_col hS h2
    obtain ⟨c3, -⟩ := vat_col hS h3
    obtain ⟨c4, -⟩ := vat_col hS h4
    have E1 := (vat_some hS ha).1; have E2 := (vat_some hS h2).1
    have E3 := (vat_some hS h3).1; have E4 := (vat_some hS h4).1
    have i2 := vat_inb hwf hS h2
    have i3 := vat_inb hwf hS h3
    unfold InBounds at i2 i3
    simp only at i2 i3
    have hk' : k + 3 < J.h := by simpa [v, makeView, idF, Frame.W] using hk
    have nx : ¬ IsEnd J (0, k + 1) := fun hx =>
      five_ends E1 E2 E3 E4 hx (by simp)
    have ny : ¬ IsEnd J (0, k + 2) := fun hy =>
      five_ends E1 E2 E3 E4 hy (by simp)
    obtain ⟨u, u', huu, hu, hu'⟩ := interior hS (v := (0, k + 1)) ⟨by omega, by omega⟩ nx
    obtain ⟨y, y', hyy, hy, hy'⟩ := interior hS (v := (0, k + 2)) ⟨by omega, by omega⟩ ny
    have cu := nb_col hS hu; have cu' := nb_col hS hu'
    have cy := nb_col hS hy; have cy' := nb_col hS hy'
    have mu := adj_mem (nb_adj hS hu); have mu' := adj_mem (nb_adj hS hu')
    have my := adj_mem (nb_adj hS hy); have my' := adj_mem (nb_adj hS hy')
    simp [nbrList] at mu mu' my my'
    simp only [Nat.add_assoc, Nat.reduceAdd] at mu mu' my my'
    -- colours of the two middle cells
    have colx : colOf p (0, k + 1) = a := by
      rcases mu with rfl | rfl | rfl <;> rcases mu' with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at huu <;> omega
    have coly : colOf p (0, k + 2) = 1 - a := by
      rcases my with rfl | rfl | rfl <;> rcases my' with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at hyy <;> omega
    -- the middle cells do not join, so each closes its path
    have lx : (pathOf p q (0, k + 1)).length = 3 := by
      rcases mu with rfl | rfl | rfl <;> rcases mu' with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at huu <;>
        first
          | omega
          | exact closure3 hS E2 E1 (by simp) hu hu'
          | exact closure3 hS E1 E2 (by simp) hu hu'
    have ly : (pathOf p q (0, k + 2)).length = 3 := by
      rcases my with rfl | rfl | rfl <;> rcases my' with rfl | rfl | rfl <;>
        simp only [ne_eq, not_true_eq_false] at hyy <;>
        first
          | omega
          | exact closure3 hS E4 E3 (by simp) hy hy'
          | exact closure3 hS E3 E4 (by simp) hy hy'
    have := both3 hS (x := (0, k + 1)) (y := (0, k + 2)) (by omega) lx ly
    have : 2 ≤ J.w := by omega
    nlinarith

/-! ### L1 and L6 -/

theorem pts_col (hS : IsSolution J p q) {x : Pt} (hx : x ∈ ptsOf J) : IsEnd J x.1 ∧ colOf p x.1 = x.2 := by
  obtain ⟨m0, m1, -, -, n2, n3⟩ := ends_mem hS
  unfold ptsOf at hx
  unfold IsEnd colOf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [m0, m1, n2, n3]

theorem l1_sound (hwf : J.WellFormed) (hS : IsSolution J p q) : ¬ L1Prop J.w J.h (ptsOf J) := by
  rintro ⟨x, hx, hall⟩
  obtain ⟨ex, cx⟩ := pts_col hS hx
  obtain ⟨u, hu⟩ := end_exists hS hwf ex
  have iu := nb_inb hS hu
  obtain ⟨e, he, heu, hcol⟩ := hall u iu.1 iu.2 (nb_adj hS hu)
  have := (pts_col hS he).2
  rw [heu] at this
  have := nb_col hS hu
  omega

theorem closureAt_some {pts : List Pt} {n1 n2 cor : Coord} {col : ℕ} (h : closureAt pts n1 n2 cor = some col) :
    (∃ a ∈ pts, a.1 = n1 ∧ a.2 = col) ∧ (∃ b ∈ pts, b.1 = n2 ∧ b.2 = col) ∧ ∀ x ∈ pts, x.1 ≠ cor := by
  unfold closureAt at h
  cases h1 : pts.find? (·.1 == n1) with
  | none => rw [h1] at h; simp at h
  | some a =>
    cases h2 : pts.find? (·.1 == n2) with
    | none => rw [h1, h2] at h; simp at h
    | some b =>
      rw [h1, h2] at h
      simp only at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_false] at hc
      refine ⟨⟨a, List.mem_of_find?_eq_some h1, by simpa using List.find?_some h1, h⟩,
        ⟨b, List.mem_of_find?_eq_some h2, by simpa using List.find?_some h2, hc.1 ▸ h⟩, ?_⟩
      intro x hx he
      exact absurd (by simp [he]) (hc.2 x hx)

/-- A corner closure: the corner cell is free and its two neighbours are endpoints of one colour,
so that colour's path has three cells. -/
theorem corner_closed (hS : IsSolution J p q) {n1 n2 cor : Coord} {col : ℕ}
    (h : closureAt (ptsOf J) n1 n2 cor = some col) (hcor : InBounds J.w J.h cor) (h12 : n1 ≠ n2)
    (hnb : ∀ u, Adjacent cor u → InBounds J.w J.h u → u = n1 ∨ u = n2) :
    (pathOf p q cor).length = 3 ∧ colOf p cor = col := by
  obtain ⟨⟨a, ha, ha1, ha2⟩, ⟨b, hb, hb1, hb2⟩, hfree⟩ := closureAt_some h
  obtain ⟨ea, ca⟩ := pts_col hS ha
  obtain ⟨eb, cb⟩ := pts_col hS hb
  rw [ha1] at ea ca
  rw [hb1] at eb cb
  have ne : ¬ IsEnd J cor := by
    intro he
    unfold IsEnd at he
    unfold ptsOf at hfree
    rcases he with e | e | e | e
    · exact hfree (J.s0, 0) (by simp) e.symm
    · exact hfree (J.t0, 0) (by simp) e.symm
    · exact hfree (J.s1, 1) (by simp) e.symm
    · exact hfree (J.t1, 1) (by simp) e.symm
  obtain ⟨u, x, hux, hu, hx⟩ := interior hS hcor ne
  have mu := hnb u (nb_adj hS hu) (nb_inb hS hu)
  have mx := hnb x (nb_adj hS hx) (nb_inb hS hx)
  have cu := nb_col hS hu
  rcases mu with rfl | rfl <;> rcases mx with rfl | rfl
  · exact absurd rfl hux
  · exact ⟨closure3 hS ea eb h12 hu hx, by omega⟩
  · exact ⟨closure3 hS eb ea (Ne.symm h12) hu hx, by omega⟩
  · exact absurd rfl hux

theorem l6_sound (_hwf : J.WellFormed) (hS : IsSolution J p q) (hw : 2 ≤ J.w) (hh : 2 ≤ J.h) :
    l6Fires J.w J.h (ptsOf J) = false := by
  unfold l6Fires
  rw [l6Closures_eq hw hh]
  by_contra hc
  simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hc
  obtain ⟨⟨h0, h1⟩, hbig⟩ := hc
  unfold l6List at h0 h1
  -- each corner closure closes a path
  have corner : ∀ col, col ∈ l6List J.w J.h (ptsOf J) →
      ∃ cor, (pathOf p q cor).length = 3 ∧ colOf p cor = col := by
    intro col hm
    unfold l6List at hm
    simp only [List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false, id] at hm
    obtain ⟨o, ho, hoc⟩ := hm
    have nb : ∀ (cor n1 n2 : Coord), (∀ u1 u2 : ℕ, (cor.1 = u1 ∧ (cor.2 + 1 = u2 ∨ u2 + 1 = cor.2) ∨
        cor.2 = u2 ∧ (cor.1 + 1 = u1 ∨ u1 + 1 = cor.1)) → u1 < J.w → u2 < J.h →
        (u1 = n1.1 ∧ u2 = n1.2) ∨ (u1 = n2.1 ∧ u2 = n2.2)) →
        ∀ u, Adjacent cor u → InBounds J.w J.h u → u = n1 ∨ u = n2 := by
      intro cor n1 n2 H u hu hi
      obtain ⟨u1, u2⟩ := u
      unfold Adjacent at hu; unfold InBounds at hi
      rcases H u1 u2 hu hi.1 hi.2 with h | h
      · left; exact Prod.ext h.1 h.2
      · right; exact Prod.ext h.1 h.2
    rcases ho with rfl | rfl | rfl | rfl
    · exact ⟨_, corner_closed hS hoc ⟨by omega, by omega⟩ (by simp)
        (nb _ _ _ (fun u1 u2 h h1 h2 => by simp only at h ⊢; omega))⟩
    · exact ⟨_, corner_closed hS hoc ⟨by omega, by omega⟩ (by simp)
        (nb _ _ _ (fun u1 u2 h h1 h2 => by simp only at h ⊢; omega))⟩
    · exact ⟨_, corner_closed hS hoc ⟨by omega, by omega⟩ (by simp)
        (nb _ _ _ (fun u1 u2 h h1 h2 => by simp only at h ⊢; omega))⟩
    · exact ⟨_, corner_closed hS hoc ⟨by omega, by omega⟩ (by simp; omega)
        (nb _ _ _ (fun u1 u2 h h1 h2 => by simp only at h ⊢; omega))⟩
  obtain ⟨c0, l0, k0⟩ := corner 0 (by unfold l6List; exact h0)
  obtain ⟨c1, l1, k1⟩ := corner 1 (by unfold l6List; exact h1)
  have := both3 hS (x := c0) (y := c1) (by omega) l0 l1
  omega

end Sol






end ZZN
