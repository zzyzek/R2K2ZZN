-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.SoundR

/-!
# Soundness of the R entry: assembly

From `effAlt3 = true` and a solution, build two disjoint doubled chains whose perimeter ends
alternate, contradicting `Planar.t1_core`.
-/

namespace ZZN

open GridHam

theorem good0 {I : Inst} (hI : InDom I) : Good I.w I.h ⟨ptsOf I, [], false⟩ := by
  obtain ⟨hw, hh, b0, b1, b2, b3, d1, d2, d3, d4, d5, d6⟩ := hI
  refine ⟨?_, ?_⟩
  · simp only [ptsOf, cellsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    exact ⟨⟨d1, d2, d3⟩, ⟨d4, d5⟩, d6, by simp, List.nodup_nil⟩
  · intro q hq
    simp only [ptsOf, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact b0
    · exact b1
    · exact b2
    · exact b3

/-! ### Positions along a rotated, sorted list -/

section Gen

variable {α : Type} [BEq α] [LawfulBEq α]

theorem idxOf_app_mem {x : α} : ∀ {l1 : List α} (l2 : List α), x ∈ l1 → (l1 ++ l2).idxOf x = l1.idxOf x
  | [], _, h => by simp at h
  | a :: l1, l2, h => by
    by_cases ha : a = x
    · subst ha; simp [List.idxOf_cons_self]
    · have : x ∈ l1 := by rcases List.mem_cons.mp h with e | e; exact absurd e.symm ha; exact e
      rw [List.cons_append, List.idxOf_cons_ne _ ha, List.idxOf_cons_ne _ ha, idxOf_app_mem l2 this]

theorem idxOf_app_not_mem {x : α} : ∀ {l1 : List α} (l2 : List α), x ∉ l1 →
    (l1 ++ l2).idxOf x = l1.length + l2.idxOf x
  | [], _, _ => by simp
  | a :: l1, l2, h => by
    have ha : a ≠ x := fun e => h (e ▸ List.mem_cons_self)
    have : x ∉ l1 := fun e => h (List.mem_cons_of_mem _ e)
    rw [List.cons_append, List.idxOf_cons_ne _ ha, idxOf_app_not_mem l2 this, List.length_cons]
    omega

theorem idxOf_inj' {L : List α} {x y : α} (hx : x ∈ L) (hy : y ∈ L) (h : L.idxOf x = L.idxOf y) : x = y := by
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hx)
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hy)
  simp only [h] at h1
  exact h1.symm.trans h2

theorem idx_rot {X Y : List α} (hn : (X ++ Y).Nodup) {x : α} (hx : x ∈ X ++ Y) :
    (Y ++ X).idxOf x = rotK X.length (X ++ Y).length ((X ++ Y).idxOf x) := by
  unfold rotK
  rw [List.length_append]
  by_cases hX : x ∈ X
  · have hY : x ∉ Y := fun hy => (List.nodup_append.mp hn).2.2 x hX x hy rfl
    rw [idxOf_app_mem _ hX, idxOf_app_not_mem _ hY]
    have := List.idxOf_lt_length_iff.mpr hX
    rw [ite_eq_left this]; omega
  · rw [idxOf_app_not_mem _ hX]
    have hY : x ∈ Y := by
      rcases List.mem_append.mp hx with h | h
      · exact absurd h hX
      · exact h
    rw [idxOf_app_mem _ hY]
    rw [ite_eq_right (by omega)]; omega

theorem idx_lt_pw {L : List α} {f : α → ℕ} (h : L.Pairwise (fun a b => f a < f b))
    {x y : α} (hx : x ∈ L) (hy : y ∈ L) : L.idxOf x < L.idxOf y ↔ f x < f y := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rw [List.pairwise_cons] at h
    by_cases hax : a = x <;> by_cases hay : a = y
    · subst hax; subst hay; simp
    · subst hax
      have hy' : y ∈ L := by rcases List.mem_cons.mp hy with e | e; exact absurd e.symm hay; exact e
      simp only [List.idxOf_cons_self, List.idxOf_cons_ne _ hay]
      have := h.1 y hy'
      constructor
      · intro _; exact this
      · intro _; omega
    · subst hay
      have hx' : x ∈ L := by rcases List.mem_cons.mp hx with e | e; exact absurd e.symm hax; exact e
      simp only [List.idxOf_cons_self, List.idxOf_cons_ne _ hax]
      have := h.1 x hx'
      constructor
      · intro h'; omega
      · intro h'; omega
    · have hx' : x ∈ L := by rcases List.mem_cons.mp hx with e | e; exact absurd e.symm hax; exact e
      have hy' : y ∈ L := by rcases List.mem_cons.mp hy with e | e; exact absurd e.symm hay; exact e
      simp only [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hay]
      rw [← ih h.2 hx' hy']
      omega

omit [BEq α] [LawfulBEq α] in
theorem pw_nodup {L : List α} {f : α → ℕ} (h : L.Pairwise (fun a b => f a < f b)) : L.Nodup :=
  h.imp fun hab e => by rw [e] at hab; exact lt_irrefl _ hab

/-- **Crossing of positions in a list is crossing of keys, when a rotation of the list is sorted
by key.** -/
theorem crosses_walk {X Y : List α} {f : α → ℕ} (hs : (Y ++ X).Pairwise (fun a b => f a < f b))
    {e0 e1 e2 e3 : α} (m0 : e0 ∈ X ++ Y) (m1 : e1 ∈ X ++ Y) (m2 : e2 ∈ X ++ Y) (m3 : e3 ∈ X ++ Y)
    (d01 : e0 ≠ e1) (d02 : e0 ≠ e2) (d03 : e0 ≠ e3) (d12 : e1 ≠ e2) (d13 : e1 ≠ e3) (d23 : e2 ≠ e3) :
    Crosses ((X ++ Y).idxOf e0) ((X ++ Y).idxOf e1) ((X ++ Y).idxOf e2) ((X ++ Y).idxOf e3) ↔
      Crosses (f e0) (f e1) (f e2) (f e3) := by
  have hn' := pw_nodup hs
  have hn : (X ++ Y).Nodup := List.nodup_append_comm.mp hn'
  have m' := fun {e : α} (h : e ∈ X ++ Y) => (List.mem_append.mpr ((List.mem_append.mp h).symm) : e ∈ Y ++ X)
  have lt := fun {e : α} (h : e ∈ X ++ Y) => List.idxOf_lt_length_iff.mpr h
  have ne := fun {a b : α} (ha : a ∈ X ++ Y) (hb : b ∈ X ++ Y) (hab : a ≠ b) =>
    (fun e => hab (idxOf_inj' ha hb e) : (X ++ Y).idxOf a ≠ (X ++ Y).idxOf b)
  rw [← crosses_rot (m := X.length) (by simp) (lt m0) (lt m1) (lt m2) (lt m3) (ne m0 m1 d01) (ne m0 m2 d02)
    (ne m0 m3 d03) (ne m1 m2 d12) (ne m1 m3 d13) (ne m2 m3 d23)]
  rw [← idx_rot hn m0, ← idx_rot hn m1, ← idx_rot hn m2, ← idx_rot hn m3]
  have i := fun {a b : α} (ha : a ∈ X ++ Y) (hb : b ∈ X ++ Y) => idx_lt_pw hs (m' ha) (m' hb)
  exact crosses_congr (i m0 m2) (i m2 m0) (i m1 m2) (i m2 m1) (i m0 m3) (i m3 m0) (i m1 m3) (i m3 m1)

end Gen

theorem idxOf_map_fst {x : Coord} : ∀ {L : List (Coord × List Coord)} {e : Coord × List Coord},
    (L.map Prod.fst).count x = 1 → e ∈ L → e.1 = x → (L.map Prod.fst).idxOf x = L.idxOf e
  | [], _, _, h, _ => by simp at h
  | a :: L, e, hc, he, hx => by
    by_cases hae : a = e
    · subst hae; subst hx; simp [List.idxOf_cons_self]
    · have he' : e ∈ L := by rcases List.mem_cons.mp he with h | h; exact absurd h.symm hae; exact h
      have hax : a.1 ≠ x := by
        intro h
        rw [List.map_cons, List.count_cons, h] at hc
        have : 0 < (L.map Prod.fst).count x := List.count_pos_iff.mpr (List.mem_map.mpr ⟨e, he', hx⟩)
        simp at hc; omega
      rw [List.map_cons, List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hae]
      rw [List.map_cons, List.count_cons] at hc
      simp [hax] at hc
      rw [idxOf_map_fst hc he' hx]

/-! ### The planar contradiction -/

theorem crosses_swap01 {k0 k1 k2 k3 : ℕ} : Crosses k0 k1 k2 k3 ↔ Crosses k1 k0 k2 k3 := by
  unfold Crosses; constructor <;> intro h <;> omega

/-- `t1_core`, with the two ends of `A` in either order and strict between-ness. -/
theorem t1_use {R C : ℕ} (hR : 2 ≤ R) (hC : 2 ≤ C) {A Q : List (ℕ × ℕ)}
    (hAc : chainAdjacent A = true) (hQc : chainAdjacent Q = true)
    (hAin : ∀ v ∈ A, v.1 < R ∧ v.2 < C) (hQin : ∀ v ∈ Q, v.1 < R ∧ v.2 < C)
    (hdis : ∀ v ∈ A, v ∉ Q) {xh xl c d : ℕ × ℕ}
    (hAh : A.head? = some xh) (hAl : A.getLast? = some xl)
    (hQh : Q.head? = some c) (hQl : Q.getLast? = some d)
    (pxh : OnPerim R C xh) (pxl : OnPerim R C xl) (pc : OnPerim R C c) (pd : OnPerim R C d)
    (n1 : Planar.anc R C xh ≠ Planar.anc R C xl) (n2 : Planar.anc R C c ≠ Planar.anc R C xh)
    (n3 : Planar.anc R C c ≠ Planar.anc R C xl) (n4 : Planar.anc R C d ≠ Planar.anc R C xh)
    (n5 : Planar.anc R C d ≠ Planar.anc R C xl) :
    ¬ Crosses (Planar.anc R C xh) (Planar.anc R C xl) (Planar.anc R C c) (Planar.anc R C d) := by
  intro hx
  unfold Crosses at hx
  rcases Nat.lt_or_gt_of_ne n1 with h | h
  · have := Planar.t1_core hR hC (chainAdjacent_reverse _ hAc) hQc (fun v hv => hAin v (List.mem_reverse.mp hv))
      hQin (fun v hv => hdis v (List.mem_reverse.mp hv)) (by rw [List.head?_reverse]; exact hAl)
      (by rw [List.getLast?_reverse]; exact hAh) hQh hQl pxl pxh pc pd h
    split_ifs at this <;> omega
  · have := Planar.t1_core hR hC hAc hQc hAin hQin hdis hAh hAl hQh hQl pxh pxl pc pd h
    split_ifs at this <;> omega

theorem chain_glue : ∀ {l : List Coord} {x : Coord} {m : List Coord}, chainAdjacent l = true →
    l.getLast? = some x → chainAdjacent (x :: m) = true → chainAdjacent (l ++ m) = true
  | [], _, _, _, h, _ => by simp at h
  | [a], x, m, _, h, hm => by simp at h; subst h; exact hm
  | a :: b :: l, x, m, hc, h, hm => by
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    rw [List.getLast?_cons_cons] at h
    have := chain_glue hc.2 h hm
    simp only [List.cons_append] at this ⊢
    rw [chainAdjacent_cons_cons, Bool.and_eq_true]
    exact ⟨hc.1, this⟩

theorem glue_last {l m : List Coord} {x y : Coord} (hl : l.getLast? = some x) (hm : (x :: m).getLast? = some y) :
    (l ++ m).getLast? = some y := by
  cases m with
  | nil => simp at hm; subst hm; simpa using hl
  | cons z m =>
    rw [List.getLast?_append, List.getLast?_cons_cons] at *
    simp only [List.getLast?_cons] at hm ⊢
    simpa using hm

/-- The doubled chain of a cut path with the exits of its two ends. -/
theorem chain_of_exits {R C : ℕ} {rem : List Coord} {P : List Coord} {ea eb : Coord × List Coord}
    (oa : ExitOK R C rem ea.1 ea.2) (ob : ExitOK R C rem eb.1 eb.2) (hPc : chainAdjacent P = true)
    (hPh : P.head? = some ea.1) (hPl : P.getLast? = some eb.1) :
    let A := ea.2.reverse ++ (dpN P).tail ++ eb.2.tail
    chainAdjacent A = true ∧ A.head? = some (ea.2.getLastD (dd ea.1)) ∧
      A.getLast? = some (eb.2.getLastD (dd eb.1)) ∧
      ∀ v ∈ A, v ∈ ea.2 ∨ v ∈ dpN P ∨ v ∈ eb.2 := by
  intro A
  obtain ⟨xa, la⟩ := ea
  obtain ⟨xb, lb⟩ := eb
  simp only [A] at *
  clear A
  obtain ⟨P0, rfl⟩ : ∃ P0, P = xa :: P0 := by
    cases P with
    | nil => simp at hPh
    | cons z P0 => simp at hPh; exact ⟨P0, by rw [hPh]⟩
  obtain ⟨T, hT⟩ := dpN_head xa P0
  have hdl := dpN_last xa P0
  have hPl' : P0.getLastD xa = xb := by simpa [List.getLast?_cons] using hPl
  rw [hPl', hT] at hdl
  obtain ⟨ha, hac, -, -, -, -, -⟩ := oa
  obtain ⟨hb, hbc, -, -, -, -, -⟩ := ob
  obtain ⟨X, rfl⟩ : ∃ X, la = dd xa :: X := by
    cases la with
    | nil => simp at ha
    | cons z X => simp at ha; exact ⟨X, by rw [ha]⟩
  obtain ⟨Z, rfl⟩ : ∃ Z, lb = dd xb :: Z := by
    cases lb with
    | nil => simp at hb
    | cons z Z => simp at hb; exact ⟨Z, by rw [hb]⟩
  have hrl : (dd xa :: X).reverse.getLast? = some (dd xa) := by simp [List.getLast?_reverse]
  have c1 : chainAdjacent ((dd xa :: X).reverse ++ T) = true :=
    chain_glue (chainAdjacent_reverse _ hac) hrl (hT ▸ dpN_chain _ hPc)
  have l1 : ((dd xa :: X).reverse ++ T).getLast? = some (dd xb) := glue_last hrl hdl
  have c2 : chainAdjacent ((dd xa :: X).reverse ++ T ++ Z) = true := chain_glue c1 l1 hbc
  have l2 : ((dd xa :: X).reverse ++ T ++ Z).getLast? = some (Z.getLastD (dd xb)) :=
    glue_last l1 (by simp [List.getLast?_cons])
  rw [hT]
  simp only [List.tail_cons, List.getLastD_cons]
  refine ⟨c2, ?_, l2, ?_⟩
  · simp [List.head?_append]
  · intro v hv
    simp only [List.mem_append, List.mem_reverse] at hv
    rcases hv with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
    · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

/-- **No crossing**: two disjoint cut paths, joined to the perimeter by the exits of their end
cells, cannot have crossing exit keys. -/
theorem no_cross {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {rem : List Coord} {S1 S2 S3 S4 : List Coord}
    (h1 : CornerShape R C rem false false S1) (h2 : CornerShape R C rem false true S2)
    (h3 : CornerShape R C rem true true S3) (h4 : CornerShape R C rem true false S4)
    {ea eb ec ed : Coord × List Coord} (ma : ea ∈ walkP R C S1 S2 S3 S4) (mb : eb ∈ walkP R C S1 S2 S3 S4)
    (mc : ec ∈ walkP R C S1 S2 S3 S4) (md : ed ∈ walkP R C S1 S2 S3 S4)
    (ra : ea.1 ∉ rem) (rb : eb.1 ∉ rem) (rc : ec.1 ∉ rem) (rd : ed.1 ∉ rem)
    {P Q : List Coord} (hPc : chainAdjacent P = true) (hQc : chainAdjacent Q = true)
    (hPb : ∀ v ∈ P, v.1 < R ∧ v.2 < C) (hQb : ∀ v ∈ Q, v.1 < R ∧ v.2 < C) (hPQ : ∀ v ∈ P, v ∉ Q)
    (hPr : ∀ v ∈ P, v ∉ rem) (hQr : ∀ v ∈ Q, v ∉ rem)
    (hPh : P.head? = some ea.1) (hPl : P.getLast? = some eb.1)
    (hQh : Q.head? = some ec.1) (hQl : Q.getLast? = some ed.1)
    (n1 : κ R C ea ≠ κ R C eb) (n2 : κ R C ec ≠ κ R C ea) (n3 : κ R C ec ≠ κ R C eb)
    (n4 : κ R C ed ≠ κ R C ea) (n5 : κ R C ed ≠ κ R C eb) :
    ¬ Crosses (κ R C ea) (κ R C eb) (κ R C ec) (κ R C ed) := by
  have oa := walkP_ok hR hC h1 h2 h3 h4 ma
  have ob := walkP_ok hR hC h1 h2 h3 h4 mb
  have oc := walkP_ok hR hC h1 h2 h3 h4 mc
  have od := walkP_ok hR hC h1 h2 h3 h4 md
  obtain ⟨cA, hA, lA, mA⟩ := chain_of_exits oa ob hPc hPh hPl
  obtain ⟨cB, hB, lB, mB⟩ := chain_of_exits oc od hQc hQh hQl
  have pa : ea.1 ∈ P := List.mem_of_mem_head? hPh
  have pb : eb.1 ∈ P := List.mem_of_getLast? hPl
  have qc : ec.1 ∈ Q := List.mem_of_mem_head? hQh
  have qd : ed.1 ∈ Q := List.mem_of_getLast? hQl
  have nPc : ec.1 ∉ P := fun h => hPQ _ h qc
  have nPd : ed.1 ∉ P := fun h => hPQ _ h qd
  have dac : ea.1 ≠ ec.1 := fun e => hPQ _ pa (e ▸ qc)
  have dad : ea.1 ≠ ed.1 := fun e => hPQ _ pa (e ▸ qd)
  have dbc : eb.1 ≠ ec.1 := fun e => hPQ _ pb (e ▸ qc)
  have dbd : eb.1 ≠ ed.1 := fun e => hPQ _ pb (e ▸ qd)
  have ex := fun {e e' : Coord × List Coord} (m : e ∈ walkP R C S1 S2 S3 S4) (m' : e' ∈ walkP R C S1 S2 S3 S4)
    (d : e.1 ≠ e'.1) (r : e.1 ∉ rem) (r' : e'.1 ∉ rem) => exits_disj hR hC h1 h2 h3 h4 m m' d r r'
  have dPb := dpN_inb hPb hPc
  have dQb := dpN_inb hQb hQc
  refine t1_use (R := 2 * R - 1) (C := 2 * C - 1) (by omega) (by omega) cA cB ?_ ?_ ?_ hA lA hB lB
    oa.2.2.2.2.1 ob.2.2.2.2.1 oc.2.2.2.2.1 od.2.2.2.2.1 n1 n2 n3 n4 n5
  · intro v hv
    rcases mA v hv with h | h | h
    · exact oa.2.2.1 v h
    · exact dPb v h
    · exact ob.2.2.1 v h
  · intro v hv
    rcases mB v hv with h | h | h
    · exact oc.2.2.1 v h
    · exact dQb v h
    · exact od.2.2.1 v h
  · intro v hv hv'
    rcases mA v hv with h | h | h <;> rcases mB v hv' with h' | h' | h'
    · exact ex ma mc dac ra rc v h h'
    · exact safe_not_dpN hQc (fun e => hPQ _ pa e) hQr (oa.2.2.2.1 v h) h'
    · exact ex ma md dad ra rd v h h'
    · exact safe_not_dpN hPc nPc hPr (oc.2.2.2.1 v h') h
    · exact dpN_disj hPc hQc hPQ h h'
    · exact safe_not_dpN hPc nPd hPr (od.2.2.2.1 v h') h
    · exact ex mb mc dbc rb rc v h h'
    · exact safe_not_dpN hQc (fun e => hPQ _ pb e) hQr (ob.2.2.2.1 v h) h'
    · exact ex mb md dbd rb rd v h h'

theorem crosses_swap23 {k0 k1 k2 k3 : ℕ} : Crosses k0 k1 k2 k3 ↔ Crosses k0 k1 k3 k2 := by
  unfold Crosses; constructor <;> intro h <;> omega

theorem chain_pre : ∀ (l1 l2 : List Coord), chainAdjacent (l1 ++ l2) = true → chainAdjacent l1 = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: l, l2, h => by
    simp only [List.cons_append] at h
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, chain_pre (b :: l) l2 (by simpa using h.2)⟩

theorem chain_infix {P L : List Coord} (h : P <:+: L) (hc : chainAdjacent L = true) : chainAdjacent P = true := by
  obtain ⟨s, t, rfl⟩ := h
  exact chainAdjacent_suffix s P (chain_pre (s ++ P) t hc)

theorem kappa_ne {L : List (Coord × List Coord)} {f : Coord × List Coord → ℕ}
    (hs : L.Pairwise (fun a b => f a < f b)) {e e' : Coord × List Coord} (he : e ∈ L) (he' : e' ∈ L)
    (hne : e ≠ e') : f e ≠ f e' := by
  intro hf
  have hi : L.idxOf e ≠ L.idxOf e' := fun h => hne (idxOf_inj' he he' h)
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · have := (idx_lt_pw hs he he').mp h; rw [hf] at this; exact lt_irrefl _ this
  · have := (idx_lt_pw hs he' he).mp h; rw [hf] at this; exact lt_irrefl _ this

/-- **R soundness**: on a solvable instance of the domain, the R entry never fires. -/
theorem r_sound (I : Inst) (hI : InDom I) (hS : Solvable I) : effAlt3 I.w I.h (ptsOf I) = false := by
  by_contra hne
  have h : effAlt3 I.w I.h (ptsOf I) = true := by simpa using hne
  obtain ⟨p, q, sol⟩ := hS
  have hw := hI.1
  have hh := hI.2.1
  have wf := hI.2.2
  have g0 := good0 hI
  obtain ⟨heff, hrem, hKw, hMw, -⟩ := rewriteAll_closed (by omega) (by omega) g0
  have heff' : (rewriteAll I.w I.h (ptsOf I)).eff =
      [(effI I I.s0, 0), (effI I I.t0, 0), (effI I I.s1, 1), (effI I I.t1, 1)] := by
    rw [heff]; rfl
  have hRS : RemShape I.w I.h (rewriteAll I.w I.h (ptsOf I)).removed := remShape_rewriteAll hw hh g0 rfl
  have hrm : ∀ x, x ∈ (rewriteAll I.w I.h (ptsOf I)).removed ↔ RmI I x := hrem
  rw [effAlt3_eq] at h
  unfold effAltFrom at h
  rw [heff'] at h
  simp only [List.any_cons, List.any_nil, List.map_cons, List.map_nil, Bool.or_false] at h
  split_ifs at h with c1 c2 c3 c4
  generalize (rewriteAll I.w I.h (ptsOf I)).removed = rem at hRS hrm c2 c4 h
  simp at c2 c3 c4
  obtain ⟨c2a, c2b, c2c, c2d⟩ := c2
  -- the four effective cells are distinct
  have nd : [effI I I.s0, effI I I.t0, effI I I.s1, effI I I.t1].Nodup := by
    have hsub := List.dedup_sublist [effI I I.s0, effI I I.t0, effI I I.s1, effI I I.t1]
    have := hsub.eq_of_length (by rw [c3]; rfl)
    rw [← this]; exact List.nodup_dedup _
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
  obtain ⟨⟨d01, d02, d03⟩, ⟨d12, d13⟩, d23, -, -⟩ := nd
  rw [positions_length, positions_length, positions_length, positions_length] at c4
  obtain ⟨k0, k1, k2, k3⟩ := c4
  -- the corner shapes, and the walk with its exits
  obtain ⟨S1, h1⟩ := hRS.2 false false
  obtain ⟨S2, h2⟩ := hRS.2 false true
  obtain ⟨S3, h3⟩ := hRS.2 true true
  obtain ⟨S4, h4⟩ := hRS.2 true false
  have hW := walkP_fst hw hh hRS h1 h2 h3 h4
  obtain ⟨X, Y, hXY, hs⟩ := walkP_sorted hw hh h1.1 h2.1 h3.1 h4.1
  rw [← hW] at h k0 k1 k2 k3
  have entry : ∀ x, ((walkP I.w I.h S1 S2 S3 S4).map Prod.fst).count x = 1 →
      ∃ e ∈ walkP I.w I.h S1 S2 S3 S4, e.1 = x ∧
        (positions ((walkP I.w I.h S1 S2 S3 S4).map Prod.fst) x).headD 0 = (walkP I.w I.h S1 S2 S3 S4).idxOf e := by
    intro x hc
    have hx : x ∈ (walkP I.w I.h S1 S2 S3 S4).map Prod.fst := List.count_pos_iff.mp (by omega)
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact ⟨e, he, rfl, by rw [positions_head hx, idxOf_map_fst hc he rfl]⟩
  obtain ⟨ea, ma, fa, ia⟩ := entry _ k0
  obtain ⟨eb, mb, fb, ib⟩ := entry _ k1
  obtain ⟨ec, mc, fc, ic⟩ := entry _ k2
  obtain ⟨ed, md, fd, idd⟩ := entry _ k3
  rw [ia, ib, ic, idd] at h
  have ne : ∀ {e e' : Coord × List Coord} {x y : Coord}, e.1 = x → e'.1 = y → x ≠ y → e ≠ e' := by
    intro e e' x y hx hy hxy he; apply hxy; rw [← hx, ← hy, he]
  have nab := ne fa fb d01
  have nac := ne fa fc d02
  have nad := ne fa fd d03
  have nbc := ne fb fc d12
  have nbd := ne fb fd d13
  have ncd := ne fc fd d23
  have ine := fun {e e' : Coord × List Coord} (m : e ∈ walkP I.w I.h S1 S2 S3 S4) (m' : e' ∈ walkP I.w I.h S1 S2 S3 S4)
    (hne : e ≠ e') => (fun h => hne (idxOf_inj' m m' h) :
      (walkP I.w I.h S1 S2 S3 S4).idxOf e ≠ (walkP I.w I.h S1 S2 S3 S4).idxOf e')
  have hc := (alt_cross (ine ma mb nab) (ine ma mc nac) (ine ma md nad) (ine mb mc nbc) (ine mb md nbd)
    (ine mc md ncd)).mp h
  -- crossing of positions is crossing of exit keys
  have m' := fun {e : Coord × List Coord} (m : e ∈ walkP I.w I.h S1 S2 S3 S4) => (hXY ▸ m : e ∈ X ++ Y)
  rw [hXY] at hc
  have hk := (crosses_walk (f := κ I.w I.h) hs (m' ma) (m' mb) (m' mc) (m' md) nab nac nad nbc nbd ncd).mp hc
  have kn := fun {e e' : Coord × List Coord} (m : e ∈ walkP I.w I.h S1 S2 S3 S4) (m2 : e' ∈ walkP I.w I.h S1 S2 S3 S4)
    (hne : e ≠ e') => kappa_ne hs (List.mem_append.mpr ((List.mem_append.mp (m' m)).symm))
      (List.mem_append.mpr ((List.mem_append.mp (m' m2)).symm)) hne
  -- the standing hypotheses, and the two cut paths
  have H : RHyp I p q := ⟨wf, sol, hw, hh, hKw, hMw, fun E hE r => by
    rcases hE with rfl | rfl | rfl | rfl
    · exact c2a ((hrm _).mpr r)
    · exact c2b ((hrm _).mpr r)
    · exact c2c ((hrm _).mpr r)
    · exact c2d ((hrm _).mpr r)⟩
  obtain ⟨-, -, -, -, w1, w2, w3, w4, w5, w6⟩ := wf
  obtain ⟨m0, m1, m2, m3, n2, n3⟩ := ends_mem sol
  have po0 : pathOf p q I.s0 = p := by unfold pathOf; simp [m0]
  have po1 : pathOf p q I.t0 = p := by unfold pathOf; simp [m1]
  have po2 : pathOf p q I.s1 = q := by unfold pathOf; simp [n2]
  have po3 : pathOf p q I.t1 = q := by unfold pathOf; simp [n3]
  have hos0 : orient p q I.s0 = p := by unfold orient; rw [po0, ite_eq_left sol.1.1]
  have hot0 : orient p q I.t0 = p.reverse := by
    unfold orient; rw [po1, ite_eq_right (fun e => w1 (Option.some.inj (sol.1.1.symm.trans e)))]
  have hos1 : orient p q I.s1 = q := by unfold orient; rw [po2, ite_eq_left sol.2.1.1]
  have hot1 : orient p q I.t1 = q.reverse := by
    unfold orient; rw [po3, ite_eq_right (fun e => w6 (Option.some.inj (sol.2.1.1.symm.trans e)))]
  have cs0 : colOf p I.s0 = 0 := by unfold colOf; simp [m0]
  have ct0 : colOf p I.t0 = 0 := by unfold colOf; simp [m1]
  have cs1 : colOf p I.s1 = 1 := by unfold colOf; simp [n2]
  have ct1 : colOf p I.t1 = 1 := by unfold colOf; simp [n3]
  have inP := fun {E v : Coord} (hE : IsEnd I E) (hv : v ∈ orient p q E) => ((orient_facts sol hE).2.2.1 v).mp hv
  obtain ⟨P, hPi, hPr, hPe⟩ := path_trim H sol.1 hos0 hot0 (Or.inl rfl) (Or.inr (Or.inl rfl))
    (fun E hE hc => by
      rcases hE with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rw [cs1, cs0] at hc; exact absurd hc (by decide)
      · rw [ct1, cs0] at hc; exact absurd hc (by decide))
    (by rw [ct0, cs0]) w1
    (fun E hE hc v hv => by
      have hv' := inP hE hv
      rcases hE with rfl | rfl | rfl | rfl
      · exact absurd rfl hc
      · exact absurd (by rw [ct0, cs0]) hc
      · rw [po2] at hv'; exact fun hp => sol.2.2.1 v hp hv'
      · rw [po3] at hv'; exact fun hp => sol.2.2.1 v hp hv')
    d01
  obtain ⟨Q, hQi, hQr, hQe⟩ := path_trim H sol.2.1 hos1 hot1 (Or.inr (Or.inr (Or.inl rfl)))
    (Or.inr (Or.inr (Or.inr rfl)))
    (fun E hE hc => by
      rcases hE with rfl | rfl | rfl | rfl
      · rw [cs0, cs1] at hc; exact absurd hc (by decide)
      · rw [ct0, cs1] at hc; exact absurd hc (by decide)
      · exact Or.inl rfl
      · exact Or.inr rfl)
    (by rw [ct1, cs1]) w6
    (fun E hE hc v hv => by
      have hv' := inP hE hv
      rcases hE with rfl | rfl | rfl | rfl
      · rw [po0] at hv'; exact sol.2.2.1 v hv'
      · rw [po1] at hv'; exact sol.2.2.1 v hv'
      · exact absurd rfl hc
      · exact absurd (by rw [ct1, cs1]) hc)
    d23
  have hPc := chain_infix hPi sol.1.2.2.2.2
  have hQc := chain_infix hQi sol.2.1.2.2.2.2
  have hPb : ∀ v ∈ P, v.1 < I.w ∧ v.2 < I.h := fun v hv => sol.1.2.2.2.1 v (hPi.subset hv)
  have hQb : ∀ v ∈ Q, v.1 < I.w ∧ v.2 < I.h := fun v hv => sol.2.1.2.2.2.1 v (hQi.subset hv)
  have hPQ : ∀ v ∈ P, v ∉ Q := fun v hv hvQ => sol.2.2.1 v (hPi.subset hv) (hQi.subset hvQ)
  have hPr' : ∀ v ∈ P, v ∉ rem := fun v hv hr => hPr v hv ((hrm v).mp hr)
  have hQr' : ∀ v ∈ Q, v ∉ rem := fun v hv hr => hQr v hv ((hrm v).mp hr)
  have ra : ea.1 ∉ rem := by rw [fa]; exact c2a
  have rb : eb.1 ∉ rem := by rw [fb]; exact c2b
  have rc : ec.1 ∉ rem := by rw [fc]; exact c2c
  have rd : ed.1 ∉ rem := by rw [fd]; exact c2d
  rw [← fa, ← fb] at hPe
  rw [← fc, ← fd] at hQe
  have nc := fun {e1 e2 e3 e4 : Coord × List Coord} (m1 : e1 ∈ walkP I.w I.h S1 S2 S3 S4)
    (m2 : e2 ∈ walkP I.w I.h S1 S2 S3 S4) (m3 : e3 ∈ walkP I.w I.h S1 S2 S3 S4)
    (m4 : e4 ∈ walkP I.w I.h S1 S2 S3 S4) (r1 : e1.1 ∉ rem) (r2 : e2.1 ∉ rem) (r3 : e3.1 ∉ rem)
    (r4 : e4.1 ∉ rem) (ph : P.head? = some e1.1) (pl : P.getLast? = some e2.1)
    (qh : Q.head? = some e3.1) (ql : Q.getLast? = some e4.1) (n12 : e1 ≠ e2) (n31 : e3 ≠ e1) (n32 : e3 ≠ e2)
    (n41 : e4 ≠ e1) (n42 : e4 ≠ e2) =>
    no_cross hw hh h1 h2 h3 h4 m1 m2 m3 m4 r1 r2 r3 r4 hPc hQc hPb hQb hPQ hPr' hQr' ph pl qh ql
      (kn m1 m2 n12) (kn m3 m1 n31) (kn m3 m2 n32) (kn m4 m1 n41) (kn m4 m2 n42)
  rcases hPe with ⟨ph, pl⟩ | ⟨ph, pl⟩ <;> rcases hQe with ⟨qh, ql⟩ | ⟨qh, ql⟩
  · exact nc ma mb mc md ra rb rc rd ph pl qh ql nab nac.symm nbc.symm nad.symm nbd.symm hk
  · exact nc ma mb md mc ra rb rd rc ph pl qh ql nab nad.symm nbd.symm nac.symm nbc.symm
      (crosses_swap23.mp hk)
  · exact nc mb ma mc md rb ra rc rd ph pl qh ql nab.symm nbc.symm nac.symm nbd.symm nad.symm
      (crosses_swap01.mp hk)
  · exact nc mb ma md mc rb ra rd rc ph pl qh ql nab.symm nbd.symm nad.symm nbc.symm nac.symm
      (crosses_swap23.mp (crosses_swap01.mp hk))


/-- **Theorem B**, with R proved: only the window entries B, C, D remain as hypotheses. -/
theorem theoremB_R (F : BFacts) {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=
  theoremB F r_sound hI hS

end ZZN
