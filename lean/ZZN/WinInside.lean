-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinRuns
import ZZN.Splice

/-!
# Window certificates: the inside DP is sound

After processing cells `0 … i−1` (row-major), some DP state lists exactly the end pairs of the
runs of the solution paths in the processed cells.
-/

namespace ZZN.Win

open GridHam

/-! ### Row-major order -/

theorem idx_lex {b : ℕ} {x y : Coord} (hx : x.2 < b) (hy : y.2 < b) :
    y.1 * b + y.2 < x.1 * b + x.2 ↔ y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 < x.2) := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy y.1 x.1 with c | c | c
    · exact Or.inl c
    · right; refine ⟨c, ?_⟩; rw [c] at h; omega
    · exfalso
      have : (x.1 + 1) * b ≤ y.1 * b := Nat.mul_le_mul_right _ c
      rw [Nat.add_mul, one_mul] at this; omega
  · rintro (c | ⟨c, d⟩)
    · have : (y.1 + 1) * b ≤ x.1 * b := Nat.mul_le_mul_right _ c
      rw [Nat.add_mul, one_mul] at this; omega
    · rw [c]; omega

theorem idx_inj {b : ℕ} {x y : Coord} (hx : x.2 < b) (hy : y.2 < b) (h : y.1 * b + y.2 = x.1 * b + x.2) :
    y = x := by
  have h1 := (idx_lex hx hy).not.mp (by omega)
  have h2 := (idx_lex hy hx).not.mp (by omega)
  obtain ⟨y1, y2⟩ := y; obtain ⟨x1, x2⟩ := x
  simp only [Prod.mk.injEq] at *; omega

/-- Cells processed after `i` steps. -/
def prI (a b i : ℕ) (y : Coord) : Prop := y.1 < a ∧ y.2 < b ∧ y.1 * b + y.2 < i

instance (a b i : ℕ) : DecidablePred (prI a b i) := fun y => by unfold prI; infer_instance

theorem cell_spec {a b i : ℕ} (hi : i < a * b) :
    (cell b i).1 < a ∧ (cell b i).2 < b ∧ (cell b i).1 * b + (cell b i).2 = i := by
  have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  unfold cell
  refine ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi), Nat.mod_lt _ hb, ?_⟩
  have := Nat.div_add_mod i b
  rw [Nat.mul_comm] at this; exact this

/-- Processed cells, in lexicographic form. -/
theorem prI_lex {a b i : ℕ} (hi : i < a * b) {y : Coord} :
    prI a b i y ↔ y.1 < a ∧ y.2 < b ∧ (y.1 < (cell b i).1 ∨ (y.1 = (cell b i).1 ∧ y.2 < (cell b i).2)) := by
  obtain ⟨c1, c2, c3⟩ := cell_spec hi
  unfold prI
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (idx_lex c2 h2).mp (by omega)⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by have := (idx_lex c2 h2).mpr h3; omega⟩

theorem prI_succ {a b i : ℕ} (hi : i < a * b) {y : Coord} :
    prI a b (i + 1) y ↔ prI a b i y ∨ y = cell b i := by
  obtain ⟨c1, c2, c3⟩ := cell_spec hi
  unfold prI
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases Nat.lt_or_ge (y.1 * b + y.2) i with d | d
    · exact Or.inl ⟨h1, h2, d⟩
    · exact Or.inr (idx_inj c2 h2 (by omega))
  · rintro (⟨h1, h2, h3⟩ | rfl)
    · exact ⟨h1, h2, by omega⟩
    · exact ⟨c1, c2, by omega⟩

theorem prI_all {a b : ℕ} {y : Coord} : prI a b (a * b) y ↔ y.1 < a ∧ y.2 < b := by
  unfold prI
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    have : (y.1 + 1) * b ≤ a * b := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, one_mul] at this; omega

/-! ### Boundary edges and their end codes -/

/-- The end code of the edge from processed `u` to unprocessed `v` (down or right). -/
def desc (a b : ℕ) (u v : Coord) : ℕ :=
  if v = (u.1 + 1, u.2) then (if u.1 + 1 < a then u.2 else exitE b (a + (b - 1 - u.2)))
  else (if u.2 + 1 < b then b else exitE b u.1)

/-- An unprocessed neighbour of a processed cell is below it or to its right. -/
theorem bd_dir {a b i : ℕ} {u v : Coord} (hu : prI a b i u) (hv : ¬ prI a b i v) (h : Adjacent u v) :
    v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  unfold Adjacent at h
  simp only at h ⊢
  simp only [Prod.mk.injEq]
  rcases h with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
  · right; omega
  · exfalso; apply hv; obtain ⟨h1, h2, h3⟩ := hu; exact ⟨h1, by simp only at h2 ⊢; omega, by simp only at h3 ⊢; omega⟩
  · left; omega
  · exfalso; apply hv; obtain ⟨h1, h2, h3⟩ := hu
    refine ⟨by simp only at h1 ⊢; omega, h2, ?_⟩
    simp only at h3 ⊢
    have : v1 * b ≤ u1 * b := Nat.mul_le_mul_right _ (by omega)
    omega

theorem desc_down {a b : ℕ} {u : Coord} : desc a b u (u.1 + 1, u.2) =
    if u.1 + 1 < a then u.2 else exitE b (a + (b - 1 - u.2)) := by
  unfold desc; rw [ite_eq_left rfl]

theorem desc_right {a b : ℕ} {u : Coord} : desc a b u (u.1, u.2 + 1) =
    if u.2 + 1 < b then b else exitE b u.1 := by
  unfold desc; rw [ite_eq_right (by simp)]

/-- End codes of boundary edges are below the endpoint codes. -/
theorem desc_lt {a b i : ℕ} {u v : Coord} (hu : prI a b i u) (hv : ¬ prI a b i v) (h : Adjacent u v) :
    desc a b u v < a + 2 * b + 1 := by
  obtain ⟨h1, h2, h3⟩ := hu
  rcases bd_dir ⟨h1, h2, h3⟩ hv h with rfl | rfl
  · rw [desc_down]; unfold exitE; split_ifs <;> omega
  · rw [desc_right]; unfold exitE; split_ifs <;> omega

/-- **The end code of a boundary edge determines the edge.** -/
theorem desc_inj {a b i : ℕ} (_hi : i ≤ a * b) {u v u' v' : Coord}
    (hu : prI a b i u) (hv : ¬ prI a b i v) (h : Adjacent u v)
    (hu' : prI a b i u') (hv' : ¬ prI a b i v') (h' : Adjacent u' v')
    (he : desc a b u v = desc a b u' v') : u = u' ∧ v = v' := by
  have d := bd_dir hu hv h
  have d' := bd_dir hu' hv' h'
  obtain ⟨u1, u2⟩ := u; obtain ⟨u1', u2'⟩ := u'
  obtain ⟨a1, a2, a3⟩ := hu
  obtain ⟨b1, b2, b3⟩ := hu'
  simp only at a1 a2 a3 b1 b2 b3 d d'
  -- unprocessed means: outside the window or not before step i
  have nv := fun (w1 w2 : ℕ) (hw : ¬ prI a b i (w1, w2)) (q1 : w1 < a) (q2 : w2 < b) =>
    (by unfold prI at hw; simp only at hw; omega : i ≤ w1 * b + w2)
  have key : ∀ r r' : ℕ, r < r' → r * b + b ≤ r' * b := fun r r' h => by
    have := Nat.mul_le_mul_right b (show r + 1 ≤ r' from h); rw [Nat.add_mul, one_mul] at this; omega
  rcases d with rfl | rfl <;> rcases d' with rfl | rfl
  · rw [desc_down, desc_down] at he
    simp only [Prod.mk.injEq]
    unfold exitE at he
    split_ifs at he with c1 c2 c2
    · subst he
      have e1 := nv _ _ hv c1 a2
      have e2 := nv _ _ hv' c2 b2
      rcases Nat.lt_trichotomy u1 u1' with c | c | c
      · have := key _ _ c; rw [Nat.add_mul, one_mul] at e1; omega
      · omega
      · have := key _ _ c; rw [Nat.add_mul, one_mul] at e2; omega
    · omega
    · omega
    · omega
  · rw [desc_down, desc_right] at he
    unfold exitE at he
    split_ifs at he <;> omega
  · rw [desc_right, desc_down] at he
    unfold exitE at he
    split_ifs at he <;> omega
  · rw [desc_right, desc_right] at he
    simp only [Prod.mk.injEq]
    unfold exitE at he
    split_ifs at he with c1 c2 c2
    · have e1 := nv _ _ hv a1 c1
      have e2 := nv _ _ hv' b1 c2
      have : u1 * b + u2 = u1' * b + u2' := by omega
      have := idx_inj (x := (u1, u2)) (y := (u1', u2')) a2 b2 this.symm
      simp only [Prod.mk.injEq] at this; omega
    · omega
    · omega
    · omega

/-! ### Piece codes -/

theorem mkP_lo {x y : ℕ} (hx : x < 32) (hy : y < 32) : lo (mkP x y) = min x y := by
  unfold lo mkP; split_ifs with h <;> omega

theorem mkP_hi {x y : ℕ} (hx : x < 32) (hy : y < 32) : hi (mkP x y) = max x y := by
  unfold hi mkP; split_ifs with h <;> omega

theorem hasEnd_mkP {e x y : ℕ} (hx : x < 32) (hy : y < 32) : hasEnd e (mkP x y) = true ↔ x = e ∨ y = e := by
  unfold hasEnd
  rw [mkP_lo hx hy, mkP_hi hx hy]
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

theorem other_mkP_l {x y : ℕ} (hx : x < 32) (hy : y < 32) : other x (mkP x y) = y := by
  unfold other; rw [mkP_lo hx hy, mkP_hi hx hy]; split_ifs with h <;> simp at h <;> omega

theorem other_mkP_r {x y : ℕ} (hx : x < 32) (hy : y < 32) : other y (mkP x y) = x := by
  unfold other; rw [mkP_lo hx hy, mkP_hi hx hy]; split_ifs with h <;> simp at h <;> omega

theorem mkP_inj {x y x' y' : ℕ} (hx : x < 32) (hy : y < 32) (hx' : x' < 32) (hy' : y' < 32)
    (h : mkP x y = mkP x' y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have h1 := mkP_lo hx hy; have h2 := mkP_hi hx hy
  rw [h, mkP_lo hx' hy'] at h1; rw [h, mkP_hi hx' hy'] at h2
  omega

theorem mkP_comm (x y : ℕ) : mkP x y = mkP y x := by
  unfold mkP; split_ifs <;> omega

/-! ### Paths -/

theorem adj_symm {u v : Coord} (h : Adjacent u v) : Adjacent v u := by
  unfold Adjacent at *; omega

theorem chain_nth : ∀ {L : List Coord}, chainAdjacent L = true → ∀ {j : ℕ}, j + 1 < L.length →
    Adjacent (nth L j) (nth L (j + 1))
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | x :: y :: L, hc, j, h => by
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    cases j with
    | zero => exact (adjacentB_iff x y).mp hc.1
    | succ j =>
      have := chain_nth hc.2 (j := j) (by simp at h ⊢; omega)
      simpa [nth] using this

/-! ### Run ends -/

def endL (a b col : ℕ) (L : List Coord) (st : ℕ) : ℕ :=
  if st = 0 then termE a b col else desc a b (nth L st) (nth L (st - 1))

def endR (a b col : ℕ) (L : List Coord) (en : ℕ) : ℕ :=
  if en + 1 = L.length then termE a b col else desc a b (nth L en) (nth L (en + 1))

def runCode (a b col : ℕ) (L : List Coord) (st en : ℕ) : ℕ := mkP (endL a b col L st) (endR a b col L en)

section Ends

variable {a b i : ℕ} {L : List Coord} {st en : ℕ}

theorem endL_bd (hc : chainAdjacent L = true) (h : IsRun (prI a b i) L st en) (h0 : st ≠ 0) :
    prI a b i (nth L st) ∧ ¬ prI a b i (nth L (st - 1)) ∧ Adjacent (nth L st) (nth L (st - 1)) := by
  refine ⟨h.all st (le_refl _) h.le, h.left.resolve_left h0, ?_⟩
  have := chain_nth hc (j := st - 1) (by have := h.lt; have := h.le; omega)
  rw [show st - 1 + 1 = st by omega] at this
  exact adj_symm this

theorem endR_bd (hc : chainAdjacent L = true) (h : IsRun (prI a b i) L st en) (h0 : en + 1 ≠ L.length) :
    prI a b i (nth L en) ∧ ¬ prI a b i (nth L (en + 1)) ∧ Adjacent (nth L en) (nth L (en + 1)) :=
  ⟨h.all en h.le (le_refl _), h.right.resolve_left h0, chain_nth hc (by have := h.lt; omega)⟩

/-- End codes: an endpoint code exactly at the path's ends, a boundary code below them otherwise. -/
theorem endL_cases (hc : chainAdjacent L = true) (h : IsRun (prI a b i) L st en) (col : ℕ) :
    (st = 0 ∧ endL a b col L st = termE a b col) ∨
      (st ≠ 0 ∧ endL a b col L st = desc a b (nth L st) (nth L (st - 1)) ∧
        endL a b col L st < a + 2 * b + 1) := by
  unfold endL
  by_cases h0 : st = 0
  · exact Or.inl ⟨h0, ite_eq_left h0⟩
  · obtain ⟨b1, b2, b3⟩ := endL_bd hc h h0
    exact Or.inr ⟨h0, ite_eq_right h0, by rw [ite_eq_right h0]; exact desc_lt b1 b2 b3⟩

theorem endR_cases (hc : chainAdjacent L = true) (h : IsRun (prI a b i) L st en) (col : ℕ) :
    (en + 1 = L.length ∧ endR a b col L en = termE a b col) ∨
      (en + 1 ≠ L.length ∧ endR a b col L en = desc a b (nth L en) (nth L (en + 1)) ∧
        endR a b col L en < a + 2 * b + 1) := by
  unfold endR
  by_cases h0 : en + 1 = L.length
  · exact Or.inl ⟨h0, ite_eq_left h0⟩
  · obtain ⟨b1, b2, b3⟩ := endR_bd hc h h0
    exact Or.inr ⟨h0, ite_eq_right h0, by rw [ite_eq_right h0]; exact desc_lt b1 b2 b3⟩

end Ends

/-! ### The solution's runs -/

section Sol

variable {a b : ℕ} {J : Inst} {p q : List Coord}

/-- The two solution paths with their colours. -/
def PathC (p q : List Coord) (L : List Coord) (col : ℕ) : Prop := (L = p ∧ col = 0) ∨ (L = q ∧ col = 1)

theorem pathC_facts (hS : IsSolution J p q) {L : List Coord} {col : ℕ} (h : PathC p q L col) :
    L.Nodup ∧ chainAdjacent L = true ∧ col ≤ 1 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hS.1.2.2.1, hS.1.2.2.2.2, by omega⟩
  · exact ⟨hS.2.1.2.2.1, hS.2.1.2.2.2.2, by omega⟩

/-- A cell lies on at most one of the two paths. -/
theorem pathC_same (hS : IsSolution J p q) {L L' : List Coord} {col col' : ℕ} (h : PathC p q L col)
    (h' : PathC p q L' col') {x : Coord} (hx : x ∈ L) (hx' : x ∈ L') : L = L' ∧ col = col' := by
  have hd := hS.2.2.1
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd hx' (hd x hx)
  · exact absurd hx (hd x hx')
  · exact ⟨rfl, rfl⟩

/-- **A boundary end determines its run**: two runs (of either path) sharing a non-endpoint end
code are the same run, and the end is on the same side. -/
theorem end_unique (hS : IsSolution J p q) {i : ℕ} (hi : i ≤ a * b)
    {L L' : List Coord} {col col' : ℕ} (hL : PathC p q L col) (hL' : PathC p q L' col')
    {st en st' en' : ℕ} (h : IsRun (prI a b i) L st en) (h' : IsRun (prI a b i) L' st' en')
    {x y : Coord} {x' y' : Coord}
    (hx : (st ≠ 0 ∧ x = nth L st ∧ y = nth L (st - 1)) ∨ (en + 1 ≠ L.length ∧ x = nth L en ∧ y = nth L (en + 1)))
    (hx' : (st' ≠ 0 ∧ x' = nth L' st' ∧ y' = nth L' (st' - 1)) ∨
      (en' + 1 ≠ L'.length ∧ x' = nth L' en' ∧ y' = nth L' (en' + 1)))
    (he : desc a b x y = desc a b x' y') :
    L = L' ∧ col = col' ∧ st = st' ∧ en = en' ∧
      ((st ≠ 0 ∧ x = nth L st ∧ y = nth L (st - 1) ∧ st' ≠ 0 ∧ x' = nth L' st' ∧ y' = nth L' (st' - 1)) ∨
       (en + 1 ≠ L.length ∧ x = nth L en ∧ y = nth L (en + 1) ∧
         en' + 1 ≠ L'.length ∧ x' = nth L' en' ∧ y' = nth L' (en' + 1))) := by
  obtain ⟨n, c, -⟩ := pathC_facts hS hL
  obtain ⟨n', c', -⟩ := pathC_facts hS hL'
  have hlt := h.lt; have hle := h.le; have hlt' := h'.lt; have hle' := h'.le
  -- the boundary edges
  have bd : prI a b i x ∧ ¬ prI a b i y ∧ Adjacent x y := by
    rcases hx with ⟨h0, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩
    · exact endL_bd c h h0
    · exact endR_bd c h h0
  have bd' : prI a b i x' ∧ ¬ prI a b i y' ∧ Adjacent x' y' := by
    rcases hx' with ⟨h0, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩
    · exact endL_bd c' h' h0
    · exact endR_bd c' h' h0
  obtain ⟨ex, ey⟩ := desc_inj hi bd.1 bd.2.1 bd.2.2 bd'.1 bd'.2.1 bd'.2.2 he
  subst ex; subst ey
  -- the same cell `x` on both paths
  have xm : x ∈ L := by rcases hx with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> exact nth_mem (by omega)
  have xm' : x ∈ L' := by rcases hx' with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> exact nth_mem (by omega)
  obtain ⟨rfl, rfl⟩ := pathC_same hS hL hL' xm xm'
  -- positions
  have ne1 : ∀ j k, j < L.length → k < L.length → nth L j = nth L k → j = k := fun j k hj hk e => nth_inj n hj hk e
  rcases hx with ⟨h0, ex, ey⟩ | ⟨h0, ex, ey⟩ <;> rcases hx' with ⟨h0', ex', ey'⟩ | ⟨h0', ex', ey'⟩
  · have e1 := ne1 st st' (by omega) (by omega) (ex.symm.trans ex')
    obtain ⟨u1, u2⟩ := run_unique h h' (le_refl _) hle (by omega) (by omega)
    exact ⟨rfl, rfl, u1, u2, Or.inl ⟨h0, ex, ey, h0', ex', ey'⟩⟩
  · have e1 := ne1 st en' (by omega) (by omega) (ex.symm.trans ex')
    have e2 := ne1 (st - 1) (en' + 1) (by omega) (by omega) (ey.symm.trans ey')
    omega
  · have e1 := ne1 en st' (by omega) (by omega) (ex.symm.trans ex')
    have e2 := ne1 (en + 1) (st' - 1) (by omega) (by omega) (ey.symm.trans ey')
    omega
  · have e1 := ne1 en en' (by omega) (by omega) (ex.symm.trans ex')
    obtain ⟨u1, u2⟩ := run_unique h h' hle (le_refl _) (by omega) (by omega)
    exact ⟨rfl, rfl, u1, u2, Or.inr ⟨h0, ex, ey, h0', ex', ey'⟩⟩

end Sol

/-! ### Boundary edges at the current cell -/

section Cur

variable {a b i : ℕ} {x1 x2 : ℕ}
  (hlex : ∀ y : Coord, prI a b i y ↔ y.1 < a ∧ y.2 < b ∧ (y.1 < x1 ∨ (y.1 = x1 ∧ y.2 < x2)))
  (hx1 : x1 < a) (hx2 : x2 < b)
include hlex hx1 hx2

omit hx1 in
/-- The plug end of column `x2` is the edge from the cell above `x` into `x`. -/
theorem bd_plug {u v : Coord} (hu : prI a b i u) (hv : ¬ prI a b i v) (h : Adjacent u v)
    (hd : desc a b u v = x2) :
    0 < x1 ∧ u = (x1 - 1, x2) ∧ v = (x1, x2) := by
  have dir := bd_dir hu hv h
  rw [hlex] at hu hv
  obtain ⟨u1, u2⟩ := u
  dsimp only at hu hv
  rcases dir with rfl | rfl
  · rw [desc_down] at hd
    unfold exitE at hd
    dsimp only at hd hv ⊢
    split_ifs at hd with c
    · refine ⟨by omega, ?_, ?_⟩ <;> simp only [Prod.mk.injEq] <;> omega
    · omega
  · rw [desc_right] at hd
    unfold exitE at hd
    dsimp only at hd
    split_ifs at hd <;> omega

omit hx1 hx2 in
/-- A left-plug end (code `b`) is the edge from the cell left of `x` into `x`. -/
theorem bd_left {u v : Coord} (hu : prI a b i u) (hv : ¬ prI a b i v) (h : Adjacent u v)
    (hd : desc a b u v = b) :
    0 < x2 ∧ u = (x1, x2 - 1) ∧ v = (x1, x2) := by
  have dir := bd_dir hu hv h
  rw [hlex] at hu hv
  obtain ⟨u1, u2⟩ := u
  dsimp only at hu hv
  rcases dir with rfl | rfl
  · rw [desc_down] at hd
    unfold exitE at hd
    dsimp only at hd
    split_ifs at hd <;> omega
  · rw [desc_right] at hd
    unfold exitE at hd
    dsimp only at hd hv ⊢
    split_ifs at hd with c
    · refine ⟨by omega, ?_, ?_⟩ <;> simp only [Prod.mk.injEq] <;> omega
    · omega

/-- The processed neighbours of the current cell are the cells above and to the left. -/
theorem nb_proc {y : Coord} (h : Adjacent (x1, x2) y) :
    prI a b i y ↔ (0 < x1 ∧ y = (x1 - 1, x2)) ∨ (0 < x2 ∧ y = (x1, x2 - 1)) := by
  rw [hlex]
  obtain ⟨y1, y2⟩ := y
  unfold Adjacent at h
  simp only [Prod.mk.injEq] at *
  omega

omit hlex hx2 in
theorem desc_up (h0 : 0 < x1) : desc a b (x1 - 1, x2) (x1, x2) = x2 := by
  have e : ((x1, x2) : Coord) = ((x1 - 1) + 1, x2) := by congr; omega
  rw [e, desc_down]; simp only; rw [ite_eq_left (by omega)]

omit hlex hx1 in
theorem desc_lft (h0 : 0 < x2) : desc a b (x1, x2 - 1) (x1, x2) = b := by
  have e : ((x1, x2) : Coord) = (x1, (x2 - 1) + 1) := by congr; omega
  rw [e, desc_right]; simp only; rw [ite_eq_left (by omega)]

end Cur

/-! ### The abstract state -/

section Abs

variable {a b : ℕ} {J : Inst} {p q : List Coord}

def Piece (a b i : ℕ) (p q : List Coord) (z : ℕ) : Prop :=
  ∃ L col st en, PathC p q L col ∧ IsRun (prI a b i) L st en ∧ ¬ (st = 0 ∧ en + 1 = L.length) ∧
    z = runCode a b col L st en

def doneMask (a b i : ℕ) (p q : List Coord) : ℕ :=
  (if ∀ y ∈ p, prI a b i y then 1 else 0) + (if ∀ y ∈ q, prI a b i y then 2 else 0)

def Inv (a b i : ℕ) (p q : List Coord) (s : St) : Prop :=
  s.1.Nodup ∧ (∀ z, z ∈ s.1 ↔ Piece a b i p q z) ∧ s.2 = doneMask a b i p q

theorem end_lt32 (ha : a ≤ 8) (hb : b ≤ 8) {i : ℕ} {L : List Coord} {st en col : ℕ} (hcol : col ≤ 1)
    (hc : chainAdjacent L = true) (h : IsRun (prI a b i) L st en) :
    endL a b col L st < 32 ∧ endR a b col L en < 32 := by
  constructor
  · rcases endL_cases hc h col with ⟨-, e⟩ | ⟨-, -, e⟩
    · rw [e]; unfold termE; omega
    · omega
  · rcases endR_cases hc h col with ⟨-, e⟩ | ⟨-, -, e⟩
    · rw [e]; unfold termE; omega
    · omega

/-- **Codes of incomplete runs determine the run.** -/
theorem code_inj (hS : IsSolution J p q) (ha : a ≤ 8) (hb : b ≤ 8) {i : ℕ} (hi : i ≤ a * b)
    {L L' : List Coord} {col col' st en st' en' : ℕ} (hL : PathC p q L col) (hL' : PathC p q L' col')
    (h : IsRun (prI a b i) L st en) (h' : IsRun (prI a b i) L' st' en')
    (hn : ¬ (st = 0 ∧ en + 1 = L.length)) (_hn' : ¬ (st' = 0 ∧ en' + 1 = L'.length))
    (he : runCode a b col L st en = runCode a b col' L' st' en') :
    L = L' ∧ col = col' ∧ st = st' ∧ en = en' := by
  obtain ⟨-, c, hc⟩ := pathC_facts hS hL
  obtain ⟨-, c', hc'⟩ := pathC_facts hS hL'
  obtain ⟨b1, b2⟩ := end_lt32 ha hb hc c h
  obtain ⟨b1', b2'⟩ := end_lt32 ha hb hc' c' h'
  have T := fun (x : ℕ) => (show termE a b x = a + 2 * b + 1 + x from rfl)
  have kL := endL_cases c h col
  have kR := endR_cases c h col
  have kL' := endL_cases c' h' col'
  have kR' := endR_cases c' h' col'
  unfold runCode at he
  rcases mkP_inj b1 b2 b1' b2' he with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · by_cases h0 : st = 0
    · have h1 : en + 1 ≠ L.length := fun e => hn ⟨h0, e⟩
      rcases kR with ⟨c1, -⟩ | ⟨-, d1, l1⟩
      · exact absurd c1 h1
      rcases kR' with ⟨c2, d2⟩ | ⟨c2, d2, -⟩
      · rw [e2, d2, T] at l1; omega
      obtain ⟨r1, r2, r3, r4, -⟩ := end_unique hS hi hL hL' h h' (Or.inr ⟨h1, rfl, rfl⟩) (Or.inr ⟨c2, rfl, rfl⟩) (by rw [← d1, ← d2, e2])
      exact ⟨r1, r2, r3, r4⟩
    · rcases kL with ⟨c1, -⟩ | ⟨-, d1, l1⟩
      · exact absurd c1 h0
      rcases kL' with ⟨c2, d2⟩ | ⟨c2, d2, -⟩
      · rw [e1, d2, T] at l1; omega
      obtain ⟨r1, r2, r3, r4, -⟩ := end_unique hS hi hL hL' h h' (Or.inl ⟨h0, rfl, rfl⟩) (Or.inl ⟨c2, rfl, rfl⟩) (by rw [← d1, ← d2, e1])
      exact ⟨r1, r2, r3, r4⟩
  · by_cases h0 : st = 0
    · have h1 : en + 1 ≠ L.length := fun e => hn ⟨h0, e⟩
      rcases kR with ⟨c1, -⟩ | ⟨-, d1, l1⟩
      · exact absurd c1 h1
      rcases kL' with ⟨c2, d2⟩ | ⟨c2, d2, -⟩
      · rw [e2, d2, T] at l1; omega
      obtain ⟨r1, r2, r3, r4, -⟩ := end_unique hS hi hL hL' h h' (Or.inr ⟨h1, rfl, rfl⟩) (Or.inl ⟨c2, rfl, rfl⟩) (by rw [← d1, ← d2, e2])
      exact ⟨r1, r2, r3, r4⟩
    · rcases kL with ⟨c1, -⟩ | ⟨-, d1, l1⟩
      · exact absurd c1 h0
      rcases kR' with ⟨c2, d2⟩ | ⟨c2, d2, -⟩
      · rw [e1, d2, T] at l1; omega
      obtain ⟨r1, r2, r3, r4, -⟩ := end_unique hS hi hL hL' h h' (Or.inl ⟨h0, rfl, rfl⟩) (Or.inr ⟨c2, rfl, rfl⟩) (by rw [← d1, ← d2, e1])
      exact ⟨r1, r2, r3, r4⟩

end Abs

end ZZN.Win
