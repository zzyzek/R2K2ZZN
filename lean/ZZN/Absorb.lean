-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Stretch

/-!
# Absorbing the inserted cells

State during the band-extension construction: two paths on the widened grid that cover every
cell except the two new cells `(r+1, y), (r+2, y)` of each column `y ∈ U` (`PState`). A column
`y` has an available *middle edge* if a path uses the edge `(r+1, y) – (r+2, y)` (`Mid`).

* `absorb`: an uncovered column next to a column with a middle edge is covered by a U-shaped
  detour of that middle edge; the new column then has a middle edge.
* `flip`: two adjacent uncovered columns `y, y+1`, with the edge `(r, y) – (r, y+1)` used, are
  covered by a detour of that edge; both then have middle edges.
* `sweepLeft` / `sweepRight`: repeated absorption from a column with a middle edge outward.
-/

namespace ZZN

open GridHam

/-! ### Edges after a splice -/

theorem infix_pair_append {A B : List Coord} {u v : Coord} (h : [u, v] <:+: A ++ B) :
    [u, v] <:+: A ∨ [u, v] <:+: B ∨ (A.getLast? = some u ∧ B.head? = some v) := by
  obtain ⟨s, t, he⟩ := infix_pair_iff.mp h
  rcases List.append_eq_append_iff.mp he with ⟨a', -, hB⟩ | ⟨c', hA, hc⟩
  · exact Or.inr (Or.inl (infix_pair_iff.mpr ⟨a', t, hB⟩))
  · rcases c' with _ | ⟨x, _ | ⟨y, c''⟩⟩
    · simp only [List.nil_append] at hc
      exact Or.inr (Or.inl (infix_pair_iff.mpr ⟨[], t, by rw [← hc]; rfl⟩))
    · simp only [List.singleton_append, List.cons.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hA]; simp
      · rw [← hc]; simp
    · simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, rfl, -⟩ := hc
      exact Or.inl (infix_pair_iff.mpr ⟨s, c'', hA⟩)

/-- Edges other than the replaced one survive a splice. -/
theorem infix_splice_of_ne {l₁ l₂ X : List Coord} {a b u v : Coord}
    (h : [u, v] <:+: l₁ ++ a :: b :: l₂) (hne : ¬(u = a ∧ v = b)) :
    [u, v] <:+: l₁ ++ a :: (X ++ b :: l₂) := by
  have e1 : l₁ ++ a :: b :: l₂ = (l₁ ++ [a]) ++ (b :: l₂) := by simp
  have e2 : l₁ ++ a :: (X ++ b :: l₂) = (l₁ ++ [a]) ++ (X ++ b :: l₂) := by simp
  rw [e1] at h
  rw [e2]
  rcases infix_pair_append h with h | h | ⟨h1, h2⟩
  · exact h.trans (List.prefix_append _ _).isInfix
  · exact h.trans ⟨(l₁ ++ [a]) ++ X, [], by simp⟩
  · simp at h1 h2
    exact absurd ⟨h1.symm, h2.symm⟩ hne

/-- The inserted list appears in the spliced path. -/
theorem infix_splice_self (l₁ l₂ X : List Coord) (a b : Coord) :
    X <:+: l₁ ++ a :: (X ++ b :: l₂) :=
  ⟨l₁ ++ [a], b :: l₂, by simp⟩

/-- One-path splice with the bookkeeping the construction needs. -/
theorem splice_edge {w h : ℕ} {s t : Coord} {L X : List Coord} {a b : Coord}
    (hL : IsPath w h s t L) (hab : [a, b] <:+: L)
    (hX : chainAdjacent (a :: (X ++ [b])) = true) (hXn : X.Nodup)
    (hXb : ∀ x ∈ X, InBounds w h x) (hfresh : ∀ x ∈ X, x ∉ L) :
    ∃ L', IsPath w h s t L' ∧ (∀ v, v ∈ L' ↔ v ∈ L ∨ v ∈ X) ∧
      (∀ u v, [u, v] <:+: L → ¬(u = a ∧ v = b) → [u, v] <:+: L') ∧ X <:+: L' := by
  obtain ⟨l₁, l₂, rfl⟩ := infix_pair_iff.mp hab
  refine ⟨l₁ ++ a :: (X ++ b :: l₂), hL.splice hX hXn hXb hfresh, fun v => mem_splice _ _ _ _ _ _,
    fun u v huv hne => infix_splice_of_ne huv hne, infix_splice_self _ _ _ _ _⟩

/-! ### The state -/

/-- Cell `v` is one of the inserted cells of a column in `U`. -/
def Uncov (r : ℕ) (U : Finset ℕ) (v : Coord) : Prop := (v.1 = r + 1 ∨ v.1 = r + 2) ∧ v.2 ∈ U

/-- Two paths on the `W × h` grid, with the given endpoints, covering exactly the cells that are
not `Uncov r U`. -/
structure PState (W h r : ℕ) (s0 t0 s1 t1 : Coord) (U : Finset ℕ) (P Q : List Coord) : Prop where
  pp   : IsPath W h s0 t0 P
  pq   : IsPath W h s1 t1 Q
  disj : ∀ v ∈ P, v ∉ Q
  cov  : ∀ v, InBounds W h v → ¬ Uncov r U v → v ∈ P ∨ v ∈ Q
  unc  : ∀ v, Uncov r U v → v ∉ P ∧ v ∉ Q
  Ub   : ∀ y ∈ U, y < h
  rb   : r + 2 < W

/-- Column `y` has an available middle edge. -/
def Mid (r : ℕ) (P Q : List Coord) (y : ℕ) : Prop :=
  Used P (r + 1, y) (r + 2, y) ∨ Used Q (r + 1, y) (r + 2, y)

/-- Splicing the fresh cells `X` into the edge `a – b` of `P` or of `Q`: the generic step. -/
theorem PState.splice {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U U' : Finset ℕ} {P Q X : List Coord}
    {a b : Coord} (st : PState W h r s0 t0 s1 t1 U P Q)
    (hab : [a, b] <:+: P ∨ [a, b] <:+: Q)
    (hX : chainAdjacent (a :: (X ++ [b])) = true) (hXn : X.Nodup)
    (hXU : ∀ v, v ∈ X ↔ Uncov r U v ∧ ¬ Uncov r U' v)
    (hU' : U' ⊆ U) :
    ∃ P' Q', PState W h r s0 t0 s1 t1 U' P' Q' ∧ (X <:+: P' ∨ X <:+: Q') ∧
      (∀ u v, ¬(u = a ∧ v = b) → ¬(u = b ∧ v = a) →
        Used P u v ∨ Used Q u v → Used P' u v ∨ Used Q' u v) := by
  have hXb : ∀ x ∈ X, InBounds W h x := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, -⟩ := (hXU x).mp hx
    have := st.Ub _ h2
    have := st.rb
    unfold InBounds; omega
  have hXP : ∀ x ∈ X, x ∉ P := fun x hx => (st.unc x ((hXU x).mp hx).1).1
  have hXQ : ∀ x ∈ X, x ∉ Q := fun x hx => (st.unc x ((hXU x).mp hx).1).2
  -- membership facts shared by both cases
  have uncU : ∀ v, Uncov r U' v → Uncov r U v := fun v ⟨h1, h2⟩ => ⟨h1, hU' h2⟩
  rcases hab with hab | hab
  · obtain ⟨P', hP', hmem, hkeep, hXin⟩ := splice_edge st.pp hab hX hXn hXb hXP
    refine ⟨P', Q, ⟨hP', st.pq, ?_, ?_, ?_, fun y hy => st.Ub y (hU' hy), st.rb⟩, Or.inl hXin, ?_⟩
    · intro v hv hq
      rcases (hmem v).mp hv with h | h
      · exact st.disj v h hq
      · exact hXQ v h hq
    · intro v hv hn
      by_cases hu : Uncov r U v
      · exact Or.inl ((hmem v).mpr (Or.inr ((hXU v).mpr ⟨hu, hn⟩)))
      · rcases st.cov v hv hu with h | h
        · exact Or.inl ((hmem v).mpr (Or.inl h))
        · exact Or.inr h
    · intro v hv
      refine ⟨fun h => ?_, (st.unc v (uncU v hv)).2⟩
      rcases (hmem v).mp h with h | h
      · exact (st.unc v (uncU v hv)).1 h
      · exact ((hXU v).mp h).2 hv
    · intro u v hne hne' huv
      rcases huv with (h | h) | h
      · exact Or.inl (Or.inl (hkeep u v h hne))
      · exact Or.inl (Or.inr (hkeep v u h (fun ⟨h1, h2⟩ => hne' ⟨h2, h1⟩)))
      · exact Or.inr h
  · obtain ⟨Q', hQ', hmem, hkeep, hXin⟩ := splice_edge st.pq hab hX hXn hXb hXQ
    refine ⟨P, Q', ⟨st.pp, hQ', ?_, ?_, ?_, fun y hy => st.Ub y (hU' hy), st.rb⟩, Or.inr hXin, ?_⟩
    · intro v hv hq
      rcases (hmem v).mp hq with h | h
      · exact st.disj v hv h
      · exact hXP v h hv
    · intro v hv hn
      by_cases hu : Uncov r U v
      · exact Or.inr ((hmem v).mpr (Or.inr ((hXU v).mpr ⟨hu, hn⟩)))
      · rcases st.cov v hv hu with h | h
        · exact Or.inl h
        · exact Or.inr ((hmem v).mpr (Or.inl h))
    · intro v hv
      refine ⟨(st.unc v (uncU v hv)).1, fun h => ?_⟩
      rcases (hmem v).mp h with h | h
      · exact (st.unc v (uncU v hv)).2 h
      · exact ((hXU v).mp h).2 hv
    · intro u v hne hne' huv
      rcases huv with h | (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (hkeep u v h hne))
      · exact Or.inr (Or.inr (hkeep v u h (fun ⟨h1, h2⟩ => hne' ⟨h2, h1⟩)))

/-! ### Absorb and flip -/

theorem used_of_infix_sub {X L : List Coord} {u v : Coord} (h1 : [u, v] <:+: X) (h2 : X <:+: L) :
    [u, v] <:+: L := h1.trans h2

theorem mid_of_X {r : ℕ} {P Q X : List Coord} {y : ℕ} (hX : X <:+: P ∨ X <:+: Q)
    (h : [(r + 1, y), (r + 2, y)] <:+: X ∨ [(r + 2, y), (r + 1, y)] <:+: X) : Mid r P Q y := by
  unfold Mid Used
  rcases hX with hX | hX <;> rcases h with h | h
  · exact Or.inl (Or.inl (h.trans hX))
  · exact Or.inl (Or.inr (h.trans hX))
  · exact Or.inr (Or.inl (h.trans hX))
  · exact Or.inr (Or.inr (h.trans hX))

theorem uncov_erase_iff {r : ℕ} {U : Finset ℕ} {y : ℕ} (hy : y ∈ U) (v : Coord) :
    (Uncov r U v ∧ ¬ Uncov r (U.erase y) v) ↔ (v = (r + 1, y) ∨ v = (r + 2, y)) := by
  obtain ⟨v1, v2⟩ := v
  simp only [Uncov, Finset.mem_erase, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have : v2 = y := by
      by_contra hne
      exact h3 ⟨h1, hne, h2⟩
    subst this
    rcases h1 with h1 | h1
    · exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr ⟨h1, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨Or.inl rfl, hy⟩, fun ⟨_, h, _⟩ => h rfl⟩
    · exact ⟨⟨Or.inr rfl, hy⟩, fun ⟨_, h, _⟩ => h rfl⟩

theorem uncov_erase2_iff {r : ℕ} {U : Finset ℕ} {y : ℕ} (hy : y ∈ U) (hy1 : y + 1 ∈ U)
    (v : Coord) :
    (Uncov r U v ∧ ¬ Uncov r ((U.erase y).erase (y + 1)) v) ↔
      (v = (r + 1, y) ∨ v = (r + 2, y) ∨ v = (r + 2, y + 1) ∨ v = (r + 1, y + 1)) := by
  obtain ⟨v1, v2⟩ := v
  simp only [Uncov, Finset.mem_erase, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have : v2 = y ∨ v2 = y + 1 := by
      by_contra hne
      push Not at hne
      exact h3 ⟨h1, hne.2, hne.1, h2⟩
    rcases this with rfl | rfl <;> rcases h1 with h1 | h1 <;> simp [h1]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨Or.inl rfl, hy⟩, fun ⟨_, _, h, _⟩ => h rfl⟩
    · exact ⟨⟨Or.inr rfl, hy⟩, fun ⟨_, _, h, _⟩ => h rfl⟩
    · exact ⟨⟨Or.inr rfl, hy1⟩, fun ⟨_, h, _⟩ => h rfl⟩
    · exact ⟨⟨Or.inl rfl, hy1⟩, fun ⟨_, h, _⟩ => h rfl⟩

theorem PState.absorb_core {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y y' : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U) {a b : Coord} {X : List Coord}
    (hab : [a, b] <:+: P ∨ [a, b] <:+: Q) (hX : chainAdjacent (a :: (X ++ [b])) = true)
    (hXn : X.Nodup) (hXset : ∀ v, v ∈ X ↔ (v = (r + 1, y) ∨ v = (r + 2, y)))
    (hmidX : [(r + 1, y), (r + 2, y)] <:+: X ∨ [(r + 2, y), (r + 1, y)] <:+: X)
    (ha : a.2 = y') (hb : b.2 = y') :
    ∃ P' Q', PState W h r s0 t0 s1 t1 (U.erase y) P' Q' ∧ Mid r P' Q' y ∧
      ∀ z, z ≠ y' → Mid r P Q z → Mid r P' Q' z := by
  obtain ⟨P', Q', st', hXin, hkeep⟩ := st.splice hab hX hXn
    (fun v => (hXset v).trans (uncov_erase_iff hy v).symm) (Finset.erase_subset _ _)
  refine ⟨P', Q', st', mid_of_X hXin hmidX, fun z hz hm => ?_⟩
  unfold Mid at hm ⊢
  have h1 : ¬((r + 1, z) = a ∧ (r + 2, z) = b) := fun ⟨h, _⟩ => hz (by rw [← ha, ← h])
  have h2 : ¬((r + 1, z) = b ∧ (r + 2, z) = a) := fun ⟨h, _⟩ => hz (by rw [← hb, ← h])
  exact hkeep _ _ h1 h2 hm

/-- **Absorb.** Cover the uncovered column `y` by a detour of the middle edge of the
neighboring column `y'`. -/
theorem PState.absorb {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y y' : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U)
    (hadj : y' + 1 = y ∨ y + 1 = y') (hmid : Mid r P Q y') :
    ∃ P' Q', PState W h r s0 t0 s1 t1 (U.erase y) P' Q' ∧ Mid r P' Q' y ∧
      ∀ z, z ≠ y' → Mid r P Q z → Mid r P' Q' z := by
  have hc1 : chainAdjacent ((r + 1, y') :: ([(r + 1, y), (r + 2, y)] ++ [(r + 2, y')])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]; omega
  have hc2 : chainAdjacent ((r + 2, y') :: ([(r + 2, y), (r + 1, y)] ++ [(r + 1, y')])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]; omega
  have hn1 : [(r + 1, y), (r + 2, y)].Nodup := by simp
  have hn2 : [(r + 2, y), (r + 1, y)].Nodup := by simp
  have hs1 : ∀ v, v ∈ [(r + 1, y), (r + 2, y)] ↔ (v = (r + 1, y) ∨ v = (r + 2, y)) := by simp
  have hs2 : ∀ v, v ∈ [(r + 2, y), (r + 1, y)] ↔ (v = (r + 1, y) ∨ v = (r + 2, y)) := by
    intro v; simp; tauto
  unfold Mid Used at hmid
  rcases hmid with (hm | hm) | (hm | hm)
  · exact st.absorb_core hy (Or.inl hm) hc1 hn1 hs1 (Or.inl ⟨[], [], rfl⟩) rfl rfl
  · exact st.absorb_core hy (Or.inl hm) hc2 hn2 hs2 (Or.inr ⟨[], [], rfl⟩) rfl rfl
  · exact st.absorb_core hy (Or.inr hm) hc1 hn1 hs1 (Or.inl ⟨[], [], rfl⟩) rfl rfl
  · exact st.absorb_core hy (Or.inr hm) hc2 hn2 hs2 (Or.inr ⟨[], [], rfl⟩) rfl rfl

theorem PState.flip_core {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U) (hy1 : y + 1 ∈ U)
    {a b : Coord} {X : List Coord}
    (hab : [a, b] <:+: P ∨ [a, b] <:+: Q) (hX : chainAdjacent (a :: (X ++ [b])) = true)
    (hXn : X.Nodup)
    (hXset : ∀ v, v ∈ X ↔
      (v = (r + 1, y) ∨ v = (r + 2, y) ∨ v = (r + 2, y + 1) ∨ v = (r + 1, y + 1)))
    (hm0 : [(r + 1, y), (r + 2, y)] <:+: X ∨ [(r + 2, y), (r + 1, y)] <:+: X)
    (hm1 : [(r + 1, y + 1), (r + 2, y + 1)] <:+: X ∨ [(r + 2, y + 1), (r + 1, y + 1)] <:+: X)
    (ha : a.1 = r) (hb : b.1 = r) :
    ∃ P' Q', PState W h r s0 t0 s1 t1 ((U.erase y).erase (y + 1)) P' Q' ∧ Mid r P' Q' y ∧
      Mid r P' Q' (y + 1) ∧ ∀ z, Mid r P Q z → Mid r P' Q' z := by
  obtain ⟨P', Q', st', hXin, hkeep⟩ := st.splice hab hX hXn
    (fun v => (hXset v).trans (uncov_erase2_iff hy hy1 v).symm)
    ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  refine ⟨P', Q', st', mid_of_X hXin hm0, mid_of_X hXin hm1, fun z hm => ?_⟩
  unfold Mid at hm ⊢
  have h1 : ¬((r + 1, z) = a ∧ (r + 2, z) = b) := fun ⟨h, _⟩ => by
    have := congrArg Prod.fst h; simp at this; omega
  have h2 : ¬((r + 1, z) = b ∧ (r + 2, z) = a) := fun ⟨h, _⟩ => by
    have := congrArg Prod.fst h; simp at this; omega
  exact hkeep _ _ h1 h2 hm

/-- **Flip.** Two adjacent uncovered columns whose row-`r` cells are joined by a path edge are
covered by a detour of that edge. -/
theorem PState.flip {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U : Finset ℕ} {P Q : List Coord}
    {y : ℕ} (st : PState W h r s0 t0 s1 t1 U P Q) (hy : y ∈ U) (hy1 : y + 1 ∈ U)
    (hu : Used P (r, y) (r, y + 1) ∨ Used Q (r, y) (r, y + 1)) :
    ∃ P' Q', PState W h r s0 t0 s1 t1 ((U.erase y).erase (y + 1)) P' Q' ∧ Mid r P' Q' y ∧
      Mid r P' Q' (y + 1) ∧ ∀ z, Mid r P Q z → Mid r P' Q' z := by
  have hc1 : chainAdjacent ((r, y) :: ([(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)]
      ++ [(r, y + 1)])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]
  have hc2 : chainAdjacent ((r, y + 1) :: ([(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)]
      ++ [(r, y)])) = true := by
    simp [chainAdjacent_cons_cons, adjacentB, Adjacent]
  have hn1 : [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)].Nodup := by simp
  have hn2 : [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)].Nodup := by simp
  have hs1 : ∀ v, v ∈ [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)] ↔
      (v = (r + 1, y) ∨ v = (r + 2, y) ∨ v = (r + 2, y + 1) ∨ v = (r + 1, y + 1)) := by simp
  have hs2 : ∀ v, v ∈ [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)] ↔
      (v = (r + 1, y) ∨ v = (r + 2, y) ∨ v = (r + 2, y + 1) ∨ v = (r + 1, y + 1)) := by
    intro v; simp; tauto
  unfold Used at hu
  rcases hu with (hm | hm) | (hm | hm)
  · exact st.flip_core hy hy1 (Or.inl hm) hc1 hn1 hs1 (Or.inl ⟨[], _, rfl⟩)
      (Or.inr ⟨[_, _], [], rfl⟩) rfl rfl
  · exact st.flip_core hy hy1 (Or.inl hm) hc2 hn2 hs2 (Or.inr ⟨[_, _], [], rfl⟩)
      (Or.inl ⟨[], _, rfl⟩) rfl rfl
  · exact st.flip_core hy hy1 (Or.inr hm) hc1 hn1 hs1 (Or.inl ⟨[], _, rfl⟩)
      (Or.inr ⟨[_, _], [], rfl⟩) rfl rfl
  · exact st.flip_core hy hy1 (Or.inr hm) hc2 hn2 hs2 (Or.inr ⟨[_, _], [], rfl⟩)
      (Or.inl ⟨[], _, rfl⟩) rfl rfl

/-! ### Sweeps -/

theorem PState.congrU {W h r : ℕ} {s0 t0 s1 t1 : Coord} {U U' : Finset ℕ} {P Q : List Coord}
    (st : PState W h r s0 t0 s1 t1 U P Q) (e : U = U') : PState W h r s0 t0 s1 t1 U' P Q :=
  e ▸ st

/-- **Left sweep.** From a column `L` with a middle edge, cover every uncovered column `≤ L`,
using the middle edges of the covered columns below `L`. Middle edges right of `L` survive. -/
theorem PState.sweepLeft {W h r : ℕ} {s0 t0 s1 t1 : Coord} :
    ∀ (L : ℕ) (U : Finset ℕ) (P Q : List Coord), PState W h r s0 t0 s1 t1 U P Q →
      L ∉ U → Mid r P Q L → (∀ z, z < L → z ∉ U → Mid r P Q z) →
      ∃ P' Q', PState W h r s0 t0 s1 t1 (U.filter (L < ·)) P' Q' ∧
        ∀ z, L < z → Mid r P Q z → Mid r P' Q' z
  | 0, U, P, Q, st, hL, _, _ => by
    refine ⟨P, Q, st.congrU ?_, fun _ _ h => h⟩
    ext z
    simp only [Finset.mem_filter]
    constructor
    · intro hz; exact ⟨hz, Nat.pos_of_ne_zero (fun h => hL (h ▸ hz))⟩
    · exact fun h => h.1
  | L + 1, U, P, Q, st, hL, hm, hbelow => by
    by_cases hLU : L ∈ U
    · obtain ⟨P1, Q1, st1, hm1, hkeep1⟩ := st.absorb (y' := L + 1) hLU (Or.inr rfl) hm
      obtain ⟨P2, Q2, st2, hkeep2⟩ := PState.sweepLeft L (U.erase L) P1 Q1 st1
        (Finset.notMem_erase _ _) hm1
        (fun z hz hzU => hkeep1 z (by omega)
          (hbelow z (by omega) (fun h => hzU (Finset.mem_erase.mpr ⟨by omega, h⟩))))
      refine ⟨P2, Q2, st2.congrU ?_, fun z hz h => hkeep2 z (by omega) (hkeep1 z (by omega) h)⟩
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, hz⟩, hlt⟩
        refine ⟨hz, ?_⟩
        rcases Nat.lt_or_ge (L + 1) z with h | h
        · exact h
        · exact absurd (show z = L + 1 by omega) (fun he => hL (he ▸ hz))
      · rintro ⟨hz, hlt⟩
        exact ⟨⟨by omega, hz⟩, by omega⟩
    · obtain ⟨P2, Q2, st2, hkeep2⟩ := PState.sweepLeft L U P Q st hLU
        (hbelow L (by omega) hLU) (fun z hz hzU => hbelow z (by omega) hzU)
      refine ⟨P2, Q2, st2.congrU ?_, fun z hz h => hkeep2 z (by omega) h⟩
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hlt⟩
        refine ⟨hz, ?_⟩
        rcases Nat.lt_or_ge (L + 1) z with h | h
        · exact h
        · exact absurd (show z = L + 1 by omega) (fun he => hL (he ▸ hz))
      · rintro ⟨hz, hlt⟩
        exact ⟨hz, by omega⟩

/-- **Right sweep.** From a column `R` with a middle edge, cover every uncovered column `≥ R`.
Middle edges left of `R` survive. -/
theorem PState.sweepRight {W h r : ℕ} {s0 t0 s1 t1 : Coord} :
    ∀ (n R : ℕ) (U : Finset ℕ) (P Q : List Coord), h - R = n →
      PState W h r s0 t0 s1 t1 U P Q →
      R ∉ U → Mid r P Q R → (∀ z, R < z → z < h → z ∉ U → Mid r P Q z) →
      ∃ P' Q', PState W h r s0 t0 s1 t1 (U.filter (· < R)) P' Q' ∧
        ∀ z, z < R → Mid r P Q z → Mid r P' Q' z
  | 0, R, U, P, Q, hn, st, hR, _, _ => by
    refine ⟨P, Q, st.congrU ?_, fun _ _ h => h⟩
    ext z
    simp only [Finset.mem_filter]
    constructor
    · intro hz; exact ⟨hz, by have := st.Ub z hz; omega⟩
    · exact fun h => h.1
  | n + 1, R, U, P, Q, hn, st, hR, hm, habove => by
    have hfilt : ∀ (V : Finset ℕ), R ∉ V → V.filter (· < R + 1) = V.filter (· < R) := by
      intro V hV
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hlt⟩
        refine ⟨hz, ?_⟩
        rcases Nat.lt_or_ge z R with h | h
        · exact h
        · exact absurd (show z = R by omega) (fun he => hV (he ▸ hz))
      · rintro ⟨hz, hlt⟩
        exact ⟨hz, by omega⟩
    by_cases hRU : R + 1 ∈ U
    · obtain ⟨P1, Q1, st1, hm1, hkeep1⟩ := st.absorb (y' := R) hRU (Or.inl rfl) hm
      obtain ⟨P2, Q2, st2, hkeep2⟩ := PState.sweepRight n (R + 1) (U.erase (R + 1)) P1 Q1
        (by omega) st1 (Finset.notMem_erase _ _) hm1
        (fun z hz hzh hzU => hkeep1 z (by omega)
          (habove z (by omega) hzh (fun h => hzU (Finset.mem_erase.mpr ⟨by omega, h⟩))))
      refine ⟨P2, Q2, st2.congrU ?_, fun z hz h => hkeep2 z (by omega) (hkeep1 z (by omega) h)⟩
      rw [hfilt _ (fun h => hR (Finset.mem_of_mem_erase h))]
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hz⟩, hlt⟩; exact ⟨hz, hlt⟩
      · rintro ⟨hz, hlt⟩; exact ⟨⟨by omega, hz⟩, hlt⟩
    · by_cases hlast : R + 1 < h
      · obtain ⟨P2, Q2, st2, hkeep2⟩ := PState.sweepRight n (R + 1) U P Q (by omega) st hRU
          (habove (R + 1) (by omega) hlast hRU)
          (fun z hz hzh hzU => habove z (by omega) hzh hzU)
        refine ⟨P2, Q2, st2.congrU (hfilt U hR), fun z hz h => hkeep2 z (by omega) h⟩
      · refine ⟨P, Q, st.congrU ?_, fun _ _ h => h⟩
        ext z
        simp only [Finset.mem_filter]
        constructor
        · intro hz
          refine ⟨hz, ?_⟩
          have := st.Ub z hz
          rcases Nat.lt_or_ge z R with h | h
          · exact h
          · exact absurd (show z = R by omega) (fun he => hR (he ▸ hz))
        · exact fun h => h.1

end ZZN
