-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PathFacts

/-!
# Inserting two lines: stretching a path

Insert two new lines `x = r+1, r+2` after the line `x = r`. Cells with `x > r` move by 2
(`shiftAt`). A path is carried over cell by cell; where it crossed between `x = r` and `x = r+1`
(a *crossing* at column `y`), the two new cells `(r+1, y), (r+2, y)` are inserted (`stretch`).
-/

namespace ZZN

open GridHam

/-- Where an old cell goes when two lines are inserted after line `r`. -/
def shiftAt (r : ℕ) (v : Coord) : Coord := if v.1 ≤ r then v else (v.1 + 2, v.2)

/-- The new cells to insert between consecutive old cells `a, b`: two cells if `a – b` crosses
between lines `r` and `r+1`, none otherwise. -/
def gap (r : ℕ) (a b : Coord) : List Coord :=
  if a.1 = r ∧ b.1 = r + 1 ∧ a.2 = b.2 then [(r + 1, a.2), (r + 2, a.2)]
  else if a.1 = r + 1 ∧ b.1 = r ∧ a.2 = b.2 then [(r + 2, a.2), (r + 1, a.2)]
  else []

/-- The stretched path. -/
def stretch (r : ℕ) : List Coord → List Coord
  | [] => []
  | [a] => [shiftAt r a]
  | a :: b :: l => shiftAt r a :: (gap r a b ++ stretch r (b :: l))

theorem shiftAt_injective (r : ℕ) : Function.Injective (shiftAt r) := by
  intro u v h
  unfold shiftAt at h
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  split_ifs at h with h1 h2 h2 <;> simp_all [Prod.ext_iff] <;> omega

theorem shiftAt_fst_ne (r : ℕ) (v : Coord) : (shiftAt r v).1 ≠ r + 1 ∧ (shiftAt r v).1 ≠ r + 2 := by
  unfold shiftAt
  split_ifs with h <;> simp <;> omega

theorem mem_gap {r : ℕ} {a b v : Coord} (h : v ∈ gap r a b) :
    (v.1 = r + 1 ∨ v.1 = r + 2) ∧ v.2 = a.2 ∧
    ((a = (r, a.2) ∧ b = (r + 1, a.2)) ∨ (a = (r + 1, a.2) ∧ b = (r, a.2))) := by
  unfold gap at h
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  split_ifs at h with h1 h2
  · simp at h; rcases h with rfl | rfl <;> simp_all
  · simp at h; rcases h with rfl | rfl <;> simp_all
  · simp at h

theorem stretch_head? (r : ℕ) (a : Coord) (l : List Coord) :
    (stretch r (a :: l)).head? = some (shiftAt r a) := by
  cases l <;> rfl

theorem stretch_ne_nil (r : ℕ) (a : Coord) (l : List Coord) : stretch r (a :: l) ≠ [] := by
  cases l <;> simp [stretch]

theorem stretch_getLast? (r : ℕ) :
    ∀ (l : List Coord), (stretch r l).getLast? = l.getLast?.map (shiftAt r)
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    have ih := stretch_getLast? r (b :: l)
    have e : stretch r (a :: b :: l) = (shiftAt r a :: gap r a b) ++ stretch r (b :: l) := rfl
    rw [e, List.getLast?_append_of_ne_nil _ (stretch_ne_nil r b l), ih]
    simp [List.getLast?_cons_cons]

theorem mem_stretch {r : ℕ} {v : Coord} :
    ∀ {l : List Coord}, v ∈ stretch r l ↔
      (∃ u ∈ l, v = shiftAt r u) ∨ (∃ a b, [a, b] <:+: l ∧ v ∈ gap r a b)
  | [] => by simp [stretch]
  | [a] => by
    simp only [stretch, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨x, y, hxy, -⟩)
      · exact h
      · exact absurd hxy.length_le (by simp)
  | a :: b :: l => by
    have ih := @mem_stretch r v (b :: l)
    simp only [stretch, List.mem_cons, List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact Or.inl ⟨a, by simp, h⟩
      · exact Or.inr ⟨a, b, ⟨[], l, by simp⟩, h⟩
      · rcases ih.mp h with ⟨u, hu, rfl⟩ | ⟨x, y, hxy, hv⟩
        · exact Or.inl ⟨u, Or.inr (List.mem_cons.mp hu), rfl⟩
        · exact Or.inr ⟨x, y, hxy.trans (List.suffix_cons _ _).isInfix, hv⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨x, y, hxy, hv⟩)
      · rcases hu with rfl | hu
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (ih.mpr (Or.inl ⟨u, List.mem_cons.mpr hu, rfl⟩)))
      · obtain ⟨s, t, he⟩ := infix_pair_iff.mp hxy
        cases s with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact Or.inr (Or.inl hv)
        | cons z s =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨-, he⟩ := he
          exact Or.inr (Or.inr (ih.mpr (Or.inr ⟨x, y, infix_pair_iff.mpr ⟨s, t, he⟩, hv⟩)))

/-- The stretched pair `shiftAt a, gap…, shiftAt b` is a chain when `a, b` are adjacent. -/
theorem chain_gap {r : ℕ} {a b : Coord} (h : Adjacent a b) :
    chainAdjacent (shiftAt r a :: (gap r a b ++ [shiftAt r b])) = true := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  unfold gap shiftAt
  unfold Adjacent at h
  simp only at h
  split_ifs <;>
    simp_all [chainAdjacent_cons_cons, adjacentB, Adjacent] <;> omega

theorem stretch_chain (r : ℕ) :
    ∀ (l : List Coord), chainAdjacent l = true → chainAdjacent (stretch r l) = true
  | [] => fun _ => rfl
  | [a] => fun _ => rfl
  | a :: b :: l => by
    intro hc
    rw [chainAdjacent_cons_cons, Bool.and_eq_true] at hc
    have ih := stretch_chain r (b :: l) hc.2
    have hab := (adjacentB_iff a b).mp hc.1
    obtain ⟨t, ht⟩ : ∃ t, stretch r (b :: l) = shiftAt r b :: t := by
      cases l <;> exact ⟨_, rfl⟩
    have e : stretch r (a :: b :: l) = (shiftAt r a :: gap r a b) ++ shiftAt r b :: t := by
      rw [← ht]; rfl
    rw [e, chainAdjacent_append_cons, Bool.and_eq_true]
    refine ⟨?_, by rw [← ht]; exact ih⟩
    simpa using chain_gap (r := r) hab

theorem gap_nodup (r : ℕ) (a b : Coord) : (gap r a b).Nodup := by
  unfold gap
  split_ifs <;> simp

/-- The stretched path has no repeats when the old one has none. -/
theorem stretch_nodup (r : ℕ) :
    ∀ (l : List Coord), l.Nodup → (stretch r l).Nodup
  | [] => fun _ => List.nodup_nil
  | [a] => fun _ => List.nodup_singleton _
  | a :: b :: l => by
    intro hn
    have hn' : (b :: l).Nodup := (List.nodup_cons.mp hn).2
    have ha : a ∉ b :: l := (List.nodup_cons.mp hn).1
    have ih := stretch_nodup r (b :: l) hn'
    show (shiftAt r a :: (gap r a b ++ stretch r (b :: l))).Nodup
    rw [List.nodup_cons, List.nodup_append]
    refine ⟨?_, gap_nodup r a b, ih, ?_⟩
    · rw [List.mem_append, not_or]
      refine ⟨fun hg => ?_, fun hs => ?_⟩
      · exact (shiftAt_fst_ne r a).1 ((mem_gap hg).1.resolve_right
          (fun h2 => (shiftAt_fst_ne r a).2 h2)) |>.elim
      · rcases mem_stretch.mp hs with ⟨u, hu, he⟩ | ⟨x, y, -, hg⟩
        · exact ha (shiftAt_injective r he ▸ hu)
        · rcases (mem_gap hg).1 with h1 | h1
          · exact (shiftAt_fst_ne r a).1 h1
          · exact (shiftAt_fst_ne r a).2 h1
    · intro v hv v' hv' hvv
      subst hvv
      obtain ⟨hx, hy, hab⟩ := mem_gap hv
      rcases mem_stretch.mp hv' with ⟨u, -, rfl⟩ | ⟨x, y, hxy, hg⟩
      · rcases hx with h1 | h1
        · exact (shiftAt_fst_ne r u).1 h1
        · exact (shiftAt_fst_ne r u).2 h1
      · -- the same crossing column twice: `a` would reappear later in the path
        obtain ⟨-, hy', hxy'⟩ := mem_gap hg
        have hcol : x.2 = a.2 := hy'.symm.trans hy
        have hmem : a ∈ b :: l := by
          have hx_in : x ∈ b :: l := hxy.subset (by simp)
          have hy_in : y ∈ b :: l := hxy.subset (by simp)
          rcases hab with ⟨ha1, -⟩ | ⟨ha1, -⟩ <;> rcases hxy' with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩
          · rw [ha1, ← hcol, ← hx1]; exact hx_in
          · rw [ha1, ← hcol, ← hy1]; exact hy_in
          · rw [ha1, ← hcol, ← hy1]; exact hy_in
          · rw [ha1, ← hcol, ← hx1]; exact hx_in
        exact ha hmem

/-- Each edge `a – b` of the old path becomes the run `shiftAt a, gap…, shiftAt b` of the new one. -/
theorem infix_stretch {r : ℕ} {a b : Coord} :
    ∀ {l : List Coord}, [a, b] <:+: l →
      (shiftAt r a :: (gap r a b ++ [shiftAt r b])) <:+: stretch r l
  | [] => fun h => absurd h.length_le (by simp)
  | [_] => fun h => absurd h.length_le (by simp)
  | x :: y :: l => by
    intro h
    obtain ⟨s, t, he⟩ := infix_pair_iff.mp h
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨h1, h2, h3⟩ := he
      subst h1 h2 h3
      obtain ⟨u, hu⟩ : ∃ u, stretch r (y :: l) = shiftAt r y :: u := by
        cases l <;> exact ⟨_, rfl⟩
      refine ⟨[], u, ?_⟩
      show _ = shiftAt r x :: (gap r x y ++ stretch r (y :: l))
      rw [hu]; simp
    | cons z s =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨-, he⟩ := he
      have ih := @infix_stretch r a b (y :: l) (infix_pair_iff.mpr ⟨s, t, he⟩)
      exact ih.trans (List.IsSuffix.isInfix ⟨shiftAt r x :: gap r x y, rfl⟩)

theorem shiftAt_inBounds {r w h : ℕ} {v : Coord} (hv : InBounds w h v) :
    InBounds (w + 2) h (shiftAt r v) := by
  unfold InBounds at hv ⊢
  unfold shiftAt
  split_ifs <;> constructor <;> (try dsimp only) <;> omega

/-- Cells of the stretched path are in bounds of the widened grid. -/
theorem stretch_inBounds {r w h : ℕ} (hr : r < w) {l : List Coord}
    (hl : ∀ v ∈ l, InBounds w h v) : ∀ v ∈ stretch r l, InBounds (w + 2) h v := by
  intro v hv
  rcases mem_stretch.mp hv with ⟨u, hu, rfl⟩ | ⟨a, b, hab, hg⟩
  · exact shiftAt_inBounds (hl u hu)
  · obtain ⟨hx, hy, -⟩ := mem_gap hg
    have ha := hl a (hab.subset (by simp))
    unfold InBounds at ha ⊢
    omega

end ZZN
