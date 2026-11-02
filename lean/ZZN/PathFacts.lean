-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Splice

/-!
# Basic facts about simple paths given as lists

* `[u, v] <:+: p` means `u, v` are consecutive in `p` (an edge of the path, in that direction).
* A cell that is on a path but is not one of its ends has a predecessor and a successor, which
  are distinct.
* In a list without repeats, a cell has at most one predecessor and at most one successor, so
  at most two path edges touch it.
-/

namespace ZZN

open GridHam

/-- In a list without repeats, a cell has one position. -/
theorem nodup_split_unique {a b c d : List Coord} {v : Coord}
    (hn : (a ++ v :: b).Nodup) (he : a ++ v :: b = c ++ v :: d) : a = c ∧ b = d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => simpa using he
    | cons x c =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp at hn
  | cons x a ih =>
    cases c with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp at hn
    | cons y c =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have hn' : (a ++ v :: b).Nodup := (List.nodup_cons.mp hn).2
      obtain ⟨h1, h2⟩ := ih hn' he
      exact ⟨by rw [h1], h2⟩

theorem infix_pair_iff {l : List Coord} {u v : Coord} :
    [u, v] <:+: l ↔ ∃ s t, l = s ++ u :: v :: t := by
  constructor
  · rintro ⟨s, t, h⟩
    exact ⟨s, t, by rw [← h]; simp⟩
  · rintro ⟨s, t, rfl⟩
    exact ⟨s, t, by simp⟩

/-- The predecessor of a cell in a list without repeats is unique. -/
theorem pred_unique {l : List Coord} {x y v : Coord} (hn : l.Nodup)
    (hx : [x, v] <:+: l) (hy : [y, v] <:+: l) : x = y := by
  obtain ⟨s1, t1, rfl⟩ := infix_pair_iff.mp hx
  obtain ⟨s2, t2, he⟩ := infix_pair_iff.mp hy
  have e1 : s1 ++ x :: v :: t1 = (s1 ++ [x]) ++ v :: t1 := by simp
  have e2 : s2 ++ y :: v :: t2 = (s2 ++ [y]) ++ v :: t2 := by simp
  rw [e1] at hn he
  rw [e2] at he
  obtain ⟨h1, -⟩ := nodup_split_unique hn he
  have := congrArg List.getLast? h1
  simpa using this

/-- The successor of a cell in a list without repeats is unique. -/
theorem succ_unique {l : List Coord} {x y v : Coord} (hn : l.Nodup)
    (hx : [v, x] <:+: l) (hy : [v, y] <:+: l) : x = y := by
  obtain ⟨s1, t1, rfl⟩ := infix_pair_iff.mp hx
  obtain ⟨s2, t2, he⟩ := infix_pair_iff.mp hy
  obtain ⟨-, h2⟩ := nodup_split_unique hn he
  simpa using congrArg List.head? h2

/-- Consecutive cells of a chain are adjacent. -/
theorem adjacent_of_infix {l : List Coord} {u v : Coord} (hc : chainAdjacent l = true)
    (h : [u, v] <:+: l) : Adjacent u v := by
  obtain ⟨s, t, rfl⟩ := infix_pair_iff.mp h
  rw [chainAdjacent_append_cons, Bool.and_eq_true] at hc
  have h2 := hc.2
  rw [chainAdjacent_cons_cons, Bool.and_eq_true] at h2
  exact (adjacentB_iff u v).mp h2.1

/-- A cell on a path that is not its first cell has a predecessor. -/
theorem exists_pred {l : List Coord} {v : Coord} (hv : v ∈ l) (hh : l.head? ≠ some v) :
    ∃ u, [u, v] <:+: l := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hv
  cases s using List.reverseRecOn with
  | nil => simp at hh
  | append_singleton s u _ => exact ⟨u, infix_pair_iff.mpr ⟨s, t, by simp⟩⟩

/-- A cell on a path that is not its last cell has a successor. -/
theorem exists_succ {l : List Coord} {v : Coord} (hv : v ∈ l) (hl : l.getLast? ≠ some v) :
    ∃ u, [v, u] <:+: l := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hv
  cases t with
  | nil => simp at hl
  | cons u t => exact ⟨u, infix_pair_iff.mpr ⟨s, t, rfl⟩⟩

/-- In a list without repeats, a cell is not its own neighbor along the list. -/
theorem ne_of_infix {l : List Coord} {u v : Coord} (hn : l.Nodup) (h : [u, v] <:+: l) : u ≠ v := by
  obtain ⟨s, t, rfl⟩ := infix_pair_iff.mp h
  intro huv
  subst huv
  have := (List.nodup_append.mp hn).2.1
  simp at this

/-- Predecessor and successor of a cell differ. -/
theorem pred_ne_succ {l : List Coord} {u v x : Coord} (hn : l.Nodup)
    (hu : [u, v] <:+: l) (hx : [v, x] <:+: l) : u ≠ x := by
  obtain ⟨s, t, rfl⟩ := infix_pair_iff.mp hu
  obtain ⟨s2, t2, he⟩ := infix_pair_iff.mp hx
  have e1 : s ++ u :: v :: t = (s ++ [u]) ++ v :: t := by simp
  rw [e1] at hn he
  have e2 : s2 ++ v :: x :: t2 = s2 ++ v :: (x :: t2) := rfl
  rw [e2] at he
  obtain ⟨h1, h2⟩ := nodup_split_unique hn he
  subst h2
  intro hux
  subst hux
  have := (List.nodup_append.mp hn).2.2
  exact this u (by simp) u (by simp) rfl

/-- `u – v` is an edge of the path `l`, in either direction. -/
def Used (l : List Coord) (u v : Coord) : Prop := [u, v] <:+: l ∨ [v, u] <:+: l

theorem Used.symm {l : List Coord} {u v : Coord} (h : Used l u v) : Used l v u := Or.symm h

/-- In a list without repeats, at most two path edges touch a cell: any three neighbors along the
list are not pairwise distinct. -/
theorem used_le_two {l : List Coord} {v a b c : Coord} (hn : l.Nodup)
    (ha : Used l v a) (hb : Used l v b) (hc : Used l v c) :
    a = b ∨ a = c ∨ b = c := by
  unfold Used at ha hb hc
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  all_goals first
    | exact Or.inl (succ_unique hn ha hb)
    | exact Or.inl (pred_unique hn ha hb)
    | exact Or.inr (Or.inl (succ_unique hn ha hc))
    | exact Or.inr (Or.inl (pred_unique hn ha hc))
    | exact Or.inr (Or.inr (succ_unique hn hb hc))
    | exact Or.inr (Or.inr (pred_unique hn hb hc))

/-- A cell of a path other than its two ends has two distinct neighbors along the path. -/
theorem interior_two {l : List Coord} {v : Coord} (hn : l.Nodup) (hv : v ∈ l)
    (hh : l.head? ≠ some v) (hl : l.getLast? ≠ some v) :
    ∃ u x, u ≠ x ∧ Used l v u ∧ Used l v x := by
  obtain ⟨u, hu⟩ := exists_pred hv hh
  obtain ⟨x, hx⟩ := exists_succ hv hl
  exact ⟨u, x, pred_ne_succ hn hu hx, Or.inr hu, Or.inl hx⟩

/-- Edges of a chain join adjacent cells. -/
theorem Used.adjacent {l : List Coord} {u v : Coord} (hc : chainAdjacent l = true)
    (h : Used l u v) : Adjacent u v := by
  rcases h with h | h
  · exact adjacent_of_infix hc h
  · have := adjacent_of_infix hc h
    unfold Adjacent at this ⊢
    omega

theorem Used.mem_left {l : List Coord} {u v : Coord} (h : Used l u v) : u ∈ l := by
  rcases h with h | h
  · exact h.subset (by simp)
  · exact h.subset (by simp)

theorem Used.mem_right {l : List Coord} {u v : Coord} (h : Used l u v) : v ∈ l :=
  h.symm.mem_left

end ZZN
