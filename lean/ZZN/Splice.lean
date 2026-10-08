-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Defs

/-!
# Path surgery

The constructions in the proof (strip splice, band extension, gluing) all have one shape: a
path uses an edge `a – b`, and we replace that edge by a detour `a, x₁, …, xₙ, b` through fresh
cells. This file proves that such a replacement keeps a path a path, and tracks which cells it
covers.
-/

namespace ZZN

open GridHam

/-! ### `chainAdjacent` on appended lists -/

@[simp] theorem chainAdjacent_nil : chainAdjacent [] = true := rfl

@[simp] theorem chainAdjacent_singleton (a : Coord) : chainAdjacent [a] = true := rfl

theorem chainAdjacent_cons_cons (a b : Coord) (l : List Coord) :
    chainAdjacent (a :: b :: l) = (adjacentB a b && chainAdjacent (b :: l)) := rfl

/-- Splitting a chain at a shared cell `a`. -/
theorem chainAdjacent_append_cons (l : List Coord) (a : Coord) (m : List Coord) :
    chainAdjacent (l ++ a :: m) = (chainAdjacent (l ++ [a]) && chainAdjacent (a :: m)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil => simp [chainAdjacent_cons_cons]
    | cons y l =>
      simp only [List.cons_append, chainAdjacent_cons_cons] at ih ⊢
      rw [ih, Bool.and_assoc]

theorem adjacentB_iff (a b : Coord) : adjacentB a b = true ↔ Adjacent a b := by
  simp [adjacentB]

/-! ### The splice -/

/-- Replacing the edge `a – b` of a chain by `a, X…, b` keeps it a chain, provided
`a, X…, b` is itself a chain. -/
theorem chainAdjacent_splice (l₁ l₂ X : List Coord) (a b : Coord)
    (hp : chainAdjacent (l₁ ++ a :: b :: l₂) = true)
    (hX : chainAdjacent (a :: (X ++ [b])) = true) :
    chainAdjacent (l₁ ++ a :: (X ++ b :: l₂)) = true := by
  rw [chainAdjacent_append_cons] at hp ⊢
  rw [Bool.and_eq_true] at hp ⊢
  refine ⟨hp.1, ?_⟩
  have h2 := hp.2
  rw [chainAdjacent_cons_cons, Bool.and_eq_true] at h2
  have : a :: (X ++ b :: l₂) = (a :: X) ++ b :: l₂ := rfl
  rw [this, chainAdjacent_append_cons, Bool.and_eq_true]
  exact ⟨by simpa using hX, h2.2⟩

/-- Membership after a splice. -/
theorem mem_splice (l₁ l₂ X : List Coord) (a b v : Coord) :
    v ∈ l₁ ++ a :: (X ++ b :: l₂) ↔ v ∈ l₁ ++ a :: b :: l₂ ∨ v ∈ X := by
  simp only [List.mem_append, List.mem_cons]
  tauto

/-- `Nodup` after a splice through cells not on the path. -/
theorem nodup_splice (l₁ l₂ X : List Coord) (a b : Coord)
    (hp : (l₁ ++ a :: b :: l₂).Nodup) (hX : X.Nodup)
    (hfresh : ∀ x ∈ X, x ∉ l₁ ++ a :: b :: l₂) :
    (l₁ ++ a :: (X ++ b :: l₂)).Nodup := by
  have hperm : (l₁ ++ a :: (X ++ b :: l₂)).Perm (X ++ (l₁ ++ a :: b :: l₂)) := by
    have e1 : l₁ ++ a :: (X ++ b :: l₂) = (l₁ ++ [a]) ++ (X ++ (b :: l₂)) := by simp
    have e2 : X ++ (l₁ ++ a :: b :: l₂) = X ++ ((l₁ ++ [a]) ++ (b :: l₂)) := by simp
    rw [e1, e2]
    exact List.perm_append_comm_assoc _ _ _
  refine hperm.nodup_iff.mpr ?_
  rw [List.nodup_append]
  refine ⟨hX, hp, ?_⟩
  intro x hx y hy hxy
  subst hxy
  exact hfresh x hx hy

theorem head?_splice (l₁ l₂ X : List Coord) (a b : Coord) :
    (l₁ ++ a :: (X ++ b :: l₂)).head? = (l₁ ++ a :: b :: l₂).head? := by
  cases l₁ <;> simp

theorem getLast?_splice (l₁ l₂ X : List Coord) (a b : Coord) :
    (l₁ ++ a :: (X ++ b :: l₂)).getLast? = (l₁ ++ a :: b :: l₂).getLast? := by
  have e1 : l₁ ++ a :: (X ++ b :: l₂) = (l₁ ++ a :: X) ++ (b :: l₂) := by simp
  have e2 : l₁ ++ a :: b :: l₂ = (l₁ ++ [a]) ++ (b :: l₂) := by simp
  rw [e1, e2, List.getLast?_append_of_ne_nil _ (by simp),
    List.getLast?_append_of_ne_nil _ (by simp)]

/-- **Splice lemma.** If `p = l₁ ++ a :: b :: l₂` is a path from `s` to `t`, and `a, X…, b` is a
chain through in-bounds cells, none of them on `p` and without repeats, then
`l₁ ++ a :: (X ++ b :: l₂)` is a path from `s` to `t` covering the cells of `p` and of `X`. -/
theorem IsPath.splice {w h : ℕ} {s t : Coord} {l₁ l₂ X : List Coord} {a b : Coord}
    (hp : IsPath w h s t (l₁ ++ a :: b :: l₂))
    (hX : chainAdjacent (a :: (X ++ [b])) = true) (hXn : X.Nodup)
    (hXb : ∀ x ∈ X, InBounds w h x)
    (hfresh : ∀ x ∈ X, x ∉ l₁ ++ a :: b :: l₂) :
    IsPath w h s t (l₁ ++ a :: (X ++ b :: l₂)) := by
  obtain ⟨hh, hl, hn, hb, hc⟩ := hp
  refine ⟨?_, ?_, nodup_splice _ _ _ _ _ hn hXn hfresh, ?_,
    chainAdjacent_splice _ _ _ _ _ hc hX⟩
  · rw [head?_splice]; exact hh
  · rw [getLast?_splice]; exact hl
  · intro v hv
    rcases (mem_splice _ _ _ _ _ _).mp hv with h | h
    · exact hb v h
    · exact hXb v h

end ZZN
