/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.Lift
public import ZZN.Constr.BandL

@[expose] public section

/-!
# Lifting in one pass

`liftL` is `liftE` with the one-pass band extension `bandExtL`. On a solution of the reduced
instance the two agree (`liftL_eq`).
-/

namespace ZZN

open GridHam

/-- `liftE` with `bandExtL`. -/
def liftL (I : Inst) (d : ℕ) (p q : List Coord) : List Coord × List Coord :=
  if d + 3 ≤ I.w ∧ freeLineB I (d + 2) = true then bandExtL (I.deleteAt d) d p q
  else bandExtL (I.deleteAt d) (d - 1) p q

theorem liftL_eq {I : Inst} {d : ℕ} {p q : List Coord} (hr : RedX I d)
    (hs : IsSolution (I.deleteAt d) p q) : liftL I d p q = liftE I d p q := by
  obtain ⟨f0, f1, hthird⟩ := hr.free
  unfold liftL liftE
  by_cases hc : d + 3 ≤ I.w ∧ freeLineB I (d + 2) = true
  · rw [ite_t hc, ite_t hc]
    have f2 : I.FreeLine (d + 2) := (freeLineB_iff I _).1 hc.2
    have hw := hc.1
    have hfree : LineFree (I.deleteAt d) d := by
      intro y
      have k : ∀ e ∈ I.ends, (d, y) ≠ delAt d e := by
        intro e he hde
        have a0 := f0 e he
        have a1 := f1 e he
        have a2 := f2 e he
        obtain ⟨ex, ey⟩ := e
        simp only at a0 a1 a2
        unfold delAt at hde
        split_ifs at hde with hlt
        · simp only [Prod.mk.injEq] at hde; simp at hlt; omega
        · simp only [Prod.mk.injEq] at hde; omega
      exact ⟨k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]),
        k _ (by simp [Inst.ends])⟩
    exact bandExtL_eq hs (by show d < I.w - 2; omega) hfree
  · rw [ite_f hc, ite_f hc]
    have h3 : 1 ≤ d ∧ d + 2 ≤ I.w ∧ I.FreeLine (d - 1) := by
      rcases hthird with ⟨h1, h2⟩ | h
      · exact absurd ⟨h1, (freeLineB_iff I _).2 h2⟩ hc
      · exact h
    obtain ⟨hd, hw, f0'⟩ := h3
    have hfree : LineFree (I.deleteAt d) (d - 1) := by
      intro y
      have k : ∀ e ∈ I.ends, (d - 1, y) ≠ delAt d e := by
        intro e he hde
        have a0 := f0' e he
        unfold delAt at hde
        split_ifs at hde with hlt
        · rw [← hde] at a0; simp at a0
        · have := congrArg Prod.fst hde; simp at this; have := f0 e he; have := f1 e he; omega
      exact ⟨k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]),
        k _ (by simp [Inst.ends])⟩
    exact bandExtL_eq hs (by show d - 1 < I.w - 2; omega) hfree


end ZZN
