-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.BandExtension

/-!
# Lifting the reductions

Every reduction of `PROOF.md` §3 (strip, compression, interior compression) deletes two
endpoint-free lines `x = d, d+1` next to a third endpoint-free line. Deleting and then inserting
two lines next to the remaining free line gives back the same instance, so `band_extension`
lifts solutions (`lift_delete`, `lift_delete'`). Transposition (`Inst.transpose`) gives the same
for the other axis.
-/

namespace ZZN

open GridHam

/-- Delete the lines `x = d, d+1`. -/
def delAt (d : ℕ) (v : Coord) : Coord := if v.1 < d then v else (v.1 - 2, v.2)

def Inst.deleteAt (I : Inst) (d : ℕ) : Inst where
  w  := I.w - 2
  h  := I.h
  s0 := delAt d I.s0
  t0 := delAt d I.t0
  s1 := delAt d I.s1
  t1 := delAt d I.t1

/-- The four endpoints of `I`. -/
def Inst.ends (I : Inst) : List Coord := [I.s0, I.t0, I.s1, I.t1]

/-- No endpoint lies on line `x = k`. -/
def Inst.FreeLine (I : Inst) (k : ℕ) : Prop := ∀ e ∈ I.ends, e.1 ≠ k

theorem shift_del (r d : ℕ) (v : Coord) (h1 : v.1 ≠ d) (h2 : v.1 ≠ d + 1) (hr : r = d ∨ r + 1 = d)
    (h3 : r = d → v.1 ≠ d + 2) (h4 : r + 1 = d → v.1 ≠ d - 1 ∨ d = 0) :
    shiftAt r (delAt d v) = v := by
  obtain ⟨x, y⟩ := v
  simp only at h1 h2 h3 h4
  unfold shiftAt delAt
  split_ifs with ha hb hb <;> simp_all <;> omega

/-- Insert after `x = d`: the lines `d, d+1, d+2` are free. -/
theorem lift_delete (I : Inst) (d : ℕ) (hw : d + 3 ≤ I.w)
    (f0 : I.FreeLine d) (f1 : I.FreeLine (d + 1)) (f2 : I.FreeLine (d + 2))
    (hS : Solvable (I.deleteAt d)) : Solvable I := by
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
  have hb := band_extension (I.deleteAt d) d (by show d < I.w - 2; omega) hfree hS
  have e : (I.deleteAt d).insertAt d = I := by
    have key : ∀ e ∈ I.ends, shiftAt d (delAt d e) = e := fun e he =>
      shift_del d d e (f0 e he) (f1 e he) (Or.inl rfl) (fun _ => f2 e he) (fun h => by omega)
    cases I
    simp only [Inst.insertAt, Inst.deleteAt, Inst.ends] at key ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at key
    obtain ⟨k0, k1, k2, k3⟩ := key
    simp only [k0, k1, k2, k3, Inst.mk.injEq, and_true]
    simp only at hw ⊢
    omega
  rw [e] at hb
  exact hb

/-- Insert after `x = d - 1`: the lines `d - 1, d, d+1` are free. -/
theorem lift_delete' (I : Inst) (d : ℕ) (hd : 1 ≤ d) (hw : d + 2 ≤ I.w)
    (f0 : I.FreeLine (d - 1)) (f1 : I.FreeLine d) (f2 : I.FreeLine (d + 1))
    (hS : Solvable (I.deleteAt d)) : Solvable I := by
  have hfree : LineFree (I.deleteAt d) (d - 1) := by
    intro y
    have k : ∀ e ∈ I.ends, (d - 1, y) ≠ delAt d e := by
      intro e he hde
      have a0 := f0 e he
      unfold delAt at hde
      split_ifs at hde with hlt
      · rw [← hde] at a0; simp at a0
      · have := congrArg Prod.fst hde; simp at this; have := f1 e he; have := f2 e he; omega
    exact ⟨k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]), k _ (by simp [Inst.ends]),
      k _ (by simp [Inst.ends])⟩
  have hb := band_extension (I.deleteAt d) (d - 1) (by show d - 1 < I.w - 2; omega) hfree hS
  have e : (I.deleteAt d).insertAt (d - 1) = I := by
    have key : ∀ e ∈ I.ends, shiftAt (d - 1) (delAt d e) = e := fun e he =>
      shift_del (d - 1) d e (f1 e he) (f2 e he) (Or.inr (by omega)) (fun h => by omega)
        (fun _ => Or.inl (f0 e he))
    cases I
    simp only [Inst.insertAt, Inst.deleteAt, Inst.ends] at key ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at key
    obtain ⟨k0, k1, k2, k3⟩ := key
    simp only [k0, k1, k2, k3, Inst.mk.injEq, and_true]
    simp only at hw ⊢
    omega
  rw [e] at hb
  exact hb

end ZZN
