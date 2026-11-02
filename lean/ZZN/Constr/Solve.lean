-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Constr.Lift
import ZZN.Main
import ZZN.TheoremA

/-!
# The construction for every rectangle

`solveRec thin` follows Algorithm 2 of the paper. A rectangle with a side at most 10 goes to the
thin solver `thin`. Otherwise, if some reduction applies (on either axis), the smaller instance is
solved and its solution lifted by band extension; an irreducible instance has both sides at most
22 and also goes to `thin`. `solveZ thin` finishes with the verified checker `solB`, so every
answer it returns is a solution (`solveZ_sound`). If `thin` solves every solvable instance with
a side at most 10 or both sides at most 22, then `solveZ thin` solves every solvable instance
(`solveZ_complete`).

Completeness uses Theorem B through `passes_iff_solvable`, so it depends on the `native_decide`
axioms of the finite case analyses; soundness does not.
-/

namespace ZZN

open GridHam

/-- Reductions keep an instance passing (the `passX` field of `Facts`, from its proofs). -/
theorem passX_all {I : Inst} {d : ℕ} (hI : InDom I) (hr : RedX I d) (hP : Passes I) :
    Passes (I.deleteAt d) := by
  obtain ⟨hw, h⟩ := hr
  rcases h with h | h | h | h
  · exact passStrip hI hw (Or.inl h) hP
  · exact passStrip hI hw (Or.inr h) hP
  · exact passX_comp hI hw (Or.inl h) hP
  · exact passX_comp hI hw (Or.inr h) hP

/-- Keep a candidate only if the verified checker accepts it. -/
def checkE (I : Inst) : Option (List Coord × List Coord) → Option (List Coord × List Coord)
  | some pq => if solB I pq.1 pq.2 then some pq else none
  | none => none

theorem checkE_some {I : Inst} {o : Option (List Coord × List Coord)} {p q : List Coord}
    (h : checkE I o = some (p, q)) : IsSolution I p q := by
  unfold checkE at h
  split at h
  · split_ifs at h with hc
    cases h
    exact solB_sound hc
  · cases h

theorem checkE_of_sol {I : Inst} {p q : List Coord} (h : IsSolution I p q) :
    checkE I (some (p, q)) = some (p, q) := by
  simp [checkE, solB_complete h]

/-- The recursive construction, with fuel. Every candidate is checked by `solB`, so the lists passed
up the recursion always have `w h` cells. -/
def solveRec (thin : Inst → Option (List Coord × List Coord)) :
    ℕ → Inst → Option (List Coord × List Coord)
  | 0, _ => none
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then checkE I (thin I) else
    match findRed I with
    | some d =>
      match solveRec thin n (I.deleteAt d) with
      | some pq => checkE I (some (liftE I d pq.1 pq.2))
      | none => none
    | none =>
      match findRed I.transpose with
      | some d =>
        match solveRec thin n (I.transpose.deleteAt d) with
        | some pq => checkE I (some ((liftE I.transpose d pq.1 pq.2).1.map Prod.swap,
            (liftE I.transpose d pq.1 pq.2).2.map Prod.swap))
        | none => none
      | none => checkE I (thin I)

/-- What the thin solver must do. -/
def ThinOK (thin : Inst → Option (List Coord × List Coord)) : Prop :=
  ∀ J, J.WellFormed → Solvable J → (J.w ≤ 10 ∨ J.h ≤ 10 ∨ (J.w ≤ 22 ∧ J.h ≤ 22)) →
    ∃ p q, thin J = some (p, q) ∧ IsSolution J p q

theorem solveRec_complete {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOK thin) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → Solvable I → I.w + I.h ≤ 2 * n →
      ∃ p q, solveRec thin n I = some (p, q) ∧ IsSolution I p q := by
  intro n
  induction n with
  | zero =>
    intro I hwf _ hn
    have := hwf.1
    unfold InBounds at this
    omega
  | succ n ih =>
    intro I hwf hS hn
    simp only [solveRec]
    by_cases hthinI : I.w ≤ 10 ∨ I.h ≤ 10
    · rw [ite_t hthinI]
      obtain ⟨p, q, hpq, hsol⟩ := hthin I hwf hS (by tauto)
      rw [hpq, checkE_of_sol hsol]
      exact ⟨p, q, rfl, hsol⟩
    · rw [ite_f hthinI]
      have hI : InDom I := ⟨by omega, by omega, hwf⟩
      have hP : Passes I := (passes_iff_solvable I hwf hI.1 hI.2.1).2 hS
      cases hf : findRed I with
      | some d =>
        have hr := findRed_some hf
        have hI' := inDom_deleteAt hI hr
        have hP' := passX_all hI hr hP
        have hS' := (passes_iff_solvable _ hI'.2.2 hI'.1 hI'.2.1).1 hP'
        have hw' : (I.deleteAt d).w = I.w - 2 := rfl
        have hh' : (I.deleteAt d).h = I.h := rfl
        obtain ⟨p, q, hpq, hsol⟩ := ih (I.deleteAt d) hI'.2.2 hS' (by rw [hw', hh']; omega)
        simp only [hpq]
        rw [checkE_of_sol (liftE_sol hr hsol)]
        exact ⟨_, _, rfl, liftE_sol hr hsol⟩
      | none =>
        have hIT := inDom_transpose hI
        have hPT := passT hI hP
        cases hfT : findRed I.transpose with
        | some d =>
          have hr := findRed_some hfT
          have hI' := inDom_deleteAt hIT hr
          have hP' := passX_all hIT hr hPT
          have hS' := (passes_iff_solvable _ hI'.2.2 hI'.1 hI'.2.1).1 hP'
          have hw' : (I.transpose.deleteAt d).w = I.h - 2 := rfl
          have hh' : (I.transpose.deleteAt d).h = I.w := rfl
          obtain ⟨p, q, hpq, hsol⟩ := ih (I.transpose.deleteAt d) hI'.2.2 hS' (by rw [hw', hh']; omega)
          simp only [hpq]
          rw [checkE_of_sol (liftE_sol hr hsol).of_transpose]
          exact ⟨_, _, rfl, (liftE_sol hr hsol).of_transpose⟩
        | none =>
          have hw22 : I.w ≤ 22 := by
            by_contra h
            obtain ⟨d, hd⟩ := redX_of_wide I (by omega)
            exact findRed_none hf d hd
          have hh22 : I.h ≤ 22 := by
            by_contra h
            obtain ⟨d, hd⟩ := redX_of_wide I.transpose (by show 23 ≤ I.h; omega)
            exact findRed_none hfT d hd
          obtain ⟨p, q, hpq, hsol⟩ := hthin I hwf hS (Or.inr (Or.inr ⟨hw22, hh22⟩))
          rw [hpq, checkE_of_sol hsol]
          exact ⟨p, q, rfl, hsol⟩

/-- **The construction**, checked. -/
def solveZ (thin : Inst → Option (List Coord × List Coord)) (I : Inst) :
    Option (List Coord × List Coord) :=
  match solveRec thin (I.w + I.h) I with
  | some pq => if solB I pq.1 pq.2 then some pq else none
  | none => none

theorem solveZ_sound (thin : Inst → Option (List Coord × List Coord)) {I : Inst}
    {p q : List Coord} (h : solveZ thin I = some (p, q)) : IsSolution I p q := by
  unfold solveZ at h
  split at h
  · split_ifs at h with hc
    cases h
    exact solB_sound hc
  · cases h

theorem solveZ_complete {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOK thin)
    {I : Inst} (hwf : I.WellFormed) (hS : Solvable I) : ∃ p q, solveZ thin I = some (p, q) := by
  obtain ⟨p, q, hpq, hsol⟩ := solveRec_complete hthin (I.w + I.h) I hwf hS (by omega)
  refine ⟨p, q, ?_⟩
  unfold solveZ
  rw [hpq]
  simp [solB_complete hsol]

end ZZN
