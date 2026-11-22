/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.Round
public import ZZN.Look.Leaf

@[expose] public section

/-!
# The construction with lookup leaves

`ThinOKL`: what the leaf solver must do, only on the leaves the construction reaches: a side at most
10, or sides 11–16 with no reduction on either axis. `solveZ3_completeL`: under `ThinOKL` the block
construction is complete (the proofs of `Round.lean` and `Solve2.lean` with the weaker hypothesis).
`leafL thin tab`: the thin solver on a side at most 10, the certificate lookup otherwise
(`leafL_ok`).
-/

namespace ZZN

open GridHam ZZN.Look ZZN.BoxK

def ThinOKL (thin : Inst → Option (List Coord × List Coord)) : Prop :=
  ∀ J, J.WellFormed → Solvable J →
    ((J.w ≤ 10 ∨ J.h ≤ 10) ∨ (InDom J ∧ J.w ≤ 16 ∧ J.h ≤ 16 ∧ NoRed J)) →
    ∃ p q, thin J = some (p, q) ∧ IsSolution J p q

theorem solveRec2_completeL {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOKL thin) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → Solvable I → I.w + I.h ≤ 2 * n →
      ∃ p q, solveRec2 thin n I = some (p, q) ∧ IsSolution I p q := by
  intro n
  induction n with
  | zero =>
    intro I hwf _ hn
    have := hwf.1
    unfold InBounds at this
    omega
  | succ n ih =>
    intro I hwf hS hn
    simp only [solveRec2]
    by_cases hthinI : I.w ≤ 10 ∨ I.h ≤ 10
    · rw [ite_t hthinI]
      obtain ⟨p, q, hpq, hsol⟩ := hthin I hwf hS (Or.inl hthinI)
      rw [hpq, checkE_of_sol hsol]
      exact ⟨p, q, rfl, hsol⟩
    · rw [ite_f hthinI]
      have hI : InDom I := ⟨by omega, by omega, hwf⟩
      have hP : Passes I := (passes_iff_solvable I hwf hI.1 hI.2.1).2 hS
      have step : ∀ (J : Inst) (d : ℕ), InDom J → Passes J → findRed2 J = some d →
          InDom (J.deleteAt d) ∧ Passes (J.deleteAt d) := by
        intro J d hJ hPJ hf
        rcases findRed2_some hf with hr | hr
        · exact ⟨inDom_deleteAt hJ hr, passX_all hJ hr hPJ⟩
        · exact ⟨inDom_deleteB hJ hr, passB hJ hr hPJ⟩
      cases hf : findRed2 I with
      | some d =>
        obtain ⟨hI', hP'⟩ := step I d hI hP hf
        have hS' := (passes_iff_solvable _ hI'.2.2 hI'.1 hI'.2.1).1 hP'
        have hw' : (I.deleteAt d).w = I.w - 2 := rfl
        have hh' : (I.deleteAt d).h = I.h := rfl
        obtain ⟨p, q, hpq, hsol⟩ := ih (I.deleteAt d) hI'.2.2 hS' (by rw [hw', hh']; omega)
        simp only [hpq]
        exact ⟨_, _, rfl, liftE_solF (findRed2_shape hf) hsol⟩
      | none =>
        have hIT := inDom_transpose hI
        have hPT := passT hI hP
        cases hfT : findRed2 I.transpose with
        | some d =>
          obtain ⟨hI', hP'⟩ := step I.transpose d hIT hPT hfT
          have hS' := (passes_iff_solvable _ hI'.2.2 hI'.1 hI'.2.1).1 hP'
          have hw' : (I.transpose.deleteAt d).w = I.h - 2 := rfl
          have hh' : (I.transpose.deleteAt d).h = I.w := rfl
          obtain ⟨p, q, hpq, hsol⟩ := ih (I.transpose.deleteAt d) hI'.2.2 hS' (by rw [hw', hh']; omega)
          simp only [hpq]
          exact ⟨_, _, rfl, (liftE_solF (findRed2_shape hfT) hsol).of_transpose⟩
        | none =>
          have hw16 : I.w ≤ 16 := leaf16 hwf hI.1 (findRed2_none hf)
          have hh16 : I.h ≤ 16 := leaf16 hIT.2.2 hIT.1 (findRed2_none hfT)
          obtain ⟨p, q, hpq, hsol⟩ := hthin I hwf hS
            (Or.inr ⟨hI, hw16, hh16, findRed2_none hf, findRed2_none hfT⟩)
          rw [hpq, checkE_of_sol hsol]
          exact ⟨p, q, rfl, hsol⟩

theorem solveZ2_completeL {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOKL thin)
    {I : Inst} (hwf : I.WellFormed) (hS : Solvable I) : ∃ p q, solveZ2 thin I = some (p, q) := by
  obtain ⟨p, q, hpq, -⟩ := solveRec2_completeL hthin (I.w + I.h) I hwf hS (by omega)
  exact ⟨p, q, by unfold solveZ2; rw [ite_t hwf]; exact hpq⟩

theorem solveR_completeL {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOKL thin) :
    ∀ (n : ℕ) (I : Inst), I.WellFormed → Solvable I → I.w + I.h ≤ n →
      ∃ p q, solveR thin n I = some (p, q) := by
  intro n
  induction n with
  | zero =>
    intro I hwf _ hn
    have := hwf.1
    unfold InBounds at this
    omega
  | succ n ih =>
    intro I hwf hS hn
    simp only [solveR]
    by_cases hs : I.w ≤ 10 ∨ I.h ≤ 10
    · rw [ite_t hs]; exact solveZ2_completeL hthin hwf hS
    · rw [ite_f hs]
      have hI := inDom_of hwf hs
      have hP : Passes I := (passes_iff_solvable I hwf hI.1 hI.2.1).2 hS
      cases hb : blkX I with
      | some b =>
        have ok := blkX_ok hI hb
        obtain ⟨hJ, hPJ⟩ := chain_pass ok.chain hI hP
        have hSJ := (passes_iff_solvable _ hJ.2.2 hJ.1 hJ.2.1).1 hPJ
        obtain ⟨p, q, hpq⟩ := ih _ hJ.2.2 hSJ (by have := ok.smaller; have := ok.sameH; omega)
        simp only [hpq]
        exact ⟨_, _, rfl⟩
      | none =>
        have hIT := inDom_transpose hI
        have hPT := passT hI hP
        cases hbT : blkX I.transpose with
        | some b =>
          have ok := blkX_ok hIT hbT
          obtain ⟨hJ, hPJ⟩ := chain_pass ok.chain hIT hPT
          have hSJ := (passes_iff_solvable _ hJ.2.2 hJ.1 hJ.2.1).1 hPJ
          have hTw : I.transpose.w = I.h := rfl
          have hTh : I.transpose.h = I.w := rfl
          obtain ⟨p, q, hpq⟩ := ih _ hJ.2.2 hSJ (by have := ok.smaller; have := ok.sameH; omega)
          simp only [hpq]
          exact ⟨_, _, rfl⟩
        | none => exact solveZ2_completeL hthin hwf hS

theorem solveZ3_completeL {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOKL thin)
    {I : Inst} (hwf : I.WellFormed) (hS : Solvable I) : ∃ p q, solveZ3 thin I = some (p, q) := by
  unfold solveZ3
  rw [ite_t hwf]
  exact solveR_completeL hthin _ I hwf hS le_rfl

/-- The leaf solver: `thin` on a side at most 10, the certificate lookup on other well-formed
instances. -/
def leafL (thin : Inst → Option (List Coord × List Coord)) (tab : ℕ → ℕ → List CData) (J : Inst) :
    Option (List Coord × List Coord) :=
  if J.w ≤ 10 ∨ J.h ≤ 10 then thin J else if J.WellFormed then lookJ tab J else none

theorem leafL_ok {thin : Inst → Option (List Coord × List Coord)} (hthin : ThinOK16 thin)
    {tab : ℕ → ℕ → List CData} (htab : TabOK tab) : ThinOKL (leafL thin tab) := by
  intro J hwf hS hc
  unfold leafL
  rcases hc with hc | ⟨hI, hw, hh, hR⟩
  · rw [ite_t hc]
    exact hthin J hwf hS (by tauto)
  · rw [ite_f (by have := hI.1; have := hI.2.1; omega), ite_t hwf]
    have hP : Passes J := (passes_iff_solvable J hwf hI.1 hI.2.1).2 hS
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (lookJ_complete htab hI hw hh hP hR)
    exact ⟨s.1, s.2, hs, lookJ_sound tab hwf hs⟩

end ZZN
