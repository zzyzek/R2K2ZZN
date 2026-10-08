-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PassXAssemble

/-!
# Theorem A, with the compression facts proved

`Facts'` drops the compression and interior-compression parts of `Facts.passX`, which are
theorems (`passX_comp`). Its remaining fields, proved in later files:

* `passStrip` — the strip reductions preserve passing (`PROOF.md` §4.3; `PassStrip.lean`);
* `passT` — the catalogue is symmetric under transposition (`PassT.lean`, `PassTR.lean`);
* `finite` — the computations (`Boxes.lean`).
-/

namespace ZZN

/-- The strip clauses of `RedX`. -/
def StripClause (I : Inst) (d : ℕ) : Prop :=
  (d = 0 ∧ ∀ k, k ≤ 3 → I.FreeLine k) ∨ (d + 2 = I.w ∧ ∀ k, I.w ≤ k + 4 → k < I.w → I.FreeLine k)

structure Facts' : Prop where
  passStrip : ∀ I d, InDom I → 13 ≤ I.w → StripClause I d → Passes I → Passes (I.deleteAt d)
  passT     : ∀ I, InDom I → Passes I → Passes I.transpose
  finite    : ∀ I, InDom I → I.w ≤ 22 → I.h ≤ 22 → Passes I → ¬ Reducible I →
    MoveOK I ∨ Solvable I

theorem facts_of (F : Facts') : Facts where
  passX I d hI hr hP := by
    obtain ⟨hw, h⟩ := hr
    rcases h with h | h | h | h
    · exact F.passStrip I d hI hw (Or.inl h) hP
    · exact F.passStrip I d hI hw (Or.inr h) hP
    · exact passX_comp hI hw (Or.inl h) hP
    · exact passX_comp hI hw (Or.inr h) hP
  passT := F.passT
  finite := F.finite

/-- **Theorem A**: given `Facts'`, every well-formed instance with both sides `≥ 11` that passes
the catalogue is solvable. -/
theorem theoremA' (F : Facts') (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h)
    (hP : Passes I) : Solvable I :=
  theoremA_main (facts_of F) I hwf hw hh hP

end ZZN
