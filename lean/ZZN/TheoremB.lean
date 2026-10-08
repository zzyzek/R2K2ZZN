-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.SoundT2
import ZZN.Parity

/-!
# Theorem B: every catalogue entry is sound on the domain

Proved here: P, T1, T2, L1–L6, E1. The effective-alternation entry R is an argument of
`theoremB` (`theoremB_R` in `ZZN/SoundRMain.lean` supplies it). Stated as hypotheses (`BFacts`):
the entries B, C, D, whose soundness comes from the window certificates (the paper, Section 7;
`bFacts_of` in `WinBCD.lean`, discharged in `Final.lean`).
-/

namespace ZZN

open GridHam

/-- The window-certificate entries B, C, D, each in the identity frame (proved by `bFacts_of`). -/
structure BFacts : Prop where
  bSound : ∀ J : Inst, J.WellFormed → Solvable J → 11 ≤ J.w → 11 ≤ J.h →
    boundaryOnly J.w J.h idF (ptsOf J) = false
  cSound : ∀ J : Inst, J.WellFormed → Solvable J → 11 ≤ J.w → 11 ≤ J.h →
    corner4 J.w J.h idF (ptsOf J) = false

theorem frameMap_dims (I : Inst) (f : Frame) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h) :
    11 ≤ (I.frameMap f).w ∧ 11 ≤ (I.frameMap f).h := by
  unfold Inst.frameMap Frame.H Frame.W; split_ifs <;> exact ⟨by assumption, by assumption⟩

/-- Every frame entry is sound. -/
theorem frames_sound (F : BFacts) {I : Inst} (hI : InDom I) (hS : Solvable I) :
    frames.any (frameFires I.w I.h (ptsOf I)) = false := by
  obtain ⟨hw, hh, hwf⟩ := hI
  rw [List.any_eq_false]
  intro f _ hf
  rw [frameFires_id] at hf
  have e : (ptsOf I).map (fun q => (f.to I.w I.h q.1, q.2)) = ptsOf (I.frameMap f) := rfl
  rw [e] at hf
  set J := I.frameMap f
  have hJ : J.WellFormed := wellFormed_frameMap f hwf
  have hSJ : Solvable J := solvable_frameMap f hS
  obtain ⟨dw, dh⟩ := frameMap_dims I f hw hh
  have ew : f.H I.w I.h = J.w := rfl
  have eh : f.W I.w I.h = J.h := rfl
  rw [ew, eh] at hf
  obtain ⟨p, q, hpq⟩ := hSJ
  unfold frameFires at hf
  dsimp only at hf
  rw [testL2_sound hJ hpq, testL3_sound hJ hpq, testL4_sound hJ hpq, testL5_sound hJ hpq,
    edgeClosure_sound hJ hpq, F.bSound J hJ ⟨p, q, hpq⟩ dw dh, F.cSound J hJ ⟨p, q, hpq⟩ dw dh] at hf
  simp at hf

/-- **Theorem B** (given `BFacts` and R soundness): a solvable instance in the domain passes the
catalogue. -/
theorem theoremB (F : BFacts) (rSound : ∀ I : Inst, InDom I → Solvable I → effAlt3 I.w I.h (ptsOf I) = false)
    {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I := by
  have hI' := hI
  obtain ⟨hw, hh, hwf⟩ := hI'
  unfold Passes fires3
  dsimp only
  have hpar := parityOk_of_solvable hS
  have ht1 := t1_sound hwf (by omega) (by omega) hS
  have ht2 := t2_sound hwf hS
  obtain ⟨p, q, hpq⟩ := hS
  have hl1 : l1Fires I.w I.h (ptsOf I) = false := by
    rw [Bool.eq_false_iff, ne_eq, l1Fires_iff]
    exact l1_sound hwf hpq
  have hl6 := l6_sound hwf hpq (by omega) (by omega)
  have hfr := frames_sound F hI ⟨p, q, hpq⟩
  have hR := rSound I hI ⟨p, q, hpq⟩
  simp only [ptsOf] at hl1 hl6 hfr hR
  simp only [hpar, ht1, ht2, hl1, hl6, hfr, hR, Bool.not_true, Bool.or_false]

end ZZN
