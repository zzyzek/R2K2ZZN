-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.BoxK.Rows
import ZZN.Finite2

/-!
# From slice certificates to `FactsFinite`

`finite_of_boxes`: if every box `w ≤ h` (sides 11–22) has a list of representative row tuples
with `rowsOK` and a `sliceOK` certificate for each, then `FactsFinite` holds.
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane ZZN.Cut GridHam

def rowsOf (J : Inst) : Fin 4 → ℕ := ![J.s0.1, J.t0.1, J.s1.1, J.t1.1]
def colsOf (J : Inst) : Fin 4 → ℕ := ![J.s0.2, J.t0.2, J.s1.2, J.t1.2]

theorem G16_comp : ∀ σ ∈ G16, ∀ τ ∈ G16, σ.comp τ ∈ G16 := by decide

theorem G16_tr : ∀ σ ∈ G16, σ.tr = false := by decide

theorem mem_G16_allSym : ∀ σ ∈ G16, σ ∈ allSym := by decide

theorem rows_apply {σ : Sym} (htr : σ.tr = false) (K : Inst) :
    rowsOf (σ.apply K) = xS σ K.w (rowsOf K) := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  simp only at htr; subst htr
  funext i
  fin_cases i <;> cases rx <;> cases ry <;> cases r0 <;> cases r1 <;> cases sw <;>
    simp [Sym.apply, Sym.geo, Sym.lab, rowsOf, xS, lperm, Inst.reflectX, reflX, Inst.reflectY,
      Inst.transpose, Inst.rev0, Inst.rev1, Inst.swapColors]

theorem wh_apply {σ : Sym} (htr : σ.tr = false) (K : Inst) :
    (σ.apply K).w = K.w ∧ (σ.apply K).h = K.h := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  simp only at htr; subst htr
  cases rx <;> cases ry <;> cases r0 <;> cases r1 <;> cases sw <;>
    simp [Sym.apply, Sym.geo, Sym.lab, Inst.reflectX, Inst.reflectY, Inst.transpose, Inst.rev0,
      Inst.rev1, Inst.swapColors]

def BoxCert (w h : ℕ) : Prop :=
  ∃ reps : List (Fin 4 → ℕ), rowsOK w reps = true ∧
    ∀ x ∈ reps, ∃ pairs fires, sliceOK w h x pairs fires = true

theorem laneI_cols {J : Inst} (hwf : J.WellFormed) :
    laneI J.w J.h (rowsOf J) (idx J.h (colsOf J)) = J := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hwf
  have hc : ∀ i, colsOf J i < J.h := by
    intro i; fin_cases i
    exacts [b0.2, b1.2, b2.2, b3.2]
  have d := digit_idx hc
  have e0 : digit J.h 0 (idx J.h (colsOf J)) = J.s0.2 := d 0
  have e1 : digit J.h 1 (idx J.h (colsOf J)) = J.t0.2 := d 1
  have e2 : digit J.h 2 (idx J.h (colsOf J)) = J.s1.2 := d 2
  have e3 : digit J.h 3 (idx J.h (colsOf J)) = J.t1.2 := d 3
  unfold laneI
  rw [e0, e1, e2, e3]
  rfl

theorem finite_le (hb : ∀ w h, 11 ≤ w → w ≤ h → h ≤ 22 → BoxCert w h) (I : Inst) (hI : InDom I)
    (hw : I.w ≤ 22) (hh : I.h ≤ 22) (hwh : I.w ≤ I.h) (hP : Passes I) (hR : ¬ Reducible I) :
    Solvable I := by
  have hwf := hI.2.2
  have hSI : SB I = true := by
    unfold SB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hI.1, hw, hI.2.1, hh⟩, axB_of_noRed (fun h => hR (Or.inl h))⟩, ?_⟩
    exact axB_of_noRed (I := I.transpose) (fun h => hR (Or.inr (Or.inl h)))
  obtain ⟨σ0, hσ0, hmin⟩ := exists_min (fun σ => keyR (rowsOf (σ.apply I))) G16 (by decide)
  set J := σ0.apply I with hJ
  have htr0 := G16_tr σ0 hσ0
  have hJS : SB J = true := by rw [hJ, SB_apply σ0 hwf]; exact hSI
  have hJD : InDom J := inDom_apply σ0 hwf hSI
  have hJwf := hJD.2.2
  obtain ⟨hJw, hJh⟩ := wh_apply htr0 I
  have hJS' := hJS
  unfold SB at hJS'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hJS'
  obtain ⟨⟨⟨w1, w2, h1, h2⟩, ax⟩, ay⟩ := hJS'
  -- J's rows are a representative
  have hrep : ∀ σ ∈ G16, keyR (rowsOf J) ≤ keyR (xS σ J.w (rowsOf J)) := by
    intro σ hσ
    rw [← rows_apply (G16_tr σ hσ), hJ, comp_apply σ σ0 hwf]
    exact hmin _ (G16_comp σ hσ σ0 hσ0)
  have hle : J.w ≤ J.h := by
    have e1 : J.w = I.w := hJw
    have e2 : J.h = I.h := hJh
    omega
  obtain ⟨reps, hrows, hsl⟩ := hb J.w J.h w1 hle h2
  have hxw : ∀ i, rowsOf J i < J.w := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.1, b1.1, b2.1, b3.1]
  have hmem := rowsOK_sound (by omega) (by omega) hrows hxw (by simpa [rowsOf, xsOf, Inst.ends] using ax)
    hrep
  obtain ⟨pairs, fires, hok⟩ := hsl _ hmem
  have hcj := idx_lt (w := J.h) (x := colsOf J) (by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.2, b1.2, b2.2, b3.2])
  have hcols : ∀ i, colsOf J i < J.h := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.2, b1.2, b2.2, b3.2]
  have hax2 : axB J.h [digit J.h 0 (idx J.h (colsOf J)), digit J.h 1 (idx J.h (colsOf J)),
      digit J.h 2 (idx J.h (colsOf J)), digit J.h 3 (idx J.h (colsOf J))] = true := by
    rw [show digit J.h 0 (idx J.h (colsOf J)) = J.s0.2 from digit_idx hcols 0,
      show digit J.h 1 (idx J.h (colsOf J)) = J.t0.2 from digit_idx hcols 1,
      show digit J.h 2 (idx J.h (colsOf J)) = J.s1.2 from digit_idx hcols 2,
      show digit J.h 3 (idx J.h (colsOf J)) = J.t1.2 from digit_idx hcols 3]
    simpa [ysOf, Inst.ends] using ay
  have hlane := laneI_cols hJwf
  have hres := slice_sound (by omega) (by omega) hok hcj hax2 (by rw [hlane]; exact hJwf)
  rw [hlane] at hres
  rcases hres with hs | hp
  · exact Sym.solvable hwf hs
  · exfalso
    obtain ⟨ρ, hρ⟩ := inv_exists σ0
    have hPJ : Passes (ρ.apply J) := by rw [hJ, hρ I hwf]; exact hP
    have := passes_refl_of_image hJD ρ hPJ
    unfold passImgB at hp
    rcases this with h | h | h | h <;> simp [h] at hp

abbrev SliceData := (Fin 4 → ℕ) × List (CTree TPos × Sym) × List ℕ

theorem boxCert_of_certs {w h : ℕ} (certs : List SliceData) (hrows : rowsOK w (certs.map (·.1)) = true)
    (hall : List.Forall (fun c : SliceData => sliceOK w h c.1 c.2.1 c.2.2 = true) certs) :
    BoxCert w h := by
  refine ⟨certs.map (·.1), hrows, fun x hx => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact ⟨c.2.1, c.2.2, List.forall_iff_forall_mem.mp hall c hc⟩

/-- **The finite facts from slice certificates.** -/
theorem finite_of_boxes (hb : ∀ w h, 11 ≤ w → w ≤ h → h ≤ 22 → BoxCert w h) : FactsFinite := by
  refine ⟨fun I hI hw hh hP hR => Or.inr ?_⟩
  by_cases hwh : I.w ≤ I.h
  · exact finite_le hb I hI hw hh hwh hP hR
  · have hIT : InDom I.transpose := ⟨hI.2.1, hI.1, wf_transpose hI.2.2⟩
    have hRT : ¬ Reducible I.transpose := by
      intro h; apply hR
      unfold Reducible at h ⊢
      rw [Inst.transpose_transpose] at h
      tauto
    have := finite_le hb I.transpose hIT hh hw (by simp [Inst.transpose]; omega) (passT hI hP) hRT
    exact solvable_transpose_iff.mp this

end ZZN.BoxK
