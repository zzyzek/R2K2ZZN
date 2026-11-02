-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.BoxK.Rows
import ZZN.Finite2
import ZZN.FiniteB

/-!
# From slice certificates to `FactsFiniteB`

`finite_of_boxes`: if every box `w ≤ h` (sides 11–22) has a list of representative row tuples
with `rowsOK` and a `sliceOK` certificate for each, then `FactsFiniteB` holds.
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane ZZN.Cut GridHam

def rowsOf (J : Inst) : Fin 4 → ℕ := ![J.s0.1, J.t0.1, J.s1.1, J.t1.1]
def colsOf (J : Inst) : Fin 4 → ℕ := ![J.s0.2, J.t0.2, J.s1.2, J.t1.2]

theorem G16_comp : ∀ σ ∈ G16, ∀ τ ∈ G16, σ.comp τ ∈ G16 := by decide

/-- The symmetries without transposition. -/
def G32 : List Sym := allSym.filter fun σ => !σ.tr

theorem G32_comp : ∀ σ ∈ G32, ∀ τ ∈ G32, σ.comp τ ∈ G32 := by decide

theorem G32_tr : ∀ σ ∈ G32, σ.tr = false := by decide

theorem G16_sub : ∀ σ ∈ G16, σ ∈ G32 := by decide

/-- The column reflection. -/
def ryS : Sym := ⟨false, false, true, false, false, false⟩

theorem ryS_mem : ryS ∈ G32 := by decide

theorem allSym_comp : ∀ σ ∈ allSym, ∀ τ ∈ allSym, σ.comp τ ∈ allSym := by decide +kernel

theorem G32_sub : ∀ σ ∈ G32, σ ∈ allSym := by decide

/-- The transposition. -/
def trS : Sym := ⟨true, false, false, false, false, false⟩

theorem trS_mem : trS ∈ allSym := by decide

/-- The symmetries used on a box: with transposition when it is square. -/
def Gbox (w h : ℕ) : List Sym := if w = h then allSym else G32

theorem Gbox_comp (w h : ℕ) : ∀ σ ∈ Gbox w h, ∀ τ ∈ Gbox w h, σ.comp τ ∈ Gbox w h := by
  unfold Gbox; split_ifs
  · exact allSym_comp
  · exact G32_comp

theorem Gbox_ne (w h : ℕ) : Gbox w h ≠ [] := by
  unfold Gbox; split_ifs <;> decide

theorem G32_Gbox (w h : ℕ) : ∀ σ ∈ G32, σ ∈ Gbox w h := by
  unfold Gbox; split_ifs
  · exact G32_sub
  · exact fun σ h => h

theorem wh_apply' (σ : Sym) (K : Inst) :
    (σ.apply K).w = (if σ.tr then K.h else K.w) ∧ (σ.apply K).h = (if σ.tr then K.w else K.h) := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases tr <;> cases rx <;> cases ry <;> cases r0 <;> cases r1 <;> cases sw <;>
    simp [Sym.apply, Sym.geo, Sym.lab, Inst.reflectX, Inst.reflectY, Inst.transpose, Inst.rev0,
      Inst.rev1, Inst.swapColors]

theorem rows_trS (K : Inst) : rowsOf (trS.apply K) = colsOf K := by
  funext i
  fin_cases i <;> simp [trS, Sym.apply, Sym.geo, Sym.lab, rowsOf, colsOf, Inst.transpose]

theorem cols_trS (K : Inst) : colsOf (trS.apply K) = rowsOf K := by
  funext i
  fin_cases i <;> simp [trS, Sym.apply, Sym.geo, Sym.lab, rowsOf, colsOf, Inst.transpose]

theorem cols_apply {σ : Sym} (htr : σ.tr = false) (K : Inst) :
    colsOf (σ.apply K) = yS0 σ K.h (colsOf K) := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  simp only at htr; subst htr
  funext i
  fin_cases i <;> cases rx <;> cases ry <;> cases r0 <;> cases r1 <;> cases sw <;>
    simp [Sym.apply, Sym.geo, Sym.lab, colsOf, yS0, lperm, Inst.reflectX, reflX, Inst.reflectY,
      Inst.transpose, Inst.rev0, Inst.rev1, Inst.swapColors]

/-- Rows first, then columns. -/
def key2 (K : Inst) : ℕ := keyR (rowsOf K) * 2 ^ 20 + keyR (colsOf K)

theorem keyR_lt {x : Fin 4 → ℕ} (hx : ∀ i, x i < 32) : keyR x < 2 ^ 20 := by
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  unfold keyR; omega

theorem rows_ryS (K : Inst) : rowsOf (ryS.apply K) = rowsOf K := by
  funext i
  fin_cases i <;> simp [ryS, Sym.apply, Sym.geo, Sym.lab, rowsOf, Inst.reflectY, Inst.transpose, Inst.reflectX, reflX]

theorem cols_ryS (K : Inst) : colsOf (ryS.apply K) = fun i => K.h - 1 - colsOf K i := by
  funext i
  fin_cases i <;> simp [ryS, Sym.apply, Sym.geo, Sym.lab, colsOf, Inst.reflectY, Inst.transpose, Inst.reflectX, reflX]

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

/-- What a slice certificate proves: each valid lane is solvable or fails the catalogue. -/
def SliceGood (w h : ℕ) (x : Fin 4 → ℕ) : Prop :=
  ∀ j, j < h ^ 4 → axBB h [digit h 0 j, digit h 1 j, digit h 2 j, digit h 3 j] = true →
    (∀ σ ∈ stabL w x, keyR (fun i => digit h i j) ≤ keyR (yS0 σ h (fun i => digit h i j))) →
    (w = h → keyR x ≤ keyR (fun i => digit h i j)) → (∀ i, x i < 32) →
    (laneI w h x j).WellFormed → Solvable (laneI w h x j) ∨ passImgB (laneI w h x j) = false

theorem sliceGood_of_sliceOK {w h : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hw32 : w ≤ 32) {x : Fin 4 → ℕ}
    {pairs : List (CTree TPos × Sym)} {fires : List ℕ} {insts : List (ℕ × Sym × CTree TPos)}
    {sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (hok : sliceOK w h x pairs fires insts sols = true) :
    SliceGood w h x :=
  fun _ hj hax hst htc hx32 hwf => slice_sound hh h32 hw32 hok hj hax hst htc hx32 hwf

def BoxCert (w h : ℕ) : Prop :=
  ∃ reps : List (Fin 4 → ℕ), rowsOK w reps = true ∧ ∀ x ∈ reps, SliceGood w h x

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

theorem finite_le (hb : ∀ w h, 11 ≤ w → w ≤ h → h ≤ 16 → BoxCert w h)
    (hnone : ∀ n, 17 ≤ n → n ≤ 22 → noneOK n = true) (I : Inst) (hI : InDom I)
    (hw : I.w ≤ 22) (hh : I.h ≤ 22) (hwh : I.w ≤ I.h) (hP : Passes I) (hR : ¬ ReducibleB I) :
    Solvable I := by
  have hwf := hI.2.2
  have hSI : SBB I = true := by
    unfold SBB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hI.1, hw, hI.2.1, hh⟩, axBB_of_noRed hwf (fun h => hR (Or.inl (Or.inl h)))
      (fun h => hR (Or.inr (Or.inl h)))⟩, ?_⟩
    exact axBB_of_noRed (I := I.transpose) (wf_transpose hwf)
      (fun h => hR (Or.inl (Or.inr (Or.inl h)))) (fun h => hR (Or.inr (Or.inr h)))
  obtain ⟨σ0, hσ0, hmin⟩ := exists_min (fun σ => key2 (σ.apply I)) (Gbox I.w I.h) (Gbox_ne _ _)
  set J := σ0.apply I with hJ
  have hJS : SBB J = true := by rw [hJ, SBB_apply σ0 hwf]; exact hSI
  have hJD : InDom J := inDom_applyB σ0 hwf hSI
  have hJwf := hJD.2.2
  have hJw : J.w = I.w ∧ J.h = I.h := by
    obtain ⟨e1, e2⟩ := wh_apply' σ0 I
    by_cases htr : σ0.tr = true
    · have hsq : I.w = I.h := by
        by_contra hne
        have : σ0 ∈ G32 := by simpa [Gbox, hne] using hσ0
        rw [G32_tr σ0 this] at htr; exact absurd htr (by simp)
      rw [htr] at e1 e2; simp only [↓reduceIte] at e1 e2
      exact ⟨e1.trans hsq.symm, e2.trans hsq⟩
    · simp only [Bool.not_eq_true] at htr
      rw [htr] at e1 e2; simp only [Bool.false_eq_true, ↓reduceIte] at e1 e2
      exact ⟨e1, e2⟩
  obtain ⟨hJw, hJh⟩ := hJw
  have hJS' := hJS
  unfold SBB at hJS'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hJS'
  obtain ⟨⟨⟨w1, w2, h1, h2⟩, ax⟩, ay⟩ := hJS'
  -- J's rows are a representative
  have hlt : ∀ K : Inst, K.WellFormed → K.w ≤ 22 → K.h ≤ 22 →
      keyR (rowsOf K) < 2 ^ 20 ∧ keyR (colsOf K) < 2 ^ 20 := by
    intro K hK hKw hKh
    obtain ⟨b0, b1, b2, b3, -⟩ := hK
    have r : ∀ i, rowsOf K i < K.w := by
      intro i; fin_cases i
      exacts [b0.1, b1.1, b2.1, b3.1]
    have c : ∀ i, colsOf K i < K.h := by
      intro i; fin_cases i
      exacts [b0.2, b1.2, b2.2, b3.2]
    exact ⟨keyR_lt fun i => by have := r i; omega, keyR_lt fun i => by have := c i; omega⟩
  have hkeyG : ∀ σ ∈ Gbox I.w I.h, key2 J ≤ key2 (σ.apply J) := by
    intro σ hσ
    rw [hJ, comp_apply σ σ0 hwf]
    exact hmin _ (Gbox_comp _ _ σ hσ σ0 hσ0)
  have hkey : ∀ σ ∈ G32, key2 J ≤ key2 (σ.apply J) := fun σ hσ => hkeyG σ (G32_Gbox _ _ σ hσ)
  have hJw22 : J.w ≤ 22 := by omega
  have hJh22 : J.h ≤ 22 := by omega
  have hrep : ∀ σ ∈ G16, keyR (rowsOf J) ≤ keyR (xS σ J.w (rowsOf J)) := by
    intro σ hσ
    have hk := hkey σ (G16_sub σ hσ)
    have htr := G16_tr σ hσ
    have hwfσ : (σ.apply J).WellFormed := (inDom_applyB σ hJwf hJS).2.2
    obtain ⟨e1, e2⟩ := wh_apply htr J
    obtain ⟨a1, a2⟩ := hlt J hJwf hJw22 hJh22
    obtain ⟨c1, c2⟩ := hlt (σ.apply J) hwfσ (by omega) (by omega)
    rw [← rows_apply htr]
    unfold key2 at hk
    by_contra hc
    push Not at hc
    have : keyR (rowsOf (σ.apply J)) + 1 ≤ keyR (rowsOf J) := hc
    nlinarith
  have hcc : ∀ σ ∈ stabL J.w (rowsOf J), keyR (colsOf J) ≤ keyR (yS0 σ J.h (colsOf J)) := by
    intro σ hσ
    simp only [stabL, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hσ
    obtain ⟨hσa, htr, hfix⟩ := hσ
    have hk := hkey σ (List.mem_filter.mpr ⟨hσa, by simp [htr]⟩)
    unfold key2 at hk
    rw [rows_apply htr, hfix, cols_apply htr] at hk
    omega
  have htc : J.w = J.h → keyR (rowsOf J) ≤ keyR (colsOf J) := by
    intro hsq
    have hk := hkeyG trS (by simp only [Gbox, show I.w = I.h by omega, ↓reduceIte]; exact trS_mem)
    unfold key2 at hk
    rw [rows_trS, cols_trS] at hk
    obtain ⟨a1, a2⟩ := hlt J hJwf hJw22 hJh22
    by_contra hc
    push Not at hc
    nlinarith
  have hle : J.w ≤ J.h := by
    have e1 : J.w = I.w := hJw
    have e2 : J.h = I.h := hJh
    omega
  have hcols0 : ∀ i, colsOf J i < J.h := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.2, b1.2, b2.2, b3.2]
  have h18 : J.h ≤ 16 := by
    by_contra hc
    have hf := noneOK_sound (by omega) (by omega) (hnone J.h (by omega) h2) hcols0
    have ht : axBB J.h [J.s0.2, J.t0.2, J.s1.2, J.t1.2] = true := by
      simpa [ysOf, Inst.ends] using ay
    rw [show [colsOf J 0, colsOf J 1, colsOf J 2, colsOf J 3] = [J.s0.2, J.t0.2, J.s1.2, J.t1.2]
      from rfl, ht] at hf
    exact absurd hf (by decide)
  obtain ⟨reps, hrows, hsl⟩ := hb J.w J.h w1 hle h18
  have hxw : ∀ i, rowsOf J i < J.w := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.1, b1.1, b2.1, b3.1]
  have hmem := rowsOK_sound (by omega) (by omega) hrows hxw (by simpa [rowsOf, xsOf, Inst.ends] using ax)
    hrep
  have hok := hsl _ hmem
  have hcj := idx_lt (w := J.h) (x := colsOf J) (by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.2, b1.2, b2.2, b3.2])
  have hcols : ∀ i, colsOf J i < J.h := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.2, b1.2, b2.2, b3.2]
  have hax2 : axBB J.h [digit J.h 0 (idx J.h (colsOf J)), digit J.h 1 (idx J.h (colsOf J)),
      digit J.h 2 (idx J.h (colsOf J)), digit J.h 3 (idx J.h (colsOf J))] = true := by
    rw [show digit J.h 0 (idx J.h (colsOf J)) = J.s0.2 from digit_idx hcols 0,
      show digit J.h 1 (idx J.h (colsOf J)) = J.t0.2 from digit_idx hcols 1,
      show digit J.h 2 (idx J.h (colsOf J)) = J.s1.2 from digit_idx hcols 2,
      show digit J.h 3 (idx J.h (colsOf J)) = J.t1.2 from digit_idx hcols 3]
    simpa [ysOf, Inst.ends] using ay
  have hlane := laneI_cols hJwf
  have hcc2 : ∀ σ ∈ stabL J.w (rowsOf J), keyR (fun i => digit J.h i (idx J.h (colsOf J))) ≤
      keyR (yS0 σ J.h (fun i => digit J.h i (idx J.h (colsOf J)))) := by
    simpa only [digit_idx hcols] using hcc
  have htc2 : J.w = J.h → keyR (rowsOf J) ≤ keyR (fun i => digit J.h i (idx J.h (colsOf J))) := by
    simpa only [digit_idx hcols] using htc
  have hres := hok _ hcj hax2 hcc2 htc2
    (fun i => by have := hxw i; omega) (by rw [hlane]; exact hJwf)
  rw [hlane] at hres
  rcases hres with hs | hp
  · exact Sym.solvable hwf hs
  · exfalso
    obtain ⟨ρ, hρ⟩ := inv_exists σ0
    have hPJ : Passes (ρ.apply J) := by rw [hJ, hρ I hwf]; exact hP
    have := passes_refl_of_image hJD ρ hPJ
    unfold passImgB at hp
    rcases this with h | h | h | h <;> simp [h] at hp

abbrev SliceData := (Fin 4 → ℕ) × List (CTree TPos × Sym) × List ℕ × List (ℕ × Sym × CTree TPos) ×
  List (ℕ × ℕ × ℕ × ℕ × ℕ)

theorem boxCert_of_certs {w h : ℕ} (certs : List SliceData) (hrows : rowsOK w (certs.map (·.1)) = true)
    (hall : List.Forall (fun c : SliceData => sliceOK w h c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 = true) certs)
    (hh : 0 < h := by decide) (h32 : h ≤ 32 := by decide) (hw32 : w ≤ 32 := by decide) :
    BoxCert w h := by
  refine ⟨certs.map (·.1), hrows, fun x hx => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact sliceGood_of_sliceOK hh h32 hw32 (List.forall_iff_forall_mem.mp hall c hc)

theorem boxCert_of_good {w h : ℕ} (reps : List (Fin 4 → ℕ)) (hrows : rowsOK w reps = true)
    (hall : List.Forall (SliceGood w h) reps) : BoxCert w h :=
  ⟨reps, hrows, List.forall_iff_forall_mem.mp hall⟩

/-- **The finite facts from slice certificates.** -/
theorem finite_of_boxes (hb : ∀ w h, 11 ≤ w → w ≤ h → h ≤ 16 → BoxCert w h)
    (hnone : ∀ n, 17 ≤ n → n ≤ 22 → noneOK n = true) : FactsFiniteB := by
  refine ⟨fun I hI hw hh hP hR => Or.inr ?_⟩
  by_cases hwh : I.w ≤ I.h
  · exact finite_le hb hnone I hI hw hh hwh hP hR
  · have hIT : InDom I.transpose := ⟨hI.2.1, hI.1, wf_transpose hI.2.2⟩
    have hRT : ¬ ReducibleB I.transpose := by
      clear hb hnone
      intro h; apply hR
      unfold ReducibleB Reducible at h ⊢
      rw [Inst.transpose_transpose] at h
      tauto
    have := finite_le hb hnone I.transpose hIT hh hw (by simp [Inst.transpose]; omega) (passT hI hP) hRT
    exact solvable_transpose_iff.mp this

/-- **Theorem A from slice certificates**, band compressions included. -/
theorem theoremA_boxes (hb : ∀ w h, 11 ≤ w → w ≤ h → h ≤ 16 → BoxCert w h)
    (hnone : ∀ n, 17 ≤ n → n ≤ 22 → noneOK n = true) :
    ∀ I, InDom I → Passes I → Solvable I :=
  theoremA_B (finite_of_boxes hb hnone)

end ZZN.BoxK
