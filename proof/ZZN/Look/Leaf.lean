/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Look.Wit
public import ZZN.Look.Build
public import ZZN.Look.Sym

@[expose] public section

/-!
# Irreducible leaves by certificate lookup

For a table `tab w h` of slice certificates (`TabOK`), `lookJ tab J` solves an irreducible instance
with sides 11–16: move it to its canonical symmetric form `K` (least `key2` over `Gbox`), find the
slice of `K`'s rows, and take the first template that checks on a symmetry of `K` (built by `tsol`)
or the stored pair of paths for `K`'s lane; then pull the solution back.

`lookJ_sound`: every answer is a solution. `lookJ_complete`: on a well-formed instance with sides
11–16, no `RedX` or `RedB` on either axis, that passes, the lookup answers.
-/

namespace ZZN.Look

open ZZN ZZN.Cut ZZN.BoxK GridHam

theorem wf_apply (σ : Sym) {I : Inst} (hI : I.WellFormed) : (σ.apply I).WellFormed := by
  have g := σ.wf_geo hI
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  simp only [Sym.apply, Sym.lab]
  generalize Sym.geo _ I = G at g ⊢
  obtain ⟨b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := g
  cases r0 <;> cases r1 <;> cases sw <;>
    simp only [Inst.rev0, Inst.rev1, Inst.swapColors, Bool.false_eq_true, ↓reduceIte] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | assumption | exact Ne.symm ‹_›

/-- The table is certified: its rows cover the representatives, and each slice has witnesses. -/
def TabOK (tab : ℕ → ℕ → List CData) : Prop :=
  ∀ w h, 11 ≤ w → w ≤ h → h ≤ 16 →
    rowsOK w ((tab w h).map (·.1)) = true ∧
    List.Forall (fun d : CData => SliceW w h d.1 d.2.2.1 d.2.2.2.2) (tab w h)

/-- Solve `K` from one slice certificate. -/
def entryP (K : Inst) (d : CData) : Option (List Coord × List Coord) :=
  match d.2.2.1.find? (fun e => tcheck e.1 (e.2.apply K)) with
  | some e => some (unSym e.2 K (tsol e.1 (e.2.apply K)))
  | none =>
    match d.2.2.2.2.find? (fun e => e.1 == idx K.h (colsOf K) &&
        solF K (decPath e.2.1 e.2.2.1) (decPath e.2.2.2.1 e.2.2.2.2)) with
    | some e => some (decPath e.2.1 e.2.2.1, decPath e.2.2.2.1 e.2.2.2.2)
    | none => none

theorem entryP_sound {K : Inst} (hK : K.WellFormed) {d : CData} {s : List Coord × List Coord}
    (h : entryP K d = some s) : IsSolution K s.1 s.2 := by
  unfold entryP at h
  split at h
  · rename_i e he
    have hc : tcheck e.1 (e.2.apply K) = true := by simpa using List.find?_some he
    cases h
    exact unSym_sol e.2 hK (tsol_sound e.1 hc)
  · split at h
    · rename_i e he
      have hc := List.find?_some he
      simp only [Bool.and_eq_true] at hc
      cases h
      exact solF_sound hc.2
    · cases h

theorem entryP_isSome {K : Inst} {d : CData}
    (h : (∃ e ∈ d.2.2.1, tcheck e.1 (e.2.apply K) = true) ∨
      (∃ e ∈ d.2.2.2.2, e.1 = idx K.h (colsOf K) ∧
        solF K (decPath e.2.1 e.2.2.1) (decPath e.2.2.2.1 e.2.2.2.2) = true)) :
    (entryP K d).isSome := by
  unfold entryP
  split
  · rfl
  · rename_i hn
    rcases h with ⟨e, he, hc⟩ | ⟨e, he, hj, hs⟩
    · exact absurd hc (by simpa using List.find?_eq_none.mp hn e he)
    · split
      · rfl
      · rename_i hn2
        have := List.find?_eq_none.mp hn2 e he
        simp [hj, hs] at this

/-- Rows equal. -/
def sameX (a b : Fin 4 → ℕ) : Bool := (List.finRange 4).all fun i => a i == b i

theorem sameX_iff (a b : Fin 4 → ℕ) : sameX a b = true ↔ a = b := by
  simp only [sameX, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  exact ⟨funext, fun h i => h ▸ rfl⟩

/-- Solve a canonical `K` from the table. -/
def lookK (tab : ℕ → ℕ → List CData) (K : Inst) : Option (List Coord × List Coord) :=
  match (tab K.w K.h).find? (fun d => sameX d.1 (rowsOf K)) with
  | some d => entryP K d
  | none => none

/-- The first element of least `f`. -/
def argminS (f : Sym → ℕ) : List Sym → Sym
  | [] => Sym.id
  | a :: l => l.foldl (fun b c => if f c < f b then c else b) a

theorem foldl_min (f : Sym → ℕ) : ∀ (l : List Sym) (a : Sym),
    (l.foldl (fun b c => if f c < f b then c else b) a ∈ a :: l) ∧
    ∀ c ∈ a :: l, f (l.foldl (fun b c => if f c < f b then c else b) a) ≤ f c
  | [], a => ⟨List.mem_singleton_self a, fun c hc => by rw [List.mem_singleton.mp hc, List.foldl_nil]⟩
  | c :: l, a => by
    simp only [List.foldl_cons]
    split_ifs with hca
    · obtain ⟨m, hm⟩ := foldl_min f l c
      refine ⟨List.mem_cons_of_mem _ m, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_trans (hm c List.mem_cons_self) hca.le
      · exact hm b hb
    · obtain ⟨m, hm⟩ := foldl_min f l a
      refine ⟨?_, fun b hb => ?_⟩
      · rcases List.mem_cons.mp m with e | e
        · rw [e]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e)
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact hm _ List.mem_cons_self
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact le_trans (hm _ List.mem_cons_self) (by omega)
          · exact hm b (List.mem_cons_of_mem _ hb)

theorem argminS_spec (f : Sym → ℕ) (l : List Sym) (hl : l ≠ []) :
    argminS f l ∈ l ∧ ∀ c ∈ l, f (argminS f l) ≤ f c := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => exact foldl_min f l a

/-- `w ≤ h`: canonical form, table, pull back. -/
def lookLe (tab : ℕ → ℕ → List CData) (J : Inst) : Option (List Coord × List Coord) :=
  let σ := argminS (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)
  (lookK tab (σ.apply J)).map (unSym σ J)

/-- **The leaf lookup.** -/
def lookJ (tab : ℕ → ℕ → List CData) (J : Inst) : Option (List Coord × List Coord) :=
  if J.w ≤ J.h then lookLe tab J
  else (lookLe tab J.transpose).map fun s => (s.1.map Prod.swap, s.2.map Prod.swap)

theorem lookLe_sound (tab : ℕ → ℕ → List CData) {J : Inst} (hJ : J.WellFormed)
    {s : List Coord × List Coord} (h : lookLe tab J = some s) : IsSolution J s.1 s.2 := by
  unfold lookLe at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  set σ := argminS (fun σ => key2 (σ.apply J)) (Gbox J.w J.h)
  have hK : (σ.apply J).WellFormed := wf_apply σ hJ
  refine unSym_sol σ hJ ?_
  unfold lookK at ht
  split at ht
  · exact entryP_sound hK ht
  · cases ht

theorem lookJ_sound (tab : ℕ → ℕ → List CData) {J : Inst} (hJ : J.WellFormed)
    {s : List Coord × List Coord} (h : lookJ tab J = some s) : IsSolution J s.1 s.2 := by
  unfold lookJ at h
  split at h
  · exact lookLe_sound tab hJ h
  · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (lookLe_sound tab (wf_transpose hJ) ht).of_transpose

/-- No reduction on either axis. -/
def NoRed (J : Inst) : Prop :=
  (∀ d, ¬ RedX J d ∧ ¬ RedB J d) ∧ (∀ d, ¬ RedX J.transpose d ∧ ¬ RedB J.transpose d)

theorem lookLe_complete {tab : ℕ → ℕ → List CData} (htab : TabOK tab) {I : Inst} (hI : InDom I)
    (hw : I.w ≤ 16) (hh : I.h ≤ 16) (hwh : I.w ≤ I.h) (hP : Passes I) (hR : NoRed I) :
    (lookLe tab I).isSome := by
  have hwf := hI.2.2
  have hSI : SBB I = true := by
    unfold SBB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hI.1, by omega, hI.2.1, by omega⟩, axBB_of_noRed hwf (fun ⟨d, h⟩ => (hR.1 d).1 h)
      (fun ⟨d, h⟩ => (hR.1 d).2 h)⟩, ?_⟩
    exact axBB_of_noRed (I := I.transpose) (wf_transpose hwf)
      (fun ⟨d, h⟩ => (hR.2 d).1 h) (fun ⟨d, h⟩ => (hR.2 d).2 h)
  obtain ⟨hσ0, hmin⟩ := argminS_spec (fun σ => key2 (σ.apply I)) (Gbox I.w I.h) (Gbox_ne _ _)
  set σ0 := argminS (fun σ => key2 (σ.apply I)) (Gbox I.w I.h) with hσ0d
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
  have hle : J.w ≤ J.h := by omega
  obtain ⟨hrows, hall⟩ := htab J.w J.h w1 hle (by omega)
  have hxw : ∀ i, rowsOf J i < J.w := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.1, b1.1, b2.1, b3.1]
  have hmem := rowsOK_sound (by omega) (by omega) hrows hxw
    (by simpa [rowsOf, xsOf, Inst.ends] using ax) hrep
  obtain ⟨d0, hd0, hd0x⟩ := List.mem_map.mp hmem
  obtain ⟨d, hfd⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun d : CData => sameX d.1 (rowsOf J))).mpr
      ⟨d0, hd0, (sameX_iff _ _).mpr hd0x⟩)
  have hd := List.mem_of_find?_eq_some hfd
  have hdx : d.1 = rowsOf J := (sameX_iff _ _).mp (by simpa using List.find?_some hfd)
  have hok := List.forall_iff_forall_mem.mp hall d hd
  rw [hdx] at hok
  have hcols : ∀ i, colsOf J i < J.h := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hJwf
    intro i; fin_cases i
    exacts [b0.2, b1.2, b2.2, b3.2]
  have hcj := idx_lt (w := J.h) (x := colsOf J) hcols
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
  · unfold lookLe
    simp only [Option.isSome_map]
    show (lookK tab J).isSome
    unfold lookK
    rw [hfd]
    apply entryP_isSome
    rcases hs with hs | hs
    · exact Or.inl (by simpa [hlane] using hs)
    · exact Or.inr (by simpa [hlane] using hs)
  · exfalso
    obtain ⟨ρ, hρ⟩ := inv_exists σ0
    have hPJ : Passes (ρ.apply J) := by rw [hJ, hρ I hwf]; exact hP
    have := passes_refl_of_image hJD ρ hPJ
    unfold passImgB at hp
    rcases this with h | h | h | h <;> simp [h] at hp

theorem lookJ_complete {tab : ℕ → ℕ → List CData} (htab : TabOK tab) {I : Inst} (hI : InDom I)
    (hw : I.w ≤ 16) (hh : I.h ≤ 16) (hP : Passes I) (hR : NoRed I) : (lookJ tab I).isSome := by
  unfold lookJ
  split
  · exact lookLe_complete htab hI hw hh (by omega) hP hR
  · simp only [Option.isSome_map]
    refine lookLe_complete htab (inDom_transpose hI) hh hw (by simp [Inst.transpose]; omega)
      (passT hI hP) ⟨?_, ?_⟩
    · exact hR.2
    · rw [Inst.transpose_transpose]; exact hR.1

end ZZN.Look
