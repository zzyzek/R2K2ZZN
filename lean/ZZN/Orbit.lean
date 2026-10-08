-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.PassSym

/-!
# Orbits under the symmetries `Sym`

Composing a symmetry with a `Sym` image gives a `Sym` image (`comp_apply`), and every `Sym` has an
inverse (`inv_exists`). So a valid move of any image is a valid move of the instance
(`MoveOK.of_apply`), and an instance is an image of each of its images.
-/

namespace ZZN

open GridHam

/-! ### Relations between the generators -/

theorem reflectY_eq (X : Inst) : X.reflectY =
    ⟨X.w, X.h, (X.s0.1, X.h - 1 - X.s0.2), (X.t0.1, X.h - 1 - X.t0.2), (X.s1.1, X.h - 1 - X.s1.2),
      (X.t1.1, X.h - 1 - X.t1.2)⟩ := by
  simp [Inst.reflectY, Inst.reflectX, Inst.transpose, reflX]

theorem transpose_reflectY (X : Inst) : X.reflectY.transpose = X.transpose.reflectX := by
  unfold Inst.reflectY; rw [Inst.transpose_transpose]

theorem transpose_reflectX (X : Inst) : X.reflectX.transpose = X.transpose.reflectY := by
  unfold Inst.reflectY; rw [Inst.transpose_transpose]

theorem reflectX_reflectY (X : Inst) : X.reflectY.reflectX = X.reflectX.reflectY := by
  rw [reflectY_eq, reflectY_eq]; simp [Inst.reflectX, reflX]

theorem reflectX_reflectX {X : Inst} (hX : X.WellFormed) : X.reflectX.reflectX = X := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hX
  obtain ⟨w, h, s0, t0, s1, t1⟩ := X
  simp only [InBounds] at b0 b1 b2 b3
  simp only [Inst.reflectX, reflX, Inst.mk.injEq]
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_⟩ <;> exact Prod.ext (by simp; omega) rfl

theorem reflectY_reflectY {X : Inst} (hX : X.WellFormed) : X.reflectY.reflectY = X := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hX
  obtain ⟨w, h, s0, t0, s1, t1⟩ := X
  simp only [InBounds] at b0 b1 b2 b3
  rw [reflectY_eq, reflectY_eq]
  simp only [Inst.mk.injEq]
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_⟩ <;> exact Prod.ext rfl (by simp; omega)

/-- The labels commute with the geometry. -/
theorem lab_transpose (σ : Sym) (X : Inst) : (σ.lab X).transpose = σ.lab X.transpose := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases r0 <;> cases r1 <;> cases sw <;> rfl

theorem lab_reflectX (σ : Sym) (X : Inst) : (σ.lab X).reflectX = σ.lab X.reflectX := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases r0 <;> cases r1 <;> cases sw <;> rfl

theorem lab_reflectY (σ : Sym) (X : Inst) : (σ.lab X).reflectY = σ.lab X.reflectY := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  cases r0 <;> cases r1 <;> cases sw <;> rfl

/-! ### Each generator after a `Sym` image -/

def Sym.gTr (σ : Sym) : Sym := ⟨!σ.tr, σ.ry, σ.rx, σ.r0, σ.r1, σ.sw⟩
def Sym.gRx (σ : Sym) : Sym := ⟨σ.tr, !σ.rx, σ.ry, σ.r0, σ.r1, σ.sw⟩
def Sym.gRy (σ : Sym) : Sym := ⟨σ.tr, σ.rx, !σ.ry, σ.r0, σ.r1, σ.sw⟩
def Sym.g0 (σ : Sym) : Sym :=
  if σ.sw then ⟨σ.tr, σ.rx, σ.ry, σ.r0, !σ.r1, σ.sw⟩ else ⟨σ.tr, σ.rx, σ.ry, !σ.r0, σ.r1, σ.sw⟩
def Sym.g1 (σ : Sym) : Sym :=
  if σ.sw then ⟨σ.tr, σ.rx, σ.ry, !σ.r0, σ.r1, σ.sw⟩ else ⟨σ.tr, σ.rx, σ.ry, σ.r0, !σ.r1, σ.sw⟩
def Sym.gSw (σ : Sym) : Sym := ⟨σ.tr, σ.rx, σ.ry, σ.r0, σ.r1, !σ.sw⟩

theorem apply_gTr (σ : Sym) (I : Inst) : (σ.apply I).transpose = σ.gTr.apply I := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.apply Sym.gTr
  rw [lab_transpose, show Sym.lab ⟨!tr, ry, rx, r0, r1, sw⟩ = Sym.lab ⟨tr, rx, ry, r0, r1, sw⟩ from rfl]
  congr 1
  unfold Sym.geo
  dsimp only
  cases tr <;> cases rx <;> cases ry <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, transpose_reflectY,
      transpose_reflectX, Inst.transpose_transpose, reflectX_reflectY]

theorem apply_gRx (σ : Sym) {I : Inst} (hI : I.WellFormed) : (σ.apply I).reflectX = σ.gRx.apply I := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.apply Sym.gRx
  rw [lab_reflectX, show Sym.lab ⟨tr, !rx, ry, r0, r1, sw⟩ = Sym.lab ⟨tr, rx, ry, r0, r1, sw⟩ from rfl]
  congr 1
  unfold Sym.geo
  dsimp only
  have h1 : (if tr then I.transpose else I).WellFormed := by
    split
    · exact wf_transpose hI
    · exact hI
  generalize (if tr then I.transpose else I) = Y at h1 ⊢
  cases rx <;> cases ry <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, reflectX_reflectY,
      reflectX_reflectX h1]

theorem apply_gRy (σ : Sym) {I : Inst} (hI : I.WellFormed) : (σ.apply I).reflectY = σ.gRy.apply I := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.apply Sym.gRy
  rw [lab_reflectY, show Sym.lab ⟨tr, rx, !ry, r0, r1, sw⟩ = Sym.lab ⟨tr, rx, ry, r0, r1, sw⟩ from rfl]
  congr 1
  unfold Sym.geo
  dsimp only
  have h2 := Sym.wf_geo ⟨tr, rx, false, r0, r1, sw⟩ hI
  unfold Sym.geo at h2
  dsimp only at h2
  simp only [Bool.false_eq_true, ↓reduceIte] at h2
  generalize (if rx then (if tr then I.transpose else I).reflectX else (if tr then I.transpose else I)) = Y
    at h2 ⊢
  cases ry <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
    reflectY_reflectY h2]

theorem apply_g0 (σ : Sym) (I : Inst) : (σ.apply I).rev0 = σ.g0.apply I := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.apply Sym.g0 Sym.lab
  cases r0 <;> cases r1 <;> cases sw <;> rfl

theorem apply_g1 (σ : Sym) (I : Inst) : (σ.apply I).rev1 = σ.g1.apply I := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.apply Sym.g1 Sym.lab
  cases r0 <;> cases r1 <;> cases sw <;> rfl

theorem apply_gSw (σ : Sym) (I : Inst) : (σ.apply I).swapColors = σ.gSw.apply I := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.apply Sym.gSw Sym.lab
  cases r0 <;> cases r1 <;> cases sw <;> rfl

/-! ### Composition and inverses -/

deriving instance DecidableEq for Sym

def Sym.comp (σ τ : Sym) : Sym :=
  let t1 := if σ.tr then τ.gTr else τ
  let t2 := if σ.rx then t1.gRx else t1
  let t3 := if σ.ry then t2.gRy else t2
  let t4 := if σ.r0 then t3.g0 else t3
  let t5 := if σ.r1 then t4.g1 else t4
  if σ.sw then t5.gSw else t5

theorem ite_gTr (b : Bool) (τ : Sym) (I : Inst) :
    (if b then (τ.apply I).transpose else τ.apply I) = (if b then τ.gTr else τ).apply I := by
  cases b
  · rfl
  · exact apply_gTr τ I

theorem ite_gRx (b : Bool) (τ : Sym) {I : Inst} (hI : I.WellFormed) :
    (if b then (τ.apply I).reflectX else τ.apply I) = (if b then τ.gRx else τ).apply I := by
  cases b
  · rfl
  · exact apply_gRx τ hI

theorem ite_gRy (b : Bool) (τ : Sym) {I : Inst} (hI : I.WellFormed) :
    (if b then (τ.apply I).reflectY else τ.apply I) = (if b then τ.gRy else τ).apply I := by
  cases b
  · rfl
  · exact apply_gRy τ hI

theorem ite_g0 (b : Bool) (τ : Sym) (I : Inst) :
    (if b then (τ.apply I).rev0 else τ.apply I) = (if b then τ.g0 else τ).apply I := by
  cases b
  · rfl
  · exact apply_g0 τ I

theorem ite_g1 (b : Bool) (τ : Sym) (I : Inst) :
    (if b then (τ.apply I).rev1 else τ.apply I) = (if b then τ.g1 else τ).apply I := by
  cases b
  · rfl
  · exact apply_g1 τ I

theorem ite_gSw (b : Bool) (τ : Sym) (I : Inst) :
    (if b then (τ.apply I).swapColors else τ.apply I) = (if b then τ.gSw else τ).apply I := by
  cases b
  · rfl
  · exact apply_gSw τ I

theorem comp_apply (σ τ : Sym) {I : Inst} (hI : I.WellFormed) :
    σ.apply (τ.apply I) = (σ.comp τ).apply I := by
  obtain ⟨a, b, c, d, e, f⟩ := σ
  show Sym.lab ⟨a, b, c, d, e, f⟩ (Sym.geo ⟨a, b, c, d, e, f⟩ (τ.apply I)) = _
  unfold Sym.geo Sym.lab Sym.comp
  dsimp only
  rw [ite_gTr, ite_gRx _ _ hI, ite_gRy _ _ hI, ite_g0, ite_g1, ite_gSw]

def Sym.id : Sym := ⟨false, false, false, false, false, false⟩

theorem Sym.id_apply (I : Inst) : Sym.id.apply I = I := rfl

def allSym : List Sym :=
  [false, true].flatMap fun tr => [false, true].flatMap fun rx => [false, true].flatMap fun ry =>
    [false, true].flatMap fun r0 => [false, true].flatMap fun r1 => [false, true].map fun sw =>
      ⟨tr, rx, ry, r0, r1, sw⟩

theorem mem_allSym (σ : Sym) : σ ∈ allSym := by
  obtain ⟨a, b, c, d, e, f⟩ := σ
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

def Sym.inv (τ : Sym) : Sym := (allSym.find? (fun ρ => ρ.comp τ == Sym.id)).getD Sym.id

theorem Sym.inv_comp (τ : Sym) : τ.inv.comp τ = Sym.id := by
  obtain ⟨a, b, c, d, e, f⟩ := τ
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem inv_exists (τ : Sym) : ∃ ρ : Sym, ∀ I : Inst, I.WellFormed → ρ.apply (τ.apply I) = I :=
  ⟨τ.inv, fun I hI => by rw [comp_apply τ.inv τ hI, Sym.inv_comp, Sym.id_apply]⟩

/-- A valid move of an image is a valid move of the instance. -/
theorem MoveOK.of_apply {τ : Sym} {I : Inst} (hI : I.WellFormed) (h : MoveOK (τ.apply I)) : MoveOK I := by
  obtain ⟨σ, hc⟩ := h
  exact ⟨σ.comp τ, by rw [← comp_apply σ τ hI]; exact hc⟩

/-! ### Passing images -/

theorem inDom_wf {I : Inst} (hI : InDom I) : I.WellFormed := hI.2.2

theorem inDom_reflectX {I : Inst} (hI : InDom I) : InDom I.reflectX :=
  ⟨hI.1, hI.2.1, wf_reflectX hI.2.2⟩

theorem inDom_reflectY {I : Inst} (hI : InDom I) : InDom I.reflectY :=
  inDom_transpose (inDom_reflectX (inDom_transpose hI))

theorem inDom_lab (σ : Sym) {I : Inst} (hI : InDom I) : InDom (σ.lab I) := by
  obtain ⟨hw, hh, hwf⟩ := hI
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.lab
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · cases r0 <;> cases r1 <;> cases sw <;> exact hw
  · cases r0 <;> cases r1 <;> cases sw <;> exact hh
  · have h3 : (if r0 then I.rev0 else I).WellFormed := by
      split
      · exact wf_rev0 hwf
      · exact hwf
    have h4 : (if r1 then (if r0 then I.rev0 else I).rev1 else (if r0 then I.rev0 else I)).WellFormed := by
      split
      · exact wf_rev1 h3
      · exact h3
    split
    · exact wf_swapColors h4
    · exact h4

theorem passes_lab (σ : Sym) {I : Inst} (hI : InDom I) : Passes (σ.lab I) ↔ Passes I := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.lab
  dsimp only
  have h3 : InDom (if r0 then I.rev0 else I) := by
    split
    · exact ⟨hI.1, hI.2.1, wf_rev0 hI.2.2⟩
    · exact hI
  have h4 : InDom (if r1 then (if r0 then I.rev0 else I).rev1 else (if r0 then I.rev0 else I)) := by
    split
    · exact ⟨h3.1, h3.2.1, wf_rev1 h3.2.2⟩
    · exact h3
  have e3 : Passes (if r0 then I.rev0 else I) ↔ Passes I := by
    split
    · exact passes_rev0 hI
    · exact Iff.rfl
  have e4 : Passes (if r1 then (if r0 then I.rev0 else I).rev1 else (if r0 then I.rev0 else I)) ↔
      Passes I := by
    split
    · exact (passes_rev1 h3).trans e3
    · exact e3
  split
  · exact (passes_swapColors h4).trans e4
  · exact e4

theorem passes_transpose_iff {I : Inst} (hI : InDom I) : Passes I.transpose ↔ Passes I := by
  constructor
  · intro h
    have := passT (inDom_transpose hI) h
    rwa [Inst.transpose_transpose] at this
  · exact passT hI

/-- If some image of `J` passes, then `J` or one of its three reflections passes. -/
theorem passes_refl_of_image {J : Inst} (hJ : InDom J) (ρ : Sym) (h : Passes (ρ.apply J)) :
    Passes J ∨ Passes J.reflectX ∨ Passes J.reflectY ∨ Passes J.reflectX.reflectY := by
  obtain ⟨a, b, c, d, e, f⟩ := ρ
  have hg := Sym.wf_geo ⟨a, b, c, d, e, f⟩ hJ.2.2
  have hD : InDom (Sym.geo ⟨a, b, c, d, e, f⟩ J) := by
    refine ⟨?_, ?_, hg⟩ <;>
    · unfold Sym.geo
      cases a <;> cases b <;> cases c <;>
        simp [Inst.transpose, Inst.reflectX, reflectY_eq, hJ.1, hJ.2.1]
  have h1 := (passes_lab ⟨a, b, c, d, e, f⟩ hD).mp h
  unfold Sym.geo at h1
  dsimp only at h1
  cases a <;> cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1
  · exact Or.inl h1
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inr h1))
  · exact Or.inl ((passes_transpose_iff hJ).mp h1)
  · rw [← transpose_reflectX] at h1
    exact Or.inr (Or.inl ((passes_transpose_iff (inDom_reflectX hJ)).mp h1))
  · rw [← transpose_reflectY] at h1
    exact Or.inr (Or.inr (Or.inl ((passes_transpose_iff (inDom_reflectY hJ)).mp h1)))
  · rw [← transpose_reflectY, ← transpose_reflectX] at h1
    have := (passes_transpose_iff (inDom_reflectX (inDom_reflectY hJ))).mp h1
    rw [reflectX_reflectY] at this
    exact Or.inr (Or.inr (Or.inr this))

end ZZN
