/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.PassB
public import ZZN.Finite2

@[expose] public section

/-!
# No reduction on an axis, band compressions included

`redGenB`: `redGen` or the band clause `bandGen` (`RedB` as a test on the coordinates). `axBB`: no
reduction on this axis. `SBB`: the search region, unchanged by every `Sym` (`SBB_apply`).
-/

namespace ZZN

open GridHam

/-- `RedB`, for given tests of free lines and endpoints below / above. The band condition: every
line `k < d` with `n < k + 8`, and every line `d + 2 ≤ k < 8`, is free. -/
def bandGen (n : ℕ) (F B A : ℕ → Bool) (d : ℕ) : Bool :=
  decide (13 ≤ n) && decide (5 ≤ d) && decide (d + 7 ≤ n) && F d && F (d + 1) &&
    ((decide (1 ≤ d) && F (d - 1)) || F (d + 2)) && B d && A (d + 1) &&
    (List.range n).all (fun k => !(decide (k < d) && decide (n < k + 8)) || F k) &&
    (List.range n).all (fun k => !(decide (d + 2 ≤ k) && decide (k < 7)) || F k)

def redGenB (n : ℕ) (F B A : ℕ → Bool) (d : ℕ) : Bool := redGen n F B A d || bandGen n F B A d

def redXBB (n : ℕ) (xs : List ℕ) (d : ℕ) : Bool := redGenB n (freeB xs) (belowB xs) (aboveB xs) d

/-- No reduction on this axis, band compressions included. -/
def axBB (n : ℕ) (xs : List ℕ) : Bool := (List.range n).all fun d => !redXBB n xs d

theorem redB_of_bandB {I : Inst} {d : ℕ} (hb : ∀ e ∈ I.ends, e.1 < I.w)
    (h : bandGen I.w (freeB (xsOf I)) (belowB (xsOf I)) (aboveB (xsOf I)) d = true) : RedB I d := by
  unfold bandGen at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, freeB_iff, belowB_iff, aboveB_iff, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h13, h5⟩, h7⟩, f0⟩, f1⟩, fn⟩, hbl⟩, hab⟩, l1⟩, l2⟩ := h
  refine ⟨h13, h5, h7, f0, f1, by omega, ?_, hbl, hab, fun e he => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rcases fn with ⟨a, b⟩ | b
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr b
  · by_contra hc
    rcases l1 e.1 (hb e he) with (l | l) | l
    · exact l hx
    · exact l (by omega)
    · exact l e he rfl
  · by_contra hc
    rcases l2 e.1 (hb e he) with (l | l) | l
    · exact l hx
    · exact l (by omega)
    · exact l e he rfl

theorem axBB_of_noRed {I : Inst} (hI : I.WellFormed) (h1 : ¬ ∃ d, RedX I d)
    (h2 : ¬ ∃ d, RedB I d) : axBB I.w (xsOf I) = true := by
  have hb : ∀ e ∈ I.ends, e.1 < I.w := by
    obtain ⟨b0, b1, b2, b3, -⟩ := hI
    intro e he
    simp only [Inst.ends, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact b0.1
    · exact b1.1
    · exact b2.1
    · exact b3.1
  unfold axBB
  rw [List.all_eq_true]
  intro d _
  unfold redXBB redGenB
  cases hr : redGen I.w (freeB (xsOf I)) (belowB (xsOf I)) (aboveB (xsOf I)) d
  · cases hb' : bandGen I.w (freeB (xsOf I)) (belowB (xsOf I)) (aboveB (xsOf I)) d
    · rfl
    · exact absurd ⟨d, redB_of_bandB hb hb'⟩ h2
  · exact absurd ⟨d, redX_of_redXB hr⟩ h1

theorem axBB_perm {n : ℕ} {xs xs' : List ℕ} (hp : xs.Perm xs') : axBB n xs' = axBB n xs := by
  unfold axBB redXBB redGenB redGen bandGen freeB belowB aboveB
  simp only [hp.all_eq, hp.any_eq]

theorem bandGen_refl {n : ℕ} {F B A F' B' A' : ℕ → Bool}
    (hF : ∀ k, k < n → F k = F' (n - 1 - k)) (hB : ∀ k, k < n → B k = A' (n - 1 - k))
    (hA : ∀ k, k < n → A k = B' (n - 1 - k)) {d : ℕ} (h : bandGen n F B A d = true) :
    bandGen n F' B' A' (n - 2 - d) = true ∧ d + 2 ≤ n := by
  unfold bandGen at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h13, h5⟩, h7⟩, f0⟩, f1⟩, fn⟩, hbl⟩, hab⟩, l1⟩, l2⟩ := h
  have eF : ∀ k, k < n → F' k = F (n - 1 - k) := by
    intro k hk; rw [hF (n - 1 - k) (by omega), show n - 1 - (n - 1 - k) = k by omega]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h13, by omega⟩, by omega⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, by omega⟩
  · rw [eF _ (by omega), show n - 1 - (n - 2 - d) = d + 1 by omega]; exact f1
  · rw [eF _ (by omega), show n - 1 - (n - 2 - d + 1) = d by omega]; exact f0
  · rcases fn with ⟨a, b⟩ | b
    · right; rw [eF _ (by omega), show n - 1 - (n - 2 - d + 2) = d - 1 by omega]; exact b
    · left; refine ⟨by omega, ?_⟩
      rw [eF _ (by omega), show n - 1 - (n - 2 - d - 1) = d + 2 by omega]; exact b
  · have := hA (d + 1) (by omega)
    rw [hab, show n - 1 - (d + 1) = n - 2 - d by omega] at this
    exact this.symm
  · have := hB d (by omega)
    rw [hbl, show n - 1 - d = n - 2 - d + 1 by omega] at this
    exact this.symm
  · intro k hk
    rcases l2 (n - 1 - k) (by omega) with (l | l) | l
    · left; left; omega
    · left; right; omega
    · right; rw [eF k hk]; exact l
  · intro k hk
    rcases l1 (n - 1 - k) (by omega) with (l | l) | l
    · left; left; omega
    · left; right; omega
    · right; rw [eF k hk]; exact l

theorem redGenB_refl {n : ℕ} {F B A F' B' A' : ℕ → Bool}
    (hF : ∀ k, k < n → F k = F' (n - 1 - k)) (hB : ∀ k, k < n → B k = A' (n - 1 - k))
    (hA : ∀ k, k < n → A k = B' (n - 1 - k)) {d : ℕ} (h : redGenB n F B A d = true) :
    redGenB n F' B' A' (n - 2 - d) = true ∧ d + 2 ≤ n := by
  unfold redGenB at h ⊢
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨a, b⟩ := redGen_refl hF hB hA h
    exact ⟨by simp [a], b⟩
  · obtain ⟨a, b⟩ := bandGen_refl hF hB hA h
    exact ⟨by simp [a], b⟩

theorem axBB_refl_imp {n : ℕ} {xs : List ℕ} (hx : ∀ x ∈ xs, x < n) (h : axBB n xs = true) :
    axBB n (reflL n xs) = true := by
  unfold axBB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro d hd
  cases hr : redXBB n (reflL n xs) d
  · rfl
  · exfalso
    unfold redXBB at hr
    have key := redGenB_refl (F' := freeB xs) (B' := belowB xs) (A' := aboveB xs) ?_ ?_ ?_ hr
    · have := h (n - 2 - d) (List.mem_range.mpr (by omega))
      unfold redXBB at this
      rw [key.1] at this
      exact absurd this (by simp)
    · intro k hk
      unfold freeB reflL
      rw [List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp, bne_iff_ne, ne_eq]
      constructor
      · intro H x hxm; have := hx x hxm; have := H x hxm; omega
      · intro H x hxm; have := hx x hxm; have := H x hxm; omega
    · intro k hk
      unfold belowB aboveB reflL
      rw [List.any_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Function.comp, decide_eq_true_eq]
      constructor
      · rintro ⟨x, hxm, H⟩; exact ⟨x, hxm, by have := hx x hxm; omega⟩
      · rintro ⟨x, hxm, H⟩; exact ⟨x, hxm, by have := hx x hxm; omega⟩
    · intro k hk
      unfold belowB aboveB reflL
      rw [List.any_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Function.comp, decide_eq_true_eq]
      constructor
      · rintro ⟨x, hxm, H⟩; exact ⟨x, hxm, by have := hx x hxm; omega⟩
      · rintro ⟨x, hxm, H⟩; exact ⟨x, hxm, by have := hx x hxm; omega⟩

theorem axBB_refl {n : ℕ} {xs : List ℕ} (hx : ∀ x ∈ xs, x < n) : axBB n (reflL n xs) = axBB n xs := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨fun h => ?_, axBB_refl_imp hx⟩
  have hx' : ∀ x ∈ reflL n xs, x < n := by
    intro x hxm
    unfold reflL at hxm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxm
    have := hx y hy
    omega
  have e : reflL n (reflL n xs) = xs := by
    unfold reflL
    rw [List.map_map]
    conv_rhs => rw [← List.map_id xs]
    apply List.map_congr_left
    intro x hxm
    have := hx x hxm
    simp only [Function.comp, id]
    omega
  have := axBB_refl_imp hx' h
  rwa [e] at this

/-- Both sides in `[11, 22]` and no reduction on either axis. -/
def SBB (I : Inst) : Bool :=
  decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) && axBB I.w (xsOf I) && axBB I.h (ysOf I)

theorem SBB_transpose (I : Inst) : SBB I.transpose = SBB I := by
  unfold SBB
  have e1 : xsOf I.transpose = ysOf I := rfl
  have e2 : ysOf I.transpose = xsOf I := rfl
  have e3 : decide (11 ≤ I.transpose.w ∧ I.transpose.w ≤ 22 ∧ 11 ≤ I.transpose.h ∧ I.transpose.h ≤ 22) =
      decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) := by
    show decide (11 ≤ I.h ∧ I.h ≤ 22 ∧ 11 ≤ I.w ∧ I.w ≤ 22) = _
    simp only [decide_eq_decide]
    tauto
  rw [e1, e2, e3]
  simp only [Inst.transpose]
  rw [Bool.and_assoc, Bool.and_comm (axBB I.h _), ← Bool.and_assoc]

theorem SBB_reflectX {I : Inst} (hI : I.WellFormed) : SBB I.reflectX = SBB I := by
  unfold SBB
  have e1 : xsOf I.reflectX = reflL I.w (xsOf I) := rfl
  have e2 : ysOf I.reflectX = ysOf I := rfl
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) && axBB I.w (xsOf I.reflectX) &&
    axBB I.h (ysOf I.reflectX)) = _
  rw [e1, e2, axBB_refl (bounds_x hI)]

theorem SBB_reflectY {I : Inst} (hI : I.WellFormed) : SBB I.reflectY = SBB I := by
  unfold Inst.reflectY
  rw [SBB_transpose, SBB_reflectX (wf_transpose hI), SBB_transpose]

theorem SBB_rev0 (I : Inst) : SBB I.rev0 = SBB I := by
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axBB I.w [I.t0.1, I.s0.1, I.s1.1, I.t1.1] && axBB I.h [I.t0.2, I.s0.2, I.s1.2, I.t1.2]) =
    (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axBB I.w [I.s0.1, I.t0.1, I.s1.1, I.t1.1] && axBB I.h [I.s0.2, I.t0.2, I.s1.2, I.t1.2])
  rw [axBB_perm (List.Perm.swap I.t0.1 I.s0.1 _), axBB_perm (List.Perm.swap I.t0.2 I.s0.2 _)]

theorem SBB_rev1 (I : Inst) : SBB I.rev1 = SBB I := by
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axBB I.w [I.s0.1, I.t0.1, I.t1.1, I.s1.1] && axBB I.h [I.s0.2, I.t0.2, I.t1.2, I.s1.2]) =
    (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axBB I.w [I.s0.1, I.t0.1, I.s1.1, I.t1.1] && axBB I.h [I.s0.2, I.t0.2, I.s1.2, I.t1.2])
  rw [axBB_perm (((List.Perm.swap I.t1.1 I.s1.1 []).cons _).cons _),
    axBB_perm (((List.Perm.swap I.t1.2 I.s1.2 []).cons _).cons _)]

theorem SBB_swapColors (I : Inst) : SBB I.swapColors = SBB I := by
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axBB I.w ([I.s1.1, I.t1.1] ++ [I.s0.1, I.t0.1]) && axBB I.h ([I.s1.2, I.t1.2] ++ [I.s0.2, I.t0.2])) =
    (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axBB I.w ([I.s0.1, I.t0.1] ++ [I.s1.1, I.t1.1]) && axBB I.h ([I.s0.2, I.t0.2] ++ [I.s1.2, I.t1.2]))
  rw [axBB_perm (List.perm_append_comm (l₁ := [I.s0.1, I.t0.1]) (l₂ := [I.s1.1, I.t1.1])),
    axBB_perm (List.perm_append_comm (l₁ := [I.s0.2, I.t0.2]) (l₂ := [I.s1.2, I.t1.2]))]

theorem SBB_apply (σ : Sym) {I : Inst} (hI : I.WellFormed) : SBB (σ.apply I) = SBB I := by
  obtain ⟨a, b, c, d, e, f⟩ := σ
  show SBB (Sym.lab _ (Sym.geo _ I)) = SBB I
  have hg := Sym.wf_geo ⟨a, b, c, d, e, f⟩ hI
  have L : SBB (Sym.lab ⟨a, b, c, d, e, f⟩ (Sym.geo ⟨a, b, c, d, e, f⟩ I)) =
      SBB (Sym.geo ⟨a, b, c, d, e, f⟩ I) := by
    unfold Sym.lab
    dsimp only
    generalize Sym.geo _ I = X
    cases d <;> cases e <;> cases f <;>
      simp only [Bool.false_eq_true, ↓reduceIte, SBB_rev0, SBB_rev1, SBB_swapColors]
  rw [L]
  unfold Sym.geo
  dsimp only
  have h1 : (if a then I.transpose else I).WellFormed := by
    split
    · exact wf_transpose hI
    · exact hI
  have s1 : SBB (if a then I.transpose else I) = SBB I := by
    split
    · exact SBB_transpose I
    · rfl
  have h2 : (if b then (if a then I.transpose else I).reflectX else (if a then I.transpose else I)).WellFormed := by
    split
    · exact wf_reflectX h1
    · exact h1
  have s2 : SBB (if b then (if a then I.transpose else I).reflectX else (if a then I.transpose else I)) = SBB I := by
    split
    · rw [SBB_reflectX h1, s1]
    · exact s1
  split
  · rw [SBB_reflectY h2, s2]
  · exact s2

theorem inDom_applyB (σ : Sym) {I : Inst} (hI : I.WellFormed) (hS : SBB I = true) :
    InDom (σ.apply I) := by
  have h := hS
  rw [← SBB_apply σ hI] at h
  unfold SBB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, -, h3, -⟩, -⟩, -⟩ := h
  exact ⟨h1, h3, Sym.wf_lab σ (Sym.wf_geo σ hI)⟩

end ZZN
