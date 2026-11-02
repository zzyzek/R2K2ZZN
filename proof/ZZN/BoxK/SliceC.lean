/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.Box
public import ZZN.BoxK.Compress
public import ZZN.BoxK.FireW
public import ZZN.Cut.FastW

@[expose] public section

/-!
# Slices certified through a row compression

A slice `(w, h, x)` reached from a smaller slice `(w0, h, x0)` by a chain of row insertions
(`applyChain`) has the same column lanes. A lane solvable in the smaller slice is solvable in the
larger one (`lift_chain`), so the cover mask of the smaller slice counts for the larger one.
`sliceCOK` checks the chain, then requires every valid lane of the larger slice to be covered by
the smaller slice's mask or by the larger slice's own residual pairs, firing lanes and solutions.

Several larger slices share one smaller slice. Its mask enters each larger slice's check as a
literal `M`, proved once to be contained in the smaller slice's cover (`subM`), so the kernel
evaluates the smaller slice's cover once.
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane ZZN.Cut GridHam

deriving instance DecidableEq for Sym

/-- `stabV` as a function of the stabiliser list alone. -/
def stabVL (N h : ℕ) (L : List Sym) (Y : Cols) : LB :=
  L.foldr (fun σ acc => LB.and (lexLeV N Y (yS σ N h Y)) acc) (LB.b true)

/-- The part of the valid mask fixed by the box and the stabiliser list: computed once per box and
stabiliser list, then used in every slice as a literal. -/
def baseM (h : ℕ) (L : List Sym) : ℕ :=
  (LB.and (axBBV (h ^ 4) h (Ycols h)) (stabVL (h ^ 4) h L (Ycols h))).mkG (h ^ 4)

/-- Valid lanes, given `B = baseM h (stabL w x)`. -/
def validM (w h : ℕ) (x : Fin 4 → ℕ) (B : ℕ) : ℕ :=
  let N := h ^ 4
  let Y := Ycols h
  B &&& (LB.and (trV N w h x Y) (LB.and (distinctV N x Y) (parityV N w h x Y))).mkG N

/-- Every valid lane has its bit set in `M`. -/
def maskOK (w h : ℕ) (x : Fin 4 → ℕ) (B M : ℕ) : Bool :=
  (validM w h x B &&& (oneS (h ^ 4) ^^^ M)) == 0

theorem maskOK_sound {w h : ℕ} (hh : 0 < h) (h32 : h ≤ 32) {x : Fin 4 → ℕ} {B M : ℕ}
    (hB : baseM h (stabL w x) = B) (hok : maskOK w h x B M = true)
    (hM : ∀ j, j < h ^ 4 → M.testBit (8 * j) = true → (laneI w h x j).WellFormed →
      Solvable (laneI w h x j) ∨ passImgB (laneI w h x j) = false) : SliceGood w h x := by
  intro j hj hax hst htc hx32 hwf
  have g : ∀ i : Fin 4, (Ycols h i).get j = digit h i j := Ycols_get hh h32 hj
  by_cases hp : parityOk w h (ptsOf' (laneI w h x j)) = true
  · unfold maskOK validM at hok
    rw [← hB] at hok
    simp only [beq_iff_eq] at hok
    have hb := congrArg (fun n => n.testBit (8 * j)) hok
    simp only [baseM, Nat.testBit_and, Nat.zero_testBit, Nat.testBit_xor, testBit_oneS, hj,
      decide_true, LB.testBit_mkG hj, LB.at_and] at hb
    have gl : ∀ i, (Ycols h i).get j < h := fun i => by rw [g]; exact digit_lt hh
    have v1 : (axBBV (h ^ 4) h (Ycols h)).get j = true := by
      rw [axBBV_get hj]; simpa [colsAt, g] using hax
    have v2 : (distinctV (h ^ 4) x (Ycols h)).get j = true := by
      rw [distinctV_get hj]
      obtain ⟨-, -, -, -, n01, n02, n03, n12, n13, n23⟩ := hwf
      simp [pairsIdx, cellAt, g, laneI] at n01 n02 n03 n12 n13 n23 ⊢
      exact ⟨imp_iff_not_or.mp n01, imp_iff_not_or.mp n02, imp_iff_not_or.mp n03,
        imp_iff_not_or.mp n12, imp_iff_not_or.mp n13, imp_iff_not_or.mp n23⟩
    have v3 : (parityV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [parityV_get hj]; simpa [ptsOf', laneI, g] using hp
    have v4 : (stabVL (h ^ 4) h (stabL w x) (Ycols h)).get j = true := by
      rw [show stabVL (h ^ 4) h (stabL w x) (Ycols h) = stabV (h ^ 4) w h x (Ycols h) from rfl,
        stabV_get hj h32 _ _ gl]
      refine List.all_eq_true.mpr fun σ hσ => ?_
      simpa [g] using hst σ hσ
    have v5 : (trV (h ^ 4) w h x (Ycols h)).get j = true := by
      rw [trV_get hj _ _ hx32 (fun i => by have := gl i; omega)]
      by_cases hwh : w = h
      · simp only [hwh, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
        simpa [g] using htc hwh
      · simp [hwh]
    rw [v1, v4, v5, v2, v3] at hb
    have hm : M.testBit (8 * j) = true := by
      cases e : M.testBit (8 * j) <;> simp_all
    exact hM j hj hm hwf
  · right
    exact passImgB_of_parity hwf (by simp only [Bool.not_eq_true] at hp; exact hp)

/-- The residual mask of a slice: its own pairs, firing lanes, instances and solutions. -/
def ownM (w h : ℕ) (x : Fin 4 → ℕ) (pairs : List (CTree TPos × Sym)) (fires : List (ℕ × ℕ))
    (insts : List (ℕ × Sym × CTree TPos)) (sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  coverFWD (h ^ 4) w h x (sel4 (YS h 0) (YS h 1) (YS h 2) (YS h 3)) pairs |||
    firesW (h ^ 4) w h x fires ||| instM (h ^ 4) w h x insts ||| solsM (h ^ 4) w h x sols

/-- Lanes of the smaller slice solved by its pairs or solutions. -/
def tgtM (w0 h : ℕ) (x0 : Fin 4 → ℕ) (tpairs : List (CTree TPos × Sym))
    (tsols : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  coverF (h ^ 4) w0 h x0 (sel4 (YS h 0) (YS h 1) (YS h 2) (YS h 3)) tpairs |||
    solsM (h ^ 4) w0 h x0 tsols

theorem ownM_sound {w h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hw32 : w ≤ 32) (hj : j < h ^ 4)
    {x : Fin 4 → ℕ} (hx32 : ∀ i, x i < 32) {pairs : List (CTree TPos × Sym)} {fires : List (ℕ × ℕ)}
    {insts : List (ℕ × Sym × CTree TPos)} {sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hb : (ownM w h x pairs fires insts sols).testBit (8 * j) = true) (hwf : (laneI w h x j).WellFormed) :
    Solvable (laneI w h x j) ∨ passImgB (laneI w h x j) = false := by
  simp only [ownM, coverFWD_eq, Nat.testBit_or, Bool.or_eq_true] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · exact Or.inl (coverFW_sound hh h32 hw32 rfl hj x hx32 (sel4_YS h) pairs hb hwf)
  · exact Or.inr (firesW_sound x fires hb)
  · exact Or.inl (instM_sound x insts hb hwf)
  · exact Or.inl (solsM_sound x sols hb)

theorem tgtM_sound {w0 h j : ℕ} (hh : 0 < h) (h32 : h ≤ 32) (hw32 : w0 ≤ 32) (hj : j < h ^ 4)
    {x0 : Fin 4 → ℕ} (hx32 : ∀ i, x0 i < 32) {tpairs : List (CTree TPos × Sym)}
    {tsols : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (hb : (tgtM w0 h x0 tpairs tsols).testBit (8 * j) = true)
    (hwf : (laneI w0 h x0 j).WellFormed) : Solvable (laneI w0 h x0 j) := by
  simp only [tgtM, Nat.testBit_or, Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · exact coverF_sound hh h32 hw32 rfl hj x0 hx32 (sel4_YS h) tpairs hb hwf
  · exact solsM_sound x0 tsols hb

/-- The chain from `(w0, x0)` reaches `(w, x)`, all rows below 32. -/
def chainTo (w0 : ℕ) (x0 : Fin 4 → ℕ) (ss : List RStep) (w : ℕ) (x : Fin 4 → ℕ) : Bool :=
  chainOK w0 x0 ss && (applyChain w0 x0 ss).1 == w &&
    (List.finRange 4).all (fun i => (applyChain w0 x0 ss).2 i == x i) && decide (w0 ≤ 32) &&
    (List.finRange 4).all (fun i => decide (x0 i < 32))

/-- **Slice check.** The stabiliser list `L` of the rows and its base mask `B = baseM h L`; the
chain from the smaller slice `(w0, x0)` and the lanes `M` known solvable there; the slice's own
pairs, firing lanes, instances and solutions. An uncompressed slice has the empty chain, `w0 = w`,
`x0 = x` and `M = 0`. Firing lanes carry witness entries (`firesW`). -/
def sliceCOK (w h : ℕ) (x : Fin 4 → ℕ) (L : List Sym) (B : ℕ) (w0 : ℕ) (x0 : Fin 4 → ℕ)
    (ss : List RStep) (M : ℕ) (pairs : List (CTree TPos × Sym)) (fires : List (ℕ × ℕ))
    (insts : List (ℕ × Sym × CTree TPos)) (sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Bool :=
  decide (stabL w x = L) && chainTo w0 x0 ss w x && maskOK w h x B (M ||| ownM w h x pairs fires insts sols)

/-- A slice certificate: rows, chain, pairs, firing lanes with witnesses, solutions. -/
abbrev CData := (Fin 4 → ℕ) × List RStep × List (CTree TPos × Sym) × List (ℕ × ℕ) ×
  List (ℕ × ℕ × ℕ × ℕ × ℕ)

/-- `M` is contained in `T`: every set bit of `M` is set in `T`. -/
def subM (M T : ℕ) : Bool := (M &&& T) == M

theorem subM_zero (T : ℕ) : subM 0 T = true := by simp [subM]

theorem subM_testBit {M T : ℕ} (h : subM M T = true) {k : ℕ} (hk : M.testBit k = true) :
    T.testBit k = true := by
  simp only [subM, beq_iff_eq] at h
  have := congrArg (fun n => n.testBit k) h
  simp only [Nat.testBit_and, hk, Bool.true_and] at this
  exact this

theorem sliceCOK_sound {w h : ℕ} (hh : 5 ≤ h) (h32 : h ≤ 32) (hw32 : w ≤ 32) {x : Fin 4 → ℕ}
    (hx32 : ∀ i, x i < 32) {L : List Sym} {B : ℕ} (hB : baseM h L = B) {w0 : ℕ} {x0 : Fin 4 → ℕ}
    {ss : List RStep} {M : ℕ}
    {tpairs : List (CTree TPos × Sym)} {tsols : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hM : subM M (tgtM w0 h x0 tpairs tsols) = true)
    {pairs : List (CTree TPos × Sym)} {fires : List (ℕ × ℕ)} {insts : List (ℕ × Sym × CTree TPos)}
    {sols : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hok : sliceCOK w h x L B w0 x0 ss M pairs fires insts sols = true) :
    SliceGood w h x := by
  simp only [sliceCOK, chainTo, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    true_implies, decide_eq_true_eq] at hok
  obtain ⟨⟨hL, ⟨⟨⟨⟨hc, hw⟩, hx⟩, hw0⟩, hx0⟩⟩, hm⟩ := hok
  have ex : (applyChain w0 x0 ss).2 = x := funext hx
  refine maskOK_sound (by omega) h32 (by rw [hL]; exact hB) hm fun j hj hb hwf => ?_
  simp only [Nat.testBit_or, Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · have hwf0 : (laneI w0 h x0 j).WellFormed :=
      wf_chain_down w0 x0 ss hc (by rw [hw, ex]; exact hwf)
    have := lift_chain (j := j) (by omega) w0 x0 ss hc
      (tgtM_sound (by omega) h32 hw0 hj hx0 (subM_testBit hM hb) hwf0)
    rw [hw, ex] at this
    exact Or.inl this
  · exact ownM_sound (by omega) h32 hw32 hj hx32 hb hwf

end ZZN.BoxK
