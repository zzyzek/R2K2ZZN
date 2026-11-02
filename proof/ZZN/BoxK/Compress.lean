/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.Slice
public import ZZN.BandExtension
public import ZZN.StripExtend
public import ZZN.Symmetry

@[expose] public section

/-!
# Row compressions of slices, for solvability only

A slice fixes the rows `x` of the endpoints; its lanes differ in the columns. Two endpoint-free
lines can be inserted into a solvable instance without losing solvability: after an endpoint-free
line (`band_extension`), or at an edge (`strip2`, lines of length at least 5). These act on the rows
alone, so on a whole slice at once: lane `j` of the larger slice is the insertion applied to lane
`j` of the smaller one (`laneI_step`), and a solvable lane lifts (`lift_chain`).
-/

namespace ZZN.BoxK

open ZZN GridHam

/-- Inserting two endpoint-free rows into an `w`-row slice: after row `r`, at the bottom, or at
the top. -/
inductive RStep where
  | band (r : ℕ)
  | bot
  | top

def RStep.rows (s : RStep) (x : Fin 4 → ℕ) : Fin 4 → ℕ :=
  match s with
  | band r => fun i => if x i ≤ r then x i else x i + 2
  | bot => x
  | top => fun i => x i + 2

/-- The step applies: rows in bounds, and for a band the row `r` holds no endpoint. -/
def RStep.ok (s : RStep) (w : ℕ) (x : Fin 4 → ℕ) : Bool :=
  (List.finRange 4).all (fun i => decide (x i < w)) &&
    match s with
    | band r => decide (r < w) && (List.finRange 4).all (fun i => x i != r)
    | bot => true
    | top => true

theorem laneI_band {w h r j : ℕ} {x : Fin 4 → ℕ} :
    (laneI w h x j).insertAt r = laneI (w + 2) h ((RStep.band r).rows x) j := by
  simp only [Inst.insertAt, laneI, RStep.rows, shiftAt]
  congr 1 <;> split <;> (rename_i hc; simp [hc])

theorem laneI_bot {w h j : ℕ} {x : Fin 4 → ℕ} :
    (laneI w h x j).widen 2 = laneI (w + 2) h (RStep.bot.rows x) j := rfl

theorem laneI_top {w h j : ℕ} {x : Fin 4 → ℕ} (hx : ∀ i, x i < w) :
    ((laneI w h x j).reflectX.widen 2).reflectX = laneI (w + 2) h (RStep.top.rows x) j := by
  simp only [Inst.reflectX, Inst.widen, laneI, reflX, RStep.rows]
  have := hx 0; have := hx 1; have := hx 2; have := hx 3
  congr 1 <;> simp only [Prod.mk.injEq, and_true] <;> omega

/-- **One step lifts solvability.** -/
theorem lift_step {s : RStep} {w h j : ℕ} {x : Fin 4 → ℕ} (h5 : 5 ≤ h) (hok : s.ok w x = true)
    (hS : Solvable (laneI w h x j)) : Solvable (laneI (w + 2) h (s.rows x) j) := by
  simp only [RStep.ok, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
    true_implies] at hok
  obtain ⟨hx, hs⟩ := hok
  cases s with
  | band r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies, bne_iff_ne, ne_eq] at hs
    rw [← laneI_band]
    refine band_extension _ r hs.1 ?_ hS
    intro y
    simp only [laneI, ne_eq, Prod.mk.injEq, not_and]
    exact ⟨fun h0 => absurd h0.symm (hs.2 0), fun h0 => absurd h0.symm (hs.2 1),
      fun h0 => absurd h0.symm (hs.2 2), fun h0 => absurd h0.symm (hs.2 3)⟩
  | bot =>
    rw [← laneI_bot]
    exact strip2 _ h5 hS
  | top =>
    rw [← laneI_top hx]
    exact solvable_reflectX (strip2 _ h5 (solvable_reflectX hS))

/-- A chain of steps from a small slice: the row count and rows reached. -/
def applyChain : ℕ → (Fin 4 → ℕ) → List RStep → ℕ × (Fin 4 → ℕ)
  | w, x, [] => (w, x)
  | w, x, s :: ss => applyChain (w + 2) (s.rows x) ss

def chainOK : ℕ → (Fin 4 → ℕ) → List RStep → Bool
  | _, _, [] => true
  | w, x, s :: ss => s.ok w x && chainOK (w + 2) (s.rows x) ss

/-- **A chain lifts solvability.** -/
theorem lift_chain {h j : ℕ} (h5 : 5 ≤ h) : ∀ (w : ℕ) (x : Fin 4 → ℕ) (ss : List RStep),
    chainOK w x ss = true → Solvable (laneI w h x j) →
      Solvable (laneI (applyChain w x ss).1 h (applyChain w x ss).2 j)
  | _, _, [], _, hS => hS
  | w, x, s :: ss, hok, hS => by
    simp only [chainOK, Bool.and_eq_true] at hok
    exact lift_chain h5 (w + 2) (s.rows x) ss hok.2 (lift_step h5 hok.1 hS)

/-! ### Well-formedness goes down the chain -/

theorem rows_inj {s : RStep} {w : ℕ} {x : Fin 4 → ℕ} (hok : s.ok w x = true) (i k : Fin 4) :
    s.rows x i = s.rows x k ↔ x i = x k := by
  cases s with
  | band r =>
    simp only [RStep.rows]
    split_ifs <;> omega
  | bot => rfl
  | top => simp [RStep.rows]

theorem rows_lt {s : RStep} {w : ℕ} {x : Fin 4 → ℕ} (hok : s.ok w x = true) (i : Fin 4) :
    s.rows x i < w + 2 := by
  simp only [RStep.ok, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
    true_implies] at hok
  have := hok.1 i
  cases s with
  | band r => simp only [RStep.rows]; split_ifs <;> omega
  | bot => simp only [RStep.rows]; omega
  | top => simp only [RStep.rows]; omega

theorem wf_step_down {s : RStep} {w h j : ℕ} {x : Fin 4 → ℕ} (hok : s.ok w x = true)
    (hwf : (laneI (w + 2) h (s.rows x) j).WellFormed) : (laneI w h x j).WellFormed := by
  have hx : ∀ i, x i < w := by
    simp only [RStep.ok, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
      true_implies] at hok
    exact hok.1
  obtain ⟨b0, b1, b2, b3, n01, n02, n03, n12, n13, n23⟩ := hwf
  have up : ∀ i k : Fin 4, (x i, digit h i j) = (x k, digit h k j) →
      (s.rows x i, digit h i j) = (s.rows x k, digit h k j) := by
    intro i k e
    simp only [Prod.mk.injEq] at e ⊢
    exact ⟨(rows_inj hok i k).mpr e.1, e.2⟩
  exact ⟨⟨hx 0, b0.2⟩, ⟨hx 1, b1.2⟩, ⟨hx 2, b2.2⟩, ⟨hx 3, b3.2⟩, fun e => n01 (up 0 1 e),
    fun e => n02 (up 0 2 e), fun e => n03 (up 0 3 e), fun e => n12 (up 1 2 e), fun e => n13 (up 1 3 e),
    fun e => n23 (up 2 3 e)⟩

theorem wf_chain_down {h j : ℕ} : ∀ (w : ℕ) (x : Fin 4 → ℕ) (ss : List RStep),
    chainOK w x ss = true →
    (laneI (applyChain w x ss).1 h (applyChain w x ss).2 j).WellFormed → (laneI w h x j).WellFormed
  | _, _, [], _, hwf => hwf
  | w, x, s :: ss, hok, hwf => by
    simp only [chainOK, Bool.and_eq_true] at hok
    exact wf_step_down hok.1 (wf_chain_down (w + 2) (s.rows x) ss hok.2 hwf)

end ZZN.BoxK
