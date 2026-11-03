/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.C8R

@[expose] public section

/-!
# The B entries with a cell at frame coordinate 5 are caught by R

Two even-grid B entries have a cell at `(0, 5)`: `((0,1),(0,5),(1,1))` and `((0,5),(1,1),(1,0))`.
On every even-area grid with both sides at least 11, in every frame, when the two cells of one
colour and the third cell of the other colour match, and the fourth endpoint lies on the
perimeter outside the 6 × 6 window, the R test fires (`b5_all`, in `ZZN.B5Fire`).

Proof: delete pairs of lines (`effAlt3_comp`) away from the entry and from the fourth endpoint,
keeping it outside the window, until both sides are at most 14 (`b5_stepR`, transposition for
the second side); the sides 11–14 are checked in `ZZN.B5Base`.
-/

namespace ZZN.Win

open GridHam

/-- The two entries as `(a, a', b)`: cells `a, a'` of one colour, `b` of the other. -/
def b5q : List (Coord × Coord × Coord) := [((0, 1), (0, 5), (1, 1)), ((0, 5), (1, 1), (1, 0))]

/-- Frame cells on the perimeter, outside the 6 × 6 window. -/
def perimOut (H W : ℕ) (x : Coord) : Bool :=
  decide (x.1 < H) && decide (x.2 < W) &&
    (x.1 == 0 || x.2 == 0 || x.1 == H - 1 || x.2 == W - 1) && !(decide (x.1 < 6) && decide (x.2 < 6))

/-- The endpoints of a match, colour 0 on the entry's pair, colour 1 on `b` and the fourth cell. -/
def b5pts (f : Frame) (R C : ℕ) (e : Coord × Coord × Coord) (x : Coord) : List Pt :=
  [(f.back R C e.1, 0), (f.back R C e.2.1, 0), (f.back R C e.2.2, 1), (f.back R C x, 1)]

theorem b5q_small : ∀ e ∈ b5q, e.1.1 ≤ 5 ∧ e.1.2 ≤ 5 ∧ e.2.1.1 ≤ 5 ∧ e.2.1.2 ≤ 5 ∧
    e.2.2.1 ≤ 5 ∧ e.2.2.2 ≤ 5 := by
  decide

/-- The frame coordinate along the first side of the grid. -/
def sA (f : Frame) (x : Coord) : ℕ := if f.tr then x.2 else x.1

/-- Replace the frame coordinate along the first side. -/
def setA (f : Frame) (x : Coord) (s : ℕ) : Coord := if f.tr then (x.1, s) else (s, x.2)

theorem back_row (f : Frame) (R C : ℕ) (x : Coord) :
    (f.back R C x).1 = rowMap f.fr R (sA f x) := by
  obtain ⟨fr, fc, tr⟩ := f
  cases tr <;> rfl

/-- Deleting the lines `d, d + 1` with `d` measured from the entry's edge. -/
theorem delAt_back {f : Frame} {R C m : ℕ} {x : Coord} (hR : m + 7 ≤ R) (hx : sA f x < R)
    (hs : sA f x ≠ m) (hs' : sA f x ≠ m + 1) :
    delAt (if f.fr then R - 2 - m else m) (f.back R C x) =
      f.back (R - 2) C (setA f x (if sA f x < m then sA f x else sA f x - 2)) := by
  obtain ⟨fr, fc, tr⟩ := f
  obtain ⟨x1, x2⟩ := x
  cases fr <;> cases tr <;> simp only [sA, setA] at hx hs hs' ⊢ <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hx hs hs' ⊢ <;>
    simp only [Frame.back, delAt, Bool.false_eq_true, ↓reduceIte] <;>
    split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> omega

/-- The fourth cell stays on the perimeter and outside the window. -/
theorem perimOut_step {f : Frame} {R C m : ℕ} {x : Coord} (hR : m + 7 ≤ R) (hm : 6 ≤ m)
    (hs : sA f x ≠ m) (hs' : sA f x ≠ m + 1) (hx : perimOut (f.H R C) (f.W R C) x = true) :
    perimOut (f.H (R - 2) C) (f.W (R - 2) C)
      (setA f x (if sA f x < m then sA f x else sA f x - 2)) = true := by
  obtain ⟨fr, fc, tr⟩ := f
  obtain ⟨x1, x2⟩ := x
  cases tr <;> simp only [sA, setA, Bool.false_eq_true, ↓reduceIte] at hs hs' ⊢ <;>
    simp only [perimOut, Frame.H, Frame.W, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at hx ⊢ <;>
    split_ifs <;> omega

/-- **One deletion along the first side**, for `R ≥ 15`. -/
theorem b5_stepR {f : Frame} {e : Coord × Coord × Coord} (he : e ∈ b5q) {R C : ℕ} (hR : 15 ≤ R)
    (hC : 4 ≤ C) {x : Coord} (hx : perimOut (f.H R C) (f.W R C) x = true) :
    ∃ x', perimOut (f.H (R - 2) C) (f.W (R - 2) C) x' = true ∧
      effAlt3 R C (b5pts f R C e x) = effAlt3 (R - 2) C (b5pts f (R - 2) C e x') := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := b5q_small e he
  set s := sA f x with hsd
  set m := if s = 6 ∨ s = 7 then 8 else 6 with hm
  have hm6 : 6 ≤ m := by rw [hm]; split_ifs <;> omega
  have hm8 : m ≤ 8 := by rw [hm]; split_ifs <;> omega
  have hsm : s ≠ m ∧ s ≠ m + 1 := by rw [hm]; split_ifs with h <;> omega
  have hxs : s < R := by
    simp only [perimOut, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hx
    obtain ⟨fr, fc, tr⟩ := f
    cases tr <;> simp_all [sA, Frame.H, Frame.W]
  refine ⟨setA f x (if s < m then s else s - 2), ?_, ?_⟩
  · exact perimOut_step (by omega) hm6 hsm.1 hsm.2 hx
  · have hp : ∀ q ∈ b5pts f R C e x, Av (if f.fr then R - 2 - m else m) R q.1 := by
      have pat : ∀ y : Coord, y.1 ≤ 5 → y.2 ≤ 5 → Av (if f.fr then R - 2 - m else m) R (f.back R C y) := by
        intro y h1 h2
        have hy : sA f y ≤ 5 := by unfold sA; split_ifs <;> omega
        refine ⟨?_, ?_, ?_⟩ <;> rw [back_row] <;> unfold rowMap <;> split_ifs <;> omega
      intro q hq
      simp only [b5pts, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact pat _ a1 a2
      · exact pat _ b1 b2
      · exact pat _ c1 c2
      · refine ⟨?_, ?_, ?_⟩ <;> rw [back_row] <;> unfold rowMap <;> split_ifs <;> omega
    rw [← effAlt3_comp (by split_ifs <;> omega) (by split_ifs <;> omega) hC hp]
    congr 1
    have pat : ∀ y : Coord, y.1 ≤ 5 → y.2 ≤ 5 →
        delAt (if f.fr then R - 2 - m else m) (f.back R C y) = f.back (R - 2) C y := by
      intro y h1 h2
      have hy : sA f y ≤ 5 := by unfold sA; split_ifs <;> omega
      have := delAt_back (f := f) (C := C) (m := m) (x := y) (by omega : m + 7 ≤ R) (by omega : sA f y < R)
        (by omega : sA f y ≠ m) (by omega : sA f y ≠ m + 1)
      rw [this, ite_eq_left (by omega)]
      congr 1
      obtain ⟨fr, fc, tr⟩ := f
      cases tr <;> rfl
    simp only [delPts, b5pts, List.map_cons, List.map_nil]
    rw [pat _ a1 a2, pat _ b1 b2, pat _ c1 c2, delAt_back (by omega) hxs hsm.1 hsm.2]

end ZZN.Win
