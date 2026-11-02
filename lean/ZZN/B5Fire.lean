-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.B5Base

/-!
# R fires on every `b5q` match

`b5_all`: on every even-area grid with both sides at least 11, in every frame, R fires on the
endpoints of a `b5q` match whose fourth cell is on the perimeter outside the 6 × 6 window.
Deletions along the first side (`b5_stepR`), transposition for the second (`swap_b5pts`), and the
base sizes 11–14 (`b5_base`).
-/

namespace ZZN.Win

open GridHam

/-- The frame of the transposed grid. -/
def flipF (f : Frame) : Frame := ⟨f.fc, f.fr, !f.tr⟩

theorem flip_back (f : Frame) (R C : ℕ) (y : Coord) : (f.back R C y).swap = (flipF f).back C R y := by
  obtain ⟨fr, fc, tr⟩ := f
  cases tr <;> rfl

theorem flip_H (f : Frame) (R C : ℕ) : (flipF f).H C R = f.H R C := by
  obtain ⟨fr, fc, tr⟩ := f
  cases tr <;> rfl

theorem flip_W (f : Frame) (R C : ℕ) : (flipF f).W C R = f.W R C := by
  obtain ⟨fr, fc, tr⟩ := f
  cases tr <;> rfl

theorem swap_b5pts (f : Frame) (R C : ℕ) (e : Coord × Coord × Coord) (x : Coord) :
    swapPts (b5pts f R C e x) = b5pts (flipF f) C R e x := by
  simp only [swapPts, b5pts, List.map_cons, List.map_nil, flip_back]

theorem b5q_cells : ∀ e ∈ b5q, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 := by decide

/-- The matched endpoints form an instance of the domain. -/
theorem b5_inDom {f : Frame} {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {e : Coord × Coord × Coord}
    (he : e ∈ b5q) {x : Coord} (hx : perimOut (f.H R C) (f.W R C) x = true) :
    InDom ⟨R, C, f.back R C e.1, f.back R C e.2.1, f.back R C e.2.2, f.back R C x⟩ := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := b5q_small e he
  obtain ⟨n1, n2, n3⟩ := b5q_cells e he
  simp only [perimOut, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at hx
  obtain ⟨⟨⟨x1, x2⟩, -⟩, hout⟩ := hx
  have hH : 11 ≤ f.H R C := by unfold Frame.H; split_ifs <;> omega
  have hW : 11 ≤ f.W R C := by unfold Frame.W; split_ifs <;> omega
  have ia : e.1.1 < f.H R C ∧ e.1.2 < f.W R C := ⟨by omega, by omega⟩
  have ib : e.2.1.1 < f.H R C ∧ e.2.1.2 < f.W R C := ⟨by omega, by omega⟩
  have ic : e.2.2.1 < f.H R C ∧ e.2.2.2 < f.W R C := ⟨by omega, by omega⟩
  have ix : x.1 < f.H R C ∧ x.2 < f.W R C := ⟨x1, x2⟩
  have nx : ∀ y : Coord, y.1 ≤ 5 → y.2 ≤ 5 → y ≠ x := by
    rintro y h1 h2 rfl; rcases hout with h | h <;> omega
  refine ⟨hR, hC, back_inb f ia.1 ia.2, back_inb f ib.1 ib.2, back_inb f ic.1 ic.2, back_inb f ix.1 ix.2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only <;> intro hc
  · exact n1 (back_inj f ia ib hc)
  · exact n2 (back_inj f ia ic hc)
  · exact nx _ a1 a2 (back_inj f ia ix hc)
  · exact n3 (back_inj f ib ic hc)
  · exact nx _ b1 b2 (back_inj f ib ix hc)
  · exact nx _ c1 c2 (back_inj f ic ix hc)

theorem b5_transpose {f : Frame} {R C : ℕ} (hR : 11 ≤ R) (hC : 11 ≤ C) {e : Coord × Coord × Coord}
    (he : e ∈ b5q) {x : Coord} (hx : perimOut (f.H R C) (f.W R C) x = true) :
    effAlt3 R C (b5pts f R C e x) = effAlt3 C R (b5pts (flipF f) C R e x) := by
  rw [← swap_b5pts]
  exact (effAlt3_transpose (b5_inDom hR hC he hx)).symm

/-- **R fires on every `b5q` match**, every frame, every even-area grid of the domain. -/
theorem b5_all : ∀ n R C, R + C = n → 11 ≤ R → 11 ≤ C → (R * C) % 2 = 0 → ∀ (f : Frame),
    ∀ e ∈ b5q, ∀ x, perimOut (f.H R C) (f.W R C) x = true → effAlt3 R C (b5pts f R C e x) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R C hn hR hC hp f e he x hx
    by_cases h1 : 15 ≤ R
    · obtain ⟨x', hx', heq⟩ := b5_stepR (f := f) he h1 (by omega) hx
      rw [heq]
      refine ih (R - 2 + C) (by omega) (R - 2) C rfl (by omega) hC ?_ f e he x' hx'
      rw [Nat.mul_mod, show (R - 2) % 2 = R % 2 by omega, ← Nat.mul_mod]; exact hp
    by_cases h2 : 15 ≤ C
    · have hx2 : perimOut ((flipF f).H C R) ((flipF f).W C R) x = true := by
        rw [flip_H, flip_W]; exact hx
      obtain ⟨x', hx', heq⟩ := b5_stepR (f := flipF f) he h2 (by omega) hx2
      rw [b5_transpose hR hC he hx, heq]
      refine ih (C - 2 + R) (by omega) (C - 2) R rfl (by omega) hR ?_ (flipF f) e he x' hx'
      rw [Nat.mul_mod, show (C - 2) % 2 = C % 2 by omega, ← Nat.mul_mod, Nat.mul_comm]; exact hp
    exact b5_base hR (by omega) hC (by omega) hp f he hx

end ZZN.Win
