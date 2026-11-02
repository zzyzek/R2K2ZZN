-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinBCD

/-!
# The 8 × 8 corner entries via the R test

Every C entry with window 8 (all four endpoints within 8 of one corner) is also caught by the
R test, on every even-area grid with both sides at least 11. The R test is sound (`r_sound`), so
these entries need no window certificate.

Side reduction: with every endpoint at line `< 8`, `effAlt3_rstrip` drops two lines of the first
side while it is at least 13, so the first side reduces to 11 or 12. `effAlt3_transpose` swaps the
sides, and the second side reduces the same way. The base sizes are `11 × 12, 12 × 11, 12 × 12`,
checked by `decide +kernel`.
-/

namespace ZZN.Win

open GridHam

/-- The six window-8 C entries as `(a, a', b, b')`: colour classes `{a, a'}` and `{b, b'}`. -/
def c8q : List (Coord × Coord × Coord × Coord) :=
  [((0, 1), (0, 6), (0, 7), (1, 1)), ((0, 1), (0, 6), (1, 1), (7, 0)),
   ((0, 1), (0, 6), (1, 2), (6, 0)), ((0, 1), (0, 7), (1, 1), (6, 0)),
   ((0, 1), (7, 0), (1, 1), (6, 0)), ((0, 6), (2, 1), (1, 2), (6, 0))]

def toAB (e : Coord × Coord × Coord × Coord) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  ([e.1, e.2.1], [e.2.2.1, e.2.2.2])

theorem big_entries' : CORNER4.filter (fun AB => ¬ winC AB = 6) = c8q.map toAB := by
  decide

/-- The endpoint tuples `(s0, t0, s1, t1)` an entry matches: either colouring, either order. -/
def ords (e : Coord × Coord × Coord × Coord) : List (Coord × Coord × Coord × Coord) :=
  let (a, a', b, b') := e
  [(a, a', b, b'), (a', a, b, b'), (a, a', b', b), (a', a, b', b),
   (b, b', a, a'), (b', b, a, a'), (b, b', a', a), (b', b, a', a)]

def quadPts (q : Coord × Coord × Coord × Coord) : List Pt :=
  [(q.1, 0), (q.2.1, 0), (q.2.2.1, 1), (q.2.2.2, 1)]

theorem c8_small : ∀ e ∈ c8q, e.1 ≠ e.2.1 ∧ e.2.2.1 ≠ e.2.2.2 ∧ ∀ q ∈ ords e,
    q.1.1 < 8 ∧ q.1.2 < 8 ∧ q.2.1.1 < 8 ∧ q.2.1.2 < 8 ∧ q.2.2.1.1 < 8 ∧ q.2.2.1.2 < 8 ∧
      q.2.2.2.1 < 8 ∧ q.2.2.2.2 < 8 := by
  decide

/-- **Base sizes**: R fires on every matched tuple, transposed, at `h' × w'`. -/
theorem c8_base : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (quadPts q)) = true := by
  decide +kernel

/-- Drop pairs of lines from the first side while it is at least 13. -/
theorem effAlt3_red {C : ℕ} (hC : 4 ≤ C) {pts : List Pt} (hp : ∀ q ∈ pts, q.1.1 < 8) :
    ∀ R, 11 ≤ R → effAlt3 R C pts = effAlt3 (12 - R % 2) C pts := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    intro hR
    by_cases h : 13 ≤ R
    · rw [← effAlt3_rstrip h hC (fun q hq => by have := hp q hq; omega),
        ih (R - 2) (by omega) (by omega), show (R - 2) % 2 = R % 2 by omega]
    · rw [show 12 - R % 2 = R by omega]

/-- **R fires on a window-8 C match**, on every even-area grid of the domain. -/
theorem c8_fires {J : Inst} (hI : InDom J) (hp : (J.w * J.h) % 2 = 0) {e} (he : e ∈ c8q)
    (hq : (J.s0, J.t0, J.s1, J.t1) ∈ ords e) : effAlt3 J.w J.h (ptsOf J) = true := by
  obtain ⟨w, h, s0, t0, s1, t1⟩ := J
  obtain ⟨hw, hh, -, -, -, -, d1, d2, d3, d4, d5, d6⟩ := hI
  simp only at hw hh hp hq d1 d2 d3 d4 d5 d6 ⊢
  obtain ⟨-, -, hs⟩ := c8_small e he
  obtain ⟨x0, y0, x1, y1, x2, y2, x3, y3⟩ := hs _ hq
  simp only at x0 y0 x1 y1 x2 y2 x3 y3
  have hpts : ptsOf ⟨w, h, s0, t0, s1, t1⟩ = quadPts (s0, t0, s1, t1) := rfl
  rw [hpts]
  have pts8 : ∀ q ∈ quadPts (s0, t0, s1, t1), q.1.1 < 8 := by
    simp only [quadPts, List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl) <;> assumption
  have swp8 : ∀ q ∈ swapPts (quadPts (s0, t0, s1, t1)), q.1.1 < 8 := by
    intro q hq'
    rw [mem_swapPts] at hq'
    simp only [quadPts, List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff, Prod.swap] at hq'
    rcases hq' with ⟨⟨-, h1⟩, -⟩ | ⟨⟨-, h1⟩, -⟩ | ⟨⟨-, h1⟩, -⟩ | ⟨⟨-, h1⟩, -⟩ <;> omega
  -- First side to `12 - w % 2`.
  rw [effAlt3_red (by omega) pts8 w hw]
  -- Transpose: the instance with first side `12 - w % 2` is in the domain.
  have hI' : InDom ⟨12 - w % 2, h, s0, t0, s1, t1⟩ :=
    ⟨show 11 ≤ 12 - w % 2 by omega, hh, ⟨show s0.1 < 12 - w % 2 ∧ s0.2 < h by omega,
      show t0.1 < 12 - w % 2 ∧ t0.2 < h by omega, show s1.1 < 12 - w % 2 ∧ s1.2 < h by omega,
      show t1.1 < 12 - w % 2 ∧ t1.2 < h by omega, d1, d2, d3, d4, d5, d6⟩⟩
  have ht := effAlt3_transpose hI'
  dsimp only at ht
  change effAlt3 h (12 - w % 2) (swapPts (quadPts (s0, t0, s1, t1))) =
      effAlt3 (12 - w % 2) h (quadPts (s0, t0, s1, t1)) at ht
  rw [← ht, effAlt3_red (by omega) swp8 h hh]
  have hpar : ¬ (w % 2 = 1 ∧ h % 2 = 1) := by
    rintro ⟨a, b⟩; rw [Nat.mul_mod, a, b] at hp; simp at hp
  have hb := c8_base e he _ hq (12 - w % 2, 12 - h % 2)
  dsimp only at hb
  refine hb ?_
  rcases Nat.mod_two_eq_zero_or_one w with a | a <;>
    rcases Nat.mod_two_eq_zero_or_one h with b | b <;> rw [a, b]
  · decide
  · decide
  · decide
  · exact absurd ⟨a, b⟩ hpar

/-- A matched entry pins the endpoint tuple to one of `ords`. -/
theorem ords_of {e : Coord × Coord × Coord × Coord} (ha : e.1 ≠ e.2.1) (hb : e.2.2.1 ≠ e.2.2.2)
    {J : Inst} (hwf : J.WellFormed) {c : Bool}
    (hm : sameSet (toAB e).1 (if c then [J.s1, J.t1] else [J.s0, J.t0]) = true ∧
      sameSet (toAB e).2 (if c then [J.s0, J.t0] else [J.s1, J.t1]) = true) :
    (J.s0, J.t0, J.s1, J.t1) ∈ ords e := by
  obtain ⟨a, a', b, b'⟩ := e
  obtain ⟨w, h, s0, t0, s1, t1⟩ := J
  obtain ⟨-, -, -, -, d1, -, -, -, -, d6⟩ := hwf
  simp only [toAB] at ha hb hm ⊢
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte] at hm
    rcases sameSet_two ha d1 hm.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases sameSet_two hb d6 hm.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ords]
  · simp only [↓reduceIte] at hm
    rcases sameSet_two ha d6 hm.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases sameSet_two hb d1 hm.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ords]

/-- **Window-8 C entries are sound without certificates**: a solvable even-area instance of the
domain never matches one, since R would fire. -/
theorem c8_sound {J : Inst} (hI : InDom J) (hS : Solvable J) (hp : (J.w * J.h) % 2 = 0)
    {AB : List (ℕ × ℕ) × List (ℕ × ℕ)} (hAB : AB ∈ CORNER4) (h8 : ¬ winC AB = 6) {c : Bool}
    (hm : sameSet AB.1 (if c then [J.s1, J.t1] else [J.s0, J.t0]) = true ∧
      sameSet AB.2 (if c then [J.s0, J.t0] else [J.s1, J.t1]) = true) : False := by
  have hm8 : AB ∈ CORNER4.filter (fun AB => ¬ winC AB = 6) := List.mem_filter.mpr ⟨hAB, by simpa using h8⟩
  rw [big_entries'] at hm8
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm8
  obtain ⟨ha, hb, -⟩ := c8_small e he
  have hq := ords_of ha hb hI.2.2 hm
  have := c8_fires hI hp he hq
  rw [r_sound J hI hS] at this
  exact Bool.false_ne_true this

end ZZN.Win
