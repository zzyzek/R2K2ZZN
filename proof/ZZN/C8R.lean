/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.WinBCD

@[expose] public section

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

/-! ### Every frame

A C entry matched in frame `f` puts the endpoints at `f.back R C` of the entry cells: each
coordinate is measured from the low or the high edge. `effAlt3_rstrip` (low) or `effAlt3_lstrip`
(high) drops two lines while the side is at least 13.
-/

def rowMap (fl : Bool) (R a : ℕ) : ℕ := if fl then R - 1 - a else a

/-- Points whose first coordinate is measured from the low (`fl = false`) or high edge. -/
def ptsAt (fl : Bool) (R : ℕ) (L : List Pt) : List Pt :=
  L.map fun q => ((rowMap fl R q.1.1, q.1.2), q.2)

theorem effAlt3_redF {C : ℕ} (hC : 4 ≤ C) (fl : Bool) {L : List Pt} (hL : ∀ q ∈ L, q.1.1 < 8) :
    ∀ R, 11 ≤ R → effAlt3 R C (ptsAt fl R L) = effAlt3 (12 - R % 2) C (ptsAt fl (12 - R % 2) L) := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    intro hR
    by_cases h : 13 ≤ R
    · have step : effAlt3 R C (ptsAt fl R L) = effAlt3 (R - 2) C (ptsAt fl (R - 2) L) := by
        cases fl
        · have e : ptsAt false (R - 2) L = ptsAt false R L := rfl
          rw [e]
          refine (effAlt3_rstrip h hC (fun q hq => ?_)).symm
          obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
          have := hL q0 hq0
          simp only [rowMap, Bool.false_eq_true, ↓reduceIte]
          omega
        · have hp : ∀ q ∈ ptsAt true R L, 4 ≤ q.1.1 ∧ q.1.1 < R := by
            intro q hq
            obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
            have := hL q0 hq0
            show 4 ≤ R - 1 - q0.1.1 ∧ R - 1 - q0.1.1 < R
            omega
          rw [← effAlt3_lstrip h hC hp]
          congr 1
          unfold delPts ptsAt
          rw [List.map_map]
          apply List.map_congr_left
          intro q hq
          have := hL q hq
          show (delAt 0 (R - 1 - q.1.1, q.1.2), q.2) = ((R - 2 - 1 - q.1.1, q.1.2), q.2)
          unfold delAt
          rw [ite_eq_right (by simp)]
          congr 2
          simp only
          omega
      rw [step, ih (R - 2) (by omega) (by omega), show (R - 2) % 2 = R % 2 by omega]
    · rw [show 12 - R % 2 = R by omega]

/-- The entry cell's coordinates before the transpose of frame `f`. -/
def src (f : Frame) (x : ℕ × ℕ) : ℕ × ℕ := if f.tr then (x.2, x.1) else x

def fpts (f : Frame) (R C : ℕ) (q : Coord × Coord × Coord × Coord) : List Pt :=
  [(f.back R C q.1, 0), (f.back R C q.2.1, 0), (f.back R C q.2.2.1, 1), (f.back R C q.2.2.2, 1)]

theorem back_eq (f : Frame) (R C : ℕ) (x : ℕ × ℕ) :
    f.back R C x = (rowMap f.fr R (src f x).1, rowMap f.fc C (src f x).2) := by
  obtain ⟨fr, fc, tr⟩ := f
  cases tr <;> rfl

/-- The endpoints, measured along the first side. -/
def lq1 (f : Frame) (C : ℕ) (q : Coord × Coord × Coord × Coord) : List Pt :=
  [(((src f q.1).1, rowMap f.fc C (src f q.1).2), 0),
   (((src f q.2.1).1, rowMap f.fc C (src f q.2.1).2), 0),
   (((src f q.2.2.1).1, rowMap f.fc C (src f q.2.2.1).2), 1),
   (((src f q.2.2.2).1, rowMap f.fc C (src f q.2.2.2).2), 1)]

/-- The transposed endpoints, measured along the second side. -/
def lq2 (f : Frame) (R : ℕ) (q : Coord × Coord × Coord × Coord) : List Pt :=
  [(((src f q.1).2, rowMap f.fr R (src f q.1).1), 0),
   (((src f q.2.1).2, rowMap f.fr R (src f q.2.1).1), 0),
   (((src f q.2.2.1).2, rowMap f.fr R (src f q.2.2.1).1), 1),
   (((src f q.2.2.2).2, rowMap f.fr R (src f q.2.2.2).1), 1)]

theorem fpts_eq1 (f : Frame) (R C : ℕ) (q : Coord × Coord × Coord × Coord) :
    fpts f R C q = ptsAt f.fr R (lq1 f C q) := by
  simp only [fpts, ptsAt, lq1, back_eq, List.map_cons, List.map_nil]

theorem fpts_eq2 (f : Frame) (R C : ℕ) (q : Coord × Coord × Coord × Coord) :
    swapPts (fpts f R C q) = ptsAt f.fc C (lq2 f R q) := by
  simp only [swapPts, fpts, ptsAt, lq2, back_eq, List.map_cons, List.map_nil, Prod.swap]

theorem c8_small' : ∀ e ∈ c8q, ∀ q ∈ ords e, [q.1, q.2.1, q.2.2.1, q.2.2.2].Nodup := by
  decide

/-- **Base sizes, every frame**, one theorem per frame. -/
theorem c8_base_fff : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨false, false, false⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_base_fft : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨false, false, true⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_base_ftf : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨false, true, false⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_base_ftt : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨false, true, true⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_base_tff : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨true, false, false⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_base_tft : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨true, false, true⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_base_ttf : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨true, true, false⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_base_ttt : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts ⟨true, true, true⟩ wh.1 wh.2 q)) = true := by
  decide +kernel

theorem c8_baseF : ∀ e ∈ c8q, ∀ q ∈ ords e, ∀ f : Frame, ∀ wh ∈ [(11, 12), (12, 11), (12, 12)],
    effAlt3 wh.2 wh.1 (swapPts (fpts f wh.1 wh.2 q)) = true := by
  intro e he q hq f
  obtain ⟨fr, fc, tr⟩ := f
  cases fr <;> cases fc <;> cases tr
  · exact c8_base_fff e he q hq
  · exact c8_base_fft e he q hq
  · exact c8_base_ftf e he q hq
  · exact c8_base_ftt e he q hq
  · exact c8_base_tff e he q hq
  · exact c8_base_tft e he q hq
  · exact c8_base_ttf e he q hq
  · exact c8_base_ttt e he q hq

theorem back_inj {R C : ℕ} (f : Frame) {a b : Coord} (ha : a.1 < f.H R C ∧ a.2 < f.W R C)
    (hb : b.1 < f.H R C ∧ b.2 < f.W R C) (h : f.back R C a = f.back R C b) : a = b := by
  rw [← to_back_eq f ha.1 ha.2, ← to_back_eq f hb.1 hb.2, h]

/-- **R fires on a window-8 C match in any frame**, on every even-area grid of the domain. -/
theorem c8_firesF {J : Inst} (hI : InDom J) (hp : (J.w * J.h) % 2 = 0) {e} (he : e ∈ c8q)
    {f : Frame} (hq : (f.to J.w J.h J.s0, f.to J.w J.h J.t0, f.to J.w J.h J.s1, f.to J.w J.h J.t1) ∈ ords e) :
    effAlt3 J.w J.h (ptsOf J) = true := by
  obtain ⟨w, h, s0, t0, s1, t1⟩ := J
  obtain ⟨hw, hh, b0, b1, b2, b3, -⟩ := hI
  simp only at hw hh hp hq b0 b1 b2 b3 ⊢
  set q := (f.to w h s0, f.to w h t0, f.to w h s1, f.to w h t1) with hqd
  obtain ⟨-, -, hs⟩ := c8_small e he
  obtain ⟨x0, y0, x1, y1, x2, y2, x3, y3⟩ := hs _ hq
  have hnd := c8_small' e he _ hq
  have hpts : ptsOf ⟨w, h, s0, t0, s1, t1⟩ = fpts f w h q := by
    simp only [ptsOf, fpts, hqd, back_to f b0, back_to f b1, back_to f b2, back_to f b3]
  rw [hpts]
  have sm : ∀ x : ℕ × ℕ, x.1 < 8 → x.2 < 8 → (src f x).1 < 8 ∧ (src f x).2 < 8 := by
    intro x a b; unfold src; split_ifs <;> exact ⟨by simpa, by simpa⟩
  have s0' := sm _ x0 y0
  have s1' := sm _ x1 y1
  have s2' := sm _ x2 y2
  have s3' := sm _ x3 y3
  have L1 : ∀ R, ∀ p ∈ lq1 f R q, p.1.1 < 8 := by
    intro R p hp'
    simp only [lq1, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    · exact s0'.1
    · exact s1'.1
    · exact s2'.1
    · exact s3'.1
  have L2 : ∀ R, ∀ p ∈ lq2 f R q, p.1.1 < 8 := by
    intro R p hp'
    simp only [lq2, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    · exact s0'.2
    · exact s1'.2
    · exact s2'.2
    · exact s3'.2
  -- First side to `12 - w % 2`.
  rw [fpts_eq1, effAlt3_redF (by omega) f.fr (L1 h) w hw, ← fpts_eq1]
  -- Transpose.
  have inw : ∀ x : ℕ × ℕ, x.1 < 8 → x.2 < 8 → x.1 < f.H (12 - w % 2) h ∧ x.2 < f.W (12 - w % 2) h := by
    intro x a b; unfold Frame.H Frame.W; split_ifs <;> omega
  have hI' : InDom ⟨12 - w % 2, h, f.back (12 - w % 2) h q.1, f.back (12 - w % 2) h q.2.1,
      f.back (12 - w % 2) h q.2.2.1, f.back (12 - w % 2) h q.2.2.2⟩ := by
    have i0 := inw _ x0 y0
    have i1 := inw _ x1 y1
    have i2 := inw _ x2 y2
    have i3 := inw _ x3 y3
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := hnd
    refine ⟨show 11 ≤ 12 - w % 2 by omega, hh, back_inb f i0.1 i0.2, back_inb f i1.1 i1.2, back_inb f i2.1 i2.2,
      back_inb f i3.1 i3.2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only <;> intro hc
    · exact n1 (back_inj f i0 i1 hc)
    · exact n2 (back_inj f i0 i2 hc)
    · exact n3 (back_inj f i0 i3 hc)
    · exact n4 (back_inj f i1 i2 hc)
    · exact n5 (back_inj f i1 i3 hc)
    · exact n6 (back_inj f i2 i3 hc)
  have ht := effAlt3_transpose hI'
  dsimp only at ht
  change effAlt3 h (12 - w % 2) (swapPts (fpts f (12 - w % 2) h q)) =
      effAlt3 (12 - w % 2) h (fpts f (12 - w % 2) h q) at ht
  rw [← ht, fpts_eq2, effAlt3_redF (by omega) f.fc (L2 (12 - w % 2)) h hh, ← fpts_eq2]
  have hpar : ¬ (w % 2 = 1 ∧ h % 2 = 1) := by
    rintro ⟨a, b⟩; rw [Nat.mul_mod, a, b] at hp; simp at hp
  have hb := c8_baseF e he _ hq f (12 - w % 2, 12 - h % 2)
  dsimp only at hb
  refine hb ?_
  rcases Nat.mod_two_eq_zero_or_one w with a | a <;>
    rcases Nat.mod_two_eq_zero_or_one h with b | b <;> rw [a, b]
  · decide
  · decide
  · decide
  · exact absurd ⟨a, b⟩ hpar

/-! ### Theorem B from the certificates -/

/-- **C and D are sound**, given the certificates: window 6 by the certificate (the other colouring
after swapping the colours), window 8 by R. -/
theorem cSound_of (CF : CertFacts) : ∀ J : Inst, J.WellFormed → Solvable J → 11 ≤ J.w → 11 ≤ J.h →
    corner4 J.w J.h idF (ptsOf J) = false := by
  intro J hwf hS hw hh
  by_contra hf
  rw [Bool.not_eq_false] at hf
  unfold corner4 at hf
  simp only [ptsOf, List.filter_cons, List.filter_nil, beq_self_eq_true, ↓reduceIte, List.map_cons,
    idF_to] at hf
  have e01 : ((1 : ℕ) == 0) = false := rfl
  have e10 : ((0 : ℕ) == 1) = false := rfl
  simp only [e01, e10, Bool.false_eq_true, ↓reduceIte] at hf
  have hwf' := wf_swapColors hwf
  have hS' := solvable_swap hS
  split_ifs at hf with hpar
  · obtain ⟨AB, hAB, h⟩ := List.any_eq_true.mp hf
    have hp : (J.w * J.h) % 2 = 0 := by simpa using hpar
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    by_cases h6 : winC AB = 6
    · have hcert : certify (winC AB) (winC AB) (tmC AB false) ((J.w * J.h) % 2) none = true := by
        rw [hp]; exact CF.c_even AB hAB h6
      rcases h with h | h
      · exact cd_sound hwf hS hw hh (List.mem_append_left _ hAB) hcert (c := false) (by simpa using h)
      · exact cd_sound (J := J.swapColors) hwf' hS' hw hh (List.mem_append_left _ hAB) hcert
          (c := false) (by simpa [Inst.swapColors] using h)
    · rcases h with h | h
      · exact c8_sound ⟨hw, hh, hwf⟩ hS hp hAB h6 (c := false) (by simpa using h)
      · exact c8_sound ⟨hw, hh, hwf⟩ hS hp hAB h6 (c := true) (by simpa using h)
  · obtain ⟨AB, hAB, h⟩ := List.any_eq_true.mp hf
    have hp : (J.w * J.h) % 2 = 1 := by simp at hpar; omega
    have hcert : certify (winC AB) (winC AB) (tmC AB false) ((J.w * J.h) % 2) none = true := by
      rw [hp]; exact CF.c_odd AB hAB
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · exact cd_sound hwf hS hw hh (List.mem_append_right _ hAB) hcert (c := false) (by simpa using h)
    · exact cd_sound (J := J.swapColors) hwf' hS' hw hh (List.mem_append_right _ hAB) hcert
        (c := false) (by simpa [Inst.swapColors] using h)

theorem bFacts_of (CF : CertFacts) : BFacts := ⟨bSound_of CF, cSound_of CF⟩

/-- **Theorem B**, given only the window certificates (a finite computation). -/
theorem theoremB_cert (CF : CertFacts) {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=
  theoremB_R (bFacts_of CF) hI hS

end ZZN.Win
