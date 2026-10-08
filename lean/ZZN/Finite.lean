-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Orbit
import ZZN.PassTR
import ZZN.Solve
import GridHam.Main

/-!
# `finite` from a computation

A checked search for valid moves (`moveB`, sound for `MoveOK`), the per-axis test that no
reduction applies (`axB`), and the reduction to one representative per orbit of `Sym`.
-/

namespace ZZN

open GridHam

/-! ### The checked move search -/

instance (I : Inst) : Decidable I.WellFormed := by
  unfold Inst.WellFormed InBounds; infer_instance

/-- A two-path piece is OK: thin pieces (short side at most `m`) by a checked solution, others by
the catalogue. -/
def pieceB (m : ℕ) (J : Inst) : Bool :=
  if J.w ≤ 10 ∨ J.h ≤ 10 then
    decide (min J.w J.h ≤ m) && parityOk J.w J.h [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)] &&
      solveCheck J
  else decide J.WellFormed && !(fires3 J.w J.h J.s0 J.t0 J.s1 J.t1)

theorem pieceB_sound {m : ℕ} {J : Inst} (h : pieceB m J = true) : PieceOK J := by
  unfold pieceB at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact Or.inl ⟨by assumption, solvable_of_solveCheck h.2⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    exact Or.inr ⟨by omega, by omega, h.1, h.2⟩

/-- A one-path piece has a Hamiltonian path (IPS). -/
def oneB (w h : ℕ) (s t : Coord) : Bool :=
  decide (s ≠ t) && decide (InBounds w h s) && decide (InBounds w h t) && decide (IsAcceptable w h s t)

theorem oneB_sound {w h : ℕ} {s t : Coord} (hb : oneB w h s t = true) : HasHamPath w h s t := by
  simp only [oneB, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hst, hs⟩, ht⟩, ha⟩ := hb
  exact (ips_characterization w h s t hs ht hst).mpr ha

/-- The canonical moves of `CanonMove`, as a search (thin pieces of short side at most `m`). -/
def canonB (m : ℕ) (I : Inst) : Bool :=
  (List.range I.w).any fun p => decide (0 < p) && (
    -- strip
    (decide (I.s0.1 < p) && decide (I.t0.1 < p) && decide (I.s1.1 < p) && decide (I.t1.1 < p) &&
      decide (2 ≤ I.w - p) && decide (((I.w - p) * I.h) % 2 = 0) && decide (5 ≤ I.h) &&
      pieceB m ⟨p, I.h, I.s0, I.t0, I.s1, I.t1⟩) ||
    -- 2/2 same
    (decide (I.s0.1 < p) && decide (I.t0.1 < p) && decide (p ≤ I.s1.1) && decide (p ≤ I.t1.1) &&
      oneB p I.h I.s0 I.t0 && oneB (I.w - p) I.h (I.s1.1 - p, I.s1.2) (I.t1.1 - p, I.t1.2)) ||
    -- 1/3
    (decide (I.s0.1 < p) && decide (p ≤ I.t0.1) && decide (p ≤ I.s1.1) && decide (p ≤ I.t1.1) &&
      (List.range I.h).any fun y => oneB p I.h I.s0 (p - 1, y) &&
        pieceB m ⟨I.w - p, I.h, (0, y), unX p I.t0, unX p I.s1, unX p I.t1⟩) ||
    -- 2/2 cross
    (decide (I.s0.1 < p) && decide (I.s1.1 < p) && decide (p ≤ I.t0.1) && decide (p ≤ I.t1.1) &&
      (List.range I.h).any fun y0 => (List.range I.h).any fun y1 =>
        pieceB m ⟨p, I.h, I.s0, (p - 1, y0), I.s1, (p - 1, y1)⟩ &&
        pieceB m ⟨I.w - p, I.h, (0, y0), unX p I.t0, (0, y1), unX p I.t1⟩) ||
    -- excursion
    (decide (I.s0.1 < p) && decide (I.t0.1 < p) && decide (p ≤ I.s1.1) && decide (p ≤ I.t1.1) &&
      (List.range I.h).any fun ya => (List.range I.h).any fun yb =>
        pieceB m ⟨p, I.h, I.s0, (p - 1, ya), (p - 1, yb), I.t0⟩ &&
        pieceB m ⟨I.w - p, I.h, unX p I.s1, unX p I.t1, (0, ya), (0, yb)⟩))

theorem canonB_sound {m : ℕ} {I : Inst} (h : canonB m I = true) : CanonMove I := by
  unfold canonB at h
  obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
  rw [List.mem_range] at hp
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at h
  obtain ⟨hp0, h⟩ := h
  refine ⟨p, hp0, hp, ?_⟩
  rcases h with ((((h | h) | h) | h) | h)
  · obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := h
    exact Or.inl ⟨pieceB_sound a8, a5, a6, a7, a1, a2, a3, a4⟩
  · obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, a3, a4, oneB_sound a5, oneB_sound a6⟩)))
  · obtain ⟨⟨⟨⟨-, a2⟩, a3⟩, a4⟩, y, hy, b1, b2⟩ := h
    exact Or.inr (Or.inl ⟨y, hy, oneB_sound b1, pieceB_sound b2, a2, a3, a4⟩)
  · obtain ⟨⟨⟨⟨-, -⟩, a3⟩, a4⟩, y0, hy0, y1, hy1, b1, b2⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨y0, y1, hy0, hy1, pieceB_sound b1, pieceB_sound b2, a3, a4⟩))
  · obtain ⟨⟨⟨⟨-, -⟩, a3⟩, a4⟩, ya, hya, yb, hyb, b1, b2⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ya, yb, hya, hyb, pieceB_sound b1, pieceB_sound b2, a3, a4⟩)))

/-- Search the images, allowing thin pieces of short side `0, 1, …, 10` in turn. -/
def moveB (I : Inst) : Bool :=
  (List.range 11).any fun m => allSym.any fun σ => canonB m (σ.apply I)

theorem moveB_sound {I : Inst} (h : moveB I = true) : MoveOK I := by
  unfold moveB at h
  obtain ⟨m, -, h⟩ := List.any_eq_true.mp h
  obtain ⟨σ, -, h⟩ := List.any_eq_true.mp h
  exact ⟨σ, canonB_sound h⟩

/-! ### No reduction on an axis, as a test on the coordinates -/

def freeB (xs : List ℕ) (k : ℕ) : Bool := xs.all (· != k)
def belowB (xs : List ℕ) (k : ℕ) : Bool := xs.any (· < k)
def aboveB (xs : List ℕ) (k : ℕ) : Bool := xs.any (k < ·)

/-- `RedX`, for given tests of free lines and endpoints below / above. -/
def redGen (n : ℕ) (F B A : ℕ → Bool) (d : ℕ) : Bool :=
  decide (13 ≤ n) && (
    (d == 0 && (List.range 4).all F) ||
    (d + 2 == n && (List.range 4).all (fun i => F (n - 4 + i))) ||
    ((List.range (d + 1)).any fun lo => decide (d + 1 ≤ lo + 9) && decide (lo + 10 ≤ n) &&
      (List.range 10).all (fun i => F (lo + i)) && B lo && A (lo + 9)) ||
    (decide (8 ≤ d) && decide (d + 10 ≤ n) && F d && F (d + 1) &&
      ((decide (1 ≤ d) && F (d - 1)) || F (d + 2)) && B d && A (d + 1)))

def redXB (n : ℕ) (xs : List ℕ) (d : ℕ) : Bool := redGen n (freeB xs) (belowB xs) (aboveB xs) d

/-- No reduction on this axis. -/
def axB (n : ℕ) (xs : List ℕ) : Bool := (List.range n).all fun d => !redXB n xs d

def xsOf (I : Inst) : List ℕ := I.ends.map (·.1)
def ysOf (I : Inst) : List ℕ := I.ends.map (·.2)

theorem freeB_iff (I : Inst) (k : ℕ) : freeB (xsOf I) k = true ↔ I.FreeLine k := by
  unfold freeB xsOf Inst.FreeLine
  simp [List.all_eq_true, bne_iff_ne]

theorem belowB_iff (I : Inst) (k : ℕ) : belowB (xsOf I) k = true ↔ EndBelow I k := by
  unfold belowB xsOf EndBelow
  simp [List.any_eq_true]

theorem aboveB_iff (I : Inst) (k : ℕ) : aboveB (xsOf I) k = true ↔ EndAbove I k := by
  unfold aboveB xsOf EndAbove
  simp [List.any_eq_true]

theorem redX_of_redXB {I : Inst} {d : ℕ} (h : redXB I.w (xsOf I) d = true) : RedX I d := by
  unfold redXB redGen at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range, freeB_iff, belowB_iff, aboveB_iff] at h
  obtain ⟨hw, h⟩ := h
  refine ⟨hw, ?_⟩
  rcases h with ((⟨rfl, hf⟩ | ⟨hd, hf⟩) | ⟨lo, hlo, ⟨⟨⟨⟨h1, h2⟩, hf⟩, hb⟩, ha⟩⟩) |
      ⟨⟨⟨⟨⟨⟨h8, h10⟩, f0⟩, f1⟩, f2⟩, hb⟩, ha⟩
  · exact Or.inl ⟨rfl, fun k hk => hf k (by omega)⟩
  · refine Or.inr (Or.inl ⟨hd, fun k hk1 hk2 => ?_⟩)
    have := hf (k - (I.w - 4)) (by omega)
    rwa [show I.w - 4 + (k - (I.w - 4)) = k by omega] at this
  · refine Or.inr (Or.inr (Or.inl ⟨lo, by omega, h1, h2, fun k hk1 hk2 => ?_, hb, ha⟩))
    have := hf (k - lo) (by omega)
    rwa [show lo + (k - lo) = k by omega] at this
  · refine Or.inr (Or.inr (Or.inr ⟨h8, h10, f0, f1, ?_, hb, ha⟩))
    rcases f2 with ⟨h1, f⟩ | f
    · exact Or.inl ⟨h1, f⟩
    · exact Or.inr f

theorem axB_of_noRed {I : Inst} (h : ¬ ∃ d, RedX I d) : axB I.w (xsOf I) = true := by
  unfold axB
  rw [List.all_eq_true]
  intro d _
  cases hb : redXB I.w (xsOf I) d
  · rfl
  · exact absurd ⟨d, redX_of_redXB hb⟩ h

/-! ### The test is unchanged by the symmetries -/

theorem axB_perm {n : ℕ} {xs xs' : List ℕ} (hp : xs.Perm xs') : axB n xs' = axB n xs := by
  unfold axB redXB redGen freeB belowB aboveB
  simp only [hp.all_eq, hp.any_eq]

theorem redGen_refl {n : ℕ} {F B A F' B' A' : ℕ → Bool}
    (hF : ∀ k, k < n → F k = F' (n - 1 - k)) (hB : ∀ k, k < n → B k = A' (n - 1 - k))
    (hA : ∀ k, k < n → A k = B' (n - 1 - k)) {d : ℕ} (h : redGen n F B A d = true) :
    redGen n F' B' A' (n - 2 - d) = true ∧ d + 2 ≤ n := by
  unfold redGen at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range] at h ⊢
  obtain ⟨hn, h⟩ := h
  rcases h with ((⟨rfl, hf⟩ | ⟨hd, hf⟩) | ⟨lo, hlo, ⟨⟨⟨⟨h1, h2⟩, hf⟩, hb⟩, ha⟩⟩) |
      ⟨⟨⟨⟨⟨⟨h8, h10⟩, f0⟩, f1⟩, f2⟩, hb⟩, ha⟩
  · refine ⟨⟨hn, Or.inl (Or.inl (Or.inr ⟨by omega, fun i hi => ?_⟩))⟩, by omega⟩
    have := hF (3 - i) (by omega)
    rw [hf (3 - i) (by omega), show n - 1 - (3 - i) = n - 4 + i by omega] at this
    exact this.symm
  · refine ⟨⟨hn, Or.inl (Or.inl (Or.inl ⟨by omega, fun i hi => ?_⟩))⟩, by omega⟩
    have := hF (n - 4 + (3 - i)) (by omega)
    rw [hf (3 - i) (by omega), show n - 1 - (n - 4 + (3 - i)) = i by omega] at this
    exact this.symm
  · refine ⟨⟨hn, Or.inl (Or.inr ⟨n - 10 - lo, by omega, ⟨⟨⟨⟨by omega, by omega⟩, fun i hi => ?_⟩, ?_⟩, ?_⟩⟩)⟩,
      by omega⟩
    · have := hF (lo + (9 - i)) (by omega)
      rw [hf (9 - i) (by omega), show n - 1 - (lo + (9 - i)) = n - 10 - lo + i by omega] at this
      exact this.symm
    · have := hA (lo + 9) (by omega)
      rw [ha, show n - 1 - (lo + 9) = n - 10 - lo by omega] at this
      exact this.symm
    · have := hB lo (by omega)
      rw [hb, show n - 1 - lo = n - 10 - lo + 9 by omega] at this
      exact this.symm
  · refine ⟨⟨hn, Or.inr ⟨⟨⟨⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩, by omega⟩
    · have := hF (d + 1) (by omega)
      rw [f1, show n - 1 - (d + 1) = n - 2 - d by omega] at this
      exact this.symm
    · have := hF d (by omega)
      rw [f0, show n - 1 - d = n - 2 - d + 1 by omega] at this
      exact this.symm
    · rcases f2 with ⟨h1, f⟩ | f
      · right
        have := hF (d - 1) (by omega)
        rw [f, show n - 1 - (d - 1) = n - 2 - d + 2 by omega] at this
        exact this.symm
      · left
        refine ⟨by omega, ?_⟩
        have := hF (d + 2) (by omega)
        rw [f, show n - 1 - (d + 2) = n - 2 - d - 1 by omega] at this
        exact this.symm
    · have := hA (d + 1) (by omega)
      rw [ha, show n - 1 - (d + 1) = n - 2 - d by omega] at this
      exact this.symm
    · have := hB d (by omega)
      rw [hb, show n - 1 - d = n - 2 - d + 1 by omega] at this
      exact this.symm

def reflL (n : ℕ) (xs : List ℕ) : List ℕ := xs.map (fun x => n - 1 - x)

theorem axB_refl_imp {n : ℕ} {xs : List ℕ} (hx : ∀ x ∈ xs, x < n) (h : axB n xs = true) :
    axB n (reflL n xs) = true := by
  unfold axB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro d hd
  cases hr : redXB n (reflL n xs) d
  · rfl
  · exfalso
    unfold redXB at hr
    have key := redGen_refl (F' := freeB xs) (B' := belowB xs) (A' := aboveB xs) ?_ ?_ ?_ hr
    · have := h (n - 2 - d) (List.mem_range.mpr (by omega))
      unfold redXB at this
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

theorem axB_refl {n : ℕ} {xs : List ℕ} (hx : ∀ x ∈ xs, x < n) : axB n (reflL n xs) = axB n xs := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨fun h => ?_, axB_refl_imp hx⟩
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
  have := axB_refl_imp hx' h
  rwa [e] at this

/-! ### The search region, unchanged by every `Sym` -/

/-- Both sides in `[11, 22]` and no reduction on either axis. -/
def SB (I : Inst) : Bool :=
  decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) && axB I.w (xsOf I) && axB I.h (ysOf I)

theorem SB_transpose (I : Inst) : SB I.transpose = SB I := by
  unfold SB
  have e1 : xsOf I.transpose = ysOf I := rfl
  have e2 : ysOf I.transpose = xsOf I := rfl
  have e3 : decide (11 ≤ I.transpose.w ∧ I.transpose.w ≤ 22 ∧ 11 ≤ I.transpose.h ∧ I.transpose.h ≤ 22) =
      decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) := by
    show decide (11 ≤ I.h ∧ I.h ≤ 22 ∧ 11 ≤ I.w ∧ I.w ≤ 22) = _
    simp only [decide_eq_decide]
    tauto
  rw [e1, e2, e3]
  simp only [Inst.transpose]
  rw [Bool.and_assoc, Bool.and_comm (axB I.h _), ← Bool.and_assoc]

theorem bounds_x {I : Inst} (hI : I.WellFormed) : ∀ x ∈ xsOf I, x < I.w := by
  obtain ⟨b0, b1, b2, b3, -⟩ := hI
  intro x hx
  simp only [xsOf, Inst.ends, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact b0.1
  · exact b1.1
  · exact b2.1
  · exact b3.1

theorem SB_reflectX {I : Inst} (hI : I.WellFormed) : SB I.reflectX = SB I := by
  unfold SB
  have e1 : xsOf I.reflectX = reflL I.w (xsOf I) := rfl
  have e2 : ysOf I.reflectX = ysOf I := rfl
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) && axB I.w (xsOf I.reflectX) &&
    axB I.h (ysOf I.reflectX)) = _
  rw [e1, e2, axB_refl (bounds_x hI)]

theorem SB_reflectY {I : Inst} (hI : I.WellFormed) : SB I.reflectY = SB I := by
  unfold Inst.reflectY
  rw [SB_transpose, SB_reflectX (wf_transpose hI), SB_transpose]

theorem SB_rev0 (I : Inst) : SB I.rev0 = SB I := by
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axB I.w [I.t0.1, I.s0.1, I.s1.1, I.t1.1] && axB I.h [I.t0.2, I.s0.2, I.s1.2, I.t1.2]) =
    (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axB I.w [I.s0.1, I.t0.1, I.s1.1, I.t1.1] && axB I.h [I.s0.2, I.t0.2, I.s1.2, I.t1.2])
  rw [axB_perm (List.Perm.swap I.t0.1 I.s0.1 _), axB_perm (List.Perm.swap I.t0.2 I.s0.2 _)]

theorem SB_rev1 (I : Inst) : SB I.rev1 = SB I := by
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axB I.w [I.s0.1, I.t0.1, I.t1.1, I.s1.1] && axB I.h [I.s0.2, I.t0.2, I.t1.2, I.s1.2]) =
    (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axB I.w [I.s0.1, I.t0.1, I.s1.1, I.t1.1] && axB I.h [I.s0.2, I.t0.2, I.s1.2, I.t1.2])
  rw [axB_perm (((List.Perm.swap I.t1.1 I.s1.1 []).cons _).cons _),
    axB_perm (((List.Perm.swap I.t1.2 I.s1.2 []).cons _).cons _)]

theorem SB_swapColors (I : Inst) : SB I.swapColors = SB I := by
  show (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axB I.w ([I.s1.1, I.t1.1] ++ [I.s0.1, I.t0.1]) && axB I.h ([I.s1.2, I.t1.2] ++ [I.s0.2, I.t0.2])) =
    (decide (11 ≤ I.w ∧ I.w ≤ 22 ∧ 11 ≤ I.h ∧ I.h ≤ 22) &&
      axB I.w ([I.s0.1, I.t0.1] ++ [I.s1.1, I.t1.1]) && axB I.h ([I.s0.2, I.t0.2] ++ [I.s1.2, I.t1.2]))
  rw [axB_perm (List.perm_append_comm (l₁ := [I.s0.1, I.t0.1]) (l₂ := [I.s1.1, I.t1.1])),
    axB_perm (List.perm_append_comm (l₁ := [I.s0.2, I.t0.2]) (l₂ := [I.s1.2, I.t1.2]))]

theorem SB_apply (σ : Sym) {I : Inst} (hI : I.WellFormed) : SB (σ.apply I) = SB I := by
  obtain ⟨a, b, c, d, e, f⟩ := σ
  show SB (Sym.lab _ (Sym.geo _ I)) = SB I
  have hg := Sym.wf_geo ⟨a, b, c, d, e, f⟩ hI
  have L : SB (Sym.lab ⟨a, b, c, d, e, f⟩ (Sym.geo ⟨a, b, c, d, e, f⟩ I)) =
      SB (Sym.geo ⟨a, b, c, d, e, f⟩ I) := by
    unfold Sym.lab
    dsimp only
    generalize Sym.geo _ I = X
    cases d <;> cases e <;> cases f <;>
      simp only [Bool.false_eq_true, ↓reduceIte, SB_rev0, SB_rev1, SB_swapColors]
  rw [L]
  unfold Sym.geo
  dsimp only
  have h1 : (if a then I.transpose else I).WellFormed := by
    split
    · exact wf_transpose hI
    · exact hI
  have s1 : SB (if a then I.transpose else I) = SB I := by
    split
    · exact SB_transpose I
    · rfl
  have h2 : (if b then (if a then I.transpose else I).reflectX else (if a then I.transpose else I)).WellFormed := by
    split
    · exact wf_reflectX h1
    · exact h1
  have s2 : SB (if b then (if a then I.transpose else I).reflectX else (if a then I.transpose else I)) = SB I := by
    split
    · rw [SB_reflectX h1, s1]
    · exact s1
  split
  · rw [SB_reflectY h2, s2]
  · exact s2

/-! ### One representative per orbit -/

/-- A sort key (all coordinates are below 32). -/
def key (J : Inst) : ℕ :=
  [J.w, J.h, J.s0.1, J.s0.2, J.t0.1, J.t0.2, J.s1.1, J.s1.2, J.t1.1, J.t1.2].foldl (fun a x => a * 32 + x) 0

def isMinB (J : Inst) : Bool := allSym.all fun σ => decide (key J ≤ key (σ.apply J))

/-- A quick necessary condition for `isMinB`, tried first. -/
def quickSyms : List Sym :=
  [⟨true, false, false, false, false, false⟩, ⟨false, false, false, true, false, false⟩,
    ⟨false, false, false, false, true, false⟩, ⟨false, false, false, false, false, true⟩,
    ⟨false, true, false, false, false, false⟩, ⟨false, false, true, false, false, false⟩]

def quickB (J : Inst) : Bool := quickSyms.all fun σ => decide (key J ≤ key (σ.apply J))

/-- `J` or one of its reflections passes. -/
def passImgB (J : Inst) : Bool :=
  decide (Passes J) || decide (Passes J.reflectX) || decide (Passes J.reflectY) ||
    decide (Passes J.reflectX.reflectY)

def checkInst (J : Inst) : Bool :=
  !(quickB J) || !(isMinB J) || !(decide J.WellFormed) || !(passImgB J) || moveB J || solveCheck J

/-- The 4-tuples of coordinates below `n` with no reduction on the axis. -/
def tuples (n : ℕ) : List (List ℕ) :=
  ((List.range n).flatMap fun a => (List.range n).flatMap fun b => (List.range n).flatMap fun c =>
    (List.range n).map fun e => [a, b, c, e]).filter (axB n)

theorem mem_tuples {n a b c e : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (he : e < n)
    (hx : axB n [a, b, c, e] = true) : [a, b, c, e] ∈ tuples n := by
  unfold tuples
  rw [List.mem_filter]
  refine ⟨?_, hx⟩
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨a, ha, b, hb, c, hc, e, he, rfl⟩

def mkInst (w h : ℕ) (xs ys : List ℕ) : Inst :=
  ⟨w, h, (xs[0]!, ys[0]!), (xs[1]!, ys[1]!), (xs[2]!, ys[2]!), (xs[3]!, ys[3]!)⟩

/-- The check of one box. -/
def checkBox (w h : ℕ) : Bool :=
  let Tw := tuples w
  let Th := tuples h
  Tw.all fun xs => Th.all fun ys => checkInst (mkInst w h xs ys)

def tuplesA (n a : ℕ) : List (List ℕ) :=
  ((List.range n).flatMap fun b => (List.range n).flatMap fun c =>
    (List.range n).map fun e => [a, b, c, e]).filter (axB n)

theorem mem_tuplesA {n a b c e : ℕ} (hb : b < n) (hc : c < n) (he : e < n)
    (hx : axB n [a, b, c, e] = true) : [a, b, c, e] ∈ tuplesA n a := by
  unfold tuplesA
  rw [List.mem_filter]
  refine ⟨?_, hx⟩
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨b, hb, c, hc, e, he, rfl⟩

/-- The part of a box with first x-coordinate `a`. -/
def checkBoxA (w h a : ℕ) : Bool :=
  let Th := tuples h
  (tuplesA w a).all fun xs => Th.all fun ys => checkInst (mkInst w h xs ys)

theorem exists_min {α : Type} (f : α → ℕ) : ∀ (l : List α), l ≠ [] → ∃ a ∈ l, ∀ b ∈ l, f a ≤ f b
  | [], h => absurd rfl h
  | [x], _ => ⟨x, List.mem_singleton_self x, fun b hb => by rw [List.mem_singleton.mp hb]⟩
  | x :: y :: l, _ => by
    obtain ⟨a, ha, hm⟩ := exists_min f (y :: l) (by simp)
    by_cases hx : f x ≤ f a
    · refine ⟨x, List.mem_cons_self, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_refl _
      · exact hx.trans (hm b hb)
    · refine ⟨a, List.mem_cons_of_mem _ ha, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · exact hm b hb

theorem Sym.wf_lab (σ : Sym) {X : Inst} (hX : X.WellFormed) : (σ.lab X).WellFormed := by
  obtain ⟨tr, rx, ry, r0, r1, sw⟩ := σ
  unfold Sym.lab
  dsimp only
  have h3 : (if r0 then X.rev0 else X).WellFormed := by
    split
    · exact wf_rev0 hX
    · exact hX
  have h4 : (if r1 then (if r0 then X.rev0 else X).rev1 else (if r0 then X.rev0 else X)).WellFormed := by
    split
    · exact wf_rev1 h3
    · exact h3
  split
  · exact wf_swapColors h4
  · exact h4

theorem inDom_apply (σ : Sym) {I : Inst} (hI : I.WellFormed) (hS : SB I = true) :
    InDom (σ.apply I) := by
  have h := hS
  rw [← SB_apply σ hI] at h
  unfold SB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, -, h3, -⟩, -⟩, -⟩ := h
  exact ⟨h1, h3, Sym.wf_lab σ (Sym.wf_geo σ hI)⟩

/-- **`finite` from the box checks.** -/
theorem finite_of_check (hc : ∀ w h a, 11 ≤ w → w ≤ 22 → 11 ≤ h → h ≤ 22 → a < w →
    checkBoxA w h a = true) : FactsFinite := by
  refine ⟨fun I hI hw hh hP hR => ?_⟩
  have hwf := hI.2.2
  -- the instance is in the search region
  have hSI : SB I = true := by
    unfold SB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hI.1, hw, hI.2.1, hh⟩, axB_of_noRed (fun h => hR (Or.inl h))⟩, ?_⟩
    exact axB_of_noRed (I := I.transpose) (fun h => hR (Or.inr (Or.inl h)))
  -- the representative: the image with the least key
  obtain ⟨σ0, -, hmin⟩ := exists_min (fun σ => key (σ.apply I)) allSym (by simp [allSym])
  set J := σ0.apply I with hJ
  have hJS : SB J = true := by rw [hJ, SB_apply σ0 hwf]; exact hSI
  have hJD : InDom J := inDom_apply σ0 hwf hSI
  have hJwf := hJD.2.2
  have hmin' : ∀ σ : Sym, key J ≤ key (σ.apply J) := by
    intro σ
    rw [hJ, comp_apply σ σ0 hwf]
    exact hmin _ (mem_allSym _)
  -- the box check covers it
  have hJS' := hJS
  unfold SB at hJS'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hJS'
  obtain ⟨⟨⟨w1, w2, h1, h2⟩, ax⟩, ay⟩ := hJS'
  have hbox := hc J.w J.h J.s0.1 w1 w2 h1 h2 hJwf.1.1
  unfold checkBoxA at hbox
  dsimp only at hbox
  have bx := bounds_x hJwf
  have by_ : ∀ y ∈ ysOf J, y < J.h := bounds_x (I := J.transpose) (wf_transpose hJwf)
  simp only [xsOf, ysOf, Inst.ends, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at bx by_
  have mx := mem_tuplesA (a := J.s0.1) bx.2.1 bx.2.2.1 bx.2.2.2 ax
  have my := mem_tuples by_.1 by_.2.1 by_.2.2.1 by_.2.2.2 ay
  have hci := List.all_eq_true.mp (List.all_eq_true.mp hbox _ mx) _ my
  have eJ : mkInst J.w J.h [J.s0.1, J.t0.1, J.s1.1, J.t1.1] [J.s0.2, J.t0.2, J.s1.2, J.t1.2] = J := by
    unfold mkInst; rfl
  rw [eJ] at hci
  unfold checkInst at hci
  -- the conditions hold
  have q1 : quickB J = true := by
    unfold quickB
    rw [List.all_eq_true]
    intro σ _
    exact decide_eq_true (hmin' σ)
  have q2 : isMinB J = true := by
    unfold isMinB
    rw [List.all_eq_true]
    intro σ _
    exact decide_eq_true (hmin' σ)
  have q3 : passImgB J = true := by
    obtain ⟨ρ, hρ⟩ := inv_exists σ0
    have hPJ : Passes (ρ.apply J) := by rw [hJ, hρ I hwf]; exact hP
    unfold passImgB
    rcases passes_refl_of_image hJD ρ hPJ with h | h | h | h <;> simp [h]
  simp only [q1, q2, q3, decide_eq_true hJwf, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hci
  rcases hci with hm | hs
  · exact Or.inl (MoveOK.of_apply hwf (moveB_sound hm))
  · exact Or.inr (Sym.solvable hwf (solvable_of_solveCheck hs))

/-- **Theorem A**, from the box checks. -/
theorem theoremA_of_check (hc : ∀ w h a, 11 ≤ w → w ≤ 22 → 11 ≤ h → h ≤ 22 → a < w →
    checkBoxA w h a = true) (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h)
    (hP : Passes I) : Solvable I :=
  theoremA_fin (finite_of_check hc) I hwf hw hh hP

end ZZN
