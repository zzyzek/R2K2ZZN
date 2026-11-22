/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Constr.Solve2

@[expose] public section

/-!
# The blocked endpoint placements on an axis of length 11–16

`axBB_iff_noRed`: on a well-formed instance, the coordinate test `axBB` holds exactly when no
`RedX` and no `RedB` applies on the x-axis. `red_outside`: below length 13 neither applies, from
length 17 on one does (`leaf16`). `noRed_iff_blk`: at lengths 13–16 neither applies exactly when
the set of lines holding an endpoint is one of the sets in `blkL w` (176, 96, 48, 16 sets). The
sets at 14–16 are one line in `0..3`, a middle pair from `M14`/`M15`/`M16`, and one line in the last
four (`prodL`). Each length is a kernel check (`blkOK`, `decide +kernel`) that the lane masks of
`axBB` and of the set test agree on all `n^4` coordinate tuples.
-/

namespace ZZN

open GridHam

theorem redXB_of_redX {I : Inst} {d : ℕ} (h : RedX I d) : redXB I.w (xsOf I) d = true := by
  unfold redXB redGen
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range, freeB_iff, belowB_iff, aboveB_iff]
  obtain ⟨hw, h⟩ := h
  refine ⟨hw, ?_⟩
  rcases h with ⟨rfl, hf⟩ | ⟨hd, hf⟩ | ⟨lo, h0, h1, h2, hf, hb, ha⟩ | ⟨h8, h10, f0, f1, f2, hb, ha⟩
  · exact Or.inl (Or.inl (Or.inl ⟨rfl, fun k hk => hf k (by omega)⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨hd, fun k hk => hf _ (by omega) (by omega)⟩))
  · exact Or.inl (Or.inr ⟨lo, by omega, ⟨⟨⟨⟨h1, h2⟩, fun k hk => hf _ (by omega) (by omega)⟩, hb⟩,
      ha⟩⟩)
  · refine Or.inr ⟨⟨⟨⟨⟨⟨h8, h10⟩, f0⟩, f1⟩, ?_⟩, hb⟩, ha⟩
    rcases f2 with ⟨h1, f⟩ | f
    · exact Or.inl ⟨h1, f⟩
    · exact Or.inr f

theorem redX_lt {I : Inst} {d : ℕ} (h : RedX I d) : d < I.w := by
  obtain ⟨hw, h⟩ := h
  rcases h with ⟨rfl, -⟩ | ⟨hd, -⟩ | ⟨lo, h0, h1, h2, -⟩ | ⟨-, h10, -⟩ <;> omega

theorem bandB_of_redB {I : Inst} {d : ℕ} (h : RedB I d) :
    bandGen I.w (freeB (xsOf I)) (belowB (xsOf I)) (aboveB (xsOf I)) d = true := by
  unfold bandGen
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, freeB_iff, belowB_iff, aboveB_iff, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  obtain ⟨h13, h5, h7, f0, f1, -, fnb, hbl, hab, far⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨h13, h5⟩, h7⟩, f0⟩, f1⟩, ?_⟩, hbl⟩, hab⟩, fun k _ => ?_⟩, fun k _ => ?_⟩
  · rcases fnb with ⟨a, b⟩ | b
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr b
  · by_cases hk : k < d ∧ I.w < k + 8
    · refine Or.inr fun e he hek => ?_
      have := (far e he).1 (by omega)
      omega
    · by_cases hk' : k < d
      · exact Or.inl (Or.inr (by omega))
      · exact Or.inl (Or.inl hk')
  · by_cases hk : d + 2 ≤ k ∧ k < 7
    · refine Or.inr fun e he hek => ?_
      have := (far e he).2 (by omega)
      omega
    · by_cases hk' : d + 2 ≤ k
      · exact Or.inl (Or.inr (by omega))
      · exact Or.inl (Or.inl hk')

/-- **The coordinate test is exact.** On a well-formed instance, `axBB` holds on the x-axis
coordinates exactly when neither `RedX` nor `RedB` applies on the x-axis. -/
theorem axBB_iff_noRed {I : Inst} (hI : I.WellFormed) :
    axBB I.w (xsOf I) = true ↔ (¬ ∃ d, RedX I d) ∧ (¬ ∃ d, RedB I d) := by
  refine ⟨fun h => ⟨fun ⟨d, hd⟩ => ?_, fun ⟨d, hd⟩ => ?_⟩, fun h => axBB_of_noRed hI h.1 h.2⟩
  · unfold axBB at h
    have := (List.all_eq_true.mp h) d (List.mem_range.mpr (redX_lt hd))
    simp [redXBB, redGenB, show redGen I.w _ _ _ d = true from redXB_of_redX hd] at this
  · unfold axBB at h
    have := (List.all_eq_true.mp h) d (List.mem_range.mpr (by obtain ⟨-, -, h7, -⟩ := hd; omega))
    simp [redXBB, redGenB, bandB_of_redB hd] at this

/-- Below length 13 neither reduction applies. -/
theorem noRed_lt13 {I : Inst} (hw : I.w < 13) : (¬ ∃ d, RedX I d) ∧ (¬ ∃ d, RedB I d) :=
  ⟨fun ⟨_, h, _⟩ => by omega, fun ⟨_, h, _⟩ => by omega⟩

end ZZN

namespace ZZN.BoxK

open ZZN ZZN.Lane

/-! ### Exact blocked sets, as lane checks -/

/-- The lines `< n` that `F` marks occupied (not free) are exactly those in `S`. -/
def occB (n : ℕ) (S : List ℕ) (F : ℕ → Bool) : Bool :=
  (List.range n).all fun k => if S.contains k then !F k else F k

/-- The occupied lines of `xs` form one of the sets in `L`. -/
def blkB (n : ℕ) (L : List (List ℕ)) (xs : List ℕ) : Bool := L.any fun S => occB n S (freeB xs)

theorem occB_iff (n : ℕ) (S xs : List ℕ) :
    occB n S (freeB xs) = true ↔ ∀ k < n, (k ∈ S ↔ k ∈ xs) := by
  unfold occB freeB
  simp only [List.all_eq_true, List.mem_range]
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  by_cases h : k ∈ S
  · simp [h, bne_iff_ne]
  · simp only [h, List.contains_iff_mem, ↓reduceIte, List.all_eq_true, bne_iff_ne, ne_eq,
      false_iff]
    exact ⟨fun H hk => H k hk rfl, fun H y hy e => H (e ▸ hy)⟩

theorem blkB_iff (n : ℕ) (L : List (List ℕ)) (xs : List ℕ) :
    blkB n L xs = true ↔ ∃ S ∈ L, ∀ k < n, (k ∈ S ↔ k ∈ xs) := by
  unfold blkB
  simp only [List.any_eq_true, occB_iff]

def occV (N n : ℕ) (S : List ℕ) (F : ℕ → LB) : LB :=
  allV (List.range n) fun k => if S.contains k then LB.not N (F k) else F k

def blkV (N n : ℕ) (L : List (List ℕ)) (Y : Cols) : LB :=
  L.foldr (fun S acc => LB.or (occV N n S (freeV N Y)) acc) (LB.b false)

theorem blkV_get {N j : ℕ} (hj : j < N) (n : ℕ) (L : List (List ℕ)) (Y : Cols) :
    (blkV N n L Y).get j = blkB n L (colsAt Y j) := by
  induction L with
  | nil => rfl
  | cons S L ih =>
    simp only [blkV, List.foldr_cons, LB.at_or, blkB, List.any_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [occV, occB, allV_get]
    congr 1
    funext k
    split <;> simp [LB.at_not hj, freeV_get hj]

/-- The lanes of `axBBV` equal those of `blkV`: on an axis of length `n`, `axBB` holds exactly
on the coordinate tuples whose occupied lines form a set in `L`. -/
def blkOK (n : ℕ) (L : List (List ℕ)) : Bool :=
  (axBBV (n ^ 4) n (Ycols n)).mkG (n ^ 4) == (blkV (n ^ 4) n L (Ycols n)).mkG (n ^ 4)

theorem blkOK_sound {n : ℕ} {L : List (List ℕ)} (hn : 0 < n) (h32 : n ≤ 32)
    (hok : blkOK n L = true) {x : Fin 4 → ℕ} (hx : ∀ i, x i < n) :
    axBB n [x 0, x 1, x 2, x 3] = blkB n L [x 0, x 1, x 2, x 3] := by
  have hj := idx_lt hx
  have g : ∀ i : Fin 4, (Ycols n i).get (idx n x) = x i := fun i => by
    rw [Ycols_get hn h32 hj, digit_idx hx]
  unfold blkOK at hok
  simp only [beq_iff_eq] at hok
  have hb := congrArg (fun m => m.testBit (8 * idx n x)) hok
  simp only [LB.testBit_mkG hj] at hb
  rw [axBBV_get hj, blkV_get hj] at hb
  simpa [colsAt, g] using hb

/-! ### The blocked sets for lengths 13–16 -/

/-- One line in `0..3`, the middle pair `(m, m')`, one line in `n - 4 .. n - 1`. -/
def prodL (n : ℕ) (M : List (ℕ × ℕ)) : List (List ℕ) :=
  M.flatMap fun p => (List.range 4).flatMap fun a => (List.range 4).map fun c => [a, p.1, p.2, n - 4 + c]

def M14 : List (ℕ × ℕ) := [(4, 7), (5, 7), (5, 8), (6, 7), (6, 8), (6, 9)]
def M15 : List (ℕ × ℕ) := [(5, 8), (6, 8), (6, 9)]
def M16 : List (ℕ × ℕ) := [(6, 9)]

/-- The 176 blocked sets at length 13. -/
def L13 : List (List ℕ) :=
  [[0,1,6,9], [0,2,6,9], [1,2,6,9], [0,3,6,9], [1,3,6,9], [2,3,6,9], [0,4,6,9], [1,4,6,9],
   [2,4,6,9], [3,4,6,9], [0,5,6,9], [1,5,6,9], [2,5,6,9], [3,5,6,9], [0,4,7,9], [1,4,7,9],
   [2,4,7,9], [3,4,7,9], [0,5,7,9], [1,5,7,9], [2,5,7,9], [3,5,7,9], [0,6,7,9], [1,6,7,9],
   [2,6,7,9], [3,6,7,9], [0,5,8,9], [1,5,8,9], [2,5,8,9], [3,5,8,9], [0,6,8,9], [1,6,8,9],
   [2,6,8,9], [3,6,8,9], [0,6,9], [1,6,9], [2,6,9], [3,6,9], [0,1,6,10], [0,2,6,10], [1,2,6,10],
   [0,3,6,10], [1,3,6,10], [2,3,6,10], [0,4,6,10], [1,4,6,10], [2,4,6,10], [3,4,6,10], [0,5,6,10],
   [1,5,6,10], [2,5,6,10], [3,5,6,10], [0,4,7,10], [1,4,7,10], [2,4,7,10], [3,4,7,10], [0,5,7,10],
   [1,5,7,10], [2,5,7,10], [3,5,7,10], [0,6,7,10], [1,6,7,10], [2,6,7,10], [3,6,7,10], [0,5,8,10],
   [1,5,8,10], [2,5,8,10], [3,5,8,10], [0,6,8,10], [1,6,8,10], [2,6,8,10], [3,6,8,10], [0,6,9,10],
   [1,6,9,10], [2,6,9,10], [3,6,9,10], [0,6,10], [1,6,10], [2,6,10], [3,6,10], [0,1,6,11],
   [0,2,6,11], [1,2,6,11], [0,3,6,11], [1,3,6,11], [2,3,6,11], [0,4,6,11], [1,4,6,11], [2,4,6,11],
   [3,4,6,11], [0,5,6,11], [1,5,6,11], [2,5,6,11], [3,5,6,11], [0,4,7,11], [1,4,7,11], [2,4,7,11],
   [3,4,7,11], [0,5,7,11], [1,5,7,11], [2,5,7,11], [3,5,7,11], [0,6,7,11], [1,6,7,11], [2,6,7,11],
   [3,6,7,11], [0,5,8,11], [1,5,8,11], [2,5,8,11], [3,5,8,11], [0,6,8,11], [1,6,8,11], [2,6,8,11],
   [3,6,8,11], [0,6,9,11], [1,6,9,11], [2,6,9,11], [3,6,9,11], [0,6,10,11], [1,6,10,11],
   [2,6,10,11], [3,6,10,11], [0,6,11], [1,6,11], [2,6,11], [3,6,11], [0,1,6,12], [0,2,6,12],
   [1,2,6,12], [0,3,6,12], [1,3,6,12], [2,3,6,12], [0,4,6,12], [1,4,6,12], [2,4,6,12], [3,4,6,12],
   [0,5,6,12], [1,5,6,12], [2,5,6,12], [3,5,6,12], [0,4,7,12], [1,4,7,12], [2,4,7,12], [3,4,7,12],
   [0,5,7,12], [1,5,7,12], [2,5,7,12], [3,5,7,12], [0,6,7,12], [1,6,7,12], [2,6,7,12], [3,6,7,12],
   [0,5,8,12], [1,5,8,12], [2,5,8,12], [3,5,8,12], [0,6,8,12], [1,6,8,12], [2,6,8,12], [3,6,8,12],
   [0,6,9,12], [1,6,9,12], [2,6,9,12], [3,6,9,12], [0,6,10,12], [1,6,10,12], [2,6,10,12],
   [3,6,10,12], [0,6,11,12], [1,6,11,12], [2,6,11,12], [3,6,11,12], [0,6,12], [1,6,12], [2,6,12],
   [3,6,12]]

theorem blk13 : blkOK 13 L13 = true := by decide +kernel
theorem blk14 : blkOK 14 (prodL 14 M14) = true := by decide +kernel
theorem blk15 : blkOK 15 (prodL 15 M15) = true := by decide +kernel
theorem blk16 : blkOK 16 (prodL 16 M16) = true := by decide +kernel

/-- The blocked sets at length `n`, for `13 ≤ n ≤ 16`. -/
def blkL (n : ℕ) : List (List ℕ) :=
  if n = 13 then L13 else if n = 14 then prodL 14 M14 else if n = 15 then prodL 15 M15
  else prodL 16 M16

theorem blkL_ok {n : ℕ} (h13 : 13 ≤ n) (h16 : n ≤ 16) : blkOK n (blkL n) = true := by
  obtain rfl | rfl | rfl | rfl : n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by omega
  exacts [blk13, blk14, blk15, blk16]

theorem L13_length : L13.length = 176 := by decide +kernel
theorem L13_nodup : L13.Nodup := by decide +kernel
theorem prodL_length : (prodL 14 M14).length = 96 ∧ (prodL 15 M15).length = 48 ∧
    (prodL 16 M16).length = 16 := by decide +kernel
theorem prodL_nodup : (prodL 14 M14).Nodup ∧ (prodL 15 M15).Nodup ∧ (prodL 16 M16).Nodup := by
  decide +kernel

/-- **The blocked placements on an axis of length 13–16.** On a well-formed instance with
`13 ≤ w ≤ 16`, neither `RedX` nor `RedB` applies on the x-axis exactly when the set of lines
holding an endpoint is one of the sets in `blkL w`. -/
theorem noRed_iff_blk {I : Inst} (hI : I.WellFormed) (h13 : 13 ≤ I.w) (h16 : I.w ≤ 16) :
    ((¬ ∃ d, RedX I d) ∧ (¬ ∃ d, RedB I d)) ↔
      ∃ S ∈ blkL I.w, ∀ k < I.w, (k ∈ S ↔ k ∈ xsOf I) := by
  rw [← axBB_iff_noRed hI, ← blkB_iff]
  obtain ⟨b0, b1, b2, b3, -⟩ := hI
  have h := blkOK_sound (by omega) (by omega) (blkL_ok h13 h16)
    (x := ![I.s0.1, I.t0.1, I.s1.1, I.t1.1]) (fun i => by
      fin_cases i
      exacts [b0.1, b1.1, b2.1, b3.1])
  have e : xsOf I = [I.s0.1, I.t0.1, I.s1.1, I.t1.1] := rfl
  rw [e]
  exact h ▸ Iff.rfl

/-- At lengths 11 and 12 nothing reduces, and at lengths 17 and up something does. -/
theorem red_outside {I : Inst} (hI : I.WellFormed) :
    (I.w < 13 → (¬ ∃ d, RedX I d) ∧ (¬ ∃ d, RedB I d)) ∧
    (17 ≤ I.w → (∃ d, RedX I d) ∨ (∃ d, RedB I d)) := by
  refine ⟨noRed_lt13, fun h17 => ?_⟩
  by_contra hc
  push Not at hc
  have := leaf16 hI (by omega) (fun d => ⟨fun h => hc.1 d h, fun h => hc.2 d h⟩)
  omega

end ZZN.BoxK
