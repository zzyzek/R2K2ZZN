-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.TimedStatement
import ZZN.Constr.Band
import ZZN.Timed.TimeM

/-!
# The counted band extension

`bandExtET` is `bandExtE` (`ZZN/Constr/Band.lean`) written with the counted operations; each
counted definition has a `*_ret` lemma saying it returns the original result.

Constant-time helpers used directly: arithmetic and comparisons, `shiftAt`, `gap` (at most two
cells), building lists of at most four cells, pattern matches on options and on list heads.
-/

namespace ZZN.T

open ZZN GridHam

/-! ### Stretch and splice -/


@[simp] lemma stretchT_ret (r : ℕ) : ∀ l : List Coord, (stretchT r l).ret = stretch r l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by simp only [stretchT, stretch, ret_bind, stretchT_ret r (b :: l)]


@[simp] lemma insBT_ret (a b : Coord) (X : List Coord) : ∀ l : List Coord, (insBT a b X l).ret = insB a b X l
  | x :: y :: l => by
    unfold insBT insB
    split_ifs
    · rfl
    · simp only [ret_bind]; rw [insBT_ret a b X (y :: l)]
  | [] => rfl
  | [_] => rfl


@[simp] lemma spliceET_ret (P Q : List Coord) (a b : Coord) (X : List Coord) :
    (spliceET P Q a b X).ret = spliceE P Q a b X := by
  unfold spliceET spliceE infix2T
  by_cases h : [a, b] <:+: P <;> simp [h]


@[simp] lemma absorbET_ret (r y y' : ℕ) (P Q : List Coord) :
    (absorbET r y y' P Q).ret = absorbE r y y' P Q := by
  unfold absorbET absorbE infix2T
  by_cases h : [(r + 1, y'), (r + 2, y')] <:+: P ∨ [(r + 1, y'), (r + 2, y')] <:+: Q
  · rw [ite_t h]
    have : (decide ([(r + 1, y'), (r + 2, y')] <:+: P) || decide ([(r + 1, y'), (r + 2, y')] <:+: Q)) = true := by
      simpa using h
    simp only [ret_bind, this, ↓reduceIte, spliceET_ret]
  · rw [ite_f h]
    have : (decide ([(r + 1, y'), (r + 2, y')] <:+: P) || decide ([(r + 1, y'), (r + 2, y')] <:+: Q)) = false := by
      simpa using h
    simp only [ret_bind, this, Bool.false_eq_true, ↓reduceIte, spliceET_ret]


@[simp] lemma flipET_ret (r y : ℕ) (P Q : List Coord) : (flipET r y P Q).ret = flipE r y P Q := by
  unfold flipET flipE infix2T
  by_cases h : [(r, y), (r, y + 1)] <:+: P ∨ [(r, y), (r, y + 1)] <:+: Q
  · rw [ite_t h]
    have : (decide ([(r, y), (r, y + 1)] <:+: P) || decide ([(r, y), (r, y + 1)] <:+: Q)) = true := by
      simpa using h
    simp only [ret_bind, this, ↓reduceIte, spliceET_ret]
  · rw [ite_f h]
    have : (decide ([(r, y), (r, y + 1)] <:+: P) || decide ([(r, y), (r, y + 1)] <:+: Q)) = false := by
      simpa using h
    simp only [ret_bind, this, Bool.false_eq_true, ↓reduceIte, spliceET_ret]

/-! ### Sweeps -/


@[simp] lemma sweepLeftET_ret (r : ℕ) : ∀ (L : ℕ) (U : Finset ℕ) (P Q : List Coord),
    (sweepLeftET r L U P Q).ret = sweepLeftE r L U P Q
  | 0, _, _, _ => rfl
  | L + 1, U, P, Q => by
    simp only [sweepLeftET, sweepLeftE, ret_bind, fmemT, feraseT]
    by_cases h : L ∈ U
    · simp only [h, decide_true, ↓reduceIte, ret_bind, absorbET_ret, sweepLeftET_ret r L]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, sweepLeftET_ret r L]


@[simp] lemma sweepRightET_ret (r h : ℕ) : ∀ (n R : ℕ) (U : Finset ℕ) (P Q : List Coord),
    (sweepRightET r h n R U P Q).ret = sweepRightE r h n R U P Q
  | 0, _, _, _, _ => rfl
  | n + 1, R, U, P, Q => by
    simp only [sweepRightET, sweepRightE, ret_bind, fmemT, feraseT]
    by_cases hm : R + 1 ∈ U
    · simp only [hm, decide_true, ↓reduceIte, ret_bind, absorbET_ret, sweepRightET_ret r h n]
    · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hl : R + 1 < h
      · simp only [hl, ↓reduceIte, sweepRightET_ret r h n]
      · simp only [hl, ↓reduceIte]; rfl

/-! ### Crossings, the seed and the whole extension -/

instance (l : List Coord) (u v : Coord) : Decidable (Used l u v) := by unfold Used; infer_instance


lemma usedT_ret (l : List Coord) (u v : Coord) : (usedT l u v).ret = decide (Used l u v) := by
  simp [usedT, infix2T, Used]


lemma crossT_ret (p q : List Coord) (r y : ℕ) : (crossT p q r y).ret = decide (Cross p q r y) := by
  by_cases a : Used p (r, y) (r + 1, y) <;> by_cases b : Used q (r, y) (r + 1, y) <;>
    simp [crossT, usedT_ret, Cross, a, b]


lemma seedAtT_ret (h : ℕ) (p q : List Coord) (r R : ℕ) :
    (seedAtT h p q r R).ret = decide (SeedAt h p q r R) := by
  simp only [seedAtT, ret_bind, ret_pure, crossT_ret, usedT_ret, SeedAt]
  by_cases a : R = 0 <;> by_cases b : R = h <;> by_cases c : Cross p q r (R - 1) <;>
    by_cases d : Cross p q r R <;> simp [a, b, c, d, Bool.and_assoc]


lemma cond1T_ret (h : ℕ) (p q : List Coord) (r R : ℕ) :
    (cond1T h p q r R).ret = decide ((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = h ∨ Cross p q r R)) := by
  simp [cond1T, crossT_ret]



lemma frange_eq (I : Inst) (p q : List Coord) (r : ℕ) :
    (frangeFilterT I.h (fun y => do let c ← crossT p q r y; pure !c)).ret =
      (Finset.range I.h).filter (fun y => ¬ Cross p q r y) := by
  ext y
  simp [frangeFilterT, crossT_ret]

@[simp] lemma bandExtET_ret (I : Inst) (r : ℕ) (p q : List Coord) :
    (bandExtET I r p q).ret = bandExtE I r p q := by
  have hf : (lfindT (seedAtT I.h p q r) (List.range (I.h + 1))).ret =
      (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) := by
    simp [lfindT, seedAtT_ret]
  simp only [bandExtET, ret_bind, stretchT_ret, rangeT, frange_eq]
  rw [hf]
  unfold bandExtE
  cases (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) with
  | none => rfl
  | some R =>
    simp only [bandFromT, ret_bind, cond1T_ret]
    by_cases h1 : (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R)
    · rw [decide_eq_true h1, ite_t h1]
      simp only [↓reduceIte]
      by_cases h0 : R = 0
      · rw [ite_t h0, ite_t h0, sweepRightET_ret]
      · rw [ite_f h0, ite_f h0]
        by_cases hh : R = I.h
        · rw [ite_t hh, ite_t hh, sweepLeftET_ret]
        · rw [ite_f hh, ite_f hh]
          simp only [ret_bind, sweepLeftET_ret, ffilterT, sweepRightET_ret]
          congr 1
    · rw [decide_eq_false h1, ite_f h1]
      simp only [Bool.false_eq_true, ↓reduceIte, ret_bind, flipET_ret, feraseT, sweepLeftET_ret,
        ffilterT, sweepRightET_ret]
      congr 1

end ZZN.T
