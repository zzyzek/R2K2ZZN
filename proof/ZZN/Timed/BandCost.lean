/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.Band
public import ZZN.Timed.CatalogueCost

@[expose] public section

/-!
# The time of the counted band extension

`bandExtET_time`: with `n = |p| + |q|` and `h` the length of the inserted lines, the counted band
extension takes at most `200 (h + 1) (n + h + 1)` steps, and its paths have at most
`3 n + 4 h + 4` cells in total (`bandExtE_len`).
-/

namespace ZZN.T

open ZZN GridHam

/-! ### Lengths -/

lemma gap_len (r : ℕ) (a b : Coord) : (gap r a b).length ≤ 2 := by
  unfold gap; split_ifs <;> simp

lemma stretch_len (r : ℕ) : ∀ l : List Coord, (stretch r l).length ≤ 3 * l.length
  | [] => by simp [stretch]
  | [_] => by simp [stretch]
  | a :: b :: l => by
    have := stretch_len r (b :: l)
    have := gap_len r a b
    simp only [stretch, List.length_cons, List.length_append] at *
    omega

lemma insB_len (a b : Coord) (X : List Coord) : ∀ l : List Coord,
    (insB a b X l).length ≤ l.length + X.length
  | x :: y :: l => by
    unfold insB
    split_ifs
    · simp; omega
    · have := insB_len a b X (y :: l); simp only [List.length_cons] at *; omega
  | [] => by simp [insB]
  | [_] => by simp [insB]

lemma spliceE_len (P Q : List Coord) (a b : Coord) (X : List Coord) :
    (spliceE P Q a b X).1.length + (spliceE P Q a b X).2.length ≤ P.length + Q.length + X.length := by
  unfold spliceE
  split_ifs
  · have := insB_len a b X P; simp only; omega
  · have := insB_len a b X Q; simp only; omega

lemma absorbE_len (r y y' : ℕ) (P Q : List Coord) :
    (absorbE r y y' P Q).1.length + (absorbE r y y' P Q).2.length ≤ P.length + Q.length + 2 := by
  unfold absorbE
  split_ifs
  · exact spliceE_len _ _ _ _ _
  · exact spliceE_len _ _ _ _ _

lemma flipE_len (r y : ℕ) (P Q : List Coord) :
    (flipE r y P Q).1.length + (flipE r y P Q).2.length ≤ P.length + Q.length + 4 := by
  unfold flipE
  split_ifs
  · exact spliceE_len _ _ _ _ _
  · exact spliceE_len _ _ _ _ _

lemma sweepLeftE_len (r : ℕ) : ∀ (L : ℕ) (U : Finset ℕ) (P Q : List Coord),
    (sweepLeftE r L U P Q).1.length + (sweepLeftE r L U P Q).2.length ≤ P.length + Q.length + 2 * L
  | 0, _, _, _ => by simp [sweepLeftE]
  | L + 1, U, P, Q => by
    unfold sweepLeftE
    split_ifs
    · have := sweepLeftE_len r L (U.erase L) (absorbE r L (L + 1) P Q).1 (absorbE r L (L + 1) P Q).2
      have := absorbE_len r L (L + 1) P Q
      omega
    · have := sweepLeftE_len r L U P Q; omega

lemma sweepRightE_len (r h : ℕ) : ∀ (n R : ℕ) (U : Finset ℕ) (P Q : List Coord),
    (sweepRightE r h n R U P Q).1.length + (sweepRightE r h n R U P Q).2.length ≤
      P.length + Q.length + 2 * n
  | 0, _, _, _, _ => by simp [sweepRightE]
  | n + 1, R, U, P, Q => by
    unfold sweepRightE
    split_ifs
    · have := sweepRightE_len r h n (R + 1) (U.erase (R + 1)) (absorbE r (R + 1) R P Q).1
        (absorbE r (R + 1) R P Q).2
      have := absorbE_len r (R + 1) R P Q
      omega
    · have := sweepRightE_len r h n (R + 1) U P Q; omega
    · simp only; omega

lemma bandExtE_len (I : Inst) (r : ℕ) (p q : List Coord) :
    (bandExtE I r p q).1.length + (bandExtE I r p q).2.length ≤
      3 * (p.length + q.length) + 4 * I.h + 4 := by
  have s1 := stretch_len r p
  have s2 := stretch_len r q
  unfold bandExtE
  dsimp only
  generalize hU : (Finset.range I.h).filter (fun y => ¬ Cross p q r y) = U0
  cases hf : (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) with
  | none => simp only; omega
  | some R =>
    have hRh : R ≤ I.h := by
      have := List.mem_range.mp (List.mem_of_find?_eq_some hf); omega
    simp only
    split_ifs
    · have := sweepRightE_len r I.h (I.h - 0) 0 U0 (stretch r p) (stretch r q)
      omega
    · have := sweepLeftE_len r (R - 1) U0 (stretch r p) (stretch r q)
      omega
    · have a := sweepLeftE_len r (R - 1) U0 (stretch r p) (stretch r q)
      have b := sweepRightE_len r I.h (I.h - R) R (U0.filter (R - 1 < ·))
        (sweepLeftE r (R - 1) U0 (stretch r p) (stretch r q)).1
        (sweepLeftE r (R - 1) U0 (stretch r p) (stretch r q)).2
      omega
    · have f := flipE_len r (R - 1) (stretch r p) (stretch r q)
      have a := sweepLeftE_len r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1))
        (flipE r (R - 1) (stretch r p) (stretch r q)).1 (flipE r (R - 1) (stretch r p) (stretch r q)).2
      have b := sweepRightE_len r I.h (I.h - (R - 1 + 1)) (R - 1 + 1)
        (((U0.erase (R - 1)).erase (R - 1 + 1)).filter (R - 1 < ·))
        (sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1))
          (flipE r (R - 1) (stretch r p) (stretch r q)).1 (flipE r (R - 1) (stretch r p) (stretch r q)).2).1
        (sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1))
          (flipE r (R - 1) (stretch r p) (stretch r q)).1 (flipE r (R - 1) (stretch r p) (stretch r q)).2).2
      omega

/-! ### Times -/

lemma stretchT_time (r : ℕ) : ∀ l : List Coord, (stretchT r l).time ≤ 3 * l.length + 1
  | [] => by simp [stretchT]
  | [_] => by simp [stretchT]
  | a :: b :: l => by
    have := stretchT_time r (b :: l)
    simp only [stretchT, time_bind, List.length_cons] at *
    omega

lemma insBT_time (a b : Coord) (X : List Coord) : ∀ l : List Coord,
    (insBT a b X l).time ≤ l.length + X.length + 1
  | x :: y :: l => by
    unfold insBT
    split_ifs
    · simp only [List.length_cons]; omega
    · have := insBT_time a b X (y :: l)
      simp only [time_bind, List.length_cons] at *
      omega
  | [] => by simp [insBT]
  | [_] => by simp [insBT]

lemma spliceET_time (P Q : List Coord) (a b : Coord) (X : List Coord) :
    (spliceET P Q a b X).time ≤ 2 * (P.length + Q.length) + X.length + 2 := by
  unfold spliceET
  simp only [time_bind, infix2T]
  split
  · have := insBT_time a b X P; simp only [time_bind, time_pure]; omega
  · have := insBT_time a b X Q; simp only [time_bind, time_pure]; omega

lemma absorbET_time (r y y' : ℕ) (P Q : List Coord) :
    (absorbET r y y' P Q).time ≤ 3 * (P.length + Q.length) + 8 := by
  unfold absorbET
  simp only [time_bind, infix2T]
  split
  · have := spliceET_time P Q (r + 1, y') (r + 2, y') [(r + 1, y), (r + 2, y)]; simp at this; omega
  · have := spliceET_time P Q (r + 2, y') (r + 1, y') [(r + 2, y), (r + 1, y)]; simp at this; omega

lemma flipET_time (r y : ℕ) (P Q : List Coord) :
    (flipET r y P Q).time ≤ 3 * (P.length + Q.length) + 10 := by
  unfold flipET
  simp only [time_bind, infix2T]
  split
  · have := spliceET_time P Q (r, y) (r, y + 1) [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)]
    simp at this; omega
  · have := spliceET_time P Q (r, y + 1) (r, y) [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)]
    simp at this; omega

lemma sweepLeftET_time (r : ℕ) : ∀ (L : ℕ) (U : Finset ℕ) (P Q : List Coord),
    (sweepLeftET r L U P Q).time ≤ L * (3 * (P.length + Q.length + 2 * L) + 2 * U.card + 12)
  | 0, _, _, _ => by simp [sweepLeftET]
  | L + 1, U, P, Q => by
    simp only [sweepLeftET, time_bind, fmemT]
    split
    · simp only [time_bind, feraseT, absorbET_ret]
      have a := absorbET_time r L (L + 1) P Q
      have l := absorbE_len r L (L + 1) P Q
      have c := Finset.card_erase_le (s := U) (a := L)
      have ih := sweepLeftET_time r L (U.erase L) (absorbE r L (L + 1) P Q).1 (absorbE r L (L + 1) P Q).2
      have m : L * (3 * ((absorbE r L (L + 1) P Q).1.length + (absorbE r L (L + 1) P Q).2.length + 2 * L) +
          2 * (U.erase L).card + 12) ≤ L * (3 * (P.length + Q.length + 2 * L + 2) + 2 * U.card + 12) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    · have ih := sweepLeftET_time r L U P Q
      have m : L * (3 * (P.length + Q.length + 2 * L) + 2 * U.card + 12) ≤
          L * (3 * (P.length + Q.length + 2 * (L + 1)) + 2 * U.card + 12) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith

lemma sweepRightET_time (r h : ℕ) : ∀ (n R : ℕ) (U : Finset ℕ) (P Q : List Coord),
    (sweepRightET r h n R U P Q).time ≤ n * (3 * (P.length + Q.length + 2 * n) + 2 * U.card + 12)
  | 0, _, _, _, _ => by simp [sweepRightET]
  | n + 1, R, U, P, Q => by
    simp only [sweepRightET, time_bind, fmemT]
    split
    · simp only [time_bind, feraseT, absorbET_ret]
      have a := absorbET_time r (R + 1) R P Q
      have l := absorbE_len r (R + 1) R P Q
      have c := Finset.card_erase_le (s := U) (a := R + 1)
      have ih := sweepRightET_time r h n (R + 1) (U.erase (R + 1)) (absorbE r (R + 1) R P Q).1
        (absorbE r (R + 1) R P Q).2
      have m : n * (3 * ((absorbE r (R + 1) R P Q).1.length + (absorbE r (R + 1) R P Q).2.length + 2 * n) +
          2 * (U.erase (R + 1)).card + 12) ≤ n * (3 * (P.length + Q.length + 2 * n + 2) + 2 * U.card + 12) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    · split
      · have ih := sweepRightET_time r h n (R + 1) U P Q
        have m : n * (3 * (P.length + Q.length + 2 * n) + 2 * U.card + 12) ≤
            n * (3 * (P.length + Q.length + 2 * (n + 1)) + 2 * U.card + 12) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith
      · simp only [time_pure]
        have := Nat.le_mul_of_pos_left (3 * (P.length + Q.length + 2 * (n + 1)) + 2 * U.card + 12)
          (by omega : 0 < n + 1)
        omega

lemma usedT_time (l : List Coord) (u v : Coord) : (usedT l u v).time ≤ 2 * l.length + 2 := by
  simp [usedT, infix2T]; omega

lemma crossT_time (p q : List Coord) (r y : ℕ) :
    (crossT p q r y).time ≤ 2 * (p.length + q.length) + 4 := by
  have a := usedT_time p (r, y) (r + 1, y)
  have b := usedT_time q (r, y) (r + 1, y)
  simp only [crossT, time_bind, time_pure]
  omega

lemma seedAtT_time (h : ℕ) (p q : List Coord) (r R : ℕ) :
    (seedAtT h p q r R).time ≤ 6 * (p.length + q.length) + 12 := by
  have a := crossT_time p q r (R - 1)
  have b := crossT_time p q r R
  have c := usedT_time p (r, R - 1) (r, R)
  have d := usedT_time q (r, R - 1) (r, R)
  simp only [seedAtT, time_bind, time_pure]
  omega

lemma cond1T_time (h : ℕ) (p q : List Coord) (r R : ℕ) :
    (cond1T h p q r R).time ≤ 4 * (p.length + q.length) + 8 := by
  have a := crossT_time p q r (R - 1)
  have b := crossT_time p q r R
  simp only [cond1T, time_bind, time_pure]
  omega

/-- `a ≤ h + 1` and `b ≤ k (N + h + 1)` give `a b ≤ k X` with `X = (h + 1) (N + h + 1)`. -/
lemma prodX {a b h N k : ℕ} (ha : a ≤ h + 1) (hb : b ≤ k * (N + h + 1)) :
    a * b ≤ k * ((h + 1) * (N + h + 1)) := by
  calc a * b ≤ (h + 1) * (k * (N + h + 1)) := Nat.mul_le_mul ha hb
    _ = k * ((h + 1) * (N + h + 1)) := by ring

lemma linX {h N : ℕ} : N + h + 1 ≤ (h + 1) * (N + h + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos h)

lemma bandFromT_time (I : Inst) (r : ℕ) (p q : List Coord) (U0 : Finset ℕ) (P0 Q0 : List Coord)
    (R : ℕ) (hR : R ≤ I.h) (hU : U0.card ≤ I.h) (hP : P0.length + Q0.length ≤ 3 * (p.length + q.length)) :
    (bandFromT I r p q U0 P0 Q0 R).time ≤ 100 * ((I.h + 1) * (p.length + q.length + I.h + 1)) := by
  have c := cond1T_time I.h p q r R
  have lx := @linX I.h (p.length + q.length)
  simp only [bandFromT, time_bind]
  split
  · split
    · have := sweepRightET_time r I.h (I.h - 0) 0 U0 P0 Q0
      have m := prodX (k := 24) (show I.h - 0 ≤ I.h + 1 by omega)
        (show 3 * (P0.length + Q0.length + 2 * (I.h - 0)) + 2 * U0.card + 12 ≤
          24 * (p.length + q.length + I.h + 1) by omega)
      omega
    · split
      · have := sweepLeftET_time r (R - 1) U0 P0 Q0
        have m := prodX (k := 24) (show R - 1 ≤ I.h + 1 by omega)
          (show 3 * (P0.length + Q0.length + 2 * (R - 1)) + 2 * U0.card + 12 ≤
            24 * (p.length + q.length + I.h + 1) by omega)
        omega
      · simp only [time_bind, ffilterT]
        have a := sweepLeftET_time r (R - 1) U0 P0 Q0
        have la := sweepLeftE_len r (R - 1) U0 P0 Q0
        have hc : (U0.filter (fun z => decide (R - 1 < z) = true)).card ≤ I.h :=
          (Finset.card_filter_le _ _).trans hU
        have b := sweepRightET_time r I.h (I.h - R) R (U0.filter (fun z => decide (R - 1 < z) = true))
          (sweepLeftET r (R - 1) U0 P0 Q0).ret.1 (sweepLeftET r (R - 1) U0 P0 Q0).ret.2
        simp only [sweepLeftET_ret] at b ⊢
        have m1 := prodX (k := 24) (show R - 1 ≤ I.h + 1 by omega)
          (show 3 * (P0.length + Q0.length + 2 * (R - 1)) + 2 * U0.card + 12 ≤
            24 * (p.length + q.length + I.h + 1) by omega)
        have m2 := prodX (k := 30) (show I.h - R ≤ I.h + 1 by omega)
          (show 3 * ((sweepLeftE r (R - 1) U0 P0 Q0).1.length + (sweepLeftE r (R - 1) U0 P0 Q0).2.length +
            2 * (I.h - R)) + 2 * (U0.filter (fun z => decide (R - 1 < z) = true)).card + 12 ≤
            30 * (p.length + q.length + I.h + 1) by omega)
        omega
  · simp only [time_bind, feraseT, ffilterT, flipET_ret]
    have f := flipET_time r (R - 1) P0 Q0
    have lf := flipE_len r (R - 1) P0 Q0
    have c1 := Finset.card_erase_le (s := U0) (a := R - 1)
    have c2 := Finset.card_erase_le (s := U0.erase (R - 1)) (a := R - 1 + 1)
    have a := sweepLeftET_time r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1))
      (flipE r (R - 1) P0 Q0).1 (flipE r (R - 1) P0 Q0).2
    have la := sweepLeftE_len r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1))
      (flipE r (R - 1) P0 Q0).1 (flipE r (R - 1) P0 Q0).2
    have hc : (((U0.erase (R - 1)).erase (R - 1 + 1)).filter (fun z => decide (R - 1 < z) = true)).card
        ≤ I.h := (Finset.card_filter_le _ _).trans (c2.trans (c1.trans hU))
    have b := sweepRightET_time r I.h (I.h - (R - 1 + 1)) (R - 1 + 1)
      (((U0.erase (R - 1)).erase (R - 1 + 1)).filter (fun z => decide (R - 1 < z) = true))
      (sweepLeftET r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1)) (flipE r (R - 1) P0 Q0).1
        (flipE r (R - 1) P0 Q0).2).ret.1
      (sweepLeftET r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1)) (flipE r (R - 1) P0 Q0).1
        (flipE r (R - 1) P0 Q0).2).ret.2
    simp only [sweepLeftET_ret] at b ⊢
    have m1 := prodX (k := 30) (show R - 1 ≤ I.h + 1 by omega)
      (show 3 * ((flipE r (R - 1) P0 Q0).1.length + (flipE r (R - 1) P0 Q0).2.length + 2 * (R - 1)) +
        2 * ((U0.erase (R - 1)).erase (R - 1 + 1)).card + 12 ≤ 30 * (p.length + q.length + I.h + 1) by omega)
    have m2 := prodX (k := 30) (show I.h - (R - 1 + 1) ≤ I.h + 1 by omega)
      (show 3 * ((sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1))
        (flipE r (R - 1) P0 Q0).1 (flipE r (R - 1) P0 Q0).2).1.length +
        (sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1))
        (flipE r (R - 1) P0 Q0).1 (flipE r (R - 1) P0 Q0).2).2.length + 2 * (I.h - (R - 1 + 1))) +
        2 * (((U0.erase (R - 1)).erase (R - 1 + 1)).filter (fun z => decide (R - 1 < z) = true)).card + 12 ≤
        30 * (p.length + q.length + I.h + 1) by omega)
    omega

/-- **The counted band extension takes at most `200 (h + 1) (n + h + 1)` steps**, `n = |p| + |q|`. -/
theorem bandExtET_time (I : Inst) (r : ℕ) (p q : List Coord) :
    (bandExtET I r p q).time ≤ 200 * ((I.h + 1) * (p.length + q.length + I.h + 1)) := by
  have lx := @linX I.h (p.length + q.length)
  have s1 := stretchT_time r p
  have s2 := stretchT_time r q
  have u : (frangeFilterT I.h (fun y => do let c ← crossT p q r y; pure !c)).time ≤
      I.h * (2 * (p.length + q.length) + 5) := by
    simp only [frangeFilterT]
    have := lsum_le (List.range I.h) (fun y => (do let c ← crossT p q r y; pure !c : TimeM Bool).time + 1)
      (2 * (p.length + q.length) + 5)
      (fun y _ => by simp only [time_bind, time_pure]; have := crossT_time p q r y; omega)
    simpa using this
  have um := prodX (k := 5) (show I.h ≤ I.h + 1 by omega)
    (show 2 * (p.length + q.length) + 5 ≤ 5 * (p.length + q.length + I.h + 1) by omega)
  have hU : (frangeFilterT I.h (fun y => do let c ← crossT p q r y; pure !c)).ret.card ≤ I.h := by
    simp only [frangeFilterT]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have fd := lfindT_time_le (seedAtT I.h p q r) (List.range (I.h + 1)) (6 * (p.length + q.length) + 12)
    (fun R _ => seedAtT_time I.h p q r R)
  simp only [List.length_range] at fd
  have fm := prodX (k := 13) (show I.h + 1 ≤ I.h + 1 by omega)
    (show 6 * (p.length + q.length) + 12 + 1 ≤ 13 * (p.length + q.length + I.h + 1) by omega)
  have hP : (stretch r p).length + (stretch r q).length ≤ 3 * (p.length + q.length) := by
    have := stretch_len r p; have := stretch_len r q; omega
  simp only [bandExtET, time_bind, rangeT, stretchT_ret]
  split
  · simp only [time_pure]; omega
  · rename_i R hR
    have hRh : R ≤ I.h := by
      simp only [lfindT] at hR
      have := List.mem_range.mp (List.mem_of_find?_eq_some hR); omega
    have b := bandFromT_time I r p q _ _ _ R hRh hU hP
    omega

end ZZN.T
