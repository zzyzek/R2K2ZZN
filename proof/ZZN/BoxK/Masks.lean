/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.Planes
public import ZZN.Cut.LaneV
public import ZZN.FiniteB

@[expose] public section

/-!
# Lane masks for the column tuples

`axBV N n Y`: lane `j` holds `axB n [Y 0 j, Y 1 j, Y 2 j, Y 3 j]` (no reduction on the column
axis), computed with lane operations (`axBV_get`). `axBBV`: the same with band compressions
(`axBB`, `axBBV_get`).
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane

def allV (l : List ℕ) (f : ℕ → LB) : LB := l.foldr (fun x acc => LB.and (f x) acc) (LB.b true)
def anyV (l : List ℕ) (f : ℕ → LB) : LB := l.foldr (fun x acc => LB.or (f x) acc) (LB.b false)

theorem allV_get (l : List ℕ) (f : ℕ → LB) (j : ℕ) :
    (allV l f).get j = l.all (fun x => (f x).get j) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [allV, LB.at_and] at ih ⊢; rw [ih]

theorem anyV_get (l : List ℕ) (f : ℕ → LB) (j : ℕ) :
    (anyV l f).get j = l.any (fun x => (f x).get j) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [anyV, LB.at_or] at ih ⊢; rw [ih]

/-- The column values of the four endpoints. -/
abbrev Cols := Fin 4 → LV

def colsAt (Y : Cols) (j : ℕ) : List ℕ := [(Y 0).get j, (Y 1).get j, (Y 2).get j, (Y 3).get j]

def freeV (N : ℕ) (Y : Cols) (k : ℕ) : LB :=
  allV [0, 1, 2, 3] fun i => LB.not N (LV.eq N (Y (Fin.ofNat 4 i)) (LV.k k))
def belowV (N : ℕ) (Y : Cols) (k : ℕ) : LB :=
  anyV [0, 1, 2, 3] fun i => LV.lt N (Y (Fin.ofNat 4 i)) (LV.k k)
def aboveV (N : ℕ) (Y : Cols) (k : ℕ) : LB :=
  anyV [0, 1, 2, 3] fun i => LV.lt N (LV.k k) (Y (Fin.ofNat 4 i))

section
variable {N j : ℕ} (hj : j < N)
include hj

theorem freeV_get (Y : Cols) (k : ℕ) : (freeV N Y k).get j = freeB (colsAt Y j) k := by
  simp [freeV, allV_get, freeB, colsAt, LB.at_not hj, LV.at_eq hj, Fin.ofNat]
  rfl

theorem belowV_get (Y : Cols) (k : ℕ) : (belowV N Y k).get j = belowB (colsAt Y j) k := by
  simp [belowV, anyV_get, belowB, colsAt, LV.at_lt hj, Fin.ofNat]
  rfl

theorem aboveV_get (Y : Cols) (k : ℕ) : (aboveV N Y k).get j = aboveB (colsAt Y j) k := by
  simp [aboveV, anyV_get, aboveB, colsAt, LV.at_lt hj, Fin.ofNat]
  rfl

end

/-- `redGen` on lanes. -/
def redGenV (n : ℕ) (F B A : ℕ → LB) (d : ℕ) : LB :=
  LB.and (LB.b (decide (13 ≤ n))) (LB.or (LB.or (LB.or
    (LB.and (LB.b (d == 0)) (allV (List.range 4) F))
    (LB.and (LB.b (d + 2 == n)) (allV (List.range 4) (fun i => F (n - 4 + i)))))
    (anyV (List.range (d + 1)) fun lo => LB.and (LB.and (LB.and (LB.and (LB.b (decide (d + 1 ≤ lo + 9)))
      (LB.b (decide (lo + 10 ≤ n)))) (allV (List.range 10) (fun i => F (lo + i)))) (B lo)) (A (lo + 9))))
    (LB.and (LB.and (LB.and (LB.and (LB.and (LB.and (LB.b (decide (8 ≤ d))) (LB.b (decide (d + 10 ≤ n))))
      (F d)) (F (d + 1))) (LB.or (LB.and (LB.b (decide (1 ≤ d))) (F (d - 1))) (F (d + 2)))) (B d)) (A (d + 1))))

theorem redGenV_get (n : ℕ) (F B A : ℕ → LB) (d j : ℕ) :
    (redGenV n F B A d).get j =
      redGen n (fun k => (F k).get j) (fun k => (B k).get j) (fun k => (A k).get j) d := by
  simp only [redGenV, redGen, LB.at_and, LB.at_or, LB.get_b, allV_get, anyV_get]

def axBV (N n : ℕ) (Y : Cols) : LB :=
  allV (List.range n) fun d => LB.not N (redGenV n (freeV N Y) (belowV N Y) (aboveV N Y) d)

theorem axBV_get {N j : ℕ} (hj : j < N) (n : ℕ) (Y : Cols) :
    (axBV N n Y).get j = axB n (colsAt Y j) := by
  simp only [axBV, allV_get, LB.at_not hj, redGenV_get, axB, redXB]
  congr 1; funext d; congr 2
  · funext k; exact freeV_get hj Y k
  · funext k; exact belowV_get hj Y k
  · funext k; exact aboveV_get hj Y k

/-- `bandGen` on lanes. -/
def bandGenV (n : ℕ) (F B A : ℕ → LB) (d : ℕ) : LB :=
  LB.and (LB.and (LB.and (LB.and (LB.and (LB.and (LB.and (LB.and (LB.and
    (LB.b (decide (13 ≤ n) && decide (5 ≤ d) && decide (d + 7 ≤ n))) (F d)) (F (d + 1)))
    (LB.or (LB.and (LB.b (decide (1 ≤ d))) (F (d - 1))) (F (d + 2)))) (B d)) (A (d + 1)))
    (allV (List.range n) fun k => LB.or (LB.b (!(decide (k < d) && decide (n < k + 8)))) (F k)))
    (allV (List.range n) fun k => LB.or (LB.b (!(decide (d + 2 ≤ k) && decide (k < 7)))) (F k)))
    (LB.b true)) (LB.b true)

theorem bandGenV_get (n : ℕ) (F B A : ℕ → LB) (d j : ℕ) :
    (bandGenV n F B A d).get j =
      bandGen n (fun k => (F k).get j) (fun k => (B k).get j) (fun k => (A k).get j) d := by
  simp only [bandGenV, bandGen, LB.at_and, LB.at_or, LB.get_b, allV_get, Bool.and_true]

def axBBV (N n : ℕ) (Y : Cols) : LB :=
  allV (List.range n) fun d => LB.not N (LB.or (redGenV n (freeV N Y) (belowV N Y) (aboveV N Y) d)
    (bandGenV n (freeV N Y) (belowV N Y) (aboveV N Y) d))

theorem axBBV_get {N j : ℕ} (hj : j < N) (n : ℕ) (Y : Cols) :
    (axBBV N n Y).get j = axBB n (colsAt Y j) := by
  simp only [axBBV, allV_get, LB.at_not hj, LB.at_or, redGenV_get, bandGenV_get, axBB, redXBB,
    redGenB]
  congr 1; funext d; congr 3
  · funext k; exact freeV_get hj Y k
  · funext k; exact belowV_get hj Y k
  · funext k; exact aboveV_get hj Y k
  · funext k; exact freeV_get hj Y k
  · funext k; exact belowV_get hj Y k
  · funext k; exact aboveV_get hj Y k

end ZZN.BoxK
