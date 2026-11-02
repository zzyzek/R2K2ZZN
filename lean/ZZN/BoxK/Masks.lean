-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.BoxK.Planes
import ZZN.Cut.LaneV
import ZZN.Finite

/-!
# Lane masks for the column tuples

`axBV N n Y`: lane `j` holds `axB n [Y 0 j, Y 1 j, Y 2 j, Y 3 j]` (no reduction on the column
axis), computed with lane operations (`axBV_get`).
-/

namespace ZZN.BoxK

open ZZN ZZN.Lane

def allV (N : ℕ) (l : List ℕ) (f : ℕ → LB) : LB := l.foldr (fun x acc => LB.and (f x) acc) (LB.b true)
def anyV (N : ℕ) (l : List ℕ) (f : ℕ → LB) : LB := l.foldr (fun x acc => LB.or (f x) acc) (LB.b false)

theorem allV_get (N : ℕ) (l : List ℕ) (f : ℕ → LB) (j : ℕ) :
    (allV N l f).get j = l.all (fun x => (f x).get j) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [allV, LB.at_and] at ih ⊢; rw [ih]

theorem anyV_get (N : ℕ) (l : List ℕ) (f : ℕ → LB) (j : ℕ) :
    (anyV N l f).get j = l.any (fun x => (f x).get j) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [anyV, LB.at_or] at ih ⊢; rw [ih]

/-- The column values of the four endpoints. -/
abbrev Cols := Fin 4 → LV

def colsAt (Y : Cols) (j : ℕ) : List ℕ := [(Y 0).get j, (Y 1).get j, (Y 2).get j, (Y 3).get j]

def freeV (N : ℕ) (Y : Cols) (k : ℕ) : LB :=
  allV N [0, 1, 2, 3] fun i => LB.not N (LV.eq N (Y (Fin.ofNat 4 i)) (LV.k k))
def belowV (N : ℕ) (Y : Cols) (k : ℕ) : LB :=
  anyV N [0, 1, 2, 3] fun i => LV.lt N (Y (Fin.ofNat 4 i)) (LV.k k)
def aboveV (N : ℕ) (Y : Cols) (k : ℕ) : LB :=
  anyV N [0, 1, 2, 3] fun i => LV.lt N (LV.k k) (Y (Fin.ofNat 4 i))

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
def redGenV (N n : ℕ) (F B A : ℕ → LB) (d : ℕ) : LB :=
  LB.and (LB.b (decide (13 ≤ n))) (LB.or (LB.or (LB.or
    (LB.and (LB.b (d == 0)) (allV N (List.range 4) F))
    (LB.and (LB.b (d + 2 == n)) (allV N (List.range 4) (fun i => F (n - 4 + i)))))
    (anyV N (List.range (d + 1)) fun lo => LB.and (LB.and (LB.and (LB.and (LB.b (decide (d + 1 ≤ lo + 9)))
      (LB.b (decide (lo + 10 ≤ n)))) (allV N (List.range 10) (fun i => F (lo + i)))) (B lo)) (A (lo + 9))))
    (LB.and (LB.and (LB.and (LB.and (LB.and (LB.and (LB.b (decide (8 ≤ d))) (LB.b (decide (d + 10 ≤ n))))
      (F d)) (F (d + 1))) (LB.or (LB.and (LB.b (decide (1 ≤ d))) (F (d - 1))) (F (d + 2)))) (B d)) (A (d + 1))))

theorem redGenV_get (N n : ℕ) (F B A : ℕ → LB) (d j : ℕ) :
    (redGenV N n F B A d).get j =
      redGen n (fun k => (F k).get j) (fun k => (B k).get j) (fun k => (A k).get j) d := by
  simp only [redGenV, redGen, LB.at_and, LB.at_or, LB.get_b, allV_get, anyV_get]

def axBV (N n : ℕ) (Y : Cols) : LB :=
  allV N (List.range n) fun d => LB.not N (redGenV N n (freeV N Y) (belowV N Y) (aboveV N Y) d)

theorem axBV_get {N j : ℕ} (hj : j < N) (n : ℕ) (Y : Cols) :
    (axBV N n Y).get j = axB n (colsAt Y j) := by
  simp only [axBV, allV_get, LB.at_not hj, redGenV_get, axB, redXB]
  congr 1; funext d; congr 2
  · funext k; exact freeV_get hj Y k
  · funext k; exact belowV_get hj Y k
  · funext k; exact aboveV_get hj Y k

end ZZN.BoxK
