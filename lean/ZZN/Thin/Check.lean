-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Catalogue
import Mathlib.Data.Nat.Pairing

/-!
# The plug DP for thin rectangles (copied from the window DP, `WinCheck.lean`)

Pieces are coded with `Nat.pair` instead of `32 x + y`, so the long side is unbounded.

# Window certificates: the computation

A port of the window-certificate program used during development, written to be evaluated by the
kernel and reasoned about.

Window `W` = rows `0 … a−1`, columns `0 … b−1` at the top-left corner. Cells are processed in
row-major order. A partial covering is abstracted to its **pieces**: maximal runs of processed
cells along a solution path, each with two **ends**, coded as naturals:
- `c` (`c < b`): a plug down from column `c` into the next row;
- `b`: a plug right, into the next cell of the row;
- `b + 1 + s`: exit slot `s` (`s < a`: right of row `s`; `s = a + j`: below column `b − 1 − j`);
- `a + 2b + 1 + col`: an endpoint of colour `col`.
A piece is the code `32 x + y` of its ends `x ≤ y` (all ends are below 32 for `a, b ≤ 8`).
A state is the sorted list of piece codes and a bitmask of the colours whose path is complete.
-/

namespace ZZN.Thin

abbrev St := List ℕ × ℕ

def mkP (x y : ℕ) : ℕ := if x ≤ y then Nat.pair x y else Nat.pair y x
def lo (p : ℕ) : ℕ := (Nat.unpair p).1
def hi (p : ℕ) : ℕ := (Nat.unpair p).2
def hasEnd (e p : ℕ) : Bool := lo p == e || hi p == e
def other (e p : ℕ) : ℕ := if lo p == e then hi p else lo p

def termE (a b col : ℕ) : ℕ := a + 2 * b + 1 + col
def isTerm (a b e : ℕ) : Bool := decide (a + 2 * b + 1 ≤ e)
def colE (a b e : ℕ) : ℕ := e - (a + 2 * b + 1)
def exitE (b s : ℕ) : ℕ := b + 1 + s
def isExit (a b e : ℕ) : Bool := decide (b + 1 ≤ e) && decide (e < a + 2 * b + 1)

def insSorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: l => if x ≤ y then x :: y :: l else y :: insSorted x l

/-- Close a piece with ends `x, y`: a complete path (two endpoints) marks its colour done. -/
def closeP (a b : ℕ) (x y : ℕ) (rest : List ℕ) (dn : ℕ) : Option St :=
  if isTerm a b x && isTerm a b y then
    if colE a b x != colE a b y then none
    else if (dn / 2 ^ colE a b x) % 2 == 1 then none
    else some (rest, dn + 2 ^ colE a b x)
  else some (insSorted (mkP x y) rest, dn)

/-- Process cell `(r, c)`, an endpoint of colour `e` or not. -/
def stepCell (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) : List St :=
  let ps := s.1
  let pu := if r = 0 then none else ps.find? (hasEnd c)
  let pl := if c = 0 then none else ps.find? (hasEnd b)
  let down := if r + 1 < a then c else exitE b (a + (b - 1 - c))
  let right := if c + 1 < b then b else exitE b r
  let nin := (if pu.isSome then 1 else 0) + (if pl.isSome then 1 else 0)
  let deg := if e.isSome then 1 else 2
  if deg < nin then [] else
  if pu.isSome && pu == pl then [] else
  let rest := if pu.isSome then (if pl.isSome then (ps.erase (pu.getD 0)).erase (pl.getD 0)
    else ps.erase (pu.getD 0)) else (if pl.isSome then ps.erase (pl.getD 0) else ps)
  let ins := (pu.map (other c)).toList ++ (pl.map (other b)).toList ++ (e.map (termE a b)).toList
  let opts : List (List ℕ) := match deg - nin with
    | 0 => [[]]
    | 1 => [[down], [right]]
    | _ => [[down, right]]
  opts.filterMap fun outs =>
    match ins ++ outs with
    | [x, y] => closeP a b x y rest s.2
    | _ => none

/-- Lexicographic order on states, for sorting. -/
def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: l, y :: m => x < y || (x == y && ltL l m)

def ltS (s t : St) : Bool := s.2 < t.2 || (s.2 == t.2 && ltL s.1 t.1)

def mergeS : ℕ → List St → List St → List St
  | 0, l, m => l ++ m
  | _ + 1, [], m => m
  | _ + 1, l, [] => l
  | f + 1, x :: l, y :: m => if ltS y x then y :: mergeS f (x :: l) m else x :: mergeS f l (y :: m)

def splitS : List St → List St × List St
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: l => let p := splitS l; (x :: p.1, y :: p.2)

/-- Merge sort with fuel (always a permutation; sorted when the fuel suffices). -/
def msortS : ℕ → List St → List St
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | f + 1, l => let p := splitS l; mergeS (l.length) (msortS f p.1) (msortS f p.2)

def dedupAdj : List St → List St
  | x :: y :: l => if x == y then dedupAdj (y :: l) else x :: dedupAdj (y :: l)
  | l => l

def normS (l : List St) : List St := dedupAdj (msortS 64 l)

def termAt (tm : List ((ℕ × ℕ) × ℕ)) (x : ℕ × ℕ) : Option ℕ := (tm.find? (·.1 == x)).map (·.2)

/-- Cell `i` in row-major order. -/
def cell (b i : ℕ) : ℕ × ℕ := (i / b, i % b)

/-- One DP stage: process cell `i`. -/
def stage (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List St) (i : ℕ) : List St :=
  normS (S.flatMap (stepCell a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2))

/-- All final states: the inside signatures of the window. -/
def inside (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : List St :=
  (List.range (a * b)).foldl (stage a b tm) [([], 0)]


end ZZN.Thin
