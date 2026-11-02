/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# The statements: definitions

The definitions the main theorems mention, in one module (Palomar's `Challenge.lean` is this file
plus the theorems): grids and paths (`GridHam`), instances and solutions (`ZZN.Defs`), the
forbidden-pattern catalogue (`ZZN.Catalogue`), the plug DP for thin rectangles (`ZZN.Thin`), the
decision procedure `solvableB`, and the construction `solveZZN`. Each block names the module it
was moved from, where its lemmas remain.
-/

-- GridHam.Basic
namespace GridHam
/-- A grid vertex, given as `(x, y)` coordinates. -/
abbrev Coord := ℕ × ℕ
/-- `v` lies within a `width × height` grid (`0 ≤ x < width`, `0 ≤ y <
height`, with the lower bound automatic since coordinates are natural
numbers). -/
def InBounds (width height : ℕ) (v : Coord) : Prop :=
  v.1 < width ∧ v.2 < height
/-- Two vertices are grid-adjacent: they differ by exactly 1 in exactly one
coordinate. -/
def Adjacent (v w : Coord) : Prop :=
  (v.1 = w.1 ∧ (v.2 + 1 = w.2 ∨ w.2 + 1 = v.2)) ∨
  (v.2 = w.2 ∧ (v.1 + 1 = w.1 ∨ w.1 + 1 = v.1))
instance : DecidableRel Adjacent := fun v w => by unfold Adjacent; infer_instance
/-- `Adjacent` as a `Bool`, for use inside the recursive chain check below. -/
def adjacentB (v w : Coord) : Bool := decide (Adjacent v w)
/-- Every consecutive pair in `p` is adjacent, checked by direct recursion
on the list (see the module note on why this doesn't use `List.Chain'`). -/
def chainAdjacent : List Coord → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => adjacentB a b && chainAdjacent (b :: rest)
end GridHam

-- ZZN.Defs
namespace ZZN
open GridHam
/-- `p` is a simple path in the `w × h` grid from `s` to `t`: it starts at `s`, ends at `t`, has no
repeated cell, stays in bounds, and consecutive cells are adjacent. -/
def IsPath (w h : ℕ) (s t : Coord) (p : List Coord) : Prop :=
  p.head? = some s ∧
  p.getLast? = some t ∧
  p.Nodup ∧
  (∀ v ∈ p, InBounds w h v) ∧
  chainAdjacent p = true
/-- An instance: a `w × h` grid with the endpoints of the two colors. -/
structure Inst where
  w  : ℕ
  h  : ℕ
  s0 : Coord
  t0 : Coord
  s1 : Coord
  t1 : Coord
/-- The instance is well formed: the four endpoints are distinct cells of the grid. -/
def Inst.WellFormed (I : Inst) : Prop :=
  InBounds I.w I.h I.s0 ∧ InBounds I.w I.h I.t0 ∧
  InBounds I.w I.h I.s1 ∧ InBounds I.w I.h I.t1 ∧
  I.s0 ≠ I.t0 ∧ I.s0 ≠ I.s1 ∧ I.s0 ≠ I.t1 ∧
  I.t0 ≠ I.s1 ∧ I.t0 ≠ I.t1 ∧ I.s1 ≠ I.t1
/-- `p, q` solve `I`: `p` is a path `s0 → t0`, `q` a path `s1 → t1`, they share no cell, and every
cell of the grid is on one of them. -/
def IsSolution (I : Inst) (p q : List Coord) : Prop :=
  IsPath I.w I.h I.s0 I.t0 p ∧
  IsPath I.w I.h I.s1 I.t1 q ∧
  (∀ v ∈ p, v ∉ q) ∧
  (∀ v, InBounds I.w I.h v → v ∈ p ∨ v ∈ q)
/-- The instance has a solution. -/
def Solvable (I : Inst) : Prop :=
  ∃ p q, IsSolution I p q
end ZZN

-- ZZN.PathFacts
namespace ZZN
open GridHam
/-- `u – v` is an edge of the path `l`, in either direction. -/
def Used (l : List Coord) (u v : Coord) : Prop := [u, v] <:+: l ∨ [v, u] <:+: l
end ZZN

-- ZZN.Stretch
namespace ZZN
open GridHam
/-- Where an old cell goes when two lines are inserted after line `r`. -/
def shiftAt (r : ℕ) (v : Coord) : Coord := if v.1 ≤ r then v else (v.1 + 2, v.2)
/-- The new cells to insert between consecutive old cells `a, b`: two cells if `a – b` crosses
between lines `r` and `r+1`, none otherwise. -/
def gap (r : ℕ) (a b : Coord) : List Coord :=
  if a.1 = r ∧ b.1 = r + 1 ∧ a.2 = b.2 then [(r + 1, a.2), (r + 2, a.2)]
  else if a.1 = r + 1 ∧ b.1 = r ∧ a.2 = b.2 then [(r + 2, a.2), (r + 1, a.2)]
  else []
/-- The stretched path. -/
def stretch (r : ℕ) : List Coord → List Coord
  | [] => []
  | [a] => [shiftAt r a]
  | a :: b :: l => shiftAt r a :: (gap r a b ++ stretch r (b :: l))
end ZZN

-- ZZN.BandExtension
namespace ZZN
open GridHam Classical
variable {I : Inst} {p q : List Coord} {r : ℕ}
/-- Column `y` is crossed between lines `r` and `r+1` by one of the paths. -/
def Cross (p q : List Coord) (r y : ℕ) : Prop :=
  Used p (r, y) (r + 1, y) ∨ Used q (r, y) (r + 1, y)
end ZZN

-- ZZN.Catalogue
namespace ZZN
/-- An endpoint with its color, in grid coordinates. -/
abbrev Pt := (ℕ × ℕ) × ℕ
/-- One of the eight corner frames: flip rows, flip columns, transpose. -/
structure Frame where
  fr : Bool
  fc : Bool
  tr : Bool
def Frame.H (R C : ℕ) (f : Frame) : ℕ := if f.tr then C else R
def Frame.W (R C : ℕ) (f : Frame) : ℕ := if f.tr then R else C
def Frame.to (R C : ℕ) (f : Frame) (p : ℕ × ℕ) : ℕ × ℕ :=
  let a := if f.fr then R - 1 - p.1 else p.1
  let b := if f.fc then C - 1 - p.2 else p.2
  if f.tr then (b, a) else (a, b)
def Frame.back (R C : ℕ) (f : Frame) (q : ℕ × ℕ) : ℕ × ℕ :=
  let r := if f.tr then q.2 else q.1
  let c := if f.tr then q.1 else q.2
  ((if f.fr then R - 1 - r else r), (if f.fc then C - 1 - c else c))
/-- The frames in the JS order. -/
def frames : List Frame :=
  [false, true].flatMap fun fr => [false, true].flatMap fun fc => [false, true].map fun tr =>
    ⟨fr, fc, tr⟩
/-- A view of the endpoints in a frame: `at r c` is the color of the endpoint at frame cell
`(r, c)`, or `none`. -/
structure View where
  H : ℕ
  W : ℕ
  pts : List Pt
def View.at (v : View) (r c : ℕ) : Option ℕ :=
  (v.pts.find? (fun q => q.1 == (r, c))).map (·.2)
def View.empty (v : View) (cells : List (ℕ × ℕ)) : Bool :=
  cells.all fun x => (v.at x.1 x.2).isNone
def makeView (R C : ℕ) (f : Frame) (pts : List Pt) : View :=
  ⟨f.H R C, f.W R C, pts.map fun q => (f.to R C q.1, q.2)⟩
def sgn (p : ℕ × ℕ) : ℤ := if (p.1 + p.2) % 2 == 0 then 1 else -1
def parityOk (R C : ℕ) (pts : List Pt) : Bool :=
  (pts.map (fun q => sgn q.1)).sum == 2 * (((R * C) % 2 : ℕ) : ℤ)
/-- Clockwise perimeter index from `(0,0)`, or `none` for interior cells. -/
def perimIndex (R C : ℕ) (p : ℕ × ℕ) : Option ℕ :=
  if p.1 == 0 then some p.2
  else if p.2 == C - 1 then some ((C - 1) + p.1)
  else if p.1 == R - 1 then some ((C - 1) + (R - 1) + (C - 1 - p.2))
  else if p.2 == 0 then some (2 * (C - 1) + (R - 1) + (R - 1 - p.1))
  else none
def alternating (cols : List ℕ) : Bool :=
  match cols with
  | [a, b, c, d] => a != b && b != c && c != d
  | _ => false
/-- Sort a list of `(key, color)` pairs by key (insertion sort; lists have 4 entries). -/
def sortByKey : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | x :: xs =>
    let s := sortByKey xs
    (s.filter (fun y => y.1 < x.1)) ++ [x] ++ (s.filter (fun y => ¬ (y.1 < x.1)))
def testL2 (v : View) : Bool :=
  match v.at 0 1, v.at 1 0 with
  | some a, some b => a != b && v.empty [(0, 0)]
  | _, _ => false
def testL3 (v : View) : Bool :=
  match v.at 0 2 with
  | some a => v.at 1 1 == some a && v.at 1 0 == some (1 - a) && v.empty [(0, 0), (0, 1)]
  | none => false
def testL4 (v : View) : Bool :=
  match v.at 0 0 with
  | some a => v.at 1 1 == some a && v.at 0 2 == some (1 - a) && decide (v.H ≥ 3) &&
      v.empty [(0, 1), (1, 0)]
  | none => false
def testL5 (v : View) : Bool :=
  match v.at 0 0 with
  | some b => v.at 0 2 == some (1 - b) && v.at 2 0 == some (1 - b) &&
      v.empty [(0, 1), (1, 0), (1, 1)]
  | none => false
def CORNER4 : List (List (ℕ × ℕ) × List (ℕ × ℕ)) := [
  ([(0, 1), (0, 3)], [(1, 1), (1, 3)]), ([(0, 1), (0, 6)], [(0, 7), (1, 1)]),
  ([(0, 1), (0, 6)], [(1, 1), (7, 0)]), ([(0, 1), (0, 6)], [(1, 2), (6, 0)]),
  ([(0, 1), (0, 7)], [(1, 1), (6, 0)]), ([(0, 1), (1, 3)], [(1, 1), (1, 2)]),
  ([(0, 1), (1, 3)], [(1, 2), (2, 2)]), ([(0, 1), (1, 3)], [(1, 2), (3, 1)]),
  ([(0, 1), (2, 2)], [(1, 1), (1, 2)]), ([(0, 1), (2, 2)], [(1, 2), (3, 1)]),
  ([(0, 1), (2, 2)], [(1, 3), (3, 0)]), ([(0, 1), (7, 0)], [(1, 1), (6, 0)]),
  ([(0, 2), (1, 1)], [(2, 1), (3, 0)]), ([(0, 2), (2, 0)], [(1, 2), (2, 1)]),
  ([(0, 3), (2, 1)], [(3, 1), (4, 0)]), ([(0, 6), (2, 1)], [(1, 2), (6, 0)]),
  ([(1, 2), (2, 2)], [(1, 3), (2, 1)]), ([(1, 2), (3, 1)], [(1, 3), (2, 1)]),
  ([(0, 1), (1, 2)], [(0, 4), (2, 2)]), ([(0, 1), (1, 2)], [(0, 4), (3, 1)]),
  ([(0, 1), (1, 2)], [(1, 3), (2, 0)]), ([(0, 1), (1, 2)], [(1, 3), (4, 0)]),
  ([(0, 1), (1, 2)], [(2, 0), (2, 2)]), ([(0, 1), (1, 2)], [(2, 2), (4, 0)]),
  ([(0, 1), (1, 2)], [(3, 1), (4, 0)]), ([(0, 1), (1, 3)], [(0, 3), (0, 4)]),
  ([(0, 1), (1, 3)], [(0, 3), (2, 0)]), ([(0, 1), (1, 3)], [(0, 3), (4, 0)]),
  ([(0, 1), (2, 1)], [(0, 2), (2, 2)]), ([(0, 1), (2, 1)], [(0, 2), (3, 1)]),
  ([(0, 1), (2, 1)], [(0, 4), (1, 3)]), ([(0, 1), (2, 1)], [(0, 4), (2, 2)]),
  ([(0, 1), (2, 1)], [(0, 4), (3, 1)]), ([(0, 1), (2, 1)], [(1, 3), (4, 0)]),
  ([(0, 1), (2, 1)], [(2, 2), (4, 0)]), ([(0, 1), (2, 1)], [(3, 1), (4, 0)]) ]
def CORNER4_ODD : List (List (ℕ × ℕ) × List (ℕ × ℕ)) := [
  ([(0, 0), (0, 1)], [(1, 1), (2, 0)]), ([(0, 0), (1, 4)], [(0, 2), (1, 3)]),
  ([(0, 0), (2, 3)], [(0, 2), (1, 3)]) ]
/-- Two cell lists hold the same set of cells (each has distinct cells). -/
def sameSet (a b : List (ℕ × ℕ)) : Bool :=
  a.length == b.length && a.all (fun x => b.contains x)
def corner4 (R C : ℕ) (f : Frame) (pts : List Pt) : Bool :=
  let A0 := (pts.filter (·.2 == 0)).map (fun q => f.to R C q.1)
  let A1 := (pts.filter (·.2 == 1)).map (fun q => f.to R C q.1)
  let list := if (R * C) % 2 == 0 then CORNER4 else CORNER4_ODD
  list.any fun (A, B) => (sameSet A A0 && sameSet B A1) || (sameSet A A1 && sameSet B A0)
def edgeClosure (v : View) : Bool :=
  (List.range v.W).any fun k =>
    decide (k + 3 < v.W) &&
    match v.at 0 k with
    | some a => v.at 1 (k + 1) == some a && v.at 0 (k + 3) == some (1 - a) &&
        v.at 1 (k + 2) == some (1 - a)
    | none => false
def BOUNDARY3_EVEN : List ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) := [
  ((0, 0), (1, 1), (1, 2)), ((0, 1), (0, 2), (1, 1)), ((0, 1), (0, 2), (1, 2)),
  ((0, 1), (0, 3), (1, 1)), ((0, 1), (0, 4), (1, 1)), ((0, 1), (0, 4), (1, 2)),
  ((0, 1), (0, 5), (1, 1)), ((0, 1), (1, 2), (1, 1)), ((0, 1), (1, 2), (1, 3)),
  ((0, 1), (1, 2), (2, 2)), ((0, 1), (1, 2), (3, 1)), ((0, 1), (1, 3), (0, 3)),
  ((0, 1), (2, 1), (1, 3)), ((0, 1), (2, 1), (2, 2)), ((0, 1), (2, 1), (3, 1)),
  ((0, 2), (2, 1), (1, 0)), ((0, 3), (1, 1), (1, 0)), ((0, 4), (1, 1), (1, 0)),
  ((0, 4), (2, 1), (1, 0)), ((0, 4), (2, 1), (1, 2)), ((0, 5), (1, 1), (1, 0)) ]
def BOUNDARY3_ODD : List ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) := [
  ((0, 0), (1, 1), (1, 2)), ((0, 0), (1, 1), (2, 2)), ((0, 1), (0, 2), (1, 1)),
  ((0, 1), (0, 4), (1, 1)), ((0, 4), (1, 1), (1, 0)) ]
def boundaryOnly (R C : ℕ) (f : Frame) (pts : List Pt) : Bool :=
  let list := if R % 2 == 1 && C % 2 == 1 then BOUNDARY3_ODD else BOUNDARY3_EVEN
  let fp := pts.map fun q => (f.to R C q.1, q.2)
  let H := f.H R C
  let W := f.W R C
  list.any fun (a1, a2, b) => [0, 1].any fun A =>
    let isA := fun (x : ℕ × ℕ) => fp.any (fun q => q.2 == A && q.1 == x)
    match fp.find? (fun q => q.2 == 1 - A && q.1 == b) with
    | none => false
    | some _ =>
      isA a1 && isA a2 &&
      match fp.find? (fun q => q.2 == 1 - A && q.1 != b) with
      | none => false
      | some (fourth, _) =>
        let onPerim := fourth.1 == 0 || fourth.2 == 0 || fourth.1 == H - 1 || fourth.2 == W - 1
        let inWin := decide (fourth.1 < 6) && decide (fourth.2 < 6)
        onPerim && !inWin
/-- A rewrite: settled cells and endpoint moves, in frame coordinates. -/
structure Rewrite where
  removed : List (ℕ × ℕ)
  moves   : List ((ℕ × ℕ) × (ℕ × ℕ))
def rewritesAt (v : View) : Option Rewrite :=
  let e := v.at
  -- R3 widget
  if (match e 1 2, e 2 1 with | some x, some y => x != y | _, _ => false) && decide (v.H ≥ 4) &&
      decide (v.W ≥ 4) && v.empty [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0), (3, 0)]
  then some ⟨[(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (1, 2), (2, 1)],
    [((1, 2), (0, 3)), ((2, 1), (3, 0))]⟩
  -- R2 diagonal pair
  else if (match e 0 0 with | some a => e 1 1 == some a | none => false) && decide (v.H ≥ 3) &&
      decide (v.W ≥ 3) && v.empty [(0, 1), (1, 0), (0, 2), (2, 0)]
  then some ⟨[(0, 0), (0, 1), (1, 0), (1, 1)], [((0, 0), (0, 2)), ((1, 1), (2, 0))]⟩
  -- R1 corner hop
  else if (e 0 1).isSome && v.empty [(0, 0), (1, 0)] && decide (v.H ≥ 2)
  then some ⟨[(0, 0), (0, 1)], [((0, 1), (1, 0))]⟩
  else none
def positions (walk : List (ℕ × ℕ)) (x : ℕ × ℕ) : List ℕ :=
  (walk.zipIdx.filter (fun q => q.1 == x)).map (·.2)
structure RWState where
  eff     : List Pt
  removed : List (ℕ × ℕ)
  any     : Bool
def moveFirst (e : List Pt) (m : (ℕ × ℕ) × (ℕ × ℕ)) : List Pt :=
  match e.findIdx? (fun q => q.1 == m.1) with
  | some i => e.modify i (fun q => (m.2, q.2))
  | none => e
def rwStep (R C : ℕ) (st : RWState) (f : Frame) : RWState :=
  match rewritesAt (makeView R C f st.eff) with
  | none => st
  | some rw =>
    let cells := rw.removed.map (f.back R C)
    let moves := rw.moves.map fun (a, b) => (f.back R C a, f.back R C b)
    if cells.any (fun x => st.removed.contains x) then st
    else if moves.any (fun m => st.removed.contains m.2) then st
    else ⟨moves.foldl moveFirst st.eff, st.removed ++ cells, true⟩
def rewriteAll (R C : ℕ) (pts : List Pt) : RWState :=
  frames.foldl (rwStep R C) ⟨pts, [], false⟩
def t1Fires (R C : ℕ) (pts : List Pt) : Bool :=
  let idx := pts.map (fun q => perimIndex R C q.1)
  idx.all Option.isSome &&
    alternating ((sortByKey ((idx.map (·.getD 0)).zip (pts.map (·.2)))).map (·.2))
def t2Fires (cells : List (ℕ × ℕ)) : Bool :=
  let rs := cells.map (·.1)
  let cs := cells.map (·.2)
  let mx := fun (l : List ℕ) => l.foldl max 0
  let mn := fun (l : List ℕ) => l.foldl min (l.headD 0)
  mx rs - mn rs == 1 && mx cs - mn cs == 1 && mn rs + 1 == mx rs && mn cs + 1 == mx cs &&
    rs[0]! != rs[1]! && cs[0]! != cs[1]!
def l1Fires (R C : ℕ) (pts : List Pt) : Bool :=
  pts.any fun (p, col) =>
    let pr : ℤ := p.1
    let pc : ℤ := p.2
    let nb : List (ℤ × ℤ) := ([(pr - 1, pc), (pr + 1, pc), (pr, pc - 1), (pr, pc + 1)] : List (ℤ × ℤ)).filter
      fun q => decide (0 ≤ q.1) && decide (q.1 < (R : ℤ)) && decide (0 ≤ q.2) && decide (q.2 < (C : ℤ))
    nb.all (fun q => pts.any fun pc' => pc'.1 == (q.1.toNat, q.2.toNat) && pc'.2 != col)
def l6Closures (R C : ℕ) (pts : List Pt) : List ℕ :=
  ([(0, 0, 1, 1), (0, (C : ℤ) - 1, 1, -1), ((R : ℤ) - 1, 0, -1, 1), ((R : ℤ) - 1, (C : ℤ) - 1, -1, -1)] :
      List (ℤ × ℤ × ℤ × ℤ)).filterMap fun (cr, cc, dr, dc) =>
    let n1 : ℕ × ℕ := (cr.toNat, (cc + dc).toNat)
    let n2 : ℕ × ℕ := ((cr + dr).toNat, cc.toNat)
    let cornerEmpty := !(pts.any (·.1 == (cr.toNat, cc.toNat)))
    match pts.find? (·.1 == n1), pts.find? (·.1 == n2) with
    | some a, some b => if a.2 == b.2 && cornerEmpty then some a.2 else none
    | _, _ => none
def l6Fires (R C : ℕ) (pts : List Pt) : Bool :=
  let cl := l6Closures R C pts
  cl.contains 0 && cl.contains 1 && decide (R * C > 6)
def frameFires (R C : ℕ) (pts : List Pt) (f : Frame) : Bool :=
  let v := makeView R C f pts
  testL2 v || testL3 v || testL4 v || testL5 v || edgeClosure v || boundaryOnly R C f pts ||
    (decide (R ≥ 10) && decide (C ≥ 10) && corner4 R C f pts)
/-- Number of removed cells in row `i` of a corner frame (rows and columns `< 4`). -/
def notchLen (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  ((List.range 4).filter fun j => removed.contains (f.back R C (i, j))).length
/-- The staircase cells, in frame coordinates, from `(k, 0)` to `(0, λ 0)`. -/
def staircase (lam : ℕ → ℕ) : List (ℕ × ℕ) :=
  let k := ((List.range 4).filter fun i => lam i > 0).length
  [(k, 0)] ++ ((List.range k).reverse.flatMap fun i =>
    ((List.range (lam i - lam (i + 1))).map fun j => (i + 1, lam (i + 1) + 1 + j)) ++ [(i, lam i)])
def frameTL : Frame := ⟨false, false, false⟩
def frameTR : Frame := ⟨false, true, false⟩
def frameBR : Frame := ⟨true, true, false⟩
def frameBL : Frame := ⟨true, false, false⟩
def stairOf (R C : ℕ) (f : Frame) (removed : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (staircase (notchLen R C f removed)).map (f.back R C)
/-- The outer walk of the grid minus corner staircases, as an explicit list. -/
def walk3 (R C : ℕ) (removed : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let tl := stairOf R C frameTL removed
  let tr := (stairOf R C frameTR removed).reverse
  let br := stairOf R C frameBR removed
  let bl := (stairOf R C frameBL removed).reverse
  let lTL := notchLen R C frameTL removed 0
  let lTR := notchLen R C frameTR removed 0
  let lBR := notchLen R C frameBR removed 0
  let lBL := notchLen R C frameBL removed 0
  let kTL := ((List.range 4).filter fun i => notchLen R C frameTL removed i > 0).length
  let kTR := ((List.range 4).filter fun i => notchLen R C frameTR removed i > 0).length
  let kBR := ((List.range 4).filter fun i => notchLen R C frameBR removed i > 0).length
  let kBL := ((List.range 4).filter fun i => notchLen R C frameBL removed i > 0).length
  -- the four sides, strictly between the staircases
  let top := ((List.range C).filter fun y => lTL < y ∧ y + 1 + lTR < C).map fun y => (0, y)
  let right := ((List.range R).filter fun x => kTR < x ∧ x + 1 + kBR < R).map fun x => (x, C - 1)
  let bottom := (((List.range C).filter fun y => lBL < y ∧ y + 1 + lBR < C).map fun y =>
    (R - 1, y)).reverse
  let left := (((List.range R).filter fun x => kTL < x ∧ x + 1 + kBL < R).map fun x =>
    (x, 0)).reverse
  tl ++ top ++ tr ++ right ++ br ++ bottom ++ bl ++ left
def effAlt3 (R C : ℕ) (pts : List Pt) : Bool :=
  let st := rewriteAll R C pts
  if !st.any then false
  else if st.eff.any (fun q => st.removed.contains q.1) then false
  else if (st.eff.map (·.1)).dedup.length != 4 then false
  else
    let walk := walk3 R C st.removed
    let places := st.eff.map fun q => (positions walk q.1, q.2)
    if places.any (fun pl => pl.1.length != 1) then false
    else alternating ((sortByKey (places.map fun pl => (pl.1.headD 0, pl.2))).map (·.2))
/-- `fires` with the explicit outer walk. -/
def fires3 (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) : Bool :=
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  !parityOk R C pts || t1Fires R C pts || t2Fires [s0, t0, s1, t1] || l1Fires R C pts ||
    l6Fires R C pts || frames.any (frameFires R C pts) || effAlt3 R C pts
/-- The instance passes the catalogue: no entry fires. Defined from the fully functional form
`fires3` (the R test via the explicit outer walk `walk3`). Checked against the JavaScript catalogue: the
verdict and, separately, the R test agree on 3.66 M instances, 18 k of them with the R test true
-/
def Passes (I : Inst) : Prop := fires3 I.w I.h I.s0 I.t0 I.s1 I.t1 = false
end ZZN

-- ZZN.Constr.Band
namespace ZZN
open GridHam
/-- Insert `X` between the first consecutive pair `a, b`. -/
def insB (a b : Coord) (X : List Coord) : List Coord → List Coord
  | x :: y :: l => if x = a ∧ y = b then x :: (X ++ y :: l) else x :: insB a b X (y :: l)
  | l => l
/-- Splice `X` into the edge `a – b` of whichever path holds it (as `a, b`). -/
def spliceE (P Q : List Coord) (a b : Coord) (X : List Coord) : List Coord × List Coord :=
  if [a, b] <:+: P then (insB a b X P, Q) else (P, insB a b X Q)
/-- Cover column `y` by a detour of the middle edge of column `y'`. -/
def absorbE (r y y' : ℕ) (P Q : List Coord) : List Coord × List Coord :=
  if [(r + 1, y'), (r + 2, y')] <:+: P ∨ [(r + 1, y'), (r + 2, y')] <:+: Q then
    spliceE P Q (r + 1, y') (r + 2, y') [(r + 1, y), (r + 2, y)]
  else spliceE P Q (r + 2, y') (r + 1, y') [(r + 2, y), (r + 1, y)]
/-- Cover columns `y, y + 1` by a detour of the row-`r` edge between them. -/
def flipE (r y : ℕ) (P Q : List Coord) : List Coord × List Coord :=
  if [(r, y), (r, y + 1)] <:+: P ∨ [(r, y), (r, y + 1)] <:+: Q then
    spliceE P Q (r, y) (r, y + 1) [(r + 1, y), (r + 2, y), (r + 2, y + 1), (r + 1, y + 1)]
  else spliceE P Q (r, y + 1) (r, y) [(r + 1, y + 1), (r + 2, y + 1), (r + 2, y), (r + 1, y)]
/-- Cover the uncovered columns below `L`, from the middle edge of column `L` down. -/
def sweepLeftE (r : ℕ) : ℕ → Finset ℕ → List Coord → List Coord → List Coord × List Coord
  | 0, _, P, Q => (P, Q)
  | L + 1, U, P, Q =>
    if L ∈ U then sweepLeftE r L (U.erase L) (absorbE r L (L + 1) P Q).1 (absorbE r L (L + 1) P Q).2
    else sweepLeftE r L U P Q
/-- Cover the uncovered columns above `R`, from the middle edge of column `R` up. -/
def sweepRightE (r h : ℕ) : ℕ → ℕ → Finset ℕ → List Coord → List Coord → List Coord × List Coord
  | 0, _, _, P, Q => (P, Q)
  | n + 1, R, U, P, Q =>
    if R + 1 ∈ U then
      sweepRightE r h n (R + 1) (U.erase (R + 1)) (absorbE r (R + 1) R P Q).1 (absorbE r (R + 1) R P Q).2
    else if R + 1 < h then sweepRightE r h n (R + 1) U P Q
    else (P, Q)
instance (p q : List Coord) (r y : ℕ) : Decidable (Cross p q r y) := by
  unfold Cross Used; infer_instance
/-- The condition of `seed_or_flip` at position `R`. -/
def SeedAt (h : ℕ) (p q : List Coord) (r R : ℕ) : Prop :=
  ((R = 0 ∨ Cross p q r (R - 1)) ∧ (R = h ∨ Cross p q r R)) ∨
    (1 ≤ R ∧ R < h ∧ ¬ Cross p q r (R - 1) ∧ ¬ Cross p q r R ∧
      (Used p (r, R - 1) (r, R) ∨ Used q (r, R - 1) (r, R)))
instance (h : ℕ) (p q : List Coord) (r R : ℕ) : Decidable (SeedAt h p q r R) := by
  unfold SeedAt Used; infer_instance
/-- The construction of `band_extension`, as a function. -/
def bandExtE (I : Inst) (r : ℕ) (p q : List Coord) : List Coord × List Coord :=
  let U0 := (Finset.range I.h).filter (fun y => ¬ Cross p q r y)
  let P0 := stretch r p
  let Q0 := stretch r q
  match (List.range (I.h + 1)).find? (fun R => decide (SeedAt I.h p q r R)) with
  | none => (P0, Q0)
  | some R =>
    if (R = 0 ∨ Cross p q r (R - 1)) ∧ (R = I.h ∨ Cross p q r R) then
      if R = 0 then sweepRightE r I.h (I.h - 0) 0 U0 P0 Q0
      else if R = I.h then sweepLeftE r (R - 1) U0 P0 Q0
      else
        sweepRightE r I.h (I.h - R) R (U0.filter (R - 1 < ·)) (sweepLeftE r (R - 1) U0 P0 Q0).1
          (sweepLeftE r (R - 1) U0 P0 Q0).2
    else
      sweepRightE r I.h (I.h - (R - 1 + 1)) (R - 1 + 1)
        (((U0.erase (R - 1)).erase (R - 1 + 1)).filter (R - 1 < ·))
        (sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1)) (flipE r (R - 1) P0 Q0).1
          (flipE r (R - 1) P0 Q0).2).1
        (sweepLeftE r (R - 1) ((U0.erase (R - 1)).erase (R - 1 + 1)) (flipE r (R - 1) P0 Q0).1
          (flipE r (R - 1) P0 Q0).2).2
end ZZN

-- ZZN.Reductions
namespace ZZN
open GridHam
/-- Delete the lines `x = d, d+1`. -/
def delAt (d : ℕ) (v : Coord) : Coord := if v.1 < d then v else (v.1 - 2, v.2)
def Inst.deleteAt (I : Inst) (d : ℕ) : Inst where
  w  := I.w - 2
  h  := I.h
  s0 := delAt d I.s0
  t0 := delAt d I.t0
  s1 := delAt d I.s1
  t1 := delAt d I.t1
/-- The four endpoints of `I`. -/
def Inst.ends (I : Inst) : List Coord := [I.s0, I.t0, I.s1, I.t1]
end ZZN

-- ZZN.Solve
namespace ZZN
open GridHam
instance (w h : ℕ) (s t : Coord) (p : List Coord) : Decidable (IsPath w h s t p) := by
  unfold IsPath InBounds; infer_instance
/-- `p, q` solve `I`; coverage is checked by counting. -/
def solB (I : Inst) (p q : List Coord) : Bool :=
  decide (IsPath I.w I.h I.s0 I.t0 p) && decide (IsPath I.w I.h I.s1 I.t1 q) &&
    decide ((p ++ q).Nodup) && (p.length + q.length == I.w * I.h)
end ZZN

-- ZZN.Symmetry
namespace ZZN
open GridHam
def Inst.transpose (I : Inst) : Inst where
  w  := I.h
  h  := I.w
  s0 := I.s0.swap
  t0 := I.t0.swap
  s1 := I.s1.swap
  t1 := I.t1.swap
end ZZN

-- ZZN.Constr.Lift
namespace ZZN
open GridHam
def freeLineB (I : Inst) (k : ℕ) : Bool := I.ends.all (fun e => e.1 != k)
def endBelowB (I : Inst) (k : ℕ) : Bool := I.ends.any (fun e => decide (e.1 < k))
def endAboveB (I : Inst) (k : ℕ) : Bool := I.ends.any (fun e => decide (k < e.1))
/-- `RedX I d`, decided. -/
def redB (I : Inst) (d : ℕ) : Bool :=
  decide (13 ≤ I.w) &&
  ((d == 0 && (List.range 4).all (freeLineB I)) ||
   (d + 2 == I.w && (List.range I.w).all (fun k => !(decide (I.w ≤ k + 4)) || freeLineB I k)) ||
   (List.range (d + 1)).any (fun lo => decide (d + 1 ≤ lo + 9) && decide (lo + 10 ≤ I.w) &&
      (List.range 10).all (fun j => freeLineB I (lo + j)) && endBelowB I lo && endAboveB I (lo + 9)) ||
   (decide (8 ≤ d) && decide (d + 10 ≤ I.w) && freeLineB I d && freeLineB I (d + 1) &&
      ((decide (1 ≤ d) && freeLineB I (d - 1)) || freeLineB I (d + 2)) && endBelowB I d && endAboveB I (d + 1)))
def findRed (I : Inst) : Option ℕ := (List.range I.w).find? (redB I)
/-- Band extension after line `d` (when line `d + 2` is free) or after line `d - 1`. -/
def liftE (I : Inst) (d : ℕ) (p q : List Coord) : List Coord × List Coord :=
  if d + 3 ≤ I.w ∧ freeLineB I (d + 2) = true then bandExtE (I.deleteAt d) d p q
  else bandExtE (I.deleteAt d) (d - 1) p q
end ZZN

-- ZZN.Constr.Solve
namespace ZZN
open GridHam
/-- Keep a candidate only if the verified checker accepts it. -/
def checkE (I : Inst) : Option (List Coord × List Coord) → Option (List Coord × List Coord)
  | some pq => if solB I pq.1 pq.2 then some pq else none
  | none => none
/-- The recursive construction, with fuel. Every candidate is checked by `solB`, so the lists passed
up the recursion always have `w h` cells. -/
def solveRec (thin : Inst → Option (List Coord × List Coord)) :
    ℕ → Inst → Option (List Coord × List Coord)
  | 0, _ => none
  | n + 1, I =>
    if I.w ≤ 10 ∨ I.h ≤ 10 then checkE I (thin I) else
    match findRed I with
    | some d =>
      match solveRec thin n (I.deleteAt d) with
      | some pq => checkE I (some (liftE I d pq.1 pq.2))
      | none => none
    | none =>
      match findRed I.transpose with
      | some d =>
        match solveRec thin n (I.transpose.deleteAt d) with
        | some pq => checkE I (some ((liftE I.transpose d pq.1 pq.2).1.map Prod.swap,
            (liftE I.transpose d pq.1 pq.2).2.map Prod.swap))
        | none => none
      | none => checkE I (thin I)
/-- **The construction**, checked. -/
def solveZ (thin : Inst → Option (List Coord × List Coord)) (I : Inst) :
    Option (List Coord × List Coord) :=
  match solveRec thin (I.w + I.h) I with
  | some pq => if solB I pq.1 pq.2 then some pq else none
  | none => none
end ZZN

-- ZZN.Thin.Check
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
end ZZN.Thin

-- ZZN.Thin.Step
namespace ZZN.Thin
open GridHam
/-- The pieces left after removing the attached runs, as `stepCell` computes them. -/
def restK (ps : List ℕ) (pu pl : Option ℕ) : List ℕ :=
  if pu.isSome then (if pl.isSome then (ps.erase (pu.getD 0)).erase (pl.getD 0) else ps.erase (pu.getD 0))
  else (if pl.isSome then ps.erase (pl.getD 0) else ps)
end ZZN.Thin

-- ZZN.Thin.Sound
namespace ZZN.Thin
open GridHam
variable (a b : ℕ) (J : Inst)
/-- The endpoints of colour `col`. -/
def ends2 (col : ℕ) : Coord × Coord := if col = 0 then (J.s0, J.t0) else (J.s1, J.t1)
end ZZN.Thin

-- ZZN.Thin.Sound
namespace ZZN.Thin
open GridHam
def tmOf (J : Inst) : List ((ℕ × ℕ) × ℕ) := [(J.s0, 0), (J.t0, 0), (J.s1, 1), (J.t1, 1)]
end ZZN.Thin

-- ZZN.Thin.Fast
namespace ZZN.Thin
open GridHam
/-- An end code that is a plug inside the grid, or an endpoint. -/
def okEnd (a b e : ℕ) : Bool := decide (e ≤ b) || isTerm a b e
def noExit (a b : ℕ) (s : St) : Bool := s.1.all fun z => okEnd a b (lo z) && okEnd a b (hi z)
def stageF (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List St) (i : ℕ) : List St :=
  (stage a b tm S i).filter (noExit a b)
def insideF (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : List St :=
  (List.range (a * b)).foldl (stageF a b tm) [([], 0)]
def dpAcceptF (J : Inst) : Bool := (insideF J.w J.h (tmOf J)).contains ([], 3)
/-- Rows along the longer side, so the frontier is the short side. -/
def thinBF (J : Inst) : Bool := if J.h ≤ J.w then dpAcceptF J else dpAcceptF J.transpose
end ZZN.Thin

-- ZZN.Constr.ThinWit
namespace ZZN.Thin
open GridHam
/-- Segments of the open pieces (keyed by piece code), and the completed paths of the colours. -/
abbrev Wit := List (ℕ × List Coord) × (List Coord × List Coord)
/-- The segment stored for piece `z` (`[]` if none). -/
def lookD (l : List (ℕ × List Coord)) (z : ℕ) : List Coord :=
  ((l.find? (fun q => q.1 == z)).map Prod.snd).getD []
def setDp (d : List Coord × List Coord) (col : ℕ) (P : List Coord) : List Coord × List Coord :=
  if col = 0 then (P, d.2) else (d.1, P)
/-- Orient the segment of piece `z` so that its end `e` comes last. -/
def orientS (e z : ℕ) (L : List Coord) : List Coord := if lo z = e then L.reverse else L
/-- Orient a segment with ends `x, y` so that the smaller code comes first. -/
def orientN (x y : ℕ) (L : List Coord) : List Coord := if x ≤ y then L else L.reverse
/-- Orient a completed path of colour `col` to start at its first endpoint. -/
def orientP (J : Inst) (col : ℕ) (L : List Coord) : List Coord :=
  if L.head? = some (ends2 J col).1 then L else L.reverse
/-- The piece plugged into cell `(r, c)` from above. -/
def puOf (s : St) (r c : ℕ) : Option ℕ := if r = 0 then none else s.1.find? (hasEnd c)
/-- The piece plugged into cell `(r, c)` from the left. -/
def plOf (b : ℕ) (s : St) (c : ℕ) : Option ℕ := if c = 0 then none else s.1.find? (hasEnd b)
/-- The new segment through cell `(r, c)`: the piece from above (ending above the cell), the cell,
then the piece from the left reversed; or the piece from the left followed by the cell. -/
def segNew (b r c : ℕ) (sg : ℕ → List Coord) (pu pl : Option ℕ) : List Coord :=
  if pu.isSome then (pu.map fun z => orientS c z (sg z)).getD [] ++ [(r, c)] ++
    ((pl.map fun z => orientS b z (sg z)).getD []).reverse
  else (pl.map fun z => orientS b z (sg z)).getD [] ++ [(r, c)]
/-- Drop the segments of the attached pieces. -/
def dropKeys (pu pl : Option ℕ) (l : List (ℕ × List Coord)) : List (ℕ × List Coord) :=
  l.filter fun q => pu != some q.1 && pl != some q.1
/-- The witness after closing a new segment `Ln` with end codes `x, y`. -/
def closeWit (J : Inst) (a b x y : ℕ) (Ln : List Coord) (sgR : List (ℕ × List Coord))
    (d : List Coord × List Coord) : Wit :=
  if isTerm a b x && isTerm a b y then (sgR, setDp d (colE a b x) (orientP J (colE a b x) Ln))
  else ((mkP x y, orientN x y Ln) :: sgR, d)
def ninOf (pu pl : Option ℕ) : ℕ := (if pu.isSome then 1 else 0) + (if pl.isSome then 1 else 0)
def degOf (e : Option ℕ) : ℕ := if e.isSome then 1 else 2
/-- The end codes entering the current cell: from the attached pieces and an endpoint. -/
def insOf (a b c : ℕ) (e pu pl : Option ℕ) : List ℕ :=
  (pu.map (other c)).toList ++ (pl.map (other b)).toList ++ (e.map (termE a b)).toList
/-- The choices of new plugs leaving the current cell. -/
def optsOf (a b r c : ℕ) (e pu pl : Option ℕ) : List (List ℕ) :=
  match degOf e - ninOf pu pl with
  | 0 => [[]]
  | 1 => [[if r + 1 < a then c else exitE b (a + (b - 1 - c))], [if c + 1 < b then b else exitE b r]]
  | _ => [[if r + 1 < a then c else exitE b (a + (b - 1 - c)), if c + 1 < b then b else exitE b r]]
/-- Close the new segment for each choice of plugs, reporting its end codes. -/
def closeOuts (a b : ℕ) (ins rest : List ℕ) (dn : ℕ) (opts : List (List ℕ)) : List ((ℕ × ℕ) × St) :=
  opts.filterMap fun outs =>
    match ins ++ outs with
    | [x, y] => (closeP a b x y rest dn).map fun s' => ((x, y), s')
    | _ => none
/-- `stepCell`, also reporting the two end codes of the new segment. -/
def stepCellG (a b : ℕ) (e : Option ℕ) (r c : ℕ) (s : St) : List ((ℕ × ℕ) × St) :=
  if degOf e < ninOf (puOf s r c) (plOf b s c) then [] else
  if (puOf s r c).isSome && puOf s r c == plOf b s c then [] else
  closeOuts a b (insOf a b c e (puOf s r c) (plOf b s c)) (restK s.1 (puOf s r c) (plOf b s c)) s.2
    (optsOf a b r c e (puOf s r c) (plOf b s c))
/-- **One cell of the witness-carrying DP.** -/
def stepCellW (J : Inst) (a b : ℕ) (e : Option ℕ) (r c : ℕ) (sw : St × Wit) : List (St × Wit) :=
  let pu := puOf sw.1 r c
  let pl := plOf b sw.1 c
  let Ln := segNew b r c (lookD sw.2.1) pu pl
  let sgR := dropKeys pu pl sw.2.1
  (stepCellG a b e r c sw.1).map fun g => (g.2, closeWit J a b g.1.1 g.1.2 Ln sgR sw.2.2)
/-- Keep the first entry of each state not in `seen`. -/
def dedupKeyAux : List St → List (St × Wit) → List (St × Wit)
  | _, [] => []
  | seen, x :: l => if x.1 ∈ seen then dedupKeyAux seen l else x :: dedupKeyAux (x.1 :: seen) l
/-- Keep the first entry of each state. -/
def dedupKey (l : List (St × Wit)) : List (St × Wit) := dedupKeyAux [] l
def stageW (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) (S : List (St × Wit)) (i : ℕ) :
    List (St × Wit) :=
  dedupKey ((S.flatMap (stepCellW J a b (termAt tm (cell b i)) (cell b i).1 (cell b i).2)).filter
    fun sw => noExit a b sw.1)
def insideW (J : Inst) (a b : ℕ) (tm : List ((ℕ × ℕ) × ℕ)) : List (St × Wit) :=
  (List.range (a * b)).foldl (stageW J a b tm) [(([], 0), ([], ([], [])))]
/-- The accepting entry's paths, rows along `J.w`. -/
def solveDP (J : Inst) : Option (List Coord × List Coord) :=
  ((insideW J J.w J.h (tmOf J)).find? fun sw => sw.1 == (([], 3) : St)).map fun sw => sw.2.2
/-- **The solver**: a solution of a well-formed instance, if there is one. Rows along the longer
side, as in `thinBF`. -/
def thinSolveW (J : Inst) : Option (List Coord × List Coord) :=
  if J.h ≤ J.w then solveDP J
  else (solveDP J.transpose).map fun pq => (pq.1.map Prod.swap, pq.2.map Prod.swap)
end ZZN.Thin

-- ZZN.Constr.Main
namespace ZZN
open GridHam
/-- The construction for every rectangle. -/
def solveZZN (I : Inst) : Option (List Coord × List Coord) := solveZ Thin.thinSolveW I
end ZZN

-- ZZN.Thin.Decide
namespace ZZN
open Thin
def solvableB (J : Inst) : Bool :=
  if 11 ≤ J.w ∧ 11 ≤ J.h then !(fires3 J.w J.h J.s0 J.t0 J.s1 J.t1) else thinBF J
end ZZN
