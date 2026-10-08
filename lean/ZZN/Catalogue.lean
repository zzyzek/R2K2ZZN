-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Defs

/-!
# The forbidden-pattern catalogue

A transcription of the catalogue implementation used for the computations in `PROOF.md` (a
JavaScript program from the project's development, not included). Coordinates: a JS cell `[r, c]` on an `R × C` grid is the cell
`(r, c)` of a `w × h` grid with `w = R`, `h = C`.

`firstPattern` returns the id of the first entry that fires (in the JS order), or `none`;
`Passes I` means no entry fires. The transcription was checked against that implementation on the
same test sets as the C implementation (the `catcheck` executable).
-/

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

/-! ### Global checks -/

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

/-! ### Local corner patterns L2–L5 -/

def isSome' (o : Option ℕ) : Bool := o.isSome

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

/-! ### Whole-configuration corner patterns (C, D) -/

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

/-! ### Edge closure (E1) -/

def edgeClosure (v : View) : Bool :=
  (List.range v.W).any fun k =>
    decide (k + 3 < v.W) &&
    match v.at 0 k with
    | some a => v.at 1 (k + 1) == some a && v.at 0 (k + 3) == some (1 - a) &&
        v.at 1 (k + 2) == some (1 - a)
    | none => false

/-! ### Boundary-only corner patterns (B) -/

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

/-! ### Forced rewrites and effective alternation (R) -/

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

/-- Directions: 0 up, 1 right, 2 down, 3 left. -/
def dR : Fin 4 → ℤ := ![-1, 0, 1, 0]
def dC : Fin 4 → ℤ := ![0, 1, 0, -1]

/-- The outer face walk of the grid minus `removed`, as in `outerFaceOrder`: walk every face
(each dart once), keep the longest walk; return, for each cell, its positions along it. -/
def outerFaceWalk (R C : ℕ) (removed : List (ℕ × ℕ)) : List (ℕ × ℕ) := Id.run do
  let N := R * C
  let rem : Array Bool := (Array.replicate N false).modify 0 id |> fun a =>
    removed.foldl (fun a q => if q.1 < R ∧ q.2 < C then a.set! (q.1 * C + q.2) true else a) a
  let ok : ℤ → ℤ → Bool := fun r c =>
    decide (0 ≤ r) && decide (r < R) && decide (0 ≤ c) && decide (c < C) &&
      !(rem.getD (r.toNat * C + c.toNat) false)
  let mut used : Array Bool := Array.replicate (4 * N) false
  let mut best : List (ℕ × ℕ) := []
  for a0 in List.range N do
    for d0n in List.range 4 do
      let d0 : Fin 4 := ⟨d0n % 4, Nat.mod_lt _ (by decide)⟩
      let r0 : ℤ := (a0 / C : ℕ)
      let c0 : ℤ := (a0 % C : ℕ)
      if rem.getD a0 false || used.getD (a0 * 4 + d0n) false || !ok (r0 + dR d0) (c0 + dC d0) then
        continue
      let mut r := r0
      let mut c := c0
      let mut d := d0
      let mut walk : Array (ℕ × ℕ) := #[]
      let mut go := true
      for _ in List.range (8 * N + 1) do
        if go then
          used := used.set! ((r.toNat * C + c.toNat) * 4 + d.val) true
          walk := walk.push (r.toNat, c.toNat)
          let vr := r + dR d
          let vc := c + dC d
          let rev : ℕ := (d.val + 2) % 4
          let mut nd : Fin 4 := d
          let mut found := false
          for k in [1, 2, 3, 4] do
            if !found then
              let dd : Fin 4 := ⟨(rev + k) % 4, Nat.mod_lt _ (by decide)⟩
              if ok (vr + dR dd) (vc + dC dd) then
                nd := dd
                found := true
          r := vr
          c := vc
          d := nd
          if (r == r0 && c == c0 && d == d0) || walk.size ≥ 8 * N then
            go := false
      if walk.size > best.length then
        best := walk.toList
  return best

def positions (walk : List (ℕ × ℕ)) (x : ℕ × ℕ) : List ℕ :=
  (walk.zipIdx.filter (fun q => q.1 == x)).map (·.2)

def effectiveAlternation (R C : ℕ) (pts : List Pt) : Bool := Id.run do
  let mut eff : List Pt := pts
  let mut removed : List (ℕ × ℕ) := []
  let mut any := false
  for f in frames do
    let v := makeView R C f eff
    match rewritesAt v with
    | none => pure ()
    | some rw =>
      let cells := rw.removed.map (f.back R C)
      if cells.any (fun x => removed.contains x) then continue
      let moves := rw.moves.map fun (a, b) => (f.back R C a, f.back R C b)
      if moves.any (fun m => removed.contains m.2) then continue
      removed := removed ++ cells
      for (a, b) in moves do
        -- the first endpoint at `a` moves to `b`
        match eff.findIdx? (fun q => q.1 == a) with
        | some i => eff := eff.modify i (fun q => (b, q.2))
        | none => pure ()
      any := true
  if !any then return false
  if eff.any (fun q => removed.contains q.1) then return false
  if (eff.map (·.1)).dedup.length != 4 then return false
  let walk := outerFaceWalk R C removed
  let places := eff.map fun q => (positions walk q.1, q.2)
  if places.any (fun pl => pl.1.length != 1) then return false
  let order := (sortByKey (places.map fun pl => (pl.1.headD 0, pl.2))).map (·.2)
  return alternating order

/-! ### A functional form of the R test

The same computation as `effectiveAlternation`, written without mutation:
* the rewrite phase is a fold over the frames (`rewriteAll`);
* the outer face is the orbit of a single dart under the face-tracing step (`outerWalk`): the
  rightward step from the first cell of row 0. The JS walks every face and keeps the longest; on
  the grids in question that is this orbit, started at the same dart (the first one the JS
  scans). Agreement is checked on the test sets.
-/

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

/-- A cell of the region: in the grid and not removed. -/
def okCell (R C : ℕ) (removed : List (ℕ × ℕ)) (r c : ℤ) : Bool :=
  decide (0 ≤ r) && decide (r < R) && decide (0 ≤ c) && decide (c < C) &&
    !removed.contains (r.toNat, c.toNat)

/-- A dart: a cell and a direction. -/
abbrev Dart := ℤ × ℤ × Fin 4

def fin4 (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

/-- The face-tracing step: move along the dart, then turn to the first direction, clockwise
from straight back, that leads into the region. -/
def stepDart (ok : ℤ → ℤ → Bool) (x : Dart) : Dart :=
  let vr := x.1 + dR x.2.2
  let vc := x.2.1 + dC x.2.2
  let rev := (x.2.2.val + 2) % 4
  match [1, 2, 3, 4].find? (fun k => ok (vr + dR (fin4 (rev + k))) (vc + dC (fin4 (rev + k)))) with
  | some k => (vr, vc, fin4 (rev + k))
  | none => (vr, vc, x.2.2)

/-- The cells (tails) of the orbit of `start`, up to `n` steps. -/
def orbitTails (ok : ℤ → ℤ → Bool) (start : Dart) : ℕ → Dart → List (ℕ × ℕ)
  | 0, _ => []
  | n + 1, x =>
    (x.1.toNat, x.2.1.toNat) ::
      (let y := stepDart ok x
       if y == start then [] else orbitTails ok start n y)

def outerWalk (R C : ℕ) (removed : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let c0 := ((List.range C).find? (fun c => !removed.contains (0, c))).getD 0
  let start : Dart := (0, c0, fin4 1)
  orbitTails (okCell R C removed) start (8 * R * C) start

def effAlt (R C : ℕ) (pts : List Pt) : Bool :=
  let st := rewriteAll R C pts
  if !st.any then false
  else if st.eff.any (fun q => st.removed.contains q.1) then false
  else if (st.eff.map (·.1)).dedup.length != 4 then false
  else
    let walk := outerWalk R C st.removed
    let places := st.eff.map fun q => (positions walk q.1, q.2)
    if places.any (fun pl => pl.1.length != 1) then false
    else alternating ((sortByKey (places.map fun pl => (pl.1.headD 0, pl.2))).map (·.2))

/-! ### The test -/

/-- The first catalogue entry that fires, in the JS order. -/
def firstPattern (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) : Option String := Id.run do
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  let cells := [s0, t0, s1, t1]
  if !parityOk R C pts then return some "P parity"
  let idx := cells.map (perimIndex R C)
  if idx.all Option.isSome then
    let order := (sortByKey ((idx.map (·.getD 0)).zip [0, 0, 1, 1])).map (·.2)
    if alternating order then return some "T1 perimeter alternation"
  let rs := cells.map (·.1)
  let cs := cells.map (·.2)
  let mx := fun (l : List ℕ) => l.foldl max 0
  let mn := fun (l : List ℕ) => l.foldl min (l.headD 0)
  if mx rs - mn rs == 1 && mx cs - mn cs == 1 && mn rs + 1 == mx rs && mn cs + 1 == mx cs &&
      rs[0]! != rs[1]! && cs[0]! != cs[1]! then
    return some "T2 unit-square alternation"
  for (p, col) in pts do
    let pr : ℤ := p.1
    let pc : ℤ := p.2
    let nb : List (ℤ × ℤ) := ([(pr - 1, pc), (pr + 1, pc), (pr, pc - 1), (pr, pc + 1)] : List (ℤ × ℤ)).filter
      fun q => decide (0 ≤ q.1) && decide (q.1 < (R : ℤ)) && decide (0 ≤ q.2) && decide (q.2 < (C : ℤ))
    if nb.all (fun q => pts.any fun pc => pc.1 == (q.1.toNat, q.2.toNat) && pc.2 != col) then
      return some "L1 isolated endpoint"
  -- L6
  let corners : List (ℤ × ℤ × ℤ × ℤ) :=
    [(0, 0, 1, 1), (0, (C : ℤ) - 1, 1, -1), ((R : ℤ) - 1, 0, -1, 1), ((R : ℤ) - 1, (C : ℤ) - 1, -1, -1)]
  let mut closures : List ℕ := []
  for (cr, cc, dr, dc) in corners do
    let n1 : ℕ × ℕ := (cr.toNat, (cc + dc).toNat)
    let n2 : ℕ × ℕ := ((cr + dr).toNat, cc.toNat)
    let e1 := pts.find? (·.1 == n1)
    let e2 := pts.find? (·.1 == n2)
    let cornerEmpty := !(pts.any (·.1 == (cr.toNat, cc.toNat)))
    match e1, e2 with
    | some a, some b => if a.2 == b.2 && cornerEmpty then closures := closures ++ [a.2]
    | _, _ => pure ()
  if closures.contains 0 && closures.contains 1 && decide (R * C > 6) then
    return some "L6 double corner closure"
  for f in frames do
    let v := makeView R C f pts
    if testL2 v then return some "L2 corner block"
    if testL3 v then return some "L3 corner wedge"
    if testL4 v then return some "L4 corner fork"
    if testL5 v then return some "L5 corner trap"
    if edgeClosure v then return some "E1 edge closure"
    if boundaryOnly R C f pts then return some "B boundary-only corner pattern"
    if decide (R ≥ 10) && decide (C ≥ 10) && corner4 R C f pts then
      return some "C4 corner configuration"
  if effectiveAlternation R C pts then return some "R effective alternation"
  return none

/-! ### A functional form: does some entry fire? -/

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

/-- Some catalogue entry fires. -/
def fires (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) : Bool :=
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  !parityOk R C pts || t1Fires R C pts || t2Fires [s0, t0, s1, t1] || l1Fires R C pts ||
    l6Fires R C pts || frames.any (frameFires R C pts) || effectiveAlternation R C pts

/-! ### The outer walk, explicitly

After the rewrites, the removed cells form a staircase (Young diagram) at each corner. The outer
walk follows: the top-left staircase, the top row, the top-right staircase, the right column, the
bottom-right staircase, the bottom row, the bottom-left staircase, the left column. The staircase of
a corner, in that corner's frame, with row lengths `λ 0 ≥ λ 1 ≥ …` (of removed cells): from
`(k, 0)` (the first row with no removed cell), right along row `i+1` and up to `(i, λ i)`, for
`i = k-1, …, 0`.
-/

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

/-- `fires` with the functional R test. -/
def fires2 (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) : Bool :=
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  !parityOk R C pts || t1Fires R C pts || t2Fires [s0, t0, s1, t1] || l1Fires R C pts ||
    l6Fires R C pts || frames.any (frameFires R C pts) || effAlt R C pts

/-- The instance passes the catalogue: no entry fires. Defined from the fully functional form
`fires3` (the R test via the explicit outer walk `walk3`). Checked against the JavaScript catalogue: the
verdict and, separately, the R test agree on 3.66 M instances, 18 k of them with the R test true
-/
def Passes (I : Inst) : Prop := fires3 I.w I.h I.s0 I.t0 I.s1 I.t1 = false

instance (I : Inst) : Decidable (Passes I) := by unfold Passes; infer_instance

end ZZN
