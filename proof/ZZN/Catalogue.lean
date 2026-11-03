/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Statement
public import ZZN.Defs

@[expose] public section

/-!
# The forbidden-pattern catalogue

A transcription of the catalogue implementation used for the computations in `PROOF.md` (a
JavaScript program from the project's development, not included). Coordinates: a JS cell `[r, c]` on an `R × C` grid is the cell
`(r, c)` of a `w × h` grid with `w = R`, `h = C`.

`firstPattern` returns the id of the first entry that fires (in the JS order), or `none`;
`Passes I` (`ZZN/Statement.lean`) is `fires3 … = false`, the form with the explicit outer walk.
-/

namespace ZZN











/-! ### Global checks -/






/-! ### Local corner patterns L2–L5 -/

def isSome' (o : Option ℕ) : Bool := o.isSome





/-! ### Whole-configuration corner patterns (C, D) -/





/-! ### Edge closure (E1) -/


/-! ### Boundary-only corner patterns (B) -/




/-! ### Forced rewrites and effective alternation (R) -/



/-- Directions: 0 up, 1 right, 2 down, 3 left. -/
def dR : Fin 4 → ℤ := ![-1, 0, 1, 0]
def dC : Fin 4 → ℤ := ![0, 1, 0, -1]

/-- The outer face walk of the grid minus `removed`, as in `outerFaceOrder`: walk every face
(each dart once) and return the longest walk, as its list of cells. -/
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







/-- Some catalogue entry fires. -/
def fires (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) : Bool :=
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  !parityOk R C pts || t1Fires R C pts || t2Fires [s0, t0, s1, t1] || l1Fires R C pts ||
    l6Fires R C pts || frames.any (frameFires R C pts) || effectiveAlternation R C pts

/-! The explicit outer walk (`staircase`, `walk3`, `effAlt3`) is in `ZZN/Statement.lean`. -/








/-- `fires` with the functional R test. -/
def fires2 (R C : ℕ) (s0 t0 s1 t1 : ℕ × ℕ) : Bool :=
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  !parityOk R C pts || t1Fires R C pts || t2Fires [s0, t0, s1, t1] || l1Fires R C pts ||
    l6Fires R C pts || frames.any (frameFires R C pts) || effAlt R C pts


instance (I : Inst) : Decidable (Passes I) := by unfold Passes; infer_instance

end ZZN
