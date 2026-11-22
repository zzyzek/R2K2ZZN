/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ZZN.Constr.Solve2

/-!
# The library's two-line reductions against the Lean definitions

Reads the cases written by `lib/tests/lean_reduce2.py` and evaluates `findRed2`, `Inst.deleteAt`
and `liftE` (`ZZN/Constr/Solve2.lean`, `ZZN/Statement.lean`) on them. Run from a built `proof/`:

    lake env lean --run <path>/ReduceEval.lean cases.txt

A `step` line (tab-separated): the instance `U` before the step, the flag `tr` (the reduction was
found on `U.transpose`), the line `d`, a solution `p, q` of `P.deleteAt d` where `P = U` (or
`U.transpose`), and the library's lifted paths. Checks: both sides of `U` are at least 11; when
`tr`, `findRed2 U = none`; `findRed2 P = some d`; `liftE P d p q` is the lifted paths.

A `leaf` line: the last instance `L`. Check: a side of `L` is at most 10, or `findRed2 L = none` and
`findRed2 L.transpose = none`. Cells are `x,y` (`r,c` in the library).
-/

open ZZN GridHam

def natsOf (s : String) : List Nat :=
  (s.splitOn " ").filterMap fun t => if t.isEmpty then none else t.toNat?

def cellsOf (s : String) : List Coord :=
  (s.splitOn " ").filterMap fun t =>
    match t.splitOn "," with
    | [a, b] => some (a.toNat!, b.toNat!)
    | _ => none

def instOf (s : String) : Option Inst :=
  match natsOf s with
  | [w, h, a, b, c, d, e, f, g, i] => some ⟨w, h, (a, b), (c, d), (e, f), (g, i)⟩
  | _ => none

def checkLine (fs : List String) : Option String :=
  match fs with
  | ["step", u, tr, d, p, q, p2, q2] =>
    match instOf u with
    | some U =>
      let isTr := tr == "1"
      let P := if isTr then U.transpose else U
      let dn := d.toNat!
      if U.w ≤ 10 ∨ U.h ≤ 10 then some "a side of U is at most 10"
      else if isTr && (findRed2 U).isSome then some "transposed, but findRed2 U is not none"
      else if findRed2 P != some dn then some s!"findRed2 P = {findRed2 P}, library {dn}"
      else
        let (lp, lq) := liftE P dn (cellsOf p) (cellsOf q)
        if lp != cellsOf p2 then some "liftE differs on the first path"
        else if lq != cellsOf q2 then some "liftE differs on the second path"
        else none
    | none => some "bad instance field"
  | ["leaf", l] =>
    match instOf l with
    | some L =>
      if L.w ≤ 10 ∨ L.h ≤ 10 then none
      else if (findRed2 L).isSome then some "leaf: findRed2 L is not none"
      else if (findRed2 L.transpose).isSome then some "leaf: findRed2 L.transpose is not none"
      else none
    | none => some "bad instance field"
  | _ => some "bad line"

def main (args : List String) : IO UInt32 := do
  let some file := args.head? | IO.println "usage: ReduceEval.lean cases.txt"; return 2
  let lines := (← IO.FS.readFile file).splitOn "\n" |>.filter (· ≠ "")
  let mut steps := 0
  let mut leaves := 0
  let mut bad := 0
  for (line, i) in lines.zip (List.range lines.length) do
    let fs := line.splitOn "\t"
    if fs.head? == some "step" then steps := steps + 1 else leaves := leaves + 1
    match checkLine fs with
    | none => pure ()
    | some why =>
      bad := bad + 1
      IO.println s!"FAIL line {i + 1}: {why}"
  IO.println s!"step cases {steps}, leaf cases {leaves}, failed {bad}"
  return (if bad == 0 then 0 else 1)
