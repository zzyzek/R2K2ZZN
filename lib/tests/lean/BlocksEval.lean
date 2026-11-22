/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ZZN.Constr.Round

/-!
# The library's block layer against the Lean definitions

Reads the cases written by `lib/tests/lean_blocks.py` and evaluates the Lean definitions `blkX`,
`Blk.del` and `Blk.lift` (`ZZN/Constr/Round.lean`) on them. It compares the results with what the
library computed. Run from a built `proof/` directory:

    lake env lean --run <path>/BlocksEval.lean cases.txt

A `step` line is one block deletion of the library's `plan`. The fields are tab-separated:

- the instance `U` before the step;
- the flag `tr` (the block was found on `U.transpose`);
- the block;
- the reduced instance `J`;
- a solution `p, q` of `J`;
- the library's lifted paths.

With `P = U` (or `U.transpose` when `tr`) the checks are:
- both sides of `U` are at least 11;
- when `tr`, `blkX U = none`;
- `blkX P` is the block;
- `Blk.del` of the block on `P` is `J`;
- `Blk.lift` of the block on `J p q` is the lifted paths.

A `leaf` line is the last instance `L` of `plan`. The check is that `L` has a side of at most 10, or
that `blkX L = none` and `blkX L.transpose = none`.

Cells are `x,y`, which is `r,c` in the library. Prints one line per failed case and a summary.
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

def instEq (I J : Inst) : Bool :=
  I.w == J.w && I.h == J.h && I.s0 == J.s0 && I.t0 == J.t0 && I.s1 == J.s1 && I.t1 == J.t1

def blkNats : Option Blk → List Nat
  | none => []
  | some (.left k) => [0, k]
  | some (.right k) => [1, k]
  | some (.inner r k) => [2, r, k]

/-- `none` if the case passes, else the first failed check. -/
def checkLine (fs : List String) : Option String :=
  match fs with
  | ["step", u, tr, b, j, p, q, p2, q2] =>
    match instOf u, instOf j with
    | some U, some J =>
      let isTr := tr == "1"
      let P := if isTr then U.transpose else U
      let bn := natsOf b
      if U.w ≤ 10 ∨ U.h ≤ 10 then some "a side of U is at most 10"
      else if isTr && blkNats (blkX U) != [] then some "transposed, but blkX U is not none"
      else if blkNats (blkX P) != bn then some s!"blkX P = {blkNats (blkX P)}, library {bn}"
      else match blkX P with
        | none => some "blkX P = none"
        | some blk =>
          if !instEq (blk.del P) J then some "Blk.del differs"
          else
            let (lp, lq) := blk.lift J (cellsOf p) (cellsOf q)
            if lp != cellsOf p2 then some "Blk.lift differs on the first path"
            else if lq != cellsOf q2 then some "Blk.lift differs on the second path"
            else none
    | _, _ => some "bad instance field"
  | ["leaf", l] =>
    match instOf l with
    | some L =>
      if L.w ≤ 10 ∨ L.h ≤ 10 then none
      else if blkNats (blkX L) != [] then some "leaf: blkX L is not none"
      else if blkNats (blkX L.transpose) != [] then some "leaf: blkX L.transpose is not none"
      else none
    | none => some "bad instance field"
  | _ => some "bad line"

def main (args : List String) : IO UInt32 := do
  let some file := args.head? | IO.println "usage: BlocksEval.lean cases.txt"; return 2
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
