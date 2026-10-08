-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import MoveCheck.Search

/-!
Timing for `Facts.finite` without symmetry reduction: enumerate every instance of a `w × h` box
whose two axes survive the gap filter (`PROOF.md` §5.2, without the B2 rule), keep the
well-formed passing ones, and search for a move with no thin pieces (`MoveCheck.search`).

Usage: `movetime w h [stride] [offset]`; checks every `stride`-th (x-tuple, y-tuple) pair.
-/

open ZZN GridHam

/-- The per-axis gap filter: no strip, compression or interior compression on this axis. -/
def axisOK (n : ℕ) (x : List ℕ) : Bool :=
  let v := x.mergeSort (· ≤ ·)
  match v with
  | [a, b, c, d] =>
    let g := [a, b - a - 1, c - b - 1, d - c - 1, n - 1 - d]
    let lo := [0, a + 1, b + 1, c + 1]
    let hi := [0, b - 1, c - 1, d - 1]
    if n < 13 then true
    else if (g[0]! ≥ 4) || (g[4]! ≥ 4) then false
    else if (g[1]! ≥ 10) || (g[2]! ≥ 10) || (g[3]! ≥ 10) then false
    else (List.range' 1 3).all fun i =>
      !((g[i]! ≥ 3) && (max lo[i]! 8 + 1 ≤ hi[i]!) && (max lo[i]! 8 + 10 ≤ n))
  | _ => false

def tuples (n : ℕ) : Array (List ℕ) := Id.run do
  let mut out := #[]
  for a in List.range n do
    for b in List.range n do
      for c in List.range n do
        for d in List.range n do
          if axisOK n [a, b, c, d] then out := out.push [a, b, c, d]
  return out

def main (args : List String) : IO Unit := do
  let ns := args.filterMap String.toNat?
  let (w, h, stride, off) := match ns with
    | [w, h] => (w, h, 1, 0)
    | [w, h, s] => (w, h, s, 0)
    | [w, h, s, o] => (w, h, s, o)
    | _ => (22, 22, 1, 0)
  let t0 ← IO.monoMsNow
  let xs := tuples w
  let ys := tuples h
  let mut k := 0
  let mut tried := 0
  let mut wf := 0
  let mut pass := 0
  let mut good := 0
  let mut thin := 0
  let mut none := 0
  for x in xs do
    for y in ys do
      if k % stride == off then
        tried := tried + 1
        let I : Inst := ⟨w, h, (x[0]!, y[0]!), (x[1]!, y[1]!), (x[2]!, y[2]!), (x[3]!, y[3]!)⟩
        if decide I.WellFormed then
          wf := wf + 1
          if !(fires3 I.w I.h I.s0 I.t0 I.s1 I.t1) then
            pass := pass + 1
            match search I 0 with
            | [(_, [])] => good := good + 1
            | [] => none := none + 1
            | _ => thin := thin + 1; IO.println s!"THIN {showI I}"
      k := k + 1
  let t1 ← IO.monoMsNow
  IO.println s!"box {w}x{h} xtuples {xs.size} ytuples {ys.size} tried {tried} wellformed {wf} passing {pass} move {good} thinonly {thin} none {none} ms {t1 - t0}"
