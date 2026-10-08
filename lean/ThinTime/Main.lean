-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Thin.Fast
import ZZN.Solve

/-! Timing and cross-check of `thinBF` against the checked solver: `thintime w h n seed`. -/

open ZZN ZZN.Thin

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

instance (I : Inst) : Decidable I.WellFormed := by
  unfold Inst.WellFormed GridHam.InBounds; infer_instance

def main (args : List String) : IO Unit := do
  let ns := args.filterMap String.toNat?
  let (w, h, n, seed) := match ns with
    | [w, h, n, sd] => (w, h, n, sd)
    | _ => (20, 6, 50, 1)
  let mut s : UInt64 := seed.toUInt64
  let mut yes := 0
  let mut agree := 0
  let mut tried := 0
  let mut tB := 0
  let mut tS := 0
  for _ in [0:n] do
    let mut pts : Array (ℕ × ℕ) := #[]
    for _ in [0:4] do
      s := lcg s; let x := ((s >>> 33) % w.toUInt64).toNat
      s := lcg s; let y := ((s >>> 33) % h.toUInt64).toNat
      pts := pts.push (x, y)
    let I : Inst := ⟨w, h, pts[0]!, pts[1]!, pts[2]!, pts[3]!⟩
    if !decide I.WellFormed then continue
    tried := tried + 1
    let t0 ← IO.monoNanosNow
    let r := thinBF I
    let t1 ← IO.monoNanosNow
    let r2 := solveCheck I
    let t2 ← IO.monoNanosNow
    tB := tB + (t1 - t0); tS := tS + (t2 - t1)
    if r then yes := yes + 1
    if r == r2 then agree := agree + 1 else IO.println s!"DISAGREE {w} {h} {pts} thinB={r} solver={r2}"
  IO.println s!"{w}x{h}: instances {tried} solvable {yes} agree-with-solver {agree} thinB-ms {tB / 1000000} solver-ms {tS / 1000000}"
