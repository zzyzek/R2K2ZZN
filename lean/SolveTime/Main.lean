-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import MoveCheck.Solve
import MoveCheck.Search

/-! Timing for `solveCheck`: instances on stdin ("w h s0x s0y t0x t0y s1x s1y t1x t1y", lines may
start with `THIN`).
* `soltime`: solve each instance directly;
* `soltime moves`: take the move candidates (`search I 64`), narrowest thin pieces first, and solve
  thin pieces until one candidate has all of them solved. -/

open ZZN

partial def readAll (h : IO.FS.Stream) (acc : Array Inst) : IO (Array Inst) := do
  let line ← h.getLine
  if line.isEmpty then return acc
  let ns := ((line.replace "\n" "").splitOn " ").filterMap String.toNat?
  match ns with
  | [w, hh, a, b, c, d, e, f, g, k] => readAll h (acc.push ⟨w, hh, (a, b), (c, d), (e, f), (g, k)⟩)
  | _ => readAll h acc

def width (l : List Inst) : ℕ := l.foldl (fun m J => max m (min J.w J.h)) 0

def main (args : List String) : IO Unit := do
  let insts ← readAll (← IO.getStdin) #[]
  let t0 ← IO.monoMsNow
  let mut ok := 0
  let mut bad := 0
  let mut solves := 0
  let mut hist : Array ℕ := Array.replicate 12 0
  for I in insts do
    if args == ["moves"] then
      let cs := (search I 64).toArray.qsort (fun a b => width a.2 < width b.2)
      let mut done := false
      for (_, pend) in cs do
        if done then break
        let mut all := true
        for J in pend do
          solves := solves + 1
          if !solveCheck J then all := false; break
        if all then
          done := true
          let wd := width pend
          hist := hist.set! wd (hist[wd]! + 1)
      if done then ok := ok + 1 else bad := bad + 1; IO.println s!"FAIL {showI I}"
    else
      if solveCheck I then ok := ok + 1
      else
        bad := bad + 1
        IO.println s!"FAIL {showI I}"
  let t1 ← IO.monoMsNow
  IO.println s!"instances {insts.size} ok {ok} failed {bad} piece-solves {solves} width-hist {hist} ms {t1 - t0}"
