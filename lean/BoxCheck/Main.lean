-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Finite2

/-! Run `checkBoxA w h a` (all `a < w` if `a` is omitted), with counts and time:
`boxcheck w h [a]`. -/

open ZZN

partial def readInsts (h : IO.FS.Stream) (acc : Array Inst) : IO (Array Inst) := do
  let line ← h.getLine
  if line.isEmpty then return acc
  let ns := ((line.replace "\n" "").splitOn " ").filterMap String.toNat?
  match ns with
  | [w, hh, a, b, c, d, e, f, g, k] => readInsts h (acc.push ⟨w, hh, (a, b), (c, d), (e, f), (g, k)⟩)
  | _ => readInsts h acc

def main (args : List String) : IO Unit := do
  if args == ["stdin"] then
    let insts ← readInsts (← IO.getStdin) #[]
    let t0 ← IO.monoMsNow
    let mut ok := 0
    let mut mx := 0
    for I in insts do
      let s ← IO.monoMsNow
      if moveB I then ok := ok + 1
      let e ← IO.monoMsNow
      mx := max mx (e - s)
    let t1 ← IO.monoMsNow
    IO.println s!"instances {insts.size} moveB {ok} ms {t1 - t0} max-ms {mx}"
    return
  if args.head? == some "prof" then
    let ns := args.tail.filterMap String.toNat?
    let (w, h, stride) := match ns with
      | [w, h, k] => (w, h, k)
      | _ => (11, 11, 1601)
    let Th := tuples h
    let mut k := 0
    let mut firstM : Array Nat := Array.replicate 12 0
    let mut timeM : Array Nat := Array.replicate 12 0
    let mut nsym : Array Nat := Array.replicate 65 0
    for a in List.range w do
      for xs in tuplesA w a do
        for ys in Th do
          if k % stride == 0 then
            let J := mkInst w h xs ys
            if quickB J && isMinB J && decide J.WellFormed && passImgB J then
              let mut found := 11
              for m in List.range 11 do
                if found == 11 then
                  let s ← IO.monoNanosNow
                  let r := typeSyms.any fun tσ => canonT tσ.1 m (tσ.2.apply J)
                  let e ← IO.monoNanosNow
                  timeM := timeM.set! m (timeM[m]! + (e - s))
                  if r then found := m
              firstM := firstM.set! found (firstM[found]! + 1)
          k := k + 1
    IO.println s!"prof {w}x{h}: first m with a move {firstM}; ms spent per m {timeM.map (· / 1000000)}"
    return
  if args.head? == some "sample" || args.head? == some "sampleold" then
    let old := args.head? == some "sampleold"
    let ns := args.tail.filterMap String.toNat?
    let (w, h, stride) := match ns with
      | [w, h, k] => (w, h, k)
      | _ => (11, 11, 1000)
    let Th := tuples h
    let mut k := 0
    let mut work : Nat := 0
    let mut canon := 0
    let mut passing := 0
    let mut mxw : Nat := 0
    let t0 ← IO.monoMsNow
    for a in List.range w do
      for xs in tuplesA w a do
        for ys in Th do
          if k % stride == 0 then
            let J := mkInst w h xs ys
            let s ← IO.monoNanosNow
            let r := if old then checkInst J else checkInst2 J
            let e ← IO.monoNanosNow
            if r == false then IO.println s!"FAIL {xs} {ys}"
            work := work + (e - s)
            mxw := max mxw (e - s)
            if quickB J && isMinB J then
              canon := canon + 1
              if passImgB J then passing := passing + 1
          k := k + 1
    let t1 ← IO.monoMsNow
    IO.println s!"{if old then "old" else "new"} {w}x{h} stride {stride} pairs {k} sampled {k / stride} canonical {canon} passing {passing} work-ms {work / 1000000} max-ms {mxw / 1000000} est-total-s {(work * stride) / 1000000000} wall-s {(t1 - t0) / 1000}"
    return
  let ns := args.filterMap String.toNat?
  let (w, h, as) := match ns with
    | [w, h] => (w, h, List.range w)
    | [w, h, a] => (w, h, [a])
    | _ => (22, 22, List.range 22)
  let Th := tuples h
  for a in as do
    let t0 ← IO.monoMsNow
    let mut n := 0
    let mut canon := 0
    let mut passing := 0
    let mut bad := 0
    for xs in tuplesA w a do
      for ys in Th do
        n := n + 1
        let J := mkInst w h xs ys
        if quickB J && isMinB J && decide J.WellFormed then
          canon := canon + 1
          if passImgB J then
            passing := passing + 1
            if !(moveB J || solveCheck J) then
              bad := bad + 1
              IO.println s!"FAIL {w} {h} {xs} {ys}"
    let t1 ← IO.monoMsNow
    IO.println s!"box {w}x{h} a={a} pairs {n} canonical {canon} passing-image {passing} failed {bad} ms {t1 - t0}"
