-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import MoveCheck.Search

/-! Is `fires3` invariant under the 32 symmetries `Sym` (and squares' transposes)? Random
instances, sides 11–22, endpoints clustered near corners half the time. -/

open ZZN

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def main (args : List String) : IO Unit := do
  let n := (args.headD "100000").toNat!
  let mut s : UInt64 := 12345
  let mut diff := 0
  let mut tested := 0
  let mut passes := 0
  let mut byKind : Array ℕ := Array.replicate 64 0
  for _ in [0:n] do
    s := lcg s; let w := 11 + ((s >>> 33) % 12).toNat
    s := lcg s; let h := 11 + ((s >>> 33) % 12).toNat
    let mut pts : Array (ℕ × ℕ) := #[]
    for _ in [0:4] do
      s := lcg s; let near := (s >>> 40) % 2 == 0
      s := lcg s; let x := ((s >>> 33) % (if near then 6 else w.toUInt64)).toNat
      s := lcg s; let y := ((s >>> 33) % (if near then 6 else h.toUInt64)).toNat
      s := lcg s; let fx := (s >>> 40) % 2 == 0
      s := lcg s; let fy := (s >>> 40) % 2 == 0
      pts := pts.push ((if near && fx then w - 1 - x else x), (if near && fy then h - 1 - y else y))
    let I : Inst := ⟨w, h, pts[0]!, pts[1]!, pts[2]!, pts[3]!⟩
    if !decide I.WellFormed then continue
    tested := tested + 1
    let base := fires3 I.w I.h I.s0 I.t0 I.s1 I.t1
    if !base then passes := passes + 1
    let mut k := 0
    for σ in allSyms do
      let J := σ.apply I
      if fires3 J.w J.h J.s0 J.t0 J.s1 J.t1 != base then
        diff := diff + 1
        byKind := byKind.set! k (byKind[k]! + 1)
        if diff ≤ 5 then IO.println s!"DIFF sym={σ.tr},{σ.rx},{σ.ry},{σ.r0},{σ.r1},{σ.sw} {showI I}"
      k := k + 1
  IO.println s!"tested {tested} passing {passes} disagreements {diff} by-sym {byKind}"
