import ZZN.WinK.Engine
/-!
Overlap of the window DP state sets across certificates: for each stage, the sum of the set
sizes and the size of their union. `lake env lean --run tools/WinUnion.lean CASES A`
(cases with window size A only).
-/
open ZZN ZZN.Win ZZN.WinK

def parseTm (s : String) : List ((ℕ × ℕ) × ℕ) :=
  (s.splitOn ";").filterMap fun t => match (t.splitOn ",").map String.toNat! with
    | [r, c, col] => some ((r, c), col)
    | _ => none

def main (args : List String) : IO Unit := do
  let [file, aS] := args | throw (IO.userError "args")
  let a := aS.toNat!
  let lines ← IO.FS.lines file
  let n := a * a
  let mut sums : Array ℕ := Array.replicate (n + 1) 0
  let mut unions : Array (Std.HashSet ℕ) := Array.replicate (n + 1) {}
  let mut cnt := 0
  for l in lines do
    match l.splitOn "|" with
    | [name, aa, _, tmS, _] =>
      if aa.toNat! != a then continue
      if !(name.endsWith "c0" || name.endsWith "A0") then continue
      cnt := cnt + 1
      let tm := parseTm tmS
      let mut S : List St := [([], 0)]
      for i in List.range (n + 1) do
        let codes := S.map enc
        sums := sums.set! i (sums[i]! + codes.length)
        unions := unions.set! i (codes.foldl (fun h c => h.insert c) unions[i]!)
        if i < n then S := stage a a tm S i
      IO.eprintln s!"{name} done"
    | _ => pure ()
  IO.println s!"cases {cnt}"
  for i in List.range (n + 1) do
    IO.println s!"stage {i}: sum {sums[i]!} union {unions[i]!.size}"
