import ZZN.WinK.Engine
/-!
Does every final state of the union of the 6×6 window DPs fail the outside test of every
(odd, F) specification in use? `lake env lean --run tools/WinUnionFin.lean CASES`
-/
open ZZN ZZN.Win ZZN.WinK

def parseTm (s : String) : List ((ℕ × ℕ) × ℕ) :=
  (s.splitOn ";").filterMap fun t => match (t.splitOn ",").map String.toNat! with
    | [r, c, col] => some ((r, c), col)
    | _ => none

def parseF (s : String) : FSpec :=
  let t := (((((s.replace "(" "").replace ")" "").replace ": ℤ" "").replace "some " "").replace " " "")
  if t == "none" then none else
  match t.splitOn "," with
  | [c, sg, x] =>
    let sv : Int := if sg.startsWith "-" then -((sg.drop 1).toNat! : Int) else (sg.toNat! : Int)
    some (c.toNat!, sv, if x == "none" then none else some x.toNat!)
  | _ => none

def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "args")
  let lines ← IO.FS.lines file
  let mut U : Std.HashSet ℕ := {}
  let mut specs : List (ℕ × String) := []
  for l in lines do
    match l.splitOn "|" with
    | [name, aa, oddS, tmS, fS] =>
      if aa.toNat! != 6 then continue
      if !(name.endsWith "c0" || name.endsWith "A0") then continue
      let S := inside 6 6 (parseTm tmS)
      U := (S.map enc).foldl (fun h c => h.insert c) U
      for F in fS.splitOn ";;" do
        if !(specs.contains (oddS.toNat!, F)) then specs := specs ++ [(oddS.toNat!, F)]
    | _ => pure ()
  IO.println s!"union final {U.size}, specs {specs.length}"
  for (odd, F) in specs do
    let Fv := parseF F
    let pass := U.toList.filter fun c => outsideOK 6 6 odd Fv (dec c)
    IO.println s!"odd {odd} F {F}: passing {pass.length}"
