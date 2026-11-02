/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.SliceC
-- `lean --run` interprets the imported functions, which needs their compiled code.
--
meta import all ZZN.BoxK.SliceC

/-!
Stabiliser classes and base masks for the slices of a box (ZZN/BoxK/SliceC.lean).

usage: (from proof/) lake env lean --run ../certgen/tools/BaseGen.lean W H REPS OUT
REPS: one row tuple `a,b,c,d` per line. OUT: lines `CLASS k L` (L a Lean list of `Sym`),
`BASE k hex` (`baseM H L` in hex), `SLICE a,b,c,d k`.
-/

public section

open ZZN ZZN.BoxK

def symTerm (σ : Sym) : String :=
  let b (v : Bool) : String := if v then "true" else "false"
  s!"⟨{b σ.tr}, {b σ.rx}, {b σ.ry}, {b σ.r0}, {b σ.r1}, {b σ.sw}⟩"

def listTerm (L : List Sym) : String := "[" ++ ", ".intercalate (L.map symTerm) ++ "]"

def main (args : List String) : IO Unit := do
  let [ws, hs, reps, out] := args | throw (IO.userError "usage: W H REPS OUT")
  let w := ws.toNat!
  let h := hs.toNat!
  let lines := (← IO.FS.lines reps).toList.filter (· ≠ "")
  let mut classes : Array (List Sym) := #[]
  let mut outLines : Array String := #[]
  for l in lines do
    let v := (l.splitOn ",").map String.toNat!
    let x : Fin 4 → ℕ := ![v[0]!, v[1]!, v[2]!, v[3]!]
    let L := stabL w x
    let k ← match classes.findIdx? (· = L) with
      | some k => pure k
      | none => do
        classes := classes.push L
        pure (classes.size - 1)
    outLines := outLines.push s!"SLICE {l} {k}"
  let mut hdr : Array String := #[]
  for k in [0:classes.size] do
    let L := classes[k]!
    hdr := hdr.push s!"CLASS {k} {listTerm L}"
    hdr := hdr.push s!"BASE {k} {(Nat.toDigits 16 (baseM h L)).asString}"
  IO.FS.writeFile out ("\n".intercalate (hdr ++ outLines).toList ++ "\n")
  IO.println s!"classes {classes.size} slices {lines.length}"

end
