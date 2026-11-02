import ZZN.BoxK.FireW

/-!
Witness entries for the firing lanes of a certificate (ZZN/BoxK/FireW.lean).

usage: lake env lean --run tools/FireGen.lean W H CERT OUT
Copies CERT to OUT, replacing each `FIRE lane` (under a `SLICE x` or `CSLICE x ...` line) by
`FIRE lane code`: per reflection, the first entry that fires in the order T1, T2, L1, L6, frames,
outer walk, parity.
-/

open ZZN ZZN.BoxK

def order : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0]

def witness (J : Inst) : Option ℕ := order.find? (fireI J ·)

def main (args : List String) : IO Unit := do
  let [ws, hs, cert, out] := args | throw (IO.userError "usage: W H CERT OUT")
  let w := ws.toNat!
  let h := hs.toNat!
  let mut x : Fin 4 → ℕ := ![0, 0, 0, 0]
  let mut res : Array String := #[]
  let mut nf := 0
  for l in (← IO.FS.lines cert) do
    let t := l.splitOn " "
    if t.head? = some "SLICE" || t.head? = some "CSLICE" then
      let v := (t[1]!.splitOn ",").map String.toNat!
      x := ![v[0]!, v[1]!, v[2]!, v[3]!]
      res := res.push l
    else if t.head? = some "FIRE" then
      let j := t[1]!.toNat!
      let J := laneI w h x j
      let rs := [J, J.reflectX, J.reflectY, J.reflectX.reflectY]
      let ks := rs.map witness
      if ks.any Option.isNone then
        throw (IO.userError s!"no firing entry: lane {j}")
      let c := ks.foldr (fun k acc => k.getD 0 + 16 * acc) 0
      res := res.push s!"FIRE {j} {c}"
      nf := nf + 1
    else
      res := res.push l
  IO.FS.writeFile out ("\n".intercalate res.toList ++ "\n")
  IO.println s!"fires {nf}"
