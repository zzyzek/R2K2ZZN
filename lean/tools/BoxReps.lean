import ZZN.BoxK.Box
/-! Print the representative row tuples of side `w` (irreducible, least key over `G16`), one per
line as `a,b,c,d`, and check `rowsOK` natively. `lake env lean --run tools/BoxReps.lean w` -/
open ZZN ZZN.BoxK

def main (args : List String) : IO Unit := do
  let w := args.head!.toNat!
  let mut reps : Array (Fin 4 → ℕ) := #[]
  for a in List.range w do
    for b in List.range w do
      for c in List.range w do
        for d in List.range w do
          let x : Fin 4 → ℕ := ![a, b, c, d]
          if axB w [a, b, c, d] && G16.all (fun σ => decide (keyR x ≤ keyR (xS σ w x))) then
            reps := reps.push x
  for x in reps do
    IO.println s!"{x 0},{x 1},{x 2},{x 3}"
  IO.eprintln s!"w {w}: reps {reps.size}, rowsOK {rowsOK w reps.toList}"
