import ZZN.WinBCD
/-! Print every window-certificate case of `CertFacts` as `name|a|odd|tm|F1;;F2;;...`. -/
open ZZN ZZN.Win

def tmStr (tm : List ((ℕ × ℕ) × ℕ)) : String :=
  String.intercalate ";" (tm.map fun ((r, c), col) => s!"{r},{c},{col}")

def fStr (col : ℕ) (sg : ℤ) (fsl : Option ℕ) : String :=
  let sl := match fsl with | none => "none" | some k => s!"some {k}"
  s!"some ({col}, ({sg} : ℤ), {sl})"

def main : IO Unit := do
  for (AB, i) in CORNER4.zip (List.range CORNER4.length) do
    for c in [false, true] do
      IO.println s!"Ce{i}c{if c then 1 else 0}|{winC AB}|0|{tmStr (tmC AB c)}|none"
  for (AB, i) in CORNER4_ODD.zip (List.range CORNER4_ODD.length) do
    for c in [false, true] do
      IO.println s!"Co{i}c{if c then 1 else 0}|{winC AB}|1|{tmStr (tmC AB c)}|none"
  for (fam, odd, es) in [("Be", 0, BOUNDARY3_EVEN), ("Bo", 1, BOUNDARY3_ODD)] do
    for (e, i) in es.zip (List.range es.length) do
      for A in [0, 1] do
        let fs := fsB e odd
        if fs = 1 ∨ fs = -1 then
          let fsls : List (Option ℕ) := if fs = 1 then [none, some 0, some 11] else [none]
          let Fs := fsls.map fun fsl => fStr (1 - A) fs fsl
          IO.println s!"{fam}{i}A{A}|6|{odd}|{tmStr (tmB e A)}|{String.intercalate ";;" Fs}"
