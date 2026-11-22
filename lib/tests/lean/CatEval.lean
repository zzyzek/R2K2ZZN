/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ZZN.Statement

/-!
Evaluate `fires3` and its entries (`ZZN/Statement.lean`) on the instances written by
`lib/tests/lean_catalogue.py` and compare with the Python verdicts. Line format:
`R C r0 c0 r1 c1 r2 c2 r3 c3 FIRES MASK NAME LAYOUT`.
-/

open ZZN

def natsOf (s : String) : List Nat :=
  (s.splitOn " ").filterMap fun t => if t.isEmpty then none else t.toNat?

def b2c (b : Bool) : Char := if b then '1' else '0'

def leanMask (R C : Nat) (s0 t0 s1 t1 : Nat × Nat) : String :=
  let pts : List Pt := [(s0, 0), (t0, 0), (s1, 1), (t1, 1)]
  let anyF := fun (g : View → Bool) => frames.any fun f => g (makeView R C f pts)
  String.ofList ([!parityOk R C pts, t1Fires R C pts, t2Fires [s0, t0, s1, t1], l1Fires R C pts,
    l6Fires R C pts, anyF testL2, anyF testL3, anyF testL4, anyF testL5, anyF edgeClosure,
    frames.any (fun f => boundaryOnly R C f pts),
    decide (R ≥ 10) && decide (C ≥ 10) && frames.any (fun f => corner4 R C f pts),
    effAlt3 R C pts].map b2c)

def main (args : List String) : IO UInt32 := do
  let path := args.head!
  let txt ← IO.FS.readFile path
  let mut n := 0
  let mut nf := 0
  let mut bad := 0
  let mut badMask := 0
  for line in txt.splitOn "\n" do
    let fs := (line.splitOn " ").filter (· ≠ "")
    match fs with
    | r :: c :: rest =>
      let ns := natsOf (" ".intercalate (r :: c :: rest.take 8))
      match ns, rest.drop 8 with
      | [R, C, a, b, d, e, g, h, i, j], fpy :: mpy :: _ =>
        let s0 := (a, b); let t0 := (d, e); let s1 := (g, h); let t1 := (i, j)
        let f := fires3 R C s0 t0 s1 t1
        let m := leanMask R C s0 t0 s1 t1
        n := n + 1
        if f then nf := nf + 1
        if (if f then "1" else "0") != fpy then
          bad := bad + 1
          IO.println s!"FIRES DIFF: {line} lean={f}"
        if m != mpy then
          badMask := badMask + 1
          IO.println s!"MASK DIFF: {line} lean={m}"
      | _, _ => pure ()
    | _ => pure ()
  IO.println s!"instances {n}, lean fires3 true {nf}, fires3 disagreements {bad}, entry-mask disagreements {badMask}"
  return (if bad + badMask == 0 then 0 else 1)
