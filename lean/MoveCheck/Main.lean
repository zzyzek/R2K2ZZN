-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import MoveCheck.Search

open ZZN GridHam

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let ns := ((line.replace "\n" "").splitOn " ").filter (· ≠ "") |>.filterMap String.toNat?
  match ns with
  | [R, C, a, b, c, d, e, f, g, k] =>
    let I : Inst := ⟨R, C, (a, b), (c, d), (e, f), (g, k)⟩
    match search I 64 with
    | [] => o.putStrLn "NONE"
    | cs =>
      for (desc, pend) in cs do
        o.putStrLn s!"OK {desc} | {String.intercalate " ; " (pend.map showI)}"
      o.putStrLn "END"
  | _ => if line.startsWith "SUMMARY" || line.startsWith "tuples" then pure () else o.putStrLn "BAD"
  o.flush
  loop h o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
