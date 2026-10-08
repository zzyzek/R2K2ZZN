-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Catalogue

/-- Read "R C s0r s0c t0r t0c s1r s1c t1r t1c" lines; print the first firing entry or NONE. -/
partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let ns := ((line.replace "\n" "").splitOn " ").filter (· ≠ "") |>.filterMap String.toNat?
  match ns with
  | [R, C, a, b, c, d, e, f, g, k] =>
    -- the functional forms: `fires2` and its R test `effAlt`
    let fz2 := ZZN.fires3 R C (a, b) (c, d) (e, f) (g, k)
    let ea2 := ZZN.effAlt3 R C [((a, b), 0), ((c, d), 0), ((e, f), 1), ((g, k), 1)]
    o.putStrLn s!"{if fz2 then "F" else "P"}|{ea2}"
  | _ => o.putStrLn "BAD"
  loop h o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
