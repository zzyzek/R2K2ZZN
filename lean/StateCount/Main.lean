-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinBCD
open ZZN.Win
def main (args : List String) : IO Unit := do
  let k := (args.headD "6").toNat!
  let AB : List (ℕ × ℕ) × List (ℕ × ℕ) := ([(0, 1), (0, 6)], [(0, 7), (1, 1)])
  let tm := tmC AB false
  let mut S : List St := [([], 0)]
  let mut mx := 0
  let mut tot := 0
  let mut words := 0
  let t0 ← IO.monoMsNow
  for i in List.range (k * k) do
    S := stage k k tm S i
    mx := max mx S.length
    tot := tot + S.length
    words := max words (S.foldl (fun a s => a + s.1.length + 1) 0)
  let t1 ← IO.monoMsNow
  IO.println s!"k={k} final {S.length} max-stage {mx} total {tot} max-numbers-per-stage {words} ms {t1 - t0}"
