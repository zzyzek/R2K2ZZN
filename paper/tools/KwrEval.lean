/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
-- Lean's own evaluation of the step constants at b = 2 and b = 3, the values that
-- paper/tools/kwr.py checks its transcription against. Run from proof/ with a built tree:
--   lake env lean ../paper/tools/KwrEval.lean
-- Output (2026-11-17): (64, 16804, 202, 63666)
import ZZN.Timed.ThinRopeCost
open ZZN.T
#eval (Nw 2, KwR 2, Nw 3, KwR 3)
