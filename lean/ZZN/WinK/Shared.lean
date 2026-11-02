-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinK.Engine

/-!
# Window certificates sharing their late stages

A DP stage sees the terminal list only through the terminal at its own cell (`stage_congr`).
Past the last terminal cell every certificate of a window size steps its states the same way, so
checkpoints for those stages can be the union over all certificates and their step checks, made
once with the empty terminal list, serve every certificate (`cov_stage_shared`). The union's final
states are checked once per outside specification.
-/

namespace ZZN.WinK

open ZZN ZZN.Win

theorem stage_congr {a b : ℕ} {tm tm' : List ((ℕ × ℕ) × ℕ)} {i : ℕ}
    (h : termAt tm (cell b i) = termAt tm' (cell b i)) (S : List St) :
    stage a b tm S i = stage a b tm' S i := by
  unfold stage; rw [h]

/-- A stage with no terminal at its cell, from step checks made with the empty terminal list. -/
theorem cov_stage_shared {a b : ℕ} {tm : List ((ℕ × ℕ) × ℕ)} {i : ℕ} {Lin Lout : KSet}
    {firsts nb : ℕ} {S : List St} (hS : Cov Lin S) (ht : termAt tm (cell b i) = none)
    (hstep : ∀ p ∈ Lin, stepOK a b [] i p.1 p.2 Lout firsts nb = true) :
    Cov Lout (stage a b tm S i) := by
  rw [stage_congr (tm' := []) (by rw [ht]; rfl)]
  exact cov_stage hS hstep

end ZZN.WinK
