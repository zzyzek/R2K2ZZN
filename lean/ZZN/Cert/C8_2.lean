-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinBCD

namespace ZZN.Win

/-- Certificate for C2 (8 × 8 window), both colourings. -/
theorem cert_c8_2 : ∀ c : Bool, certify (winC ([(0, 1), (0, 6)], [(0, 7), (1, 1)])) (winC ([(0, 1), (0, 6)], [(0, 7), (1, 1)])) (tmC ([(0, 1), (0, 6)], [(0, 7), (1, 1)]) c) 0 none = true := by
  native_decide

end ZZN.Win
