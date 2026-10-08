-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinBCD

namespace ZZN.Win

/-- Certificate for C4 (8 × 8 window), both colourings. -/
theorem cert_c8_4 : ∀ c : Bool, certify (winC ([(0, 1), (0, 6)], [(1, 2), (6, 0)])) (winC ([(0, 1), (0, 6)], [(1, 2), (6, 0)])) (tmC ([(0, 1), (0, 6)], [(1, 2), (6, 0)]) c) 0 none = true := by
  native_decide

end ZZN.Win
