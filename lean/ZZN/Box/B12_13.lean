-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Finite2

/-! The box 12 × 13, checked by `native_decide` with the move search `moveB2`. -/

namespace ZZN

theorem box_12_13 : (List.range 12).all (checkBoxC checkInst2 12 13) = true := by native_decide

end ZZN
