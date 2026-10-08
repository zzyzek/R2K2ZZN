-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Finite2

/-! The box 19 × 16, checked by `native_decide` with the move search `moveB2`. -/

namespace ZZN

theorem box_19_16 : (List.range 19).all (checkBoxC checkInst2 19 16) = true := by native_decide

end ZZN
