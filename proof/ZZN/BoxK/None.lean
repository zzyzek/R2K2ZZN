/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.BoxK.Box

@[expose] public section

/-!
# Sides 17–22 have no irreducible tuple

Band and strip compressions apply to every tuple of side 17 to 22, so only boxes with both
sides at most 16 need slice certificates.
-/

namespace ZZN.BoxK

theorem none17 : noneOK 17 = true := by decide +kernel
theorem none18 : noneOK 18 = true := by decide +kernel
theorem none19 : noneOK 19 = true := by decide +kernel
theorem none20 : noneOK 20 = true := by decide +kernel
theorem none21 : noneOK 21 = true := by decide +kernel
theorem none22 : noneOK 22 = true := by decide +kernel

theorem none_all : ∀ n, 17 ≤ n → n ≤ 22 → noneOK n = true := by
  intro n h1 h2
  obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 := by omega
  exacts [none17, none18, none19, none20, none21, none22]

end ZZN.BoxK
