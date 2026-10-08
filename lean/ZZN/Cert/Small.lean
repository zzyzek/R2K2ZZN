-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.WinBCD

namespace ZZN.Win

/-- Certificates for the C entries on 6 × 6 windows. -/
theorem cert_c6 : ∀ AB ∈ CORNER4.filter (fun AB => winC AB = 6), ∀ c : Bool,
    certify (winC AB) (winC AB) (tmC AB c) 0 none = true := by
  native_decide

/-- Certificates for the D entries. -/
theorem cert_d : ∀ AB ∈ CORNER4_ODD, ∀ c : Bool, certify (winC AB) (winC AB) (tmC AB c) 1 none = true := by
  native_decide

end ZZN.Win
