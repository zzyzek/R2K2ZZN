-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cert.Small
import ZZN.Cert.BOdd
import ZZN.Cert.BEven
import ZZN.Cert.C8_2
import ZZN.Cert.C8_3
import ZZN.Cert.C8_4
import ZZN.Cert.C8_5
import ZZN.Cert.C8_12
import ZZN.Cert.C8_16

/-!
# The final assembly

The window certificates, checked by `native_decide` (compiled code; see the paper, Section 9), give
`CertFacts`, and with it Theorem B on the domain.
-/

namespace ZZN.Win

theorem big_entries : CORNER4.filter (fun AB => ¬ winC AB = 6) = [([(0, 1), (0, 6)], [(0, 7), (1, 1)]), ([(0, 1), (0, 6)], [(1, 1), (7, 0)]), ([(0, 1), (0, 6)], [(1, 2), (6, 0)]), ([(0, 1), (0, 7)], [(1, 1), (6, 0)]), ([(0, 1), (7, 0)], [(1, 1), (6, 0)]), ([(0, 6), (2, 1)], [(1, 2), (6, 0)])] := by
  decide

/-- **The window certificates.** -/
theorem certFacts : CertFacts := by
  refine ⟨fun AB hAB c => ?_, cert_d, cert_b_even, cert_b_odd⟩
  by_cases h : winC AB = 6
  · exact cert_c6 AB (List.mem_filter.mpr ⟨hAB, by simpa using h⟩) c
  · have hm : AB ∈ CORNER4.filter (fun AB => ¬ winC AB = 6) := List.mem_filter.mpr ⟨hAB, by simpa using h⟩
    rw [big_entries] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_c8_2 c
    · exact cert_c8_3 c
    · exact cert_c8_4 c
    · exact cert_c8_5 c
    · exact cert_c8_12 c
    · exact cert_c8_16 c

/-- **Theorem B**: on the domain, a solvable instance passes the catalogue. -/
theorem theoremB_final {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=
  theoremB_cert certFacts hI hS

end ZZN.Win
