-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Cert.Small
import ZZN.Cert.BOdd
import ZZN.Cert.BEven
import ZZN.C8R

/-!
# The final assembly

The window certificates, checked by `native_decide` (compiled code; see the paper, Section 9), give
`CertFacts`, and with it Theorem B on the domain.
-/

namespace ZZN.Win

/-- **The window certificates.** -/
theorem certFacts : CertFacts :=
  ⟨fun AB hAB h6 => cert_c6 AB (List.mem_filter.mpr ⟨hAB, by simpa using h6⟩) false,
   fun AB hAB => cert_d AB hAB false,
   fun e he fsl hfsl h1 h2 => cert_b_even e he 0 (by norm_num) fsl hfsl h1 h2,
   fun e he fsl hfsl h1 h2 => cert_b_odd e he 0 (by norm_num) fsl hfsl h1 h2⟩

/-- **Theorem B**: on the domain, a solvable instance passes the catalogue. -/
theorem theoremB_final {I : Inst} (hI : InDom I) (hS : Solvable I) : Passes I :=
  theoremB_cert certFacts hI hS

end ZZN.Win
