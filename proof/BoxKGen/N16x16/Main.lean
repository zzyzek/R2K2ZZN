/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import BoxKGen.N16x16.S0

@[expose] public section

set_option Elab.async false
namespace BoxKGen.N16x16
open ZZN ZZN.Cut ZZN.BoxK BoxKGen

set_option maxRecDepth 100000
theorem rows : rowsOK 16 [d0.1, d1.1, d2.1, d3.1, d4.1, d5.1, d6.1, d7.1, d8.1, d9.1, d10.1, d11.1, d12.1, d13.1, d14.1, d15.1, d16.1, d17.1, d18.1, d19.1, d20.1, d21.1, d22.1, d23.1, d24.1, d25.1, d26.1, d27.1, d28.1, d29.1] = true := by decide +kernel
theorem all : List.Forall (SliceGood 16 16) [d0.1, d1.1, d2.1, d3.1, d4.1, d5.1, d6.1, d7.1, d8.1, d9.1, d10.1, d11.1, d12.1, d13.1, d14.1, d15.1, d16.1, d17.1, d18.1, d19.1, d20.1, d21.1, d22.1, d23.1, d24.1, d25.1, d26.1, d27.1, d28.1, d29.1] :=
  ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29⟩
theorem box : BoxCert 16 16 := boxCert_of_good _ rows all
end BoxKGen.N16x16
