/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import BoxKGen.N15x16.S0

@[expose] public section

set_option Elab.async false
namespace BoxKGen.N15x16
open ZZN ZZN.Cut ZZN.BoxK BoxKGen

set_option maxRecDepth 100000
theorem rows : rowsOK 15 [d0.1, d1.1, d2.1, d3.1, d4.1, d5.1, d6.1, d7.1, d8.1, d9.1, d10.1, d11.1, d12.1, d13.1, d14.1, d15.1, d16.1, d17.1, d18.1, d19.1, d20.1, d21.1, d22.1, d23.1, d24.1, d25.1, d26.1, d27.1, d28.1, d29.1, d30.1, d31.1, d32.1, d33.1, d34.1, d35.1, d36.1, d37.1, d38.1, d39.1, d40.1, d41.1, d42.1, d43.1, d44.1, d45.1, d46.1, d47.1, d48.1, d49.1, d50.1, d51.1, d52.1, d53.1, d54.1, d55.1, d56.1, d57.1, d58.1, d59.1, d60.1, d61.1, d62.1, d63.1, d64.1, d65.1, d66.1, d67.1, d68.1, d69.1, d70.1, d71.1, d72.1, d73.1, d74.1, d75.1, d76.1, d77.1] = true := by decide +kernel
theorem all : List.Forall (SliceGood 15 16) [d0.1, d1.1, d2.1, d3.1, d4.1, d5.1, d6.1, d7.1, d8.1, d9.1, d10.1, d11.1, d12.1, d13.1, d14.1, d15.1, d16.1, d17.1, d18.1, d19.1, d20.1, d21.1, d22.1, d23.1, d24.1, d25.1, d26.1, d27.1, d28.1, d29.1, d30.1, d31.1, d32.1, d33.1, d34.1, d35.1, d36.1, d37.1, d38.1, d39.1, d40.1, d41.1, d42.1, d43.1, d44.1, d45.1, d46.1, d47.1, d48.1, d49.1, d50.1, d51.1, d52.1, d53.1, d54.1, d55.1, d56.1, d57.1, d58.1, d59.1, d60.1, d61.1, d62.1, d63.1, d64.1, d65.1, d66.1, d67.1, d68.1, d69.1, d70.1, d71.1, d72.1, d73.1, d74.1, d75.1, d76.1, d77.1] :=
  ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77⟩
theorem box : BoxCert 15 16 := boxCert_of_good _ rows all
end BoxKGen.N15x16
