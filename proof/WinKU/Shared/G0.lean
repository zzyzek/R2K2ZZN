/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import WinKU.Shared.D
public import ZZN.WinK.SigL

@[expose] public section

set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_0 : finalSigOKL 6 6 UB36_0.1 UB36_0.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_0 : finalSigOK 6 6 (none) UB36_0.1 UB36_0.2 SA0 NS0 = true :=
  finalSigOKL_get fall_0 0 (by decide)
theorem fsig1_0 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_0.1 UB36_0.2 SA1 NS1 = true :=
  finalSigOKL_get fall_0 1 (by decide)
theorem fsig2_0 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_0.1 UB36_0.2 SA2 NS2 = true :=
  finalSigOKL_get fall_0 2 (by decide)
theorem fsig3_0 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_0.1 UB36_0.2 SA3 NS3 = true :=
  finalSigOKL_get fall_0 3 (by decide)
theorem fsig4_0 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_0.1 UB36_0.2 SA4 NS4 = true :=
  finalSigOKL_get fall_0 4 (by decide)
theorem fall_16 : finalSigOKL 6 6 UB36_16.1 UB36_16.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_16 : finalSigOK 6 6 (none) UB36_16.1 UB36_16.2 SA0 NS0 = true :=
  finalSigOKL_get fall_16 0 (by decide)
theorem fsig1_16 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_16.1 UB36_16.2 SA1 NS1 = true :=
  finalSigOKL_get fall_16 1 (by decide)
theorem fsig2_16 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_16.1 UB36_16.2 SA2 NS2 = true :=
  finalSigOKL_get fall_16 2 (by decide)
theorem fsig3_16 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_16.1 UB36_16.2 SA3 NS3 = true :=
  finalSigOKL_get fall_16 3 (by decide)
theorem fsig4_16 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_16.1 UB36_16.2 SA4 NS4 = true :=
  finalSigOKL_get fall_16 4 (by decide)
theorem fall_32 : finalSigOKL 6 6 UB36_32.1 UB36_32.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_32 : finalSigOK 6 6 (none) UB36_32.1 UB36_32.2 SA0 NS0 = true :=
  finalSigOKL_get fall_32 0 (by decide)
theorem fsig1_32 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_32.1 UB36_32.2 SA1 NS1 = true :=
  finalSigOKL_get fall_32 1 (by decide)
theorem fsig2_32 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_32.1 UB36_32.2 SA2 NS2 = true :=
  finalSigOKL_get fall_32 2 (by decide)
theorem fsig3_32 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_32.1 UB36_32.2 SA3 NS3 = true :=
  finalSigOKL_get fall_32 3 (by decide)
theorem fsig4_32 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_32.1 UB36_32.2 SA4 NS4 = true :=
  finalSigOKL_get fall_32 4 (by decide)
theorem fall_48 : finalSigOKL 6 6 UB36_48.1 UB36_48.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_48 : finalSigOK 6 6 (none) UB36_48.1 UB36_48.2 SA0 NS0 = true :=
  finalSigOKL_get fall_48 0 (by decide)
theorem fsig1_48 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_48.1 UB36_48.2 SA1 NS1 = true :=
  finalSigOKL_get fall_48 1 (by decide)
theorem fsig2_48 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_48.1 UB36_48.2 SA2 NS2 = true :=
  finalSigOKL_get fall_48 2 (by decide)
theorem fsig3_48 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_48.1 UB36_48.2 SA3 NS3 = true :=
  finalSigOKL_get fall_48 3 (by decide)
theorem fsig4_48 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_48.1 UB36_48.2 SA4 NS4 = true :=
  finalSigOKL_get fall_48 4 (by decide)
theorem fall_64 : finalSigOKL 6 6 UB36_64.1 UB36_64.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_64 : finalSigOK 6 6 (none) UB36_64.1 UB36_64.2 SA0 NS0 = true :=
  finalSigOKL_get fall_64 0 (by decide)
theorem fsig1_64 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_64.1 UB36_64.2 SA1 NS1 = true :=
  finalSigOKL_get fall_64 1 (by decide)
theorem fsig2_64 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_64.1 UB36_64.2 SA2 NS2 = true :=
  finalSigOKL_get fall_64 2 (by decide)
theorem fsig3_64 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_64.1 UB36_64.2 SA3 NS3 = true :=
  finalSigOKL_get fall_64 3 (by decide)
theorem fsig4_64 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_64.1 UB36_64.2 SA4 NS4 = true :=
  finalSigOKL_get fall_64 4 (by decide)
theorem fall_80 : finalSigOKL 6 6 UB36_80.1 UB36_80.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_80 : finalSigOK 6 6 (none) UB36_80.1 UB36_80.2 SA0 NS0 = true :=
  finalSigOKL_get fall_80 0 (by decide)
theorem fsig1_80 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_80.1 UB36_80.2 SA1 NS1 = true :=
  finalSigOKL_get fall_80 1 (by decide)
theorem fsig2_80 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_80.1 UB36_80.2 SA2 NS2 = true :=
  finalSigOKL_get fall_80 2 (by decide)
theorem fsig3_80 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_80.1 UB36_80.2 SA3 NS3 = true :=
  finalSigOKL_get fall_80 3 (by decide)
theorem fsig4_80 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_80.1 UB36_80.2 SA4 NS4 = true :=
  finalSigOKL_get fall_80 4 (by decide)
theorem fall_96 : finalSigOKL 6 6 UB36_96.1 UB36_96.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_96 : finalSigOK 6 6 (none) UB36_96.1 UB36_96.2 SA0 NS0 = true :=
  finalSigOKL_get fall_96 0 (by decide)
theorem fsig1_96 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_96.1 UB36_96.2 SA1 NS1 = true :=
  finalSigOKL_get fall_96 1 (by decide)
theorem fsig2_96 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_96.1 UB36_96.2 SA2 NS2 = true :=
  finalSigOKL_get fall_96 2 (by decide)
theorem fsig3_96 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_96.1 UB36_96.2 SA3 NS3 = true :=
  finalSigOKL_get fall_96 3 (by decide)
theorem fsig4_96 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_96.1 UB36_96.2 SA4 NS4 = true :=
  finalSigOKL_get fall_96 4 (by decide)
theorem fall_112 : finalSigOKL 6 6 UB36_112.1 UB36_112.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_112 : finalSigOK 6 6 (none) UB36_112.1 UB36_112.2 SA0 NS0 = true :=
  finalSigOKL_get fall_112 0 (by decide)
theorem fsig1_112 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_112.1 UB36_112.2 SA1 NS1 = true :=
  finalSigOKL_get fall_112 1 (by decide)
theorem fsig2_112 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_112.1 UB36_112.2 SA2 NS2 = true :=
  finalSigOKL_get fall_112 2 (by decide)
theorem fsig3_112 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_112.1 UB36_112.2 SA3 NS3 = true :=
  finalSigOKL_get fall_112 3 (by decide)
theorem fsig4_112 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_112.1 UB36_112.2 SA4 NS4 = true :=
  finalSigOKL_get fall_112 4 (by decide)
theorem sg0_0_8 : sigsOKR 0 SA0 512 576 = true := by decide +kernel
theorem sg1_0_11 : sigsOKR 1 SA0 704 768 = true := by decide +kernel
theorem sg0_2_1 : sigsOKR 0 SA2 64 128 = true := by decide +kernel
theorem sg0_3_4 : sigsOKR 0 SA3 256 320 = true := by decide +kernel
theorem sg0_4_2 : sigsOKR 0 SA4 128 192 = true := by decide +kernel
theorem sg1_2_0 : sigsOKR 1 SA2 0 64 = true := by decide +kernel
theorem sg1_3_3 : sigsOKR 1 SA3 192 256 = true := by decide +kernel
theorem sg1_4_1 : sigsOKR 1 SA4 64 128 = true := by decide +kernel
theorem sg1_4_17 : sigsOKR 1 SA4 1088 1148 = true := by decide +kernel
end WinKU.Shared
