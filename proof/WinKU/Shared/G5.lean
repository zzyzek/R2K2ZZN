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
theorem fall_5 : finalSigOKL 6 6 UB36_5.1 UB36_5.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_5 : finalSigOK 6 6 (none) UB36_5.1 UB36_5.2 SA0 NS0 = true :=
  finalSigOKL_get fall_5 0 (by decide)
theorem fsig1_5 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_5.1 UB36_5.2 SA1 NS1 = true :=
  finalSigOKL_get fall_5 1 (by decide)
theorem fsig2_5 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_5.1 UB36_5.2 SA2 NS2 = true :=
  finalSigOKL_get fall_5 2 (by decide)
theorem fsig3_5 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_5.1 UB36_5.2 SA3 NS3 = true :=
  finalSigOKL_get fall_5 3 (by decide)
theorem fsig4_5 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_5.1 UB36_5.2 SA4 NS4 = true :=
  finalSigOKL_get fall_5 4 (by decide)
theorem fall_21 : finalSigOKL 6 6 UB36_21.1 UB36_21.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_21 : finalSigOK 6 6 (none) UB36_21.1 UB36_21.2 SA0 NS0 = true :=
  finalSigOKL_get fall_21 0 (by decide)
theorem fsig1_21 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_21.1 UB36_21.2 SA1 NS1 = true :=
  finalSigOKL_get fall_21 1 (by decide)
theorem fsig2_21 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_21.1 UB36_21.2 SA2 NS2 = true :=
  finalSigOKL_get fall_21 2 (by decide)
theorem fsig3_21 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_21.1 UB36_21.2 SA3 NS3 = true :=
  finalSigOKL_get fall_21 3 (by decide)
theorem fsig4_21 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_21.1 UB36_21.2 SA4 NS4 = true :=
  finalSigOKL_get fall_21 4 (by decide)
theorem fall_37 : finalSigOKL 6 6 UB36_37.1 UB36_37.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_37 : finalSigOK 6 6 (none) UB36_37.1 UB36_37.2 SA0 NS0 = true :=
  finalSigOKL_get fall_37 0 (by decide)
theorem fsig1_37 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_37.1 UB36_37.2 SA1 NS1 = true :=
  finalSigOKL_get fall_37 1 (by decide)
theorem fsig2_37 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_37.1 UB36_37.2 SA2 NS2 = true :=
  finalSigOKL_get fall_37 2 (by decide)
theorem fsig3_37 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_37.1 UB36_37.2 SA3 NS3 = true :=
  finalSigOKL_get fall_37 3 (by decide)
theorem fsig4_37 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_37.1 UB36_37.2 SA4 NS4 = true :=
  finalSigOKL_get fall_37 4 (by decide)
theorem fall_53 : finalSigOKL 6 6 UB36_53.1 UB36_53.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_53 : finalSigOK 6 6 (none) UB36_53.1 UB36_53.2 SA0 NS0 = true :=
  finalSigOKL_get fall_53 0 (by decide)
theorem fsig1_53 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_53.1 UB36_53.2 SA1 NS1 = true :=
  finalSigOKL_get fall_53 1 (by decide)
theorem fsig2_53 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_53.1 UB36_53.2 SA2 NS2 = true :=
  finalSigOKL_get fall_53 2 (by decide)
theorem fsig3_53 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_53.1 UB36_53.2 SA3 NS3 = true :=
  finalSigOKL_get fall_53 3 (by decide)
theorem fsig4_53 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_53.1 UB36_53.2 SA4 NS4 = true :=
  finalSigOKL_get fall_53 4 (by decide)
theorem fall_69 : finalSigOKL 6 6 UB36_69.1 UB36_69.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_69 : finalSigOK 6 6 (none) UB36_69.1 UB36_69.2 SA0 NS0 = true :=
  finalSigOKL_get fall_69 0 (by decide)
theorem fsig1_69 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_69.1 UB36_69.2 SA1 NS1 = true :=
  finalSigOKL_get fall_69 1 (by decide)
theorem fsig2_69 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_69.1 UB36_69.2 SA2 NS2 = true :=
  finalSigOKL_get fall_69 2 (by decide)
theorem fsig3_69 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_69.1 UB36_69.2 SA3 NS3 = true :=
  finalSigOKL_get fall_69 3 (by decide)
theorem fsig4_69 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_69.1 UB36_69.2 SA4 NS4 = true :=
  finalSigOKL_get fall_69 4 (by decide)
theorem fall_85 : finalSigOKL 6 6 UB36_85.1 UB36_85.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_85 : finalSigOK 6 6 (none) UB36_85.1 UB36_85.2 SA0 NS0 = true :=
  finalSigOKL_get fall_85 0 (by decide)
theorem fsig1_85 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_85.1 UB36_85.2 SA1 NS1 = true :=
  finalSigOKL_get fall_85 1 (by decide)
theorem fsig2_85 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_85.1 UB36_85.2 SA2 NS2 = true :=
  finalSigOKL_get fall_85 2 (by decide)
theorem fsig3_85 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_85.1 UB36_85.2 SA3 NS3 = true :=
  finalSigOKL_get fall_85 3 (by decide)
theorem fsig4_85 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_85.1 UB36_85.2 SA4 NS4 = true :=
  finalSigOKL_get fall_85 4 (by decide)
theorem fall_101 : finalSigOKL 6 6 UB36_101.1 UB36_101.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_101 : finalSigOK 6 6 (none) UB36_101.1 UB36_101.2 SA0 NS0 = true :=
  finalSigOKL_get fall_101 0 (by decide)
theorem fsig1_101 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_101.1 UB36_101.2 SA1 NS1 = true :=
  finalSigOKL_get fall_101 1 (by decide)
theorem fsig2_101 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_101.1 UB36_101.2 SA2 NS2 = true :=
  finalSigOKL_get fall_101 2 (by decide)
theorem fsig3_101 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_101.1 UB36_101.2 SA3 NS3 = true :=
  finalSigOKL_get fall_101 3 (by decide)
theorem fsig4_101 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_101.1 UB36_101.2 SA4 NS4 = true :=
  finalSigOKL_get fall_101 4 (by decide)
theorem fall_117 : finalSigOKL 6 6 UB36_117.1 UB36_117.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_117 : finalSigOK 6 6 (none) UB36_117.1 UB36_117.2 SA0 NS0 = true :=
  finalSigOKL_get fall_117 0 (by decide)
theorem fsig1_117 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_117.1 UB36_117.2 SA1 NS1 = true :=
  finalSigOKL_get fall_117 1 (by decide)
theorem fsig2_117 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_117.1 UB36_117.2 SA2 NS2 = true :=
  finalSigOKL_get fall_117 2 (by decide)
theorem fsig3_117 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_117.1 UB36_117.2 SA3 NS3 = true :=
  finalSigOKL_get fall_117 3 (by decide)
theorem fsig4_117 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_117.1 UB36_117.2 SA4 NS4 = true :=
  finalSigOKL_get fall_117 4 (by decide)
theorem sg1_0_0 : sigsOKR 1 SA0 0 64 = true := by decide +kernel
theorem sg0_1_3 : sigsOKR 0 SA1 192 256 = true := by decide +kernel
theorem sg0_2_6 : sigsOKR 0 SA2 384 448 = true := by decide +kernel
theorem sg0_3_9 : sigsOKR 0 SA3 576 640 = true := by decide +kernel
theorem sg0_4_7 : sigsOKR 0 SA4 448 512 = true := by decide +kernel
theorem sg1_2_5 : sigsOKR 1 SA2 320 384 = true := by decide +kernel
theorem sg1_3_8 : sigsOKR 1 SA3 512 576 = true := by decide +kernel
theorem sg1_4_6 : sigsOKR 1 SA4 384 448 = true := by decide +kernel
theorem sg1_1_4 : sigsOKR 1 SA1 256 320 = true := by decide +kernel
end WinKU.Shared
