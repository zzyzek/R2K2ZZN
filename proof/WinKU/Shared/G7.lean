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
theorem fall_7 : finalSigOKL 6 6 UB36_7.1 UB36_7.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_7 : finalSigOK 6 6 (none) UB36_7.1 UB36_7.2 SA0 NS0 = true :=
  finalSigOKL_get fall_7 0 (by decide)
theorem fsig1_7 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_7.1 UB36_7.2 SA1 NS1 = true :=
  finalSigOKL_get fall_7 1 (by decide)
theorem fsig2_7 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_7.1 UB36_7.2 SA2 NS2 = true :=
  finalSigOKL_get fall_7 2 (by decide)
theorem fsig3_7 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_7.1 UB36_7.2 SA3 NS3 = true :=
  finalSigOKL_get fall_7 3 (by decide)
theorem fsig4_7 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_7.1 UB36_7.2 SA4 NS4 = true :=
  finalSigOKL_get fall_7 4 (by decide)
theorem fall_23 : finalSigOKL 6 6 UB36_23.1 UB36_23.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_23 : finalSigOK 6 6 (none) UB36_23.1 UB36_23.2 SA0 NS0 = true :=
  finalSigOKL_get fall_23 0 (by decide)
theorem fsig1_23 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_23.1 UB36_23.2 SA1 NS1 = true :=
  finalSigOKL_get fall_23 1 (by decide)
theorem fsig2_23 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_23.1 UB36_23.2 SA2 NS2 = true :=
  finalSigOKL_get fall_23 2 (by decide)
theorem fsig3_23 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_23.1 UB36_23.2 SA3 NS3 = true :=
  finalSigOKL_get fall_23 3 (by decide)
theorem fsig4_23 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_23.1 UB36_23.2 SA4 NS4 = true :=
  finalSigOKL_get fall_23 4 (by decide)
theorem fall_39 : finalSigOKL 6 6 UB36_39.1 UB36_39.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_39 : finalSigOK 6 6 (none) UB36_39.1 UB36_39.2 SA0 NS0 = true :=
  finalSigOKL_get fall_39 0 (by decide)
theorem fsig1_39 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_39.1 UB36_39.2 SA1 NS1 = true :=
  finalSigOKL_get fall_39 1 (by decide)
theorem fsig2_39 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_39.1 UB36_39.2 SA2 NS2 = true :=
  finalSigOKL_get fall_39 2 (by decide)
theorem fsig3_39 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_39.1 UB36_39.2 SA3 NS3 = true :=
  finalSigOKL_get fall_39 3 (by decide)
theorem fsig4_39 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_39.1 UB36_39.2 SA4 NS4 = true :=
  finalSigOKL_get fall_39 4 (by decide)
theorem fall_55 : finalSigOKL 6 6 UB36_55.1 UB36_55.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_55 : finalSigOK 6 6 (none) UB36_55.1 UB36_55.2 SA0 NS0 = true :=
  finalSigOKL_get fall_55 0 (by decide)
theorem fsig1_55 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_55.1 UB36_55.2 SA1 NS1 = true :=
  finalSigOKL_get fall_55 1 (by decide)
theorem fsig2_55 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_55.1 UB36_55.2 SA2 NS2 = true :=
  finalSigOKL_get fall_55 2 (by decide)
theorem fsig3_55 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_55.1 UB36_55.2 SA3 NS3 = true :=
  finalSigOKL_get fall_55 3 (by decide)
theorem fsig4_55 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_55.1 UB36_55.2 SA4 NS4 = true :=
  finalSigOKL_get fall_55 4 (by decide)
theorem fall_71 : finalSigOKL 6 6 UB36_71.1 UB36_71.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_71 : finalSigOK 6 6 (none) UB36_71.1 UB36_71.2 SA0 NS0 = true :=
  finalSigOKL_get fall_71 0 (by decide)
theorem fsig1_71 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_71.1 UB36_71.2 SA1 NS1 = true :=
  finalSigOKL_get fall_71 1 (by decide)
theorem fsig2_71 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_71.1 UB36_71.2 SA2 NS2 = true :=
  finalSigOKL_get fall_71 2 (by decide)
theorem fsig3_71 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_71.1 UB36_71.2 SA3 NS3 = true :=
  finalSigOKL_get fall_71 3 (by decide)
theorem fsig4_71 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_71.1 UB36_71.2 SA4 NS4 = true :=
  finalSigOKL_get fall_71 4 (by decide)
theorem fall_87 : finalSigOKL 6 6 UB36_87.1 UB36_87.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_87 : finalSigOK 6 6 (none) UB36_87.1 UB36_87.2 SA0 NS0 = true :=
  finalSigOKL_get fall_87 0 (by decide)
theorem fsig1_87 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_87.1 UB36_87.2 SA1 NS1 = true :=
  finalSigOKL_get fall_87 1 (by decide)
theorem fsig2_87 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_87.1 UB36_87.2 SA2 NS2 = true :=
  finalSigOKL_get fall_87 2 (by decide)
theorem fsig3_87 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_87.1 UB36_87.2 SA3 NS3 = true :=
  finalSigOKL_get fall_87 3 (by decide)
theorem fsig4_87 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_87.1 UB36_87.2 SA4 NS4 = true :=
  finalSigOKL_get fall_87 4 (by decide)
theorem fall_103 : finalSigOKL 6 6 UB36_103.1 UB36_103.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_103 : finalSigOK 6 6 (none) UB36_103.1 UB36_103.2 SA0 NS0 = true :=
  finalSigOKL_get fall_103 0 (by decide)
theorem fsig1_103 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_103.1 UB36_103.2 SA1 NS1 = true :=
  finalSigOKL_get fall_103 1 (by decide)
theorem fsig2_103 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_103.1 UB36_103.2 SA2 NS2 = true :=
  finalSigOKL_get fall_103 2 (by decide)
theorem fsig3_103 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_103.1 UB36_103.2 SA3 NS3 = true :=
  finalSigOKL_get fall_103 3 (by decide)
theorem fsig4_103 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_103.1 UB36_103.2 SA4 NS4 = true :=
  finalSigOKL_get fall_103 4 (by decide)
theorem fall_119 : finalSigOKL 6 6 UB36_119.1 UB36_119.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_119 : finalSigOK 6 6 (none) UB36_119.1 UB36_119.2 SA0 NS0 = true :=
  finalSigOKL_get fall_119 0 (by decide)
theorem fsig1_119 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_119.1 UB36_119.2 SA1 NS1 = true :=
  finalSigOKL_get fall_119 1 (by decide)
theorem fsig2_119 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_119.1 UB36_119.2 SA2 NS2 = true :=
  finalSigOKL_get fall_119 2 (by decide)
theorem fsig3_119 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_119.1 UB36_119.2 SA3 NS3 = true :=
  finalSigOKL_get fall_119 3 (by decide)
theorem fsig4_119 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_119.1 UB36_119.2 SA4 NS4 = true :=
  finalSigOKL_get fall_119 4 (by decide)
theorem sg1_0_2 : sigsOKR 1 SA0 128 192 = true := by decide +kernel
theorem sg0_1_5 : sigsOKR 0 SA1 320 384 = true := by decide +kernel
theorem sg0_2_8 : sigsOKR 0 SA2 512 576 = true := by decide +kernel
theorem sg0_3_11 : sigsOKR 0 SA3 704 768 = true := by decide +kernel
theorem sg0_4_9 : sigsOKR 0 SA4 576 640 = true := by decide +kernel
theorem sg1_2_7 : sigsOKR 1 SA2 448 512 = true := by decide +kernel
theorem sg1_3_10 : sigsOKR 1 SA3 640 704 = true := by decide +kernel
theorem sg1_4_8 : sigsOKR 1 SA4 512 576 = true := by decide +kernel
theorem sg1_1_6 : sigsOKR 1 SA1 384 448 = true := by decide +kernel
end WinKU.Shared
