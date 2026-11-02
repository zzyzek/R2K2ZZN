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
theorem fall_8 : finalSigOKL 6 6 UB36_8.1 UB36_8.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_8 : finalSigOK 6 6 (none) UB36_8.1 UB36_8.2 SA0 NS0 = true :=
  finalSigOKL_get fall_8 0 (by decide)
theorem fsig1_8 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_8.1 UB36_8.2 SA1 NS1 = true :=
  finalSigOKL_get fall_8 1 (by decide)
theorem fsig2_8 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_8.1 UB36_8.2 SA2 NS2 = true :=
  finalSigOKL_get fall_8 2 (by decide)
theorem fsig3_8 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_8.1 UB36_8.2 SA3 NS3 = true :=
  finalSigOKL_get fall_8 3 (by decide)
theorem fsig4_8 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_8.1 UB36_8.2 SA4 NS4 = true :=
  finalSigOKL_get fall_8 4 (by decide)
theorem fall_24 : finalSigOKL 6 6 UB36_24.1 UB36_24.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_24 : finalSigOK 6 6 (none) UB36_24.1 UB36_24.2 SA0 NS0 = true :=
  finalSigOKL_get fall_24 0 (by decide)
theorem fsig1_24 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_24.1 UB36_24.2 SA1 NS1 = true :=
  finalSigOKL_get fall_24 1 (by decide)
theorem fsig2_24 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_24.1 UB36_24.2 SA2 NS2 = true :=
  finalSigOKL_get fall_24 2 (by decide)
theorem fsig3_24 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_24.1 UB36_24.2 SA3 NS3 = true :=
  finalSigOKL_get fall_24 3 (by decide)
theorem fsig4_24 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_24.1 UB36_24.2 SA4 NS4 = true :=
  finalSigOKL_get fall_24 4 (by decide)
theorem fall_40 : finalSigOKL 6 6 UB36_40.1 UB36_40.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_40 : finalSigOK 6 6 (none) UB36_40.1 UB36_40.2 SA0 NS0 = true :=
  finalSigOKL_get fall_40 0 (by decide)
theorem fsig1_40 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_40.1 UB36_40.2 SA1 NS1 = true :=
  finalSigOKL_get fall_40 1 (by decide)
theorem fsig2_40 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_40.1 UB36_40.2 SA2 NS2 = true :=
  finalSigOKL_get fall_40 2 (by decide)
theorem fsig3_40 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_40.1 UB36_40.2 SA3 NS3 = true :=
  finalSigOKL_get fall_40 3 (by decide)
theorem fsig4_40 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_40.1 UB36_40.2 SA4 NS4 = true :=
  finalSigOKL_get fall_40 4 (by decide)
theorem fall_56 : finalSigOKL 6 6 UB36_56.1 UB36_56.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_56 : finalSigOK 6 6 (none) UB36_56.1 UB36_56.2 SA0 NS0 = true :=
  finalSigOKL_get fall_56 0 (by decide)
theorem fsig1_56 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_56.1 UB36_56.2 SA1 NS1 = true :=
  finalSigOKL_get fall_56 1 (by decide)
theorem fsig2_56 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_56.1 UB36_56.2 SA2 NS2 = true :=
  finalSigOKL_get fall_56 2 (by decide)
theorem fsig3_56 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_56.1 UB36_56.2 SA3 NS3 = true :=
  finalSigOKL_get fall_56 3 (by decide)
theorem fsig4_56 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_56.1 UB36_56.2 SA4 NS4 = true :=
  finalSigOKL_get fall_56 4 (by decide)
theorem fall_72 : finalSigOKL 6 6 UB36_72.1 UB36_72.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_72 : finalSigOK 6 6 (none) UB36_72.1 UB36_72.2 SA0 NS0 = true :=
  finalSigOKL_get fall_72 0 (by decide)
theorem fsig1_72 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_72.1 UB36_72.2 SA1 NS1 = true :=
  finalSigOKL_get fall_72 1 (by decide)
theorem fsig2_72 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_72.1 UB36_72.2 SA2 NS2 = true :=
  finalSigOKL_get fall_72 2 (by decide)
theorem fsig3_72 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_72.1 UB36_72.2 SA3 NS3 = true :=
  finalSigOKL_get fall_72 3 (by decide)
theorem fsig4_72 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_72.1 UB36_72.2 SA4 NS4 = true :=
  finalSigOKL_get fall_72 4 (by decide)
theorem fall_88 : finalSigOKL 6 6 UB36_88.1 UB36_88.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_88 : finalSigOK 6 6 (none) UB36_88.1 UB36_88.2 SA0 NS0 = true :=
  finalSigOKL_get fall_88 0 (by decide)
theorem fsig1_88 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_88.1 UB36_88.2 SA1 NS1 = true :=
  finalSigOKL_get fall_88 1 (by decide)
theorem fsig2_88 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_88.1 UB36_88.2 SA2 NS2 = true :=
  finalSigOKL_get fall_88 2 (by decide)
theorem fsig3_88 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_88.1 UB36_88.2 SA3 NS3 = true :=
  finalSigOKL_get fall_88 3 (by decide)
theorem fsig4_88 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_88.1 UB36_88.2 SA4 NS4 = true :=
  finalSigOKL_get fall_88 4 (by decide)
theorem fall_104 : finalSigOKL 6 6 UB36_104.1 UB36_104.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_104 : finalSigOK 6 6 (none) UB36_104.1 UB36_104.2 SA0 NS0 = true :=
  finalSigOKL_get fall_104 0 (by decide)
theorem fsig1_104 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_104.1 UB36_104.2 SA1 NS1 = true :=
  finalSigOKL_get fall_104 1 (by decide)
theorem fsig2_104 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_104.1 UB36_104.2 SA2 NS2 = true :=
  finalSigOKL_get fall_104 2 (by decide)
theorem fsig3_104 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_104.1 UB36_104.2 SA3 NS3 = true :=
  finalSigOKL_get fall_104 3 (by decide)
theorem fsig4_104 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_104.1 UB36_104.2 SA4 NS4 = true :=
  finalSigOKL_get fall_104 4 (by decide)
theorem sg0_0_0 : sigsOKR 0 SA0 0 64 = true := by decide +kernel
theorem sg1_0_3 : sigsOKR 1 SA0 192 256 = true := by decide +kernel
theorem sg0_1_6 : sigsOKR 0 SA1 384 448 = true := by decide +kernel
theorem sg0_2_9 : sigsOKR 0 SA2 576 640 = true := by decide +kernel
theorem sg0_3_12 : sigsOKR 0 SA3 768 832 = true := by decide +kernel
theorem sg0_4_10 : sigsOKR 0 SA4 640 704 = true := by decide +kernel
theorem sg1_2_8 : sigsOKR 1 SA2 512 576 = true := by decide +kernel
theorem sg1_3_11 : sigsOKR 1 SA3 704 768 = true := by decide +kernel
theorem sg1_4_9 : sigsOKR 1 SA4 576 640 = true := by decide +kernel
theorem sg1_1_7 : sigsOKR 1 SA1 448 512 = true := by decide +kernel
end WinKU.Shared
