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
theorem fall_4 : finalSigOKL 6 6 UB36_4.1 UB36_4.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_4 : finalSigOK 6 6 (none) UB36_4.1 UB36_4.2 SA0 NS0 = true :=
  finalSigOKL_get fall_4 0 (by decide)
theorem fsig1_4 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_4.1 UB36_4.2 SA1 NS1 = true :=
  finalSigOKL_get fall_4 1 (by decide)
theorem fsig2_4 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_4.1 UB36_4.2 SA2 NS2 = true :=
  finalSigOKL_get fall_4 2 (by decide)
theorem fsig3_4 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_4.1 UB36_4.2 SA3 NS3 = true :=
  finalSigOKL_get fall_4 3 (by decide)
theorem fsig4_4 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_4.1 UB36_4.2 SA4 NS4 = true :=
  finalSigOKL_get fall_4 4 (by decide)
theorem fall_20 : finalSigOKL 6 6 UB36_20.1 UB36_20.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_20 : finalSigOK 6 6 (none) UB36_20.1 UB36_20.2 SA0 NS0 = true :=
  finalSigOKL_get fall_20 0 (by decide)
theorem fsig1_20 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_20.1 UB36_20.2 SA1 NS1 = true :=
  finalSigOKL_get fall_20 1 (by decide)
theorem fsig2_20 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_20.1 UB36_20.2 SA2 NS2 = true :=
  finalSigOKL_get fall_20 2 (by decide)
theorem fsig3_20 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_20.1 UB36_20.2 SA3 NS3 = true :=
  finalSigOKL_get fall_20 3 (by decide)
theorem fsig4_20 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_20.1 UB36_20.2 SA4 NS4 = true :=
  finalSigOKL_get fall_20 4 (by decide)
theorem fall_36 : finalSigOKL 6 6 UB36_36.1 UB36_36.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_36 : finalSigOK 6 6 (none) UB36_36.1 UB36_36.2 SA0 NS0 = true :=
  finalSigOKL_get fall_36 0 (by decide)
theorem fsig1_36 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_36.1 UB36_36.2 SA1 NS1 = true :=
  finalSigOKL_get fall_36 1 (by decide)
theorem fsig2_36 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_36.1 UB36_36.2 SA2 NS2 = true :=
  finalSigOKL_get fall_36 2 (by decide)
theorem fsig3_36 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_36.1 UB36_36.2 SA3 NS3 = true :=
  finalSigOKL_get fall_36 3 (by decide)
theorem fsig4_36 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_36.1 UB36_36.2 SA4 NS4 = true :=
  finalSigOKL_get fall_36 4 (by decide)
theorem fall_52 : finalSigOKL 6 6 UB36_52.1 UB36_52.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_52 : finalSigOK 6 6 (none) UB36_52.1 UB36_52.2 SA0 NS0 = true :=
  finalSigOKL_get fall_52 0 (by decide)
theorem fsig1_52 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_52.1 UB36_52.2 SA1 NS1 = true :=
  finalSigOKL_get fall_52 1 (by decide)
theorem fsig2_52 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_52.1 UB36_52.2 SA2 NS2 = true :=
  finalSigOKL_get fall_52 2 (by decide)
theorem fsig3_52 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_52.1 UB36_52.2 SA3 NS3 = true :=
  finalSigOKL_get fall_52 3 (by decide)
theorem fsig4_52 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_52.1 UB36_52.2 SA4 NS4 = true :=
  finalSigOKL_get fall_52 4 (by decide)
theorem fall_68 : finalSigOKL 6 6 UB36_68.1 UB36_68.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_68 : finalSigOK 6 6 (none) UB36_68.1 UB36_68.2 SA0 NS0 = true :=
  finalSigOKL_get fall_68 0 (by decide)
theorem fsig1_68 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_68.1 UB36_68.2 SA1 NS1 = true :=
  finalSigOKL_get fall_68 1 (by decide)
theorem fsig2_68 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_68.1 UB36_68.2 SA2 NS2 = true :=
  finalSigOKL_get fall_68 2 (by decide)
theorem fsig3_68 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_68.1 UB36_68.2 SA3 NS3 = true :=
  finalSigOKL_get fall_68 3 (by decide)
theorem fsig4_68 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_68.1 UB36_68.2 SA4 NS4 = true :=
  finalSigOKL_get fall_68 4 (by decide)
theorem fall_84 : finalSigOKL 6 6 UB36_84.1 UB36_84.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_84 : finalSigOK 6 6 (none) UB36_84.1 UB36_84.2 SA0 NS0 = true :=
  finalSigOKL_get fall_84 0 (by decide)
theorem fsig1_84 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_84.1 UB36_84.2 SA1 NS1 = true :=
  finalSigOKL_get fall_84 1 (by decide)
theorem fsig2_84 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_84.1 UB36_84.2 SA2 NS2 = true :=
  finalSigOKL_get fall_84 2 (by decide)
theorem fsig3_84 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_84.1 UB36_84.2 SA3 NS3 = true :=
  finalSigOKL_get fall_84 3 (by decide)
theorem fsig4_84 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_84.1 UB36_84.2 SA4 NS4 = true :=
  finalSigOKL_get fall_84 4 (by decide)
theorem fall_100 : finalSigOKL 6 6 UB36_100.1 UB36_100.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_100 : finalSigOK 6 6 (none) UB36_100.1 UB36_100.2 SA0 NS0 = true :=
  finalSigOKL_get fall_100 0 (by decide)
theorem fsig1_100 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_100.1 UB36_100.2 SA1 NS1 = true :=
  finalSigOKL_get fall_100 1 (by decide)
theorem fsig2_100 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_100.1 UB36_100.2 SA2 NS2 = true :=
  finalSigOKL_get fall_100 2 (by decide)
theorem fsig3_100 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_100.1 UB36_100.2 SA3 NS3 = true :=
  finalSigOKL_get fall_100 3 (by decide)
theorem fsig4_100 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_100.1 UB36_100.2 SA4 NS4 = true :=
  finalSigOKL_get fall_100 4 (by decide)
theorem fall_116 : finalSigOKL 6 6 UB36_116.1 UB36_116.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_116 : finalSigOK 6 6 (none) UB36_116.1 UB36_116.2 SA0 NS0 = true :=
  finalSigOKL_get fall_116 0 (by decide)
theorem fsig1_116 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_116.1 UB36_116.2 SA1 NS1 = true :=
  finalSigOKL_get fall_116 1 (by decide)
theorem fsig2_116 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_116.1 UB36_116.2 SA2 NS2 = true :=
  finalSigOKL_get fall_116 2 (by decide)
theorem fsig3_116 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_116.1 UB36_116.2 SA3 NS3 = true :=
  finalSigOKL_get fall_116 3 (by decide)
theorem fsig4_116 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_116.1 UB36_116.2 SA4 NS4 = true :=
  finalSigOKL_get fall_116 4 (by decide)
theorem sg0_0_12 : sigsOKR 0 SA0 768 796 = true := by decide +kernel
theorem sg0_1_2 : sigsOKR 0 SA1 128 192 = true := by decide +kernel
theorem sg0_2_5 : sigsOKR 0 SA2 320 384 = true := by decide +kernel
theorem sg0_3_8 : sigsOKR 0 SA3 512 576 = true := by decide +kernel
theorem sg0_4_6 : sigsOKR 0 SA4 384 448 = true := by decide +kernel
theorem sg1_2_4 : sigsOKR 1 SA2 256 320 = true := by decide +kernel
theorem sg1_3_7 : sigsOKR 1 SA3 448 512 = true := by decide +kernel
theorem sg1_4_5 : sigsOKR 1 SA4 320 384 = true := by decide +kernel
theorem sg1_1_3 : sigsOKR 1 SA1 192 256 = true := by decide +kernel
end WinKU.Shared
