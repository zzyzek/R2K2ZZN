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
theorem fall_2 : finalSigOKL 6 6 UB36_2.1 UB36_2.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_2 : finalSigOK 6 6 (none) UB36_2.1 UB36_2.2 SA0 NS0 = true :=
  finalSigOKL_get fall_2 0 (by decide)
theorem fsig1_2 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_2.1 UB36_2.2 SA1 NS1 = true :=
  finalSigOKL_get fall_2 1 (by decide)
theorem fsig2_2 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_2.1 UB36_2.2 SA2 NS2 = true :=
  finalSigOKL_get fall_2 2 (by decide)
theorem fsig3_2 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_2.1 UB36_2.2 SA3 NS3 = true :=
  finalSigOKL_get fall_2 3 (by decide)
theorem fsig4_2 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_2.1 UB36_2.2 SA4 NS4 = true :=
  finalSigOKL_get fall_2 4 (by decide)
theorem fall_18 : finalSigOKL 6 6 UB36_18.1 UB36_18.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_18 : finalSigOK 6 6 (none) UB36_18.1 UB36_18.2 SA0 NS0 = true :=
  finalSigOKL_get fall_18 0 (by decide)
theorem fsig1_18 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_18.1 UB36_18.2 SA1 NS1 = true :=
  finalSigOKL_get fall_18 1 (by decide)
theorem fsig2_18 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_18.1 UB36_18.2 SA2 NS2 = true :=
  finalSigOKL_get fall_18 2 (by decide)
theorem fsig3_18 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_18.1 UB36_18.2 SA3 NS3 = true :=
  finalSigOKL_get fall_18 3 (by decide)
theorem fsig4_18 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_18.1 UB36_18.2 SA4 NS4 = true :=
  finalSigOKL_get fall_18 4 (by decide)
theorem fall_34 : finalSigOKL 6 6 UB36_34.1 UB36_34.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_34 : finalSigOK 6 6 (none) UB36_34.1 UB36_34.2 SA0 NS0 = true :=
  finalSigOKL_get fall_34 0 (by decide)
theorem fsig1_34 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_34.1 UB36_34.2 SA1 NS1 = true :=
  finalSigOKL_get fall_34 1 (by decide)
theorem fsig2_34 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_34.1 UB36_34.2 SA2 NS2 = true :=
  finalSigOKL_get fall_34 2 (by decide)
theorem fsig3_34 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_34.1 UB36_34.2 SA3 NS3 = true :=
  finalSigOKL_get fall_34 3 (by decide)
theorem fsig4_34 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_34.1 UB36_34.2 SA4 NS4 = true :=
  finalSigOKL_get fall_34 4 (by decide)
theorem fall_50 : finalSigOKL 6 6 UB36_50.1 UB36_50.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_50 : finalSigOK 6 6 (none) UB36_50.1 UB36_50.2 SA0 NS0 = true :=
  finalSigOKL_get fall_50 0 (by decide)
theorem fsig1_50 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_50.1 UB36_50.2 SA1 NS1 = true :=
  finalSigOKL_get fall_50 1 (by decide)
theorem fsig2_50 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_50.1 UB36_50.2 SA2 NS2 = true :=
  finalSigOKL_get fall_50 2 (by decide)
theorem fsig3_50 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_50.1 UB36_50.2 SA3 NS3 = true :=
  finalSigOKL_get fall_50 3 (by decide)
theorem fsig4_50 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_50.1 UB36_50.2 SA4 NS4 = true :=
  finalSigOKL_get fall_50 4 (by decide)
theorem fall_66 : finalSigOKL 6 6 UB36_66.1 UB36_66.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_66 : finalSigOK 6 6 (none) UB36_66.1 UB36_66.2 SA0 NS0 = true :=
  finalSigOKL_get fall_66 0 (by decide)
theorem fsig1_66 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_66.1 UB36_66.2 SA1 NS1 = true :=
  finalSigOKL_get fall_66 1 (by decide)
theorem fsig2_66 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_66.1 UB36_66.2 SA2 NS2 = true :=
  finalSigOKL_get fall_66 2 (by decide)
theorem fsig3_66 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_66.1 UB36_66.2 SA3 NS3 = true :=
  finalSigOKL_get fall_66 3 (by decide)
theorem fsig4_66 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_66.1 UB36_66.2 SA4 NS4 = true :=
  finalSigOKL_get fall_66 4 (by decide)
theorem fall_82 : finalSigOKL 6 6 UB36_82.1 UB36_82.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_82 : finalSigOK 6 6 (none) UB36_82.1 UB36_82.2 SA0 NS0 = true :=
  finalSigOKL_get fall_82 0 (by decide)
theorem fsig1_82 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_82.1 UB36_82.2 SA1 NS1 = true :=
  finalSigOKL_get fall_82 1 (by decide)
theorem fsig2_82 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_82.1 UB36_82.2 SA2 NS2 = true :=
  finalSigOKL_get fall_82 2 (by decide)
theorem fsig3_82 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_82.1 UB36_82.2 SA3 NS3 = true :=
  finalSigOKL_get fall_82 3 (by decide)
theorem fsig4_82 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_82.1 UB36_82.2 SA4 NS4 = true :=
  finalSigOKL_get fall_82 4 (by decide)
theorem fall_98 : finalSigOKL 6 6 UB36_98.1 UB36_98.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_98 : finalSigOK 6 6 (none) UB36_98.1 UB36_98.2 SA0 NS0 = true :=
  finalSigOKL_get fall_98 0 (by decide)
theorem fsig1_98 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_98.1 UB36_98.2 SA1 NS1 = true :=
  finalSigOKL_get fall_98 1 (by decide)
theorem fsig2_98 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_98.1 UB36_98.2 SA2 NS2 = true :=
  finalSigOKL_get fall_98 2 (by decide)
theorem fsig3_98 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_98.1 UB36_98.2 SA3 NS3 = true :=
  finalSigOKL_get fall_98 3 (by decide)
theorem fsig4_98 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_98.1 UB36_98.2 SA4 NS4 = true :=
  finalSigOKL_get fall_98 4 (by decide)
theorem fall_114 : finalSigOKL 6 6 UB36_114.1 UB36_114.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_114 : finalSigOK 6 6 (none) UB36_114.1 UB36_114.2 SA0 NS0 = true :=
  finalSigOKL_get fall_114 0 (by decide)
theorem fsig1_114 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_114.1 UB36_114.2 SA1 NS1 = true :=
  finalSigOKL_get fall_114 1 (by decide)
theorem fsig2_114 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_114.1 UB36_114.2 SA2 NS2 = true :=
  finalSigOKL_get fall_114 2 (by decide)
theorem fsig3_114 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_114.1 UB36_114.2 SA3 NS3 = true :=
  finalSigOKL_get fall_114 3 (by decide)
theorem fsig4_114 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_114.1 UB36_114.2 SA4 NS4 = true :=
  finalSigOKL_get fall_114 4 (by decide)
theorem sg0_0_10 : sigsOKR 0 SA0 640 704 = true := by decide +kernel
theorem sg0_1_0 : sigsOKR 0 SA1 0 64 = true := by decide +kernel
theorem sg0_2_3 : sigsOKR 0 SA2 192 256 = true := by decide +kernel
theorem sg0_3_6 : sigsOKR 0 SA3 384 448 = true := by decide +kernel
theorem sg0_4_4 : sigsOKR 0 SA4 256 320 = true := by decide +kernel
theorem sg1_2_2 : sigsOKR 1 SA2 128 192 = true := by decide +kernel
theorem sg1_3_5 : sigsOKR 1 SA3 320 384 = true := by decide +kernel
theorem sg1_4_3 : sigsOKR 1 SA4 192 256 = true := by decide +kernel
theorem sg1_1_1 : sigsOKR 1 SA1 64 128 = true := by decide +kernel
end WinKU.Shared
