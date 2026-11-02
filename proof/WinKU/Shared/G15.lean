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
theorem fall_15 : finalSigOKL 6 6 UB36_15.1 UB36_15.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_15 : finalSigOK 6 6 (none) UB36_15.1 UB36_15.2 SA0 NS0 = true :=
  finalSigOKL_get fall_15 0 (by decide)
theorem fsig1_15 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_15.1 UB36_15.2 SA1 NS1 = true :=
  finalSigOKL_get fall_15 1 (by decide)
theorem fsig2_15 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_15.1 UB36_15.2 SA2 NS2 = true :=
  finalSigOKL_get fall_15 2 (by decide)
theorem fsig3_15 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_15.1 UB36_15.2 SA3 NS3 = true :=
  finalSigOKL_get fall_15 3 (by decide)
theorem fsig4_15 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_15.1 UB36_15.2 SA4 NS4 = true :=
  finalSigOKL_get fall_15 4 (by decide)
theorem fall_31 : finalSigOKL 6 6 UB36_31.1 UB36_31.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_31 : finalSigOK 6 6 (none) UB36_31.1 UB36_31.2 SA0 NS0 = true :=
  finalSigOKL_get fall_31 0 (by decide)
theorem fsig1_31 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_31.1 UB36_31.2 SA1 NS1 = true :=
  finalSigOKL_get fall_31 1 (by decide)
theorem fsig2_31 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_31.1 UB36_31.2 SA2 NS2 = true :=
  finalSigOKL_get fall_31 2 (by decide)
theorem fsig3_31 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_31.1 UB36_31.2 SA3 NS3 = true :=
  finalSigOKL_get fall_31 3 (by decide)
theorem fsig4_31 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_31.1 UB36_31.2 SA4 NS4 = true :=
  finalSigOKL_get fall_31 4 (by decide)
theorem fall_47 : finalSigOKL 6 6 UB36_47.1 UB36_47.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_47 : finalSigOK 6 6 (none) UB36_47.1 UB36_47.2 SA0 NS0 = true :=
  finalSigOKL_get fall_47 0 (by decide)
theorem fsig1_47 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_47.1 UB36_47.2 SA1 NS1 = true :=
  finalSigOKL_get fall_47 1 (by decide)
theorem fsig2_47 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_47.1 UB36_47.2 SA2 NS2 = true :=
  finalSigOKL_get fall_47 2 (by decide)
theorem fsig3_47 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_47.1 UB36_47.2 SA3 NS3 = true :=
  finalSigOKL_get fall_47 3 (by decide)
theorem fsig4_47 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_47.1 UB36_47.2 SA4 NS4 = true :=
  finalSigOKL_get fall_47 4 (by decide)
theorem fall_63 : finalSigOKL 6 6 UB36_63.1 UB36_63.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_63 : finalSigOK 6 6 (none) UB36_63.1 UB36_63.2 SA0 NS0 = true :=
  finalSigOKL_get fall_63 0 (by decide)
theorem fsig1_63 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_63.1 UB36_63.2 SA1 NS1 = true :=
  finalSigOKL_get fall_63 1 (by decide)
theorem fsig2_63 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_63.1 UB36_63.2 SA2 NS2 = true :=
  finalSigOKL_get fall_63 2 (by decide)
theorem fsig3_63 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_63.1 UB36_63.2 SA3 NS3 = true :=
  finalSigOKL_get fall_63 3 (by decide)
theorem fsig4_63 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_63.1 UB36_63.2 SA4 NS4 = true :=
  finalSigOKL_get fall_63 4 (by decide)
theorem fall_79 : finalSigOKL 6 6 UB36_79.1 UB36_79.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_79 : finalSigOK 6 6 (none) UB36_79.1 UB36_79.2 SA0 NS0 = true :=
  finalSigOKL_get fall_79 0 (by decide)
theorem fsig1_79 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_79.1 UB36_79.2 SA1 NS1 = true :=
  finalSigOKL_get fall_79 1 (by decide)
theorem fsig2_79 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_79.1 UB36_79.2 SA2 NS2 = true :=
  finalSigOKL_get fall_79 2 (by decide)
theorem fsig3_79 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_79.1 UB36_79.2 SA3 NS3 = true :=
  finalSigOKL_get fall_79 3 (by decide)
theorem fsig4_79 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_79.1 UB36_79.2 SA4 NS4 = true :=
  finalSigOKL_get fall_79 4 (by decide)
theorem fall_95 : finalSigOKL 6 6 UB36_95.1 UB36_95.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_95 : finalSigOK 6 6 (none) UB36_95.1 UB36_95.2 SA0 NS0 = true :=
  finalSigOKL_get fall_95 0 (by decide)
theorem fsig1_95 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_95.1 UB36_95.2 SA1 NS1 = true :=
  finalSigOKL_get fall_95 1 (by decide)
theorem fsig2_95 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_95.1 UB36_95.2 SA2 NS2 = true :=
  finalSigOKL_get fall_95 2 (by decide)
theorem fsig3_95 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_95.1 UB36_95.2 SA3 NS3 = true :=
  finalSigOKL_get fall_95 3 (by decide)
theorem fsig4_95 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_95.1 UB36_95.2 SA4 NS4 = true :=
  finalSigOKL_get fall_95 4 (by decide)
theorem fall_111 : finalSigOKL 6 6 UB36_111.1 UB36_111.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_111 : finalSigOK 6 6 (none) UB36_111.1 UB36_111.2 SA0 NS0 = true :=
  finalSigOKL_get fall_111 0 (by decide)
theorem fsig1_111 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_111.1 UB36_111.2 SA1 NS1 = true :=
  finalSigOKL_get fall_111 1 (by decide)
theorem fsig2_111 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_111.1 UB36_111.2 SA2 NS2 = true :=
  finalSigOKL_get fall_111 2 (by decide)
theorem fsig3_111 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_111.1 UB36_111.2 SA3 NS3 = true :=
  finalSigOKL_get fall_111 3 (by decide)
theorem fsig4_111 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_111.1 UB36_111.2 SA4 NS4 = true :=
  finalSigOKL_get fall_111 4 (by decide)
theorem sg0_0_7 : sigsOKR 0 SA0 448 512 = true := by decide +kernel
theorem sg1_0_10 : sigsOKR 1 SA0 640 704 = true := by decide +kernel
theorem sg0_2_0 : sigsOKR 0 SA2 0 64 = true := by decide +kernel
theorem sg0_3_3 : sigsOKR 0 SA3 192 256 = true := by decide +kernel
theorem sg0_4_1 : sigsOKR 0 SA4 64 128 = true := by decide +kernel
theorem sg0_4_17 : sigsOKR 0 SA4 1088 1148 = true := by decide +kernel
theorem sg1_3_2 : sigsOKR 1 SA3 128 192 = true := by decide +kernel
theorem sg1_4_0 : sigsOKR 1 SA4 0 64 = true := by decide +kernel
theorem sg1_4_16 : sigsOKR 1 SA4 1024 1088 = true := by decide +kernel
end WinKU.Shared
