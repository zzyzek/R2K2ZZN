/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import WinKU.Shared.D
public import ZZN.WinK.SigL
-- Build order only (at most 2 certificate modules build at once).
import BoxKGen.N12x15.S4

@[expose] public section

set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_13 : finalSigOKL 6 6 UB36_13.1 UB36_13.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_13 : finalSigOK 6 6 (none) UB36_13.1 UB36_13.2 SA0 NS0 = true :=
  finalSigOKL_get fall_13 0 (by decide)
theorem fsig1_13 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_13.1 UB36_13.2 SA1 NS1 = true :=
  finalSigOKL_get fall_13 1 (by decide)
theorem fsig2_13 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_13.1 UB36_13.2 SA2 NS2 = true :=
  finalSigOKL_get fall_13 2 (by decide)
theorem fsig3_13 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_13.1 UB36_13.2 SA3 NS3 = true :=
  finalSigOKL_get fall_13 3 (by decide)
theorem fsig4_13 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_13.1 UB36_13.2 SA4 NS4 = true :=
  finalSigOKL_get fall_13 4 (by decide)
theorem fall_29 : finalSigOKL 6 6 UB36_29.1 UB36_29.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_29 : finalSigOK 6 6 (none) UB36_29.1 UB36_29.2 SA0 NS0 = true :=
  finalSigOKL_get fall_29 0 (by decide)
theorem fsig1_29 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_29.1 UB36_29.2 SA1 NS1 = true :=
  finalSigOKL_get fall_29 1 (by decide)
theorem fsig2_29 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_29.1 UB36_29.2 SA2 NS2 = true :=
  finalSigOKL_get fall_29 2 (by decide)
theorem fsig3_29 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_29.1 UB36_29.2 SA3 NS3 = true :=
  finalSigOKL_get fall_29 3 (by decide)
theorem fsig4_29 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_29.1 UB36_29.2 SA4 NS4 = true :=
  finalSigOKL_get fall_29 4 (by decide)
theorem fall_45 : finalSigOKL 6 6 UB36_45.1 UB36_45.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_45 : finalSigOK 6 6 (none) UB36_45.1 UB36_45.2 SA0 NS0 = true :=
  finalSigOKL_get fall_45 0 (by decide)
theorem fsig1_45 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_45.1 UB36_45.2 SA1 NS1 = true :=
  finalSigOKL_get fall_45 1 (by decide)
theorem fsig2_45 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_45.1 UB36_45.2 SA2 NS2 = true :=
  finalSigOKL_get fall_45 2 (by decide)
theorem fsig3_45 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_45.1 UB36_45.2 SA3 NS3 = true :=
  finalSigOKL_get fall_45 3 (by decide)
theorem fsig4_45 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_45.1 UB36_45.2 SA4 NS4 = true :=
  finalSigOKL_get fall_45 4 (by decide)
theorem fall_61 : finalSigOKL 6 6 UB36_61.1 UB36_61.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_61 : finalSigOK 6 6 (none) UB36_61.1 UB36_61.2 SA0 NS0 = true :=
  finalSigOKL_get fall_61 0 (by decide)
theorem fsig1_61 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_61.1 UB36_61.2 SA1 NS1 = true :=
  finalSigOKL_get fall_61 1 (by decide)
theorem fsig2_61 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_61.1 UB36_61.2 SA2 NS2 = true :=
  finalSigOKL_get fall_61 2 (by decide)
theorem fsig3_61 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_61.1 UB36_61.2 SA3 NS3 = true :=
  finalSigOKL_get fall_61 3 (by decide)
theorem fsig4_61 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_61.1 UB36_61.2 SA4 NS4 = true :=
  finalSigOKL_get fall_61 4 (by decide)
theorem fall_77 : finalSigOKL 6 6 UB36_77.1 UB36_77.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_77 : finalSigOK 6 6 (none) UB36_77.1 UB36_77.2 SA0 NS0 = true :=
  finalSigOKL_get fall_77 0 (by decide)
theorem fsig1_77 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_77.1 UB36_77.2 SA1 NS1 = true :=
  finalSigOKL_get fall_77 1 (by decide)
theorem fsig2_77 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_77.1 UB36_77.2 SA2 NS2 = true :=
  finalSigOKL_get fall_77 2 (by decide)
theorem fsig3_77 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_77.1 UB36_77.2 SA3 NS3 = true :=
  finalSigOKL_get fall_77 3 (by decide)
theorem fsig4_77 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_77.1 UB36_77.2 SA4 NS4 = true :=
  finalSigOKL_get fall_77 4 (by decide)
theorem fall_93 : finalSigOKL 6 6 UB36_93.1 UB36_93.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_93 : finalSigOK 6 6 (none) UB36_93.1 UB36_93.2 SA0 NS0 = true :=
  finalSigOKL_get fall_93 0 (by decide)
theorem fsig1_93 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_93.1 UB36_93.2 SA1 NS1 = true :=
  finalSigOKL_get fall_93 1 (by decide)
theorem fsig2_93 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_93.1 UB36_93.2 SA2 NS2 = true :=
  finalSigOKL_get fall_93 2 (by decide)
theorem fsig3_93 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_93.1 UB36_93.2 SA3 NS3 = true :=
  finalSigOKL_get fall_93 3 (by decide)
theorem fsig4_93 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_93.1 UB36_93.2 SA4 NS4 = true :=
  finalSigOKL_get fall_93 4 (by decide)
theorem fall_109 : finalSigOKL 6 6 UB36_109.1 UB36_109.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_109 : finalSigOK 6 6 (none) UB36_109.1 UB36_109.2 SA0 NS0 = true :=
  finalSigOKL_get fall_109 0 (by decide)
theorem fsig1_109 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_109.1 UB36_109.2 SA1 NS1 = true :=
  finalSigOKL_get fall_109 1 (by decide)
theorem fsig2_109 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_109.1 UB36_109.2 SA2 NS2 = true :=
  finalSigOKL_get fall_109 2 (by decide)
theorem fsig3_109 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_109.1 UB36_109.2 SA3 NS3 = true :=
  finalSigOKL_get fall_109 3 (by decide)
theorem fsig4_109 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_109.1 UB36_109.2 SA4 NS4 = true :=
  finalSigOKL_get fall_109 4 (by decide)
theorem sg0_0_5 : sigsOKR 0 SA0 320 384 = true := by decide +kernel
theorem sg1_0_8 : sigsOKR 1 SA0 512 576 = true := by decide +kernel
theorem sg0_1_11 : sigsOKR 0 SA1 704 768 = true := by decide +kernel
theorem sg0_3_1 : sigsOKR 0 SA3 64 128 = true := by decide +kernel
theorem sg0_3_17 : sigsOKR 0 SA3 1088 1146 = true := by decide +kernel
theorem sg0_4_15 : sigsOKR 0 SA4 960 1024 = true := by decide +kernel
theorem sg1_3_0 : sigsOKR 1 SA3 0 64 = true := by decide +kernel
theorem sg1_3_16 : sigsOKR 1 SA3 1024 1088 = true := by decide +kernel
theorem sg1_4_14 : sigsOKR 1 SA4 896 960 = true := by decide +kernel
theorem sg1_1_12 : sigsOKR 1 SA1 768 796 = true := by decide +kernel
end WinKU.Shared
