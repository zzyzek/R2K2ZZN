/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import WinKU.Shared.D
public import ZZN.WinK.SigL
-- Build order only (at most 2 certificate modules build at once).
import WinKU.Shared.G4

@[expose] public section

set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_11 : finalSigOKL 6 6 UB36_11.1 UB36_11.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_11 : finalSigOK 6 6 (none) UB36_11.1 UB36_11.2 SA0 NS0 = true :=
  finalSigOKL_get fall_11 0 (by decide)
theorem fsig1_11 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_11.1 UB36_11.2 SA1 NS1 = true :=
  finalSigOKL_get fall_11 1 (by decide)
theorem fsig2_11 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_11.1 UB36_11.2 SA2 NS2 = true :=
  finalSigOKL_get fall_11 2 (by decide)
theorem fsig3_11 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_11.1 UB36_11.2 SA3 NS3 = true :=
  finalSigOKL_get fall_11 3 (by decide)
theorem fsig4_11 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_11.1 UB36_11.2 SA4 NS4 = true :=
  finalSigOKL_get fall_11 4 (by decide)
theorem fall_27 : finalSigOKL 6 6 UB36_27.1 UB36_27.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_27 : finalSigOK 6 6 (none) UB36_27.1 UB36_27.2 SA0 NS0 = true :=
  finalSigOKL_get fall_27 0 (by decide)
theorem fsig1_27 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_27.1 UB36_27.2 SA1 NS1 = true :=
  finalSigOKL_get fall_27 1 (by decide)
theorem fsig2_27 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_27.1 UB36_27.2 SA2 NS2 = true :=
  finalSigOKL_get fall_27 2 (by decide)
theorem fsig3_27 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_27.1 UB36_27.2 SA3 NS3 = true :=
  finalSigOKL_get fall_27 3 (by decide)
theorem fsig4_27 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_27.1 UB36_27.2 SA4 NS4 = true :=
  finalSigOKL_get fall_27 4 (by decide)
theorem fall_43 : finalSigOKL 6 6 UB36_43.1 UB36_43.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_43 : finalSigOK 6 6 (none) UB36_43.1 UB36_43.2 SA0 NS0 = true :=
  finalSigOKL_get fall_43 0 (by decide)
theorem fsig1_43 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_43.1 UB36_43.2 SA1 NS1 = true :=
  finalSigOKL_get fall_43 1 (by decide)
theorem fsig2_43 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_43.1 UB36_43.2 SA2 NS2 = true :=
  finalSigOKL_get fall_43 2 (by decide)
theorem fsig3_43 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_43.1 UB36_43.2 SA3 NS3 = true :=
  finalSigOKL_get fall_43 3 (by decide)
theorem fsig4_43 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_43.1 UB36_43.2 SA4 NS4 = true :=
  finalSigOKL_get fall_43 4 (by decide)
theorem fall_59 : finalSigOKL 6 6 UB36_59.1 UB36_59.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_59 : finalSigOK 6 6 (none) UB36_59.1 UB36_59.2 SA0 NS0 = true :=
  finalSigOKL_get fall_59 0 (by decide)
theorem fsig1_59 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_59.1 UB36_59.2 SA1 NS1 = true :=
  finalSigOKL_get fall_59 1 (by decide)
theorem fsig2_59 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_59.1 UB36_59.2 SA2 NS2 = true :=
  finalSigOKL_get fall_59 2 (by decide)
theorem fsig3_59 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_59.1 UB36_59.2 SA3 NS3 = true :=
  finalSigOKL_get fall_59 3 (by decide)
theorem fsig4_59 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_59.1 UB36_59.2 SA4 NS4 = true :=
  finalSigOKL_get fall_59 4 (by decide)
theorem fall_75 : finalSigOKL 6 6 UB36_75.1 UB36_75.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_75 : finalSigOK 6 6 (none) UB36_75.1 UB36_75.2 SA0 NS0 = true :=
  finalSigOKL_get fall_75 0 (by decide)
theorem fsig1_75 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_75.1 UB36_75.2 SA1 NS1 = true :=
  finalSigOKL_get fall_75 1 (by decide)
theorem fsig2_75 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_75.1 UB36_75.2 SA2 NS2 = true :=
  finalSigOKL_get fall_75 2 (by decide)
theorem fsig3_75 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_75.1 UB36_75.2 SA3 NS3 = true :=
  finalSigOKL_get fall_75 3 (by decide)
theorem fsig4_75 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_75.1 UB36_75.2 SA4 NS4 = true :=
  finalSigOKL_get fall_75 4 (by decide)
theorem fall_91 : finalSigOKL 6 6 UB36_91.1 UB36_91.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_91 : finalSigOK 6 6 (none) UB36_91.1 UB36_91.2 SA0 NS0 = true :=
  finalSigOKL_get fall_91 0 (by decide)
theorem fsig1_91 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_91.1 UB36_91.2 SA1 NS1 = true :=
  finalSigOKL_get fall_91 1 (by decide)
theorem fsig2_91 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_91.1 UB36_91.2 SA2 NS2 = true :=
  finalSigOKL_get fall_91 2 (by decide)
theorem fsig3_91 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_91.1 UB36_91.2 SA3 NS3 = true :=
  finalSigOKL_get fall_91 3 (by decide)
theorem fsig4_91 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_91.1 UB36_91.2 SA4 NS4 = true :=
  finalSigOKL_get fall_91 4 (by decide)
theorem fall_107 : finalSigOKL 6 6 UB36_107.1 UB36_107.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_107 : finalSigOK 6 6 (none) UB36_107.1 UB36_107.2 SA0 NS0 = true :=
  finalSigOKL_get fall_107 0 (by decide)
theorem fsig1_107 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_107.1 UB36_107.2 SA1 NS1 = true :=
  finalSigOKL_get fall_107 1 (by decide)
theorem fsig2_107 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_107.1 UB36_107.2 SA2 NS2 = true :=
  finalSigOKL_get fall_107 2 (by decide)
theorem fsig3_107 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_107.1 UB36_107.2 SA3 NS3 = true :=
  finalSigOKL_get fall_107 3 (by decide)
theorem fsig4_107 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_107.1 UB36_107.2 SA4 NS4 = true :=
  finalSigOKL_get fall_107 4 (by decide)
theorem sg0_0_3 : sigsOKR 0 SA0 192 256 = true := by decide +kernel
theorem sg1_0_6 : sigsOKR 1 SA0 384 448 = true := by decide +kernel
theorem sg0_1_9 : sigsOKR 0 SA1 576 640 = true := by decide +kernel
theorem sg0_2_12 : sigsOKR 0 SA2 768 796 = true := by decide +kernel
theorem sg0_3_15 : sigsOKR 0 SA3 960 1024 = true := by decide +kernel
theorem sg0_4_13 : sigsOKR 0 SA4 832 896 = true := by decide +kernel
theorem sg1_2_11 : sigsOKR 1 SA2 704 768 = true := by decide +kernel
theorem sg1_3_14 : sigsOKR 1 SA3 896 960 = true := by decide +kernel
theorem sg1_4_12 : sigsOKR 1 SA4 768 832 = true := by decide +kernel
theorem sg1_1_10 : sigsOKR 1 SA1 640 704 = true := by decide +kernel
end WinKU.Shared
