/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import WinKU.Shared.D
public import ZZN.WinK.SigL
-- Build order only (at most 2 certificate modules build at once).
import BoxKGen.N12x12.S9

@[expose] public section

set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_9 : finalSigOKL 6 6 UB36_9.1 UB36_9.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_9 : finalSigOK 6 6 (none) UB36_9.1 UB36_9.2 SA0 NS0 = true :=
  finalSigOKL_get fall_9 0 (by decide)
theorem fsig1_9 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_9.1 UB36_9.2 SA1 NS1 = true :=
  finalSigOKL_get fall_9 1 (by decide)
theorem fsig2_9 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_9.1 UB36_9.2 SA2 NS2 = true :=
  finalSigOKL_get fall_9 2 (by decide)
theorem fsig3_9 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_9.1 UB36_9.2 SA3 NS3 = true :=
  finalSigOKL_get fall_9 3 (by decide)
theorem fsig4_9 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_9.1 UB36_9.2 SA4 NS4 = true :=
  finalSigOKL_get fall_9 4 (by decide)
theorem fall_25 : finalSigOKL 6 6 UB36_25.1 UB36_25.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_25 : finalSigOK 6 6 (none) UB36_25.1 UB36_25.2 SA0 NS0 = true :=
  finalSigOKL_get fall_25 0 (by decide)
theorem fsig1_25 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_25.1 UB36_25.2 SA1 NS1 = true :=
  finalSigOKL_get fall_25 1 (by decide)
theorem fsig2_25 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_25.1 UB36_25.2 SA2 NS2 = true :=
  finalSigOKL_get fall_25 2 (by decide)
theorem fsig3_25 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_25.1 UB36_25.2 SA3 NS3 = true :=
  finalSigOKL_get fall_25 3 (by decide)
theorem fsig4_25 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_25.1 UB36_25.2 SA4 NS4 = true :=
  finalSigOKL_get fall_25 4 (by decide)
theorem fall_41 : finalSigOKL 6 6 UB36_41.1 UB36_41.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_41 : finalSigOK 6 6 (none) UB36_41.1 UB36_41.2 SA0 NS0 = true :=
  finalSigOKL_get fall_41 0 (by decide)
theorem fsig1_41 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_41.1 UB36_41.2 SA1 NS1 = true :=
  finalSigOKL_get fall_41 1 (by decide)
theorem fsig2_41 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_41.1 UB36_41.2 SA2 NS2 = true :=
  finalSigOKL_get fall_41 2 (by decide)
theorem fsig3_41 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_41.1 UB36_41.2 SA3 NS3 = true :=
  finalSigOKL_get fall_41 3 (by decide)
theorem fsig4_41 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_41.1 UB36_41.2 SA4 NS4 = true :=
  finalSigOKL_get fall_41 4 (by decide)
theorem fall_57 : finalSigOKL 6 6 UB36_57.1 UB36_57.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_57 : finalSigOK 6 6 (none) UB36_57.1 UB36_57.2 SA0 NS0 = true :=
  finalSigOKL_get fall_57 0 (by decide)
theorem fsig1_57 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_57.1 UB36_57.2 SA1 NS1 = true :=
  finalSigOKL_get fall_57 1 (by decide)
theorem fsig2_57 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_57.1 UB36_57.2 SA2 NS2 = true :=
  finalSigOKL_get fall_57 2 (by decide)
theorem fsig3_57 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_57.1 UB36_57.2 SA3 NS3 = true :=
  finalSigOKL_get fall_57 3 (by decide)
theorem fsig4_57 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_57.1 UB36_57.2 SA4 NS4 = true :=
  finalSigOKL_get fall_57 4 (by decide)
theorem fall_73 : finalSigOKL 6 6 UB36_73.1 UB36_73.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_73 : finalSigOK 6 6 (none) UB36_73.1 UB36_73.2 SA0 NS0 = true :=
  finalSigOKL_get fall_73 0 (by decide)
theorem fsig1_73 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_73.1 UB36_73.2 SA1 NS1 = true :=
  finalSigOKL_get fall_73 1 (by decide)
theorem fsig2_73 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_73.1 UB36_73.2 SA2 NS2 = true :=
  finalSigOKL_get fall_73 2 (by decide)
theorem fsig3_73 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_73.1 UB36_73.2 SA3 NS3 = true :=
  finalSigOKL_get fall_73 3 (by decide)
theorem fsig4_73 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_73.1 UB36_73.2 SA4 NS4 = true :=
  finalSigOKL_get fall_73 4 (by decide)
theorem fall_89 : finalSigOKL 6 6 UB36_89.1 UB36_89.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_89 : finalSigOK 6 6 (none) UB36_89.1 UB36_89.2 SA0 NS0 = true :=
  finalSigOKL_get fall_89 0 (by decide)
theorem fsig1_89 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_89.1 UB36_89.2 SA1 NS1 = true :=
  finalSigOKL_get fall_89 1 (by decide)
theorem fsig2_89 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_89.1 UB36_89.2 SA2 NS2 = true :=
  finalSigOKL_get fall_89 2 (by decide)
theorem fsig3_89 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_89.1 UB36_89.2 SA3 NS3 = true :=
  finalSigOKL_get fall_89 3 (by decide)
theorem fsig4_89 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_89.1 UB36_89.2 SA4 NS4 = true :=
  finalSigOKL_get fall_89 4 (by decide)
theorem fall_105 : finalSigOKL 6 6 UB36_105.1 UB36_105.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_105 : finalSigOK 6 6 (none) UB36_105.1 UB36_105.2 SA0 NS0 = true :=
  finalSigOKL_get fall_105 0 (by decide)
theorem fsig1_105 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_105.1 UB36_105.2 SA1 NS1 = true :=
  finalSigOKL_get fall_105 1 (by decide)
theorem fsig2_105 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_105.1 UB36_105.2 SA2 NS2 = true :=
  finalSigOKL_get fall_105 2 (by decide)
theorem fsig3_105 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_105.1 UB36_105.2 SA3 NS3 = true :=
  finalSigOKL_get fall_105 3 (by decide)
theorem fsig4_105 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_105.1 UB36_105.2 SA4 NS4 = true :=
  finalSigOKL_get fall_105 4 (by decide)
theorem sg0_0_1 : sigsOKR 0 SA0 64 128 = true := by decide +kernel
theorem sg1_0_4 : sigsOKR 1 SA0 256 320 = true := by decide +kernel
theorem sg0_1_7 : sigsOKR 0 SA1 448 512 = true := by decide +kernel
theorem sg0_2_10 : sigsOKR 0 SA2 640 704 = true := by decide +kernel
theorem sg0_3_13 : sigsOKR 0 SA3 832 896 = true := by decide +kernel
theorem sg0_4_11 : sigsOKR 0 SA4 704 768 = true := by decide +kernel
theorem sg1_2_9 : sigsOKR 1 SA2 576 640 = true := by decide +kernel
theorem sg1_3_12 : sigsOKR 1 SA3 768 832 = true := by decide +kernel
theorem sg1_4_10 : sigsOKR 1 SA4 640 704 = true := by decide +kernel
theorem sg1_1_8 : sigsOKR 1 SA1 512 576 = true := by decide +kernel
end WinKU.Shared
