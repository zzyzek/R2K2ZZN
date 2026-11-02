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
theorem fall_3 : finalSigOKL 6 6 UB36_3.1 UB36_3.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_3 : finalSigOK 6 6 (none) UB36_3.1 UB36_3.2 SA0 NS0 = true :=
  finalSigOKL_get fall_3 0 (by decide)
theorem fsig1_3 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_3.1 UB36_3.2 SA1 NS1 = true :=
  finalSigOKL_get fall_3 1 (by decide)
theorem fsig2_3 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_3.1 UB36_3.2 SA2 NS2 = true :=
  finalSigOKL_get fall_3 2 (by decide)
theorem fsig3_3 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_3.1 UB36_3.2 SA3 NS3 = true :=
  finalSigOKL_get fall_3 3 (by decide)
theorem fsig4_3 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_3.1 UB36_3.2 SA4 NS4 = true :=
  finalSigOKL_get fall_3 4 (by decide)
theorem fall_19 : finalSigOKL 6 6 UB36_19.1 UB36_19.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_19 : finalSigOK 6 6 (none) UB36_19.1 UB36_19.2 SA0 NS0 = true :=
  finalSigOKL_get fall_19 0 (by decide)
theorem fsig1_19 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_19.1 UB36_19.2 SA1 NS1 = true :=
  finalSigOKL_get fall_19 1 (by decide)
theorem fsig2_19 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_19.1 UB36_19.2 SA2 NS2 = true :=
  finalSigOKL_get fall_19 2 (by decide)
theorem fsig3_19 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_19.1 UB36_19.2 SA3 NS3 = true :=
  finalSigOKL_get fall_19 3 (by decide)
theorem fsig4_19 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_19.1 UB36_19.2 SA4 NS4 = true :=
  finalSigOKL_get fall_19 4 (by decide)
theorem fall_35 : finalSigOKL 6 6 UB36_35.1 UB36_35.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_35 : finalSigOK 6 6 (none) UB36_35.1 UB36_35.2 SA0 NS0 = true :=
  finalSigOKL_get fall_35 0 (by decide)
theorem fsig1_35 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_35.1 UB36_35.2 SA1 NS1 = true :=
  finalSigOKL_get fall_35 1 (by decide)
theorem fsig2_35 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_35.1 UB36_35.2 SA2 NS2 = true :=
  finalSigOKL_get fall_35 2 (by decide)
theorem fsig3_35 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_35.1 UB36_35.2 SA3 NS3 = true :=
  finalSigOKL_get fall_35 3 (by decide)
theorem fsig4_35 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_35.1 UB36_35.2 SA4 NS4 = true :=
  finalSigOKL_get fall_35 4 (by decide)
theorem fall_51 : finalSigOKL 6 6 UB36_51.1 UB36_51.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_51 : finalSigOK 6 6 (none) UB36_51.1 UB36_51.2 SA0 NS0 = true :=
  finalSigOKL_get fall_51 0 (by decide)
theorem fsig1_51 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_51.1 UB36_51.2 SA1 NS1 = true :=
  finalSigOKL_get fall_51 1 (by decide)
theorem fsig2_51 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_51.1 UB36_51.2 SA2 NS2 = true :=
  finalSigOKL_get fall_51 2 (by decide)
theorem fsig3_51 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_51.1 UB36_51.2 SA3 NS3 = true :=
  finalSigOKL_get fall_51 3 (by decide)
theorem fsig4_51 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_51.1 UB36_51.2 SA4 NS4 = true :=
  finalSigOKL_get fall_51 4 (by decide)
theorem fall_67 : finalSigOKL 6 6 UB36_67.1 UB36_67.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_67 : finalSigOK 6 6 (none) UB36_67.1 UB36_67.2 SA0 NS0 = true :=
  finalSigOKL_get fall_67 0 (by decide)
theorem fsig1_67 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_67.1 UB36_67.2 SA1 NS1 = true :=
  finalSigOKL_get fall_67 1 (by decide)
theorem fsig2_67 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_67.1 UB36_67.2 SA2 NS2 = true :=
  finalSigOKL_get fall_67 2 (by decide)
theorem fsig3_67 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_67.1 UB36_67.2 SA3 NS3 = true :=
  finalSigOKL_get fall_67 3 (by decide)
theorem fsig4_67 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_67.1 UB36_67.2 SA4 NS4 = true :=
  finalSigOKL_get fall_67 4 (by decide)
theorem fall_83 : finalSigOKL 6 6 UB36_83.1 UB36_83.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_83 : finalSigOK 6 6 (none) UB36_83.1 UB36_83.2 SA0 NS0 = true :=
  finalSigOKL_get fall_83 0 (by decide)
theorem fsig1_83 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_83.1 UB36_83.2 SA1 NS1 = true :=
  finalSigOKL_get fall_83 1 (by decide)
theorem fsig2_83 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_83.1 UB36_83.2 SA2 NS2 = true :=
  finalSigOKL_get fall_83 2 (by decide)
theorem fsig3_83 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_83.1 UB36_83.2 SA3 NS3 = true :=
  finalSigOKL_get fall_83 3 (by decide)
theorem fsig4_83 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_83.1 UB36_83.2 SA4 NS4 = true :=
  finalSigOKL_get fall_83 4 (by decide)
theorem fall_99 : finalSigOKL 6 6 UB36_99.1 UB36_99.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_99 : finalSigOK 6 6 (none) UB36_99.1 UB36_99.2 SA0 NS0 = true :=
  finalSigOKL_get fall_99 0 (by decide)
theorem fsig1_99 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_99.1 UB36_99.2 SA1 NS1 = true :=
  finalSigOKL_get fall_99 1 (by decide)
theorem fsig2_99 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_99.1 UB36_99.2 SA2 NS2 = true :=
  finalSigOKL_get fall_99 2 (by decide)
theorem fsig3_99 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_99.1 UB36_99.2 SA3 NS3 = true :=
  finalSigOKL_get fall_99 3 (by decide)
theorem fsig4_99 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_99.1 UB36_99.2 SA4 NS4 = true :=
  finalSigOKL_get fall_99 4 (by decide)
theorem fall_115 : finalSigOKL 6 6 UB36_115.1 UB36_115.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_115 : finalSigOK 6 6 (none) UB36_115.1 UB36_115.2 SA0 NS0 = true :=
  finalSigOKL_get fall_115 0 (by decide)
theorem fsig1_115 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_115.1 UB36_115.2 SA1 NS1 = true :=
  finalSigOKL_get fall_115 1 (by decide)
theorem fsig2_115 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_115.1 UB36_115.2 SA2 NS2 = true :=
  finalSigOKL_get fall_115 2 (by decide)
theorem fsig3_115 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_115.1 UB36_115.2 SA3 NS3 = true :=
  finalSigOKL_get fall_115 3 (by decide)
theorem fsig4_115 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_115.1 UB36_115.2 SA4 NS4 = true :=
  finalSigOKL_get fall_115 4 (by decide)
theorem sg0_0_11 : sigsOKR 0 SA0 704 768 = true := by decide +kernel
theorem sg0_1_1 : sigsOKR 0 SA1 64 128 = true := by decide +kernel
theorem sg0_2_4 : sigsOKR 0 SA2 256 320 = true := by decide +kernel
theorem sg0_3_7 : sigsOKR 0 SA3 448 512 = true := by decide +kernel
theorem sg0_4_5 : sigsOKR 0 SA4 320 384 = true := by decide +kernel
theorem sg1_2_3 : sigsOKR 1 SA2 192 256 = true := by decide +kernel
theorem sg1_3_6 : sigsOKR 1 SA3 384 448 = true := by decide +kernel
theorem sg1_4_4 : sigsOKR 1 SA4 256 320 = true := by decide +kernel
theorem sg1_1_2 : sigsOKR 1 SA1 128 192 = true := by decide +kernel
end WinKU.Shared
