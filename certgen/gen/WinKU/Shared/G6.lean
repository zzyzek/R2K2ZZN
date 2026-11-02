import WinKU.Shared.D
import ZZN.WinK.SigL
set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_6 : finalSigOKL 6 6 UB36_6.1 UB36_6.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_6 : finalSigOK 6 6 (none) UB36_6.1 UB36_6.2 SA0 NS0 = true :=
  finalSigOKL_get fall_6 0 (by decide)
theorem fsig1_6 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_6.1 UB36_6.2 SA1 NS1 = true :=
  finalSigOKL_get fall_6 1 (by decide)
theorem fsig2_6 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_6.1 UB36_6.2 SA2 NS2 = true :=
  finalSigOKL_get fall_6 2 (by decide)
theorem fsig3_6 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_6.1 UB36_6.2 SA3 NS3 = true :=
  finalSigOKL_get fall_6 3 (by decide)
theorem fsig4_6 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_6.1 UB36_6.2 SA4 NS4 = true :=
  finalSigOKL_get fall_6 4 (by decide)
theorem fall_22 : finalSigOKL 6 6 UB36_22.1 UB36_22.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_22 : finalSigOK 6 6 (none) UB36_22.1 UB36_22.2 SA0 NS0 = true :=
  finalSigOKL_get fall_22 0 (by decide)
theorem fsig1_22 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_22.1 UB36_22.2 SA1 NS1 = true :=
  finalSigOKL_get fall_22 1 (by decide)
theorem fsig2_22 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_22.1 UB36_22.2 SA2 NS2 = true :=
  finalSigOKL_get fall_22 2 (by decide)
theorem fsig3_22 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_22.1 UB36_22.2 SA3 NS3 = true :=
  finalSigOKL_get fall_22 3 (by decide)
theorem fsig4_22 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_22.1 UB36_22.2 SA4 NS4 = true :=
  finalSigOKL_get fall_22 4 (by decide)
theorem fall_38 : finalSigOKL 6 6 UB36_38.1 UB36_38.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_38 : finalSigOK 6 6 (none) UB36_38.1 UB36_38.2 SA0 NS0 = true :=
  finalSigOKL_get fall_38 0 (by decide)
theorem fsig1_38 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_38.1 UB36_38.2 SA1 NS1 = true :=
  finalSigOKL_get fall_38 1 (by decide)
theorem fsig2_38 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_38.1 UB36_38.2 SA2 NS2 = true :=
  finalSigOKL_get fall_38 2 (by decide)
theorem fsig3_38 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_38.1 UB36_38.2 SA3 NS3 = true :=
  finalSigOKL_get fall_38 3 (by decide)
theorem fsig4_38 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_38.1 UB36_38.2 SA4 NS4 = true :=
  finalSigOKL_get fall_38 4 (by decide)
theorem fall_54 : finalSigOKL 6 6 UB36_54.1 UB36_54.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_54 : finalSigOK 6 6 (none) UB36_54.1 UB36_54.2 SA0 NS0 = true :=
  finalSigOKL_get fall_54 0 (by decide)
theorem fsig1_54 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_54.1 UB36_54.2 SA1 NS1 = true :=
  finalSigOKL_get fall_54 1 (by decide)
theorem fsig2_54 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_54.1 UB36_54.2 SA2 NS2 = true :=
  finalSigOKL_get fall_54 2 (by decide)
theorem fsig3_54 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_54.1 UB36_54.2 SA3 NS3 = true :=
  finalSigOKL_get fall_54 3 (by decide)
theorem fsig4_54 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_54.1 UB36_54.2 SA4 NS4 = true :=
  finalSigOKL_get fall_54 4 (by decide)
theorem fall_70 : finalSigOKL 6 6 UB36_70.1 UB36_70.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_70 : finalSigOK 6 6 (none) UB36_70.1 UB36_70.2 SA0 NS0 = true :=
  finalSigOKL_get fall_70 0 (by decide)
theorem fsig1_70 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_70.1 UB36_70.2 SA1 NS1 = true :=
  finalSigOKL_get fall_70 1 (by decide)
theorem fsig2_70 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_70.1 UB36_70.2 SA2 NS2 = true :=
  finalSigOKL_get fall_70 2 (by decide)
theorem fsig3_70 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_70.1 UB36_70.2 SA3 NS3 = true :=
  finalSigOKL_get fall_70 3 (by decide)
theorem fsig4_70 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_70.1 UB36_70.2 SA4 NS4 = true :=
  finalSigOKL_get fall_70 4 (by decide)
theorem fall_86 : finalSigOKL 6 6 UB36_86.1 UB36_86.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_86 : finalSigOK 6 6 (none) UB36_86.1 UB36_86.2 SA0 NS0 = true :=
  finalSigOKL_get fall_86 0 (by decide)
theorem fsig1_86 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_86.1 UB36_86.2 SA1 NS1 = true :=
  finalSigOKL_get fall_86 1 (by decide)
theorem fsig2_86 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_86.1 UB36_86.2 SA2 NS2 = true :=
  finalSigOKL_get fall_86 2 (by decide)
theorem fsig3_86 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_86.1 UB36_86.2 SA3 NS3 = true :=
  finalSigOKL_get fall_86 3 (by decide)
theorem fsig4_86 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_86.1 UB36_86.2 SA4 NS4 = true :=
  finalSigOKL_get fall_86 4 (by decide)
theorem fall_102 : finalSigOKL 6 6 UB36_102.1 UB36_102.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_102 : finalSigOK 6 6 (none) UB36_102.1 UB36_102.2 SA0 NS0 = true :=
  finalSigOKL_get fall_102 0 (by decide)
theorem fsig1_102 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_102.1 UB36_102.2 SA1 NS1 = true :=
  finalSigOKL_get fall_102 1 (by decide)
theorem fsig2_102 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_102.1 UB36_102.2 SA2 NS2 = true :=
  finalSigOKL_get fall_102 2 (by decide)
theorem fsig3_102 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_102.1 UB36_102.2 SA3 NS3 = true :=
  finalSigOKL_get fall_102 3 (by decide)
theorem fsig4_102 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_102.1 UB36_102.2 SA4 NS4 = true :=
  finalSigOKL_get fall_102 4 (by decide)
theorem fall_118 : finalSigOKL 6 6 UB36_118.1 UB36_118.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_118 : finalSigOK 6 6 (none) UB36_118.1 UB36_118.2 SA0 NS0 = true :=
  finalSigOKL_get fall_118 0 (by decide)
theorem fsig1_118 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_118.1 UB36_118.2 SA1 NS1 = true :=
  finalSigOKL_get fall_118 1 (by decide)
theorem fsig2_118 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_118.1 UB36_118.2 SA2 NS2 = true :=
  finalSigOKL_get fall_118 2 (by decide)
theorem fsig3_118 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_118.1 UB36_118.2 SA3 NS3 = true :=
  finalSigOKL_get fall_118 3 (by decide)
theorem fsig4_118 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_118.1 UB36_118.2 SA4 NS4 = true :=
  finalSigOKL_get fall_118 4 (by decide)
theorem sg1_0_1 : sigsOKR 1 SA0 64 128 = true := by decide +kernel
theorem sg0_1_4 : sigsOKR 0 SA1 256 320 = true := by decide +kernel
theorem sg0_2_7 : sigsOKR 0 SA2 448 512 = true := by decide +kernel
theorem sg0_3_10 : sigsOKR 0 SA3 640 704 = true := by decide +kernel
theorem sg0_4_8 : sigsOKR 0 SA4 512 576 = true := by decide +kernel
theorem sg1_2_6 : sigsOKR 1 SA2 384 448 = true := by decide +kernel
theorem sg1_3_9 : sigsOKR 1 SA3 576 640 = true := by decide +kernel
theorem sg1_4_7 : sigsOKR 1 SA4 448 512 = true := by decide +kernel
theorem sg1_1_5 : sigsOKR 1 SA1 320 384 = true := by decide +kernel
end WinKU.Shared
