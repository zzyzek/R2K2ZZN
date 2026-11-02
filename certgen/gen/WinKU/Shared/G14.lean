import WinKU.Shared.D
import ZZN.WinK.SigL
set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_14 : finalSigOKL 6 6 UB36_14.1 UB36_14.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_14 : finalSigOK 6 6 (none) UB36_14.1 UB36_14.2 SA0 NS0 = true :=
  finalSigOKL_get fall_14 0 (by decide)
theorem fsig1_14 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_14.1 UB36_14.2 SA1 NS1 = true :=
  finalSigOKL_get fall_14 1 (by decide)
theorem fsig2_14 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_14.1 UB36_14.2 SA2 NS2 = true :=
  finalSigOKL_get fall_14 2 (by decide)
theorem fsig3_14 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_14.1 UB36_14.2 SA3 NS3 = true :=
  finalSigOKL_get fall_14 3 (by decide)
theorem fsig4_14 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_14.1 UB36_14.2 SA4 NS4 = true :=
  finalSigOKL_get fall_14 4 (by decide)
theorem fall_30 : finalSigOKL 6 6 UB36_30.1 UB36_30.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_30 : finalSigOK 6 6 (none) UB36_30.1 UB36_30.2 SA0 NS0 = true :=
  finalSigOKL_get fall_30 0 (by decide)
theorem fsig1_30 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_30.1 UB36_30.2 SA1 NS1 = true :=
  finalSigOKL_get fall_30 1 (by decide)
theorem fsig2_30 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_30.1 UB36_30.2 SA2 NS2 = true :=
  finalSigOKL_get fall_30 2 (by decide)
theorem fsig3_30 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_30.1 UB36_30.2 SA3 NS3 = true :=
  finalSigOKL_get fall_30 3 (by decide)
theorem fsig4_30 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_30.1 UB36_30.2 SA4 NS4 = true :=
  finalSigOKL_get fall_30 4 (by decide)
theorem fall_46 : finalSigOKL 6 6 UB36_46.1 UB36_46.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_46 : finalSigOK 6 6 (none) UB36_46.1 UB36_46.2 SA0 NS0 = true :=
  finalSigOKL_get fall_46 0 (by decide)
theorem fsig1_46 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_46.1 UB36_46.2 SA1 NS1 = true :=
  finalSigOKL_get fall_46 1 (by decide)
theorem fsig2_46 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_46.1 UB36_46.2 SA2 NS2 = true :=
  finalSigOKL_get fall_46 2 (by decide)
theorem fsig3_46 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_46.1 UB36_46.2 SA3 NS3 = true :=
  finalSigOKL_get fall_46 3 (by decide)
theorem fsig4_46 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_46.1 UB36_46.2 SA4 NS4 = true :=
  finalSigOKL_get fall_46 4 (by decide)
theorem fall_62 : finalSigOKL 6 6 UB36_62.1 UB36_62.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_62 : finalSigOK 6 6 (none) UB36_62.1 UB36_62.2 SA0 NS0 = true :=
  finalSigOKL_get fall_62 0 (by decide)
theorem fsig1_62 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_62.1 UB36_62.2 SA1 NS1 = true :=
  finalSigOKL_get fall_62 1 (by decide)
theorem fsig2_62 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_62.1 UB36_62.2 SA2 NS2 = true :=
  finalSigOKL_get fall_62 2 (by decide)
theorem fsig3_62 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_62.1 UB36_62.2 SA3 NS3 = true :=
  finalSigOKL_get fall_62 3 (by decide)
theorem fsig4_62 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_62.1 UB36_62.2 SA4 NS4 = true :=
  finalSigOKL_get fall_62 4 (by decide)
theorem fall_78 : finalSigOKL 6 6 UB36_78.1 UB36_78.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_78 : finalSigOK 6 6 (none) UB36_78.1 UB36_78.2 SA0 NS0 = true :=
  finalSigOKL_get fall_78 0 (by decide)
theorem fsig1_78 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_78.1 UB36_78.2 SA1 NS1 = true :=
  finalSigOKL_get fall_78 1 (by decide)
theorem fsig2_78 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_78.1 UB36_78.2 SA2 NS2 = true :=
  finalSigOKL_get fall_78 2 (by decide)
theorem fsig3_78 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_78.1 UB36_78.2 SA3 NS3 = true :=
  finalSigOKL_get fall_78 3 (by decide)
theorem fsig4_78 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_78.1 UB36_78.2 SA4 NS4 = true :=
  finalSigOKL_get fall_78 4 (by decide)
theorem fall_94 : finalSigOKL 6 6 UB36_94.1 UB36_94.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_94 : finalSigOK 6 6 (none) UB36_94.1 UB36_94.2 SA0 NS0 = true :=
  finalSigOKL_get fall_94 0 (by decide)
theorem fsig1_94 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_94.1 UB36_94.2 SA1 NS1 = true :=
  finalSigOKL_get fall_94 1 (by decide)
theorem fsig2_94 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_94.1 UB36_94.2 SA2 NS2 = true :=
  finalSigOKL_get fall_94 2 (by decide)
theorem fsig3_94 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_94.1 UB36_94.2 SA3 NS3 = true :=
  finalSigOKL_get fall_94 3 (by decide)
theorem fsig4_94 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_94.1 UB36_94.2 SA4 NS4 = true :=
  finalSigOKL_get fall_94 4 (by decide)
theorem fall_110 : finalSigOKL 6 6 UB36_110.1 UB36_110.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_110 : finalSigOK 6 6 (none) UB36_110.1 UB36_110.2 SA0 NS0 = true :=
  finalSigOKL_get fall_110 0 (by decide)
theorem fsig1_110 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_110.1 UB36_110.2 SA1 NS1 = true :=
  finalSigOKL_get fall_110 1 (by decide)
theorem fsig2_110 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_110.1 UB36_110.2 SA2 NS2 = true :=
  finalSigOKL_get fall_110 2 (by decide)
theorem fsig3_110 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_110.1 UB36_110.2 SA3 NS3 = true :=
  finalSigOKL_get fall_110 3 (by decide)
theorem fsig4_110 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_110.1 UB36_110.2 SA4 NS4 = true :=
  finalSigOKL_get fall_110 4 (by decide)
theorem sg0_0_6 : sigsOKR 0 SA0 384 448 = true := by decide +kernel
theorem sg1_0_9 : sigsOKR 1 SA0 576 640 = true := by decide +kernel
theorem sg0_1_12 : sigsOKR 0 SA1 768 796 = true := by decide +kernel
theorem sg0_3_2 : sigsOKR 0 SA3 128 192 = true := by decide +kernel
theorem sg0_4_0 : sigsOKR 0 SA4 0 64 = true := by decide +kernel
theorem sg0_4_16 : sigsOKR 0 SA4 1024 1088 = true := by decide +kernel
theorem sg1_3_1 : sigsOKR 1 SA3 64 128 = true := by decide +kernel
theorem sg1_3_17 : sigsOKR 1 SA3 1088 1146 = true := by decide +kernel
theorem sg1_4_15 : sigsOKR 1 SA4 960 1024 = true := by decide +kernel
end WinKU.Shared
