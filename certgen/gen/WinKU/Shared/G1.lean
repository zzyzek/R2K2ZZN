import WinKU.Shared.D
import ZZN.WinK.SigL
set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_1 : finalSigOKL 6 6 UB36_1.1 UB36_1.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_1 : finalSigOK 6 6 (none) UB36_1.1 UB36_1.2 SA0 NS0 = true :=
  finalSigOKL_get fall_1 0 (by decide)
theorem fsig1_1 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_1.1 UB36_1.2 SA1 NS1 = true :=
  finalSigOKL_get fall_1 1 (by decide)
theorem fsig2_1 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_1.1 UB36_1.2 SA2 NS2 = true :=
  finalSigOKL_get fall_1 2 (by decide)
theorem fsig3_1 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_1.1 UB36_1.2 SA3 NS3 = true :=
  finalSigOKL_get fall_1 3 (by decide)
theorem fsig4_1 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_1.1 UB36_1.2 SA4 NS4 = true :=
  finalSigOKL_get fall_1 4 (by decide)
theorem fall_17 : finalSigOKL 6 6 UB36_17.1 UB36_17.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_17 : finalSigOK 6 6 (none) UB36_17.1 UB36_17.2 SA0 NS0 = true :=
  finalSigOKL_get fall_17 0 (by decide)
theorem fsig1_17 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_17.1 UB36_17.2 SA1 NS1 = true :=
  finalSigOKL_get fall_17 1 (by decide)
theorem fsig2_17 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_17.1 UB36_17.2 SA2 NS2 = true :=
  finalSigOKL_get fall_17 2 (by decide)
theorem fsig3_17 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_17.1 UB36_17.2 SA3 NS3 = true :=
  finalSigOKL_get fall_17 3 (by decide)
theorem fsig4_17 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_17.1 UB36_17.2 SA4 NS4 = true :=
  finalSigOKL_get fall_17 4 (by decide)
theorem fall_33 : finalSigOKL 6 6 UB36_33.1 UB36_33.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_33 : finalSigOK 6 6 (none) UB36_33.1 UB36_33.2 SA0 NS0 = true :=
  finalSigOKL_get fall_33 0 (by decide)
theorem fsig1_33 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_33.1 UB36_33.2 SA1 NS1 = true :=
  finalSigOKL_get fall_33 1 (by decide)
theorem fsig2_33 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_33.1 UB36_33.2 SA2 NS2 = true :=
  finalSigOKL_get fall_33 2 (by decide)
theorem fsig3_33 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_33.1 UB36_33.2 SA3 NS3 = true :=
  finalSigOKL_get fall_33 3 (by decide)
theorem fsig4_33 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_33.1 UB36_33.2 SA4 NS4 = true :=
  finalSigOKL_get fall_33 4 (by decide)
theorem fall_49 : finalSigOKL 6 6 UB36_49.1 UB36_49.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_49 : finalSigOK 6 6 (none) UB36_49.1 UB36_49.2 SA0 NS0 = true :=
  finalSigOKL_get fall_49 0 (by decide)
theorem fsig1_49 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_49.1 UB36_49.2 SA1 NS1 = true :=
  finalSigOKL_get fall_49 1 (by decide)
theorem fsig2_49 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_49.1 UB36_49.2 SA2 NS2 = true :=
  finalSigOKL_get fall_49 2 (by decide)
theorem fsig3_49 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_49.1 UB36_49.2 SA3 NS3 = true :=
  finalSigOKL_get fall_49 3 (by decide)
theorem fsig4_49 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_49.1 UB36_49.2 SA4 NS4 = true :=
  finalSigOKL_get fall_49 4 (by decide)
theorem fall_65 : finalSigOKL 6 6 UB36_65.1 UB36_65.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_65 : finalSigOK 6 6 (none) UB36_65.1 UB36_65.2 SA0 NS0 = true :=
  finalSigOKL_get fall_65 0 (by decide)
theorem fsig1_65 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_65.1 UB36_65.2 SA1 NS1 = true :=
  finalSigOKL_get fall_65 1 (by decide)
theorem fsig2_65 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_65.1 UB36_65.2 SA2 NS2 = true :=
  finalSigOKL_get fall_65 2 (by decide)
theorem fsig3_65 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_65.1 UB36_65.2 SA3 NS3 = true :=
  finalSigOKL_get fall_65 3 (by decide)
theorem fsig4_65 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_65.1 UB36_65.2 SA4 NS4 = true :=
  finalSigOKL_get fall_65 4 (by decide)
theorem fall_81 : finalSigOKL 6 6 UB36_81.1 UB36_81.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_81 : finalSigOK 6 6 (none) UB36_81.1 UB36_81.2 SA0 NS0 = true :=
  finalSigOKL_get fall_81 0 (by decide)
theorem fsig1_81 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_81.1 UB36_81.2 SA1 NS1 = true :=
  finalSigOKL_get fall_81 1 (by decide)
theorem fsig2_81 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_81.1 UB36_81.2 SA2 NS2 = true :=
  finalSigOKL_get fall_81 2 (by decide)
theorem fsig3_81 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_81.1 UB36_81.2 SA3 NS3 = true :=
  finalSigOKL_get fall_81 3 (by decide)
theorem fsig4_81 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_81.1 UB36_81.2 SA4 NS4 = true :=
  finalSigOKL_get fall_81 4 (by decide)
theorem fall_97 : finalSigOKL 6 6 UB36_97.1 UB36_97.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_97 : finalSigOK 6 6 (none) UB36_97.1 UB36_97.2 SA0 NS0 = true :=
  finalSigOKL_get fall_97 0 (by decide)
theorem fsig1_97 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_97.1 UB36_97.2 SA1 NS1 = true :=
  finalSigOKL_get fall_97 1 (by decide)
theorem fsig2_97 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_97.1 UB36_97.2 SA2 NS2 = true :=
  finalSigOKL_get fall_97 2 (by decide)
theorem fsig3_97 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_97.1 UB36_97.2 SA3 NS3 = true :=
  finalSigOKL_get fall_97 3 (by decide)
theorem fsig4_97 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_97.1 UB36_97.2 SA4 NS4 = true :=
  finalSigOKL_get fall_97 4 (by decide)
theorem fall_113 : finalSigOKL 6 6 UB36_113.1 UB36_113.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_113 : finalSigOK 6 6 (none) UB36_113.1 UB36_113.2 SA0 NS0 = true :=
  finalSigOKL_get fall_113 0 (by decide)
theorem fsig1_113 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_113.1 UB36_113.2 SA1 NS1 = true :=
  finalSigOKL_get fall_113 1 (by decide)
theorem fsig2_113 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_113.1 UB36_113.2 SA2 NS2 = true :=
  finalSigOKL_get fall_113 2 (by decide)
theorem fsig3_113 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_113.1 UB36_113.2 SA3 NS3 = true :=
  finalSigOKL_get fall_113 3 (by decide)
theorem fsig4_113 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_113.1 UB36_113.2 SA4 NS4 = true :=
  finalSigOKL_get fall_113 4 (by decide)
theorem sg0_0_9 : sigsOKR 0 SA0 576 640 = true := by decide +kernel
theorem sg1_0_12 : sigsOKR 1 SA0 768 796 = true := by decide +kernel
theorem sg0_2_2 : sigsOKR 0 SA2 128 192 = true := by decide +kernel
theorem sg0_3_5 : sigsOKR 0 SA3 320 384 = true := by decide +kernel
theorem sg0_4_3 : sigsOKR 0 SA4 192 256 = true := by decide +kernel
theorem sg1_2_1 : sigsOKR 1 SA2 64 128 = true := by decide +kernel
theorem sg1_3_4 : sigsOKR 1 SA3 256 320 = true := by decide +kernel
theorem sg1_4_2 : sigsOKR 1 SA4 128 192 = true := by decide +kernel
theorem sg1_1_0 : sigsOKR 1 SA1 0 64 = true := by decide +kernel
end WinKU.Shared
