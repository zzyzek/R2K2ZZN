import WinKU.Shared.D
import ZZN.WinK.SigL
set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_10 : finalSigOKL 6 6 UB36_10.1 UB36_10.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_10 : finalSigOK 6 6 (none) UB36_10.1 UB36_10.2 SA0 NS0 = true :=
  finalSigOKL_get fall_10 0 (by decide)
theorem fsig1_10 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_10.1 UB36_10.2 SA1 NS1 = true :=
  finalSigOKL_get fall_10 1 (by decide)
theorem fsig2_10 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_10.1 UB36_10.2 SA2 NS2 = true :=
  finalSigOKL_get fall_10 2 (by decide)
theorem fsig3_10 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_10.1 UB36_10.2 SA3 NS3 = true :=
  finalSigOKL_get fall_10 3 (by decide)
theorem fsig4_10 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_10.1 UB36_10.2 SA4 NS4 = true :=
  finalSigOKL_get fall_10 4 (by decide)
theorem fall_26 : finalSigOKL 6 6 UB36_26.1 UB36_26.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_26 : finalSigOK 6 6 (none) UB36_26.1 UB36_26.2 SA0 NS0 = true :=
  finalSigOKL_get fall_26 0 (by decide)
theorem fsig1_26 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_26.1 UB36_26.2 SA1 NS1 = true :=
  finalSigOKL_get fall_26 1 (by decide)
theorem fsig2_26 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_26.1 UB36_26.2 SA2 NS2 = true :=
  finalSigOKL_get fall_26 2 (by decide)
theorem fsig3_26 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_26.1 UB36_26.2 SA3 NS3 = true :=
  finalSigOKL_get fall_26 3 (by decide)
theorem fsig4_26 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_26.1 UB36_26.2 SA4 NS4 = true :=
  finalSigOKL_get fall_26 4 (by decide)
theorem fall_42 : finalSigOKL 6 6 UB36_42.1 UB36_42.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_42 : finalSigOK 6 6 (none) UB36_42.1 UB36_42.2 SA0 NS0 = true :=
  finalSigOKL_get fall_42 0 (by decide)
theorem fsig1_42 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_42.1 UB36_42.2 SA1 NS1 = true :=
  finalSigOKL_get fall_42 1 (by decide)
theorem fsig2_42 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_42.1 UB36_42.2 SA2 NS2 = true :=
  finalSigOKL_get fall_42 2 (by decide)
theorem fsig3_42 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_42.1 UB36_42.2 SA3 NS3 = true :=
  finalSigOKL_get fall_42 3 (by decide)
theorem fsig4_42 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_42.1 UB36_42.2 SA4 NS4 = true :=
  finalSigOKL_get fall_42 4 (by decide)
theorem fall_58 : finalSigOKL 6 6 UB36_58.1 UB36_58.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_58 : finalSigOK 6 6 (none) UB36_58.1 UB36_58.2 SA0 NS0 = true :=
  finalSigOKL_get fall_58 0 (by decide)
theorem fsig1_58 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_58.1 UB36_58.2 SA1 NS1 = true :=
  finalSigOKL_get fall_58 1 (by decide)
theorem fsig2_58 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_58.1 UB36_58.2 SA2 NS2 = true :=
  finalSigOKL_get fall_58 2 (by decide)
theorem fsig3_58 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_58.1 UB36_58.2 SA3 NS3 = true :=
  finalSigOKL_get fall_58 3 (by decide)
theorem fsig4_58 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_58.1 UB36_58.2 SA4 NS4 = true :=
  finalSigOKL_get fall_58 4 (by decide)
theorem fall_74 : finalSigOKL 6 6 UB36_74.1 UB36_74.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_74 : finalSigOK 6 6 (none) UB36_74.1 UB36_74.2 SA0 NS0 = true :=
  finalSigOKL_get fall_74 0 (by decide)
theorem fsig1_74 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_74.1 UB36_74.2 SA1 NS1 = true :=
  finalSigOKL_get fall_74 1 (by decide)
theorem fsig2_74 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_74.1 UB36_74.2 SA2 NS2 = true :=
  finalSigOKL_get fall_74 2 (by decide)
theorem fsig3_74 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_74.1 UB36_74.2 SA3 NS3 = true :=
  finalSigOKL_get fall_74 3 (by decide)
theorem fsig4_74 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_74.1 UB36_74.2 SA4 NS4 = true :=
  finalSigOKL_get fall_74 4 (by decide)
theorem fall_90 : finalSigOKL 6 6 UB36_90.1 UB36_90.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_90 : finalSigOK 6 6 (none) UB36_90.1 UB36_90.2 SA0 NS0 = true :=
  finalSigOKL_get fall_90 0 (by decide)
theorem fsig1_90 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_90.1 UB36_90.2 SA1 NS1 = true :=
  finalSigOKL_get fall_90 1 (by decide)
theorem fsig2_90 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_90.1 UB36_90.2 SA2 NS2 = true :=
  finalSigOKL_get fall_90 2 (by decide)
theorem fsig3_90 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_90.1 UB36_90.2 SA3 NS3 = true :=
  finalSigOKL_get fall_90 3 (by decide)
theorem fsig4_90 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_90.1 UB36_90.2 SA4 NS4 = true :=
  finalSigOKL_get fall_90 4 (by decide)
theorem fall_106 : finalSigOKL 6 6 UB36_106.1 UB36_106.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_106 : finalSigOK 6 6 (none) UB36_106.1 UB36_106.2 SA0 NS0 = true :=
  finalSigOKL_get fall_106 0 (by decide)
theorem fsig1_106 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_106.1 UB36_106.2 SA1 NS1 = true :=
  finalSigOKL_get fall_106 1 (by decide)
theorem fsig2_106 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_106.1 UB36_106.2 SA2 NS2 = true :=
  finalSigOKL_get fall_106 2 (by decide)
theorem fsig3_106 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_106.1 UB36_106.2 SA3 NS3 = true :=
  finalSigOKL_get fall_106 3 (by decide)
theorem fsig4_106 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_106.1 UB36_106.2 SA4 NS4 = true :=
  finalSigOKL_get fall_106 4 (by decide)
theorem sg0_0_2 : sigsOKR 0 SA0 128 192 = true := by decide +kernel
theorem sg1_0_5 : sigsOKR 1 SA0 320 384 = true := by decide +kernel
theorem sg0_1_8 : sigsOKR 0 SA1 512 576 = true := by decide +kernel
theorem sg0_2_11 : sigsOKR 0 SA2 704 768 = true := by decide +kernel
theorem sg0_3_14 : sigsOKR 0 SA3 896 960 = true := by decide +kernel
theorem sg0_4_12 : sigsOKR 0 SA4 768 832 = true := by decide +kernel
theorem sg1_2_10 : sigsOKR 1 SA2 640 704 = true := by decide +kernel
theorem sg1_3_13 : sigsOKR 1 SA3 832 896 = true := by decide +kernel
theorem sg1_4_11 : sigsOKR 1 SA4 704 768 = true := by decide +kernel
theorem sg1_1_9 : sigsOKR 1 SA1 576 640 = true := by decide +kernel
end WinKU.Shared
