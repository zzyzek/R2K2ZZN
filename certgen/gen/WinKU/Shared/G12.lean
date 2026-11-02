import WinKU.Shared.D
import ZZN.WinK.SigL
set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem fall_12 : finalSigOKL 6 6 UB36_12.1 UB36_12.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_12 : finalSigOK 6 6 (none) UB36_12.1 UB36_12.2 SA0 NS0 = true :=
  finalSigOKL_get fall_12 0 (by decide)
theorem fsig1_12 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_12.1 UB36_12.2 SA1 NS1 = true :=
  finalSigOKL_get fall_12 1 (by decide)
theorem fsig2_12 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_12.1 UB36_12.2 SA2 NS2 = true :=
  finalSigOKL_get fall_12 2 (by decide)
theorem fsig3_12 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_12.1 UB36_12.2 SA3 NS3 = true :=
  finalSigOKL_get fall_12 3 (by decide)
theorem fsig4_12 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_12.1 UB36_12.2 SA4 NS4 = true :=
  finalSigOKL_get fall_12 4 (by decide)
theorem fall_28 : finalSigOKL 6 6 UB36_28.1 UB36_28.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_28 : finalSigOK 6 6 (none) UB36_28.1 UB36_28.2 SA0 NS0 = true :=
  finalSigOKL_get fall_28 0 (by decide)
theorem fsig1_28 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_28.1 UB36_28.2 SA1 NS1 = true :=
  finalSigOKL_get fall_28 1 (by decide)
theorem fsig2_28 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_28.1 UB36_28.2 SA2 NS2 = true :=
  finalSigOKL_get fall_28 2 (by decide)
theorem fsig3_28 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_28.1 UB36_28.2 SA3 NS3 = true :=
  finalSigOKL_get fall_28 3 (by decide)
theorem fsig4_28 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_28.1 UB36_28.2 SA4 NS4 = true :=
  finalSigOKL_get fall_28 4 (by decide)
theorem fall_44 : finalSigOKL 6 6 UB36_44.1 UB36_44.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_44 : finalSigOK 6 6 (none) UB36_44.1 UB36_44.2 SA0 NS0 = true :=
  finalSigOKL_get fall_44 0 (by decide)
theorem fsig1_44 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_44.1 UB36_44.2 SA1 NS1 = true :=
  finalSigOKL_get fall_44 1 (by decide)
theorem fsig2_44 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_44.1 UB36_44.2 SA2 NS2 = true :=
  finalSigOKL_get fall_44 2 (by decide)
theorem fsig3_44 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_44.1 UB36_44.2 SA3 NS3 = true :=
  finalSigOKL_get fall_44 3 (by decide)
theorem fsig4_44 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_44.1 UB36_44.2 SA4 NS4 = true :=
  finalSigOKL_get fall_44 4 (by decide)
theorem fall_60 : finalSigOKL 6 6 UB36_60.1 UB36_60.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_60 : finalSigOK 6 6 (none) UB36_60.1 UB36_60.2 SA0 NS0 = true :=
  finalSigOKL_get fall_60 0 (by decide)
theorem fsig1_60 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_60.1 UB36_60.2 SA1 NS1 = true :=
  finalSigOKL_get fall_60 1 (by decide)
theorem fsig2_60 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_60.1 UB36_60.2 SA2 NS2 = true :=
  finalSigOKL_get fall_60 2 (by decide)
theorem fsig3_60 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_60.1 UB36_60.2 SA3 NS3 = true :=
  finalSigOKL_get fall_60 3 (by decide)
theorem fsig4_60 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_60.1 UB36_60.2 SA4 NS4 = true :=
  finalSigOKL_get fall_60 4 (by decide)
theorem fall_76 : finalSigOKL 6 6 UB36_76.1 UB36_76.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_76 : finalSigOK 6 6 (none) UB36_76.1 UB36_76.2 SA0 NS0 = true :=
  finalSigOKL_get fall_76 0 (by decide)
theorem fsig1_76 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_76.1 UB36_76.2 SA1 NS1 = true :=
  finalSigOKL_get fall_76 1 (by decide)
theorem fsig2_76 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_76.1 UB36_76.2 SA2 NS2 = true :=
  finalSigOKL_get fall_76 2 (by decide)
theorem fsig3_76 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_76.1 UB36_76.2 SA3 NS3 = true :=
  finalSigOKL_get fall_76 3 (by decide)
theorem fsig4_76 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_76.1 UB36_76.2 SA4 NS4 = true :=
  finalSigOKL_get fall_76 4 (by decide)
theorem fall_92 : finalSigOKL 6 6 UB36_92.1 UB36_92.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_92 : finalSigOK 6 6 (none) UB36_92.1 UB36_92.2 SA0 NS0 = true :=
  finalSigOKL_get fall_92 0 (by decide)
theorem fsig1_92 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_92.1 UB36_92.2 SA1 NS1 = true :=
  finalSigOKL_get fall_92 1 (by decide)
theorem fsig2_92 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_92.1 UB36_92.2 SA2 NS2 = true :=
  finalSigOKL_get fall_92 2 (by decide)
theorem fsig3_92 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_92.1 UB36_92.2 SA3 NS3 = true :=
  finalSigOKL_get fall_92 3 (by decide)
theorem fsig4_92 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_92.1 UB36_92.2 SA4 NS4 = true :=
  finalSigOKL_get fall_92 4 (by decide)
theorem fall_108 : finalSigOKL 6 6 UB36_108.1 UB36_108.2 [((none), SA0, NS0), ((some (1, (-1 : ℤ), none)), SA1, NS1), ((some (1, (1 : ℤ), none)), SA2, NS2), ((some (1, (1 : ℤ), some 0)), SA3, NS3), ((some (1, (1 : ℤ), some 11)), SA4, NS4)] = true := by decide +kernel
theorem fsig0_108 : finalSigOK 6 6 (none) UB36_108.1 UB36_108.2 SA0 NS0 = true :=
  finalSigOKL_get fall_108 0 (by decide)
theorem fsig1_108 : finalSigOK 6 6 (some (1, (-1 : ℤ), none)) UB36_108.1 UB36_108.2 SA1 NS1 = true :=
  finalSigOKL_get fall_108 1 (by decide)
theorem fsig2_108 : finalSigOK 6 6 (some (1, (1 : ℤ), none)) UB36_108.1 UB36_108.2 SA2 NS2 = true :=
  finalSigOKL_get fall_108 2 (by decide)
theorem fsig3_108 : finalSigOK 6 6 (some (1, (1 : ℤ), some 0)) UB36_108.1 UB36_108.2 SA3 NS3 = true :=
  finalSigOKL_get fall_108 3 (by decide)
theorem fsig4_108 : finalSigOK 6 6 (some (1, (1 : ℤ), some 11)) UB36_108.1 UB36_108.2 SA4 NS4 = true :=
  finalSigOKL_get fall_108 4 (by decide)
theorem sg0_0_4 : sigsOKR 0 SA0 256 320 = true := by decide +kernel
theorem sg1_0_7 : sigsOKR 1 SA0 448 512 = true := by decide +kernel
theorem sg0_1_10 : sigsOKR 0 SA1 640 704 = true := by decide +kernel
theorem sg0_3_0 : sigsOKR 0 SA3 0 64 = true := by decide +kernel
theorem sg0_3_16 : sigsOKR 0 SA3 1024 1088 = true := by decide +kernel
theorem sg0_4_14 : sigsOKR 0 SA4 896 960 = true := by decide +kernel
theorem sg1_2_12 : sigsOKR 1 SA2 768 796 = true := by decide +kernel
theorem sg1_3_15 : sigsOKR 1 SA3 960 1024 = true := by decide +kernel
theorem sg1_4_13 : sigsOKR 1 SA4 832 896 = true := by decide +kernel
theorem sg1_1_11 : sigsOKR 1 SA1 704 768 = true := by decide +kernel
end WinKU.Shared
