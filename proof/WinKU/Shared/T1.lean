/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import WinKU.Shared.D
public import ZZN.WinK.FastE
-- Build order only (at most 2 certificate modules build at once).
import BoxKGen.N12x12.S1

@[expose] public section

set_option Elab.async false
namespace WinKU.Shared
open ZZN.WinK ZZN.Win
theorem stU31_16D : stepOKD 6 6 [] 31 UB31_16.1 UB31_16.2 UL32 UF32 UN32 = true := by decide +kernel
theorem stU31_16 : stepOK 6 6 [] 31 UB31_16.1 UB31_16.2 UL32 UF32 UN32 = true := by rw [← stepOKD_eq]; exact stU31_16D
theorem stU31_17D : stepOKD 6 6 [] 31 UB31_17.1 UB31_17.2 UL32 UF32 UN32 = true := by decide +kernel
theorem stU31_17 : stepOK 6 6 [] 31 UB31_17.1 UB31_17.2 UL32 UF32 UN32 = true := by rw [← stepOKD_eq]; exact stU31_17D
theorem stU32_0D : stepOKD 6 6 [] 32 UB32_0.1 UB32_0.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_0 : stepOK 6 6 [] 32 UB32_0.1 UB32_0.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_0D
theorem stU32_1D : stepOKD 6 6 [] 32 UB32_1.1 UB32_1.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_1 : stepOK 6 6 [] 32 UB32_1.1 UB32_1.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_1D
theorem stU32_2D : stepOKD 6 6 [] 32 UB32_2.1 UB32_2.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_2 : stepOK 6 6 [] 32 UB32_2.1 UB32_2.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_2D
theorem stU32_3D : stepOKD 6 6 [] 32 UB32_3.1 UB32_3.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_3 : stepOK 6 6 [] 32 UB32_3.1 UB32_3.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_3D
theorem stU32_4D : stepOKD 6 6 [] 32 UB32_4.1 UB32_4.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_4 : stepOK 6 6 [] 32 UB32_4.1 UB32_4.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_4D
theorem stU32_5D : stepOKD 6 6 [] 32 UB32_5.1 UB32_5.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_5 : stepOK 6 6 [] 32 UB32_5.1 UB32_5.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_5D
theorem stU32_6D : stepOKD 6 6 [] 32 UB32_6.1 UB32_6.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_6 : stepOK 6 6 [] 32 UB32_6.1 UB32_6.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_6D
theorem stU32_7D : stepOKD 6 6 [] 32 UB32_7.1 UB32_7.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_7 : stepOK 6 6 [] 32 UB32_7.1 UB32_7.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_7D
theorem stU32_8D : stepOKD 6 6 [] 32 UB32_8.1 UB32_8.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_8 : stepOK 6 6 [] 32 UB32_8.1 UB32_8.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_8D
theorem stU32_9D : stepOKD 6 6 [] 32 UB32_9.1 UB32_9.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_9 : stepOK 6 6 [] 32 UB32_9.1 UB32_9.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_9D
theorem stU32_10D : stepOKD 6 6 [] 32 UB32_10.1 UB32_10.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_10 : stepOK 6 6 [] 32 UB32_10.1 UB32_10.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_10D
theorem stU32_11D : stepOKD 6 6 [] 32 UB32_11.1 UB32_11.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_11 : stepOK 6 6 [] 32 UB32_11.1 UB32_11.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_11D
theorem stU32_12D : stepOKD 6 6 [] 32 UB32_12.1 UB32_12.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_12 : stepOK 6 6 [] 32 UB32_12.1 UB32_12.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_12D
theorem stU32_13D : stepOKD 6 6 [] 32 UB32_13.1 UB32_13.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_13 : stepOK 6 6 [] 32 UB32_13.1 UB32_13.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_13D
theorem stU32_14D : stepOKD 6 6 [] 32 UB32_14.1 UB32_14.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_14 : stepOK 6 6 [] 32 UB32_14.1 UB32_14.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_14D
theorem stU32_15D : stepOKD 6 6 [] 32 UB32_15.1 UB32_15.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_15 : stepOK 6 6 [] 32 UB32_15.1 UB32_15.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_15D
theorem stU32_16D : stepOKD 6 6 [] 32 UB32_16.1 UB32_16.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_16 : stepOK 6 6 [] 32 UB32_16.1 UB32_16.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_16D
theorem stU32_17D : stepOKD 6 6 [] 32 UB32_17.1 UB32_17.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_17 : stepOK 6 6 [] 32 UB32_17.1 UB32_17.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_17D
theorem stU32_18D : stepOKD 6 6 [] 32 UB32_18.1 UB32_18.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_18 : stepOK 6 6 [] 32 UB32_18.1 UB32_18.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_18D
theorem stU32_19D : stepOKD 6 6 [] 32 UB32_19.1 UB32_19.2 UL33 UF33 UN33 = true := by decide +kernel
theorem stU32_19 : stepOK 6 6 [] 32 UB32_19.1 UB32_19.2 UL33 UF33 UN33 = true := by rw [← stepOKD_eq]; exact stU32_19D
theorem stU33_0D : stepOKD 6 6 [] 33 UB33_0.1 UB33_0.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_0 : stepOK 6 6 [] 33 UB33_0.1 UB33_0.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_0D
theorem stU33_1D : stepOKD 6 6 [] 33 UB33_1.1 UB33_1.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_1 : stepOK 6 6 [] 33 UB33_1.1 UB33_1.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_1D
theorem stU33_2D : stepOKD 6 6 [] 33 UB33_2.1 UB33_2.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_2 : stepOK 6 6 [] 33 UB33_2.1 UB33_2.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_2D
theorem stU33_3D : stepOKD 6 6 [] 33 UB33_3.1 UB33_3.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_3 : stepOK 6 6 [] 33 UB33_3.1 UB33_3.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_3D
theorem stU33_4D : stepOKD 6 6 [] 33 UB33_4.1 UB33_4.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_4 : stepOK 6 6 [] 33 UB33_4.1 UB33_4.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_4D
theorem stU33_5D : stepOKD 6 6 [] 33 UB33_5.1 UB33_5.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_5 : stepOK 6 6 [] 33 UB33_5.1 UB33_5.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_5D
theorem stU33_6D : stepOKD 6 6 [] 33 UB33_6.1 UB33_6.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_6 : stepOK 6 6 [] 33 UB33_6.1 UB33_6.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_6D
theorem stU33_7D : stepOKD 6 6 [] 33 UB33_7.1 UB33_7.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_7 : stepOK 6 6 [] 33 UB33_7.1 UB33_7.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_7D
theorem stU33_8D : stepOKD 6 6 [] 33 UB33_8.1 UB33_8.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_8 : stepOK 6 6 [] 33 UB33_8.1 UB33_8.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_8D
theorem stU33_9D : stepOKD 6 6 [] 33 UB33_9.1 UB33_9.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_9 : stepOK 6 6 [] 33 UB33_9.1 UB33_9.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_9D
theorem stU33_10D : stepOKD 6 6 [] 33 UB33_10.1 UB33_10.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_10 : stepOK 6 6 [] 33 UB33_10.1 UB33_10.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_10D
theorem stU33_11D : stepOKD 6 6 [] 33 UB33_11.1 UB33_11.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_11 : stepOK 6 6 [] 33 UB33_11.1 UB33_11.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_11D
theorem stU33_12D : stepOKD 6 6 [] 33 UB33_12.1 UB33_12.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_12 : stepOK 6 6 [] 33 UB33_12.1 UB33_12.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_12D
theorem stU33_13D : stepOKD 6 6 [] 33 UB33_13.1 UB33_13.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_13 : stepOK 6 6 [] 33 UB33_13.1 UB33_13.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_13D
theorem stU33_14D : stepOKD 6 6 [] 33 UB33_14.1 UB33_14.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_14 : stepOK 6 6 [] 33 UB33_14.1 UB33_14.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_14D
theorem stU33_15D : stepOKD 6 6 [] 33 UB33_15.1 UB33_15.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_15 : stepOK 6 6 [] 33 UB33_15.1 UB33_15.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_15D
theorem stU33_16D : stepOKD 6 6 [] 33 UB33_16.1 UB33_16.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_16 : stepOK 6 6 [] 33 UB33_16.1 UB33_16.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_16D
theorem stU33_17D : stepOKD 6 6 [] 33 UB33_17.1 UB33_17.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_17 : stepOK 6 6 [] 33 UB33_17.1 UB33_17.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_17D
theorem stU33_18D : stepOKD 6 6 [] 33 UB33_18.1 UB33_18.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_18 : stepOK 6 6 [] 33 UB33_18.1 UB33_18.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_18D
theorem stU33_19D : stepOKD 6 6 [] 33 UB33_19.1 UB33_19.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_19 : stepOK 6 6 [] 33 UB33_19.1 UB33_19.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_19D
theorem stU33_20D : stepOKD 6 6 [] 33 UB33_20.1 UB33_20.2 UL34 UF34 UN34 = true := by decide +kernel
theorem stU33_20 : stepOK 6 6 [] 33 UB33_20.1 UB33_20.2 UL34 UF34 UN34 = true := by rw [← stepOKD_eq]; exact stU33_20D
theorem stU34_0D : stepOKD 6 6 [] 34 UB34_0.1 UB34_0.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_0 : stepOK 6 6 [] 34 UB34_0.1 UB34_0.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_0D
theorem stU34_1D : stepOKD 6 6 [] 34 UB34_1.1 UB34_1.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_1 : stepOK 6 6 [] 34 UB34_1.1 UB34_1.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_1D
theorem stU34_2D : stepOKD 6 6 [] 34 UB34_2.1 UB34_2.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_2 : stepOK 6 6 [] 34 UB34_2.1 UB34_2.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_2D
theorem stU34_3D : stepOKD 6 6 [] 34 UB34_3.1 UB34_3.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_3 : stepOK 6 6 [] 34 UB34_3.1 UB34_3.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_3D
theorem stU34_4D : stepOKD 6 6 [] 34 UB34_4.1 UB34_4.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_4 : stepOK 6 6 [] 34 UB34_4.1 UB34_4.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_4D
theorem stU34_5D : stepOKD 6 6 [] 34 UB34_5.1 UB34_5.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_5 : stepOK 6 6 [] 34 UB34_5.1 UB34_5.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_5D
theorem stU34_6D : stepOKD 6 6 [] 34 UB34_6.1 UB34_6.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_6 : stepOK 6 6 [] 34 UB34_6.1 UB34_6.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_6D
theorem stU34_7D : stepOKD 6 6 [] 34 UB34_7.1 UB34_7.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_7 : stepOK 6 6 [] 34 UB34_7.1 UB34_7.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_7D
theorem stU34_8D : stepOKD 6 6 [] 34 UB34_8.1 UB34_8.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_8 : stepOK 6 6 [] 34 UB34_8.1 UB34_8.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_8D
theorem stU34_9D : stepOKD 6 6 [] 34 UB34_9.1 UB34_9.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_9 : stepOK 6 6 [] 34 UB34_9.1 UB34_9.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_9D
theorem stU34_10D : stepOKD 6 6 [] 34 UB34_10.1 UB34_10.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_10 : stepOK 6 6 [] 34 UB34_10.1 UB34_10.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_10D
theorem stU34_11D : stepOKD 6 6 [] 34 UB34_11.1 UB34_11.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_11 : stepOK 6 6 [] 34 UB34_11.1 UB34_11.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_11D
theorem stU34_12D : stepOKD 6 6 [] 34 UB34_12.1 UB34_12.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_12 : stepOK 6 6 [] 34 UB34_12.1 UB34_12.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_12D
theorem stU34_13D : stepOKD 6 6 [] 34 UB34_13.1 UB34_13.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_13 : stepOK 6 6 [] 34 UB34_13.1 UB34_13.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_13D
theorem stU34_14D : stepOKD 6 6 [] 34 UB34_14.1 UB34_14.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_14 : stepOK 6 6 [] 34 UB34_14.1 UB34_14.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_14D
theorem stU34_15D : stepOKD 6 6 [] 34 UB34_15.1 UB34_15.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_15 : stepOK 6 6 [] 34 UB34_15.1 UB34_15.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_15D
theorem stU34_16D : stepOKD 6 6 [] 34 UB34_16.1 UB34_16.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_16 : stepOK 6 6 [] 34 UB34_16.1 UB34_16.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_16D
theorem stU34_17D : stepOKD 6 6 [] 34 UB34_17.1 UB34_17.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_17 : stepOK 6 6 [] 34 UB34_17.1 UB34_17.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_17D
theorem stU34_18D : stepOKD 6 6 [] 34 UB34_18.1 UB34_18.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_18 : stepOK 6 6 [] 34 UB34_18.1 UB34_18.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_18D
theorem stU34_19D : stepOKD 6 6 [] 34 UB34_19.1 UB34_19.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_19 : stepOK 6 6 [] 34 UB34_19.1 UB34_19.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_19D
theorem stU34_20D : stepOKD 6 6 [] 34 UB34_20.1 UB34_20.2 UL35 UF35 UN35 = true := by decide +kernel
theorem stU34_20 : stepOK 6 6 [] 34 UB34_20.1 UB34_20.2 UL35 UF35 UN35 = true := by rw [← stepOKD_eq]; exact stU34_20D
end WinKU.Shared
