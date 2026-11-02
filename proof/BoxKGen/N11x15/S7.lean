/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import BoxKGen.Templates
public import BoxKGen.N11x15.Base

@[expose] public section

set_option Elab.async false
namespace BoxKGen.N11x15
open ZZN ZZN.Cut ZZN.BoxK BoxKGen

noncomputable def d1120 : CData := (![4,4,4,6], [], [(t2, ⟨false, false, false, false, false, false⟩), (t60, ⟨false, false, false, true, false, false⟩), (t4339, ⟨false, false, false, true, true, true⟩), (t3957, ⟨false, false, false, true, true, false⟩), (t5630, ⟨false, false, false, true, true, false⟩), (t3792, ⟨false, false, false, true, true, true⟩), (t5594, ⟨false, false, false, true, true, true⟩), (t9237, ⟨false, false, false, true, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t6381, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl1120 : sliceCOK 11 15 d1120.1 L1 b1 11 ![4,4,4,6] d1120.2.1 0 d1120.2.2.1 d1120.2.2.2.1 [] d1120.2.2.2.2 = true := by decide +kernel
theorem g1120 : SliceGood 11 15 d1120.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 11 15 ![4,4,4,6] [] [])) sl1120
noncomputable def d1121 : CData := (![4,4,5,5], [], [(t5, ⟨false, false, false, false, false, false⟩), (t4366, ⟨false, false, false, true, true, true⟩), (t4364, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl1121 : sliceCOK 11 15 d1121.1 L2 b2 11 ![4,4,5,5] d1121.2.1 0 d1121.2.2.1 d1121.2.2.2.1 [] d1121.2.2.2.2 = true := by decide +kernel
theorem g1121 : SliceGood 11 15 d1121.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 11 15 ![4,4,5,5] [] [])) sl1121
noncomputable def d1122 : CData := (![4,4,5,6], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t3814, ⟨false, false, false, false, true, true⟩), (t4366, ⟨false, false, false, true, true, true⟩), (t93, ⟨false, false, false, false, false, false⟩), (t4121, ⟨false, false, false, true, false, true⟩), (t1569, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1122 : sliceCOK 11 15 d1122.1 L1 b1 11 ![4,4,5,6] d1122.2.1 0 d1122.2.2.1 d1122.2.2.2.1 [] d1122.2.2.2.2 = true := by decide +kernel
theorem g1122 : SliceGood 11 15 d1122.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 11 15 ![4,4,5,6] [] [])) sl1122
noncomputable def d1123 : CData := (![4,4,6,6], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t5, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1123 : sliceCOK 11 15 d1123.1 L3 b3 11 ![4,4,6,6] d1123.2.1 0 d1123.2.2.1 d1123.2.2.2.1 [] d1123.2.2.2.2 = true := by decide +kernel
theorem g1123 : SliceGood 11 15 d1123.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base3 (subM_zero (tgtM 11 15 ![4,4,6,6] [] [])) sl1123
noncomputable def d1124 : CData := (![4,5,4,5], [], [(t5708, ⟨false, false, false, true, true, true⟩), (t1625, ⟨false, false, false, false, false, false⟩), (t4663, ⟨false, false, false, true, false, true⟩), (t15, ⟨false, false, false, true, false, false⟩), (t5591, ⟨false, false, false, true, false, true⟩), (t9701, ⟨false, false, false, false, false, false⟩), (t3979, ⟨false, false, false, false, false, false⟩), (t5577, ⟨false, false, false, false, true, false⟩), (t6090, ⟨false, false, false, true, true, true⟩), (t3763, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl1124 : sliceCOK 11 15 d1124.1 L4 b4 11 ![4,5,4,5] d1124.2.1 0 d1124.2.2.1 d1124.2.2.2.1 [] d1124.2.2.2.2 = true := by decide +kernel
theorem g1124 : SliceGood 11 15 d1124.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base4 (subM_zero (tgtM 11 15 ![4,5,4,5] [] [])) sl1124
noncomputable def d1125 : CData := (![4,5,4,6], [], [(t2252, ⟨false, false, false, false, false, false⟩), (t248, ⟨false, false, false, false, false, false⟩), (t3770, ⟨false, false, false, true, true, false⟩), (t4479, ⟨false, false, false, true, false, false⟩), (t10, ⟨false, false, false, true, false, false⟩), (t4835, ⟨false, false, false, true, true, false⟩), (t1375, ⟨false, false, false, false, false, false⟩), (t15, ⟨false, false, false, true, false, false⟩), (t4901, ⟨false, false, false, false, true, true⟩), (t6348, ⟨false, false, false, false, false, true⟩), (t3876, ⟨false, false, false, true, true, false⟩), (t9458, ⟨false, false, false, true, true, true⟩), (t3876, ⟨false, false, false, true, true, true⟩), (t9071, ⟨false, false, false, true, true, true⟩), (t1402, ⟨false, false, false, false, false, false⟩), (t4, ⟨false, false, false, false, false, false⟩), (t6378, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl1125 : sliceCOK 11 15 d1125.1 L5 b5 11 ![4,5,4,6] d1125.2.1 0 d1125.2.2.1 d1125.2.2.2.1 [] d1125.2.2.2.2 = true := by decide +kernel
theorem g1125 : SliceGood 11 15 d1125.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 11 15 ![4,5,4,6] [] [])) sl1125
noncomputable def d1126 : CData := (![4,5,5,5], [], [(t3763, ⟨false, false, false, false, false, true⟩), (t6414, ⟨false, false, false, false, false, false⟩), (t3801, ⟨false, false, false, false, false, true⟩), (t4307, ⟨false, false, false, true, false, true⟩), (t3979, ⟨false, false, false, false, false, true⟩), (t6791, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl1126 : sliceCOK 11 15 d1126.1 L6 b6 11 ![4,5,5,5] d1126.2.1 0 d1126.2.2.1 d1126.2.2.2.1 [] d1126.2.2.2.2 = true := by decide +kernel
theorem g1126 : SliceGood 11 15 d1126.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 11 15 ![4,5,5,5] [] [])) sl1126
noncomputable def d1127 : CData := (![4,5,5,6], [], [(t2, ⟨false, false, false, false, false, false⟩), (t3998, ⟨false, false, false, true, true, true⟩), (t1625, ⟨false, false, false, false, false, false⟩), (t4902, ⟨false, false, false, false, true, false⟩), (t1418, ⟨false, false, false, false, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t1263, ⟨false, false, false, false, true, false⟩), (t3999, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl1127 : sliceCOK 11 15 d1127.1 L7 b7 11 ![4,5,5,6] d1127.2.1 0 d1127.2.2.1 d1127.2.2.2.1 [] d1127.2.2.2.2 = true := by decide +kernel
theorem g1127 : SliceGood 11 15 d1127.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base7 (subM_zero (tgtM 11 15 ![4,5,5,6] [] [])) sl1127
noncomputable def d1128 : CData := (![4,6,4,6], [], [(t3742, ⟨false, false, false, false, false, true⟩), (t4210, ⟨false, false, false, false, true, false⟩), (t3879, ⟨false, false, false, true, true, false⟩), (t92, ⟨false, false, false, false, false, false⟩), (t4293, ⟨false, false, false, true, false, false⟩), (t25, ⟨false, false, false, false, false, false⟩), (t4539, ⟨false, false, false, true, true, true⟩), (t6381, ⟨false, false, false, false, false, false⟩), (t6382, ⟨false, false, false, true, false, true⟩)], [], [])
theorem sl1128 : sliceCOK 11 15 d1128.1 L8 b8 11 ![4,6,4,6] d1128.2.1 0 d1128.2.2.1 d1128.2.2.2.1 [] d1128.2.2.2.2 = true := by decide +kernel
theorem g1128 : SliceGood 11 15 d1128.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base8 (subM_zero (tgtM 11 15 ![4,6,4,6] [] [])) sl1128
noncomputable def d1129 : CData := (![4,6,5,5], [], [(t3925, ⟨false, false, false, false, true, true⟩), (t1611, ⟨false, false, false, false, false, true⟩), (t3763, ⟨false, false, false, false, false, true⟩), (t1670, ⟨false, false, false, false, false, false⟩), (t6380, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl1129 : sliceCOK 11 15 d1129.1 L10 b10 11 ![4,6,5,5] d1129.2.1 0 d1129.2.2.1 d1129.2.2.2.1 [] d1129.2.2.2.2 = true := by decide +kernel
theorem g1129 : SliceGood 11 15 d1129.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base10 (subM_zero (tgtM 11 15 ![4,6,5,5] [] [])) sl1129
noncomputable def d1130 : CData := (![5,5,5,5], [], [(t3763, ⟨false, false, false, false, false, true⟩), (t5511, ⟨false, false, false, false, false, false⟩), (t1867, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl1130 : sliceCOK 11 15 d1130.1 L11 b11 11 ![5,5,5,5] d1130.2.1 0 d1130.2.2.1 d1130.2.2.2.1 [] d1130.2.2.2.2 = true := by decide +kernel
theorem g1130 : SliceGood 11 15 d1130.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base11 (subM_zero (tgtM 11 15 ![5,5,5,5] [] [])) sl1130
end BoxKGen.N11x15
