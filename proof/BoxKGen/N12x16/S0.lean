/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import BoxKGen.Templates
public import BoxKGen.N12x16.Base
-- Build order only (at most 2 certificate modules build at once).
import BoxKGen.N12x16.S5

@[expose] public section

set_option Elab.async false
namespace BoxKGen.N12x16
open ZZN ZZN.Cut ZZN.BoxK BoxKGen

noncomputable def d0 : CData := (![0,0,0,0], [], [(t2284, ⟨false, false, false, false, false, false⟩), (t3742, ⟨false, false, false, false, false, true⟩), (t3979, ⟨false, false, false, false, false, false⟩), (t1611, ⟨false, false, false, false, false, false⟩)], [(2413, 4369), (2415, 4369), (6508, 4369), (6510, 4369), (10605, 4369), (14700, 4369)], [])
theorem sl0 : sliceCOK 12 16 d0.1 L0 b0 12 ![0,0,0,0] d0.2.1 0 d0.2.2.1 d0.2.2.2.1 [] d0.2.2.2.2 = true := by decide +kernel
theorem g0 : SliceGood 12 16 d0.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base0 (subM_zero (tgtM 12 16 ![0,0,0,0] [] [])) sl0
noncomputable def d1 : CData := (![0,0,0,1], [], [(t2291, ⟨false, false, false, false, false, false⟩), (t2296, ⟨false, false, false, false, false, false⟩), (t5713, ⟨false, false, false, false, false, true⟩), (t4, ⟨false, false, false, false, false, false⟩), (t5389, ⟨false, false, false, false, true, false⟩), (t6769, ⟨false, false, false, true, false, false⟩), (t3879, ⟨false, false, false, true, true, true⟩), (t1626, ⟨false, false, false, false, false, false⟩)], [(6511, 4369), (14703, 4369)], [])
theorem sl1 : sliceCOK 12 16 d1.1 L1 b1 12 ![0,0,0,1] d1.2.1 0 d1.2.2.1 d1.2.2.2.1 [] d1.2.2.2.2 = true := by decide +kernel
theorem g1 : SliceGood 12 16 d1.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,1] [] [])) sl1
noncomputable def d2 : CData := (![0,0,0,2], [], [(t10, ⟨false, false, false, false, false, false⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1626, ⟨false, false, false, false, false, false⟩), (t1955, ⟨false, false, false, true, false, true⟩), (t1975, ⟨false, false, false, false, false, false⟩), (t1998, ⟨false, false, false, true, false, true⟩)], [(2415, 4369), (10607, 4369)], [])
theorem sl2 : sliceCOK 12 16 d2.1 L1 b1 12 ![0,0,0,2] d2.2.1 0 d2.2.2.1 d2.2.2.2.1 [] d2.2.2.2.2 = true := by decide +kernel
theorem g2 : SliceGood 12 16 d2.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,2] [] [])) sl2
noncomputable def d3 : CData := (![0,0,0,3], [], [(t10, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t1857, ⟨false, false, false, false, false, false⟩), (t1330, ⟨false, false, false, false, false, false⟩), (t668, ⟨false, false, false, false, true, false⟩), (t2455, ⟨false, false, false, true, false, true⟩)], [(6511, 4369), (14703, 4369)], [])
theorem sl3 : sliceCOK 12 16 d3.1 L1 b1 12 ![0,0,0,3] d3.2.1 0 d3.2.2.1 d3.2.2.2.1 [] d3.2.2.2.2 = true := by decide +kernel
theorem g3 : SliceGood 12 16 d3.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,3] [] [])) sl3
noncomputable def d4 : CData := (![0,0,0,4], [], [(t10, ⟨false, false, false, false, false, false⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1976, ⟨false, false, false, false, false, false⟩), (t1555, ⟨false, false, false, false, false, false⟩), (t1998, ⟨false, false, false, true, false, true⟩)], [(2415, 4369), (10607, 4369)], [])
theorem sl4 : sliceCOK 12 16 d4.1 L1 b1 12 ![0,0,0,4] d4.2.1 0 d4.2.2.1 d4.2.2.2.1 [] d4.2.2.2.2 = true := by decide +kernel
theorem g4 : SliceGood 12 16 d4.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,4] [] [])) sl4
noncomputable def d5 : CData := (![0,0,0,5], [], [(t3163, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1857, ⟨false, false, false, false, false, false⟩), (t1330, ⟨false, false, false, false, false, false⟩), (t668, ⟨false, false, false, false, true, false⟩), (t2455, ⟨false, false, false, true, false, true⟩)], [(6511, 4369), (14703, 4369)], [])
theorem sl5 : sliceCOK 12 16 d5.1 L1 b1 12 ![0,0,0,5] d5.2.1 0 d5.2.2.1 d5.2.2.2.1 [] d5.2.2.2.2 = true := by decide +kernel
theorem g5 : SliceGood 12 16 d5.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,5] [] [])) sl5
noncomputable def d6 : CData := (![0,0,0,6], [], [(t10, ⟨false, false, false, false, false, false⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1976, ⟨false, false, false, false, false, false⟩), (t1555, ⟨false, false, false, false, false, false⟩), (t1998, ⟨false, false, false, true, false, true⟩)], [(2415, 4369), (10607, 4369)], [])
theorem sl6 : sliceCOK 12 16 d6.1 L1 b1 12 ![0,0,0,6] d6.2.1 0 d6.2.2.1 d6.2.2.2.1 [] d6.2.2.2.2 = true := by decide +kernel
theorem g6 : SliceGood 12 16 d6.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,6] [] [])) sl6
noncomputable def d7 : CData := (![0,0,0,7], [], [(t3163, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1857, ⟨false, false, false, false, false, false⟩), (t1330, ⟨false, false, false, false, false, false⟩), (t668, ⟨false, false, false, false, true, false⟩), (t2455, ⟨false, false, false, true, false, true⟩)], [(6511, 4369), (14703, 4369)], [])
theorem sl7 : sliceCOK 12 16 d7.1 L1 b1 12 ![0,0,0,7] d7.2.1 0 d7.2.2.1 d7.2.2.2.1 [] d7.2.2.2.2 = true := by decide +kernel
theorem g7 : SliceGood 12 16 d7.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,7] [] [])) sl7
noncomputable def d8 : CData := (![0,0,0,8], [], [(t10, ⟨false, false, false, false, false, false⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1976, ⟨false, false, false, false, false, false⟩), (t1555, ⟨false, false, false, false, false, false⟩), (t1998, ⟨false, false, false, true, false, true⟩)], [(2415, 4369), (10607, 4369)], [])
theorem sl8 : sliceCOK 12 16 d8.1 L1 b1 12 ![0,0,0,8] d8.2.1 0 d8.2.2.1 d8.2.2.2.1 [] d8.2.2.2.2 = true := by decide +kernel
theorem g8 : SliceGood 12 16 d8.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,8] [] [])) sl8
noncomputable def d9 : CData := (![0,0,0,9], [], [(t3163, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1857, ⟨false, false, false, false, false, false⟩), (t1330, ⟨false, false, false, false, false, false⟩), (t1315, ⟨false, false, false, false, false, false⟩), (t2455, ⟨false, false, false, true, false, true⟩)], [(6511, 4369), (14703, 4369)], [])
theorem sl9 : sliceCOK 12 16 d9.1 L1 b1 12 ![0,0,0,9] d9.2.1 0 d9.2.2.1 d9.2.2.2.1 [] d9.2.2.2.2 = true := by decide +kernel
theorem g9 : SliceGood 12 16 d9.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,9] [] [])) sl9
noncomputable def d10 : CData := (![0,0,0,10], [], [(t7936, ⟨false, false, false, false, false, true⟩), (t1976, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t3798, ⟨false, false, false, false, false, false⟩), (t3772, ⟨false, false, false, false, true, false⟩), (t9733, ⟨false, false, false, true, true, true⟩)], [(2415, 4369), (10607, 4369)], [])
theorem sl10 : sliceCOK 12 16 d10.1 L1 b1 12 ![0,0,0,10] d10.2.1 0 d10.2.2.1 d10.2.2.2.1 [] d10.2.2.2.2 = true := by decide +kernel
theorem g10 : SliceGood 12 16 d10.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,10] [] [])) sl10
noncomputable def d11 : CData := (![0,0,0,11], [], [(t3163, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩)], [(2412, 4369), (2414, 4369), (3222, 4369), (3734, 4369), (6509, 4369), (6511, 4369), (7529, 4369), (10604, 4369), (10606, 4369), (11414, 4369), (14701, 4369), (14703, 4369)], [])
theorem sl11 : sliceCOK 12 16 d11.1 L1 b1 12 ![0,0,0,11] d11.2.1 0 d11.2.2.1 d11.2.2.2.1 [] d11.2.2.2.2 = true := by decide +kernel
theorem g11 : SliceGood 12 16 d11.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,0,11] [] [])) sl11
noncomputable def d12 : CData := (![0,0,1,1], [], [(t1331, ⟨false, false, false, false, false, true⟩), (t3742, ⟨false, false, false, false, false, true⟩), (t5389, ⟨false, false, false, false, false, false⟩), (t3979, ⟨false, false, false, false, false, false⟩), (t6815, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl12 : sliceCOK 12 16 d12.1 L2 b2 12 ![0,0,1,1] d12.2.1 0 d12.2.2.1 d12.2.2.2.1 [] d12.2.2.2.2 = true := by decide +kernel
theorem g12 : SliceGood 12 16 d12.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,1,1] [] [])) sl12
noncomputable def d13 : CData := (![0,0,1,2], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3954, ⟨false, false, false, true, true, true⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t1569, ⟨false, false, false, false, false, false⟩), (t4029, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl13 : sliceCOK 12 16 d13.1 L1 b1 12 ![0,0,1,2] d13.2.1 0 d13.2.2.1 d13.2.2.2.1 [] d13.2.2.2.2 = true := by decide +kernel
theorem g13 : SliceGood 12 16 d13.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,2] [] [])) sl13
noncomputable def d14 : CData := (![0,0,1,3], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t6824, ⟨false, false, false, true, false, false⟩), (t2343, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl14 : sliceCOK 12 16 d14.1 L1 b1 12 ![0,0,1,3] d14.2.1 0 d14.2.2.1 d14.2.2.2.1 [] d14.2.2.2.2 = true := by decide +kernel
theorem g14 : SliceGood 12 16 d14.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,3] [] [])) sl14
noncomputable def d15 : CData := (![0,0,1,4], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t1569, ⟨false, false, false, false, false, false⟩), (t3799, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl15 : sliceCOK 12 16 d15.1 L1 b1 12 ![0,0,1,4] d15.2.1 0 d15.2.2.1 d15.2.2.2.1 [] d15.2.2.2.2 = true := by decide +kernel
theorem g15 : SliceGood 12 16 d15.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,4] [] [])) sl15
noncomputable def d16 : CData := (![0,0,1,5], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t6824, ⟨false, false, false, true, false, false⟩), (t2343, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl16 : sliceCOK 12 16 d16.1 L1 b1 12 ![0,0,1,5] d16.2.1 0 d16.2.2.1 d16.2.2.2.1 [] d16.2.2.2.2 = true := by decide +kernel
theorem g16 : SliceGood 12 16 d16.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,5] [] [])) sl16
noncomputable def d17 : CData := (![0,0,1,6], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t1569, ⟨false, false, false, false, false, false⟩), (t3799, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl17 : sliceCOK 12 16 d17.1 L1 b1 12 ![0,0,1,6] d17.2.1 0 d17.2.2.1 d17.2.2.2.1 [] d17.2.2.2.2 = true := by decide +kernel
theorem g17 : SliceGood 12 16 d17.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,6] [] [])) sl17
noncomputable def d18 : CData := (![0,0,1,7], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t6824, ⟨false, false, false, true, false, false⟩), (t2343, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl18 : sliceCOK 12 16 d18.1 L1 b1 12 ![0,0,1,7] d18.2.1 0 d18.2.2.1 d18.2.2.2.1 [] d18.2.2.2.2 = true := by decide +kernel
theorem g18 : SliceGood 12 16 d18.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,7] [] [])) sl18
noncomputable def d19 : CData := (![0,0,1,8], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t1569, ⟨false, false, false, false, false, false⟩), (t3799, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl19 : sliceCOK 12 16 d19.1 L1 b1 12 ![0,0,1,8] d19.2.1 0 d19.2.2.1 d19.2.2.2.1 [] d19.2.2.2.2 = true := by decide +kernel
theorem g19 : SliceGood 12 16 d19.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,8] [] [])) sl19
noncomputable def d20 : CData := (![0,0,1,9], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t6824, ⟨false, false, false, true, false, false⟩), (t2343, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl20 : sliceCOK 12 16 d20.1 L1 b1 12 ![0,0,1,9] d20.2.1 0 d20.2.2.1 d20.2.2.2.1 [] d20.2.2.2.2 = true := by decide +kernel
theorem g20 : SliceGood 12 16 d20.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,9] [] [])) sl20
noncomputable def d21 : CData := (![0,0,1,10], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t2307, ⟨false, false, false, false, false, false⟩), (t1569, ⟨false, false, false, false, false, false⟩), (t3799, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl21 : sliceCOK 12 16 d21.1 L1 b1 12 ![0,0,1,10] d21.2.1 0 d21.2.2.1 d21.2.2.2.1 [] d21.2.2.2.2 = true := by decide +kernel
theorem g21 : SliceGood 12 16 d21.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,10] [] [])) sl21
noncomputable def d22 : CData := (![0,0,1,11], [], [(t3936, ⟨false, false, false, true, true, true⟩), (t6824, ⟨false, false, false, true, false, false⟩), (t3787, ⟨false, false, false, false, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl22 : sliceCOK 12 16 d22.1 L1 b1 12 ![0,0,1,11] d22.2.1 0 d22.2.2.1 d22.2.2.2.1 [] d22.2.2.2.2 = true := by decide +kernel
theorem g22 : SliceGood 12 16 d22.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,1,11] [] [])) sl22
noncomputable def d23 : CData := (![0,0,2,2], [], [(t5, ⟨false, false, false, false, false, false⟩), (t3874, ⟨false, false, false, false, false, true⟩), (t1263, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl23 : sliceCOK 12 16 d23.1 L2 b2 12 ![0,0,2,2] d23.2.1 0 d23.2.2.1 d23.2.2.2.1 [] d23.2.2.2.2 = true := by decide +kernel
theorem g23 : SliceGood 12 16 d23.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,2,2] [] [])) sl23
noncomputable def d24 : CData := (![0,0,2,3], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl24 : sliceCOK 12 16 d24.1 L1 b1 12 ![0,0,2,3] d24.2.1 0 d24.2.2.1 d24.2.2.2.1 [] d24.2.2.2.2 = true := by decide +kernel
theorem g24 : SliceGood 12 16 d24.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,3] [] [])) sl24
noncomputable def d25 : CData := (![0,0,2,4], [], [(t5, ⟨false, false, false, false, true, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t3857, ⟨false, false, false, true, true, true⟩), (t1263, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl25 : sliceCOK 12 16 d25.1 L1 b1 12 ![0,0,2,4] d25.2.1 0 d25.2.2.1 d25.2.2.2.1 [] d25.2.2.2.2 = true := by decide +kernel
theorem g25 : SliceGood 12 16 d25.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,4] [] [])) sl25
noncomputable def d26 : CData := (![0,0,2,5], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl26 : sliceCOK 12 16 d26.1 L1 b1 12 ![0,0,2,5] d26.2.1 0 d26.2.2.1 d26.2.2.2.1 [] d26.2.2.2.2 = true := by decide +kernel
theorem g26 : SliceGood 12 16 d26.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,5] [] [])) sl26
noncomputable def d27 : CData := (![0,0,2,6], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t3857, ⟨false, false, false, true, true, true⟩), (t1263, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl27 : sliceCOK 12 16 d27.1 L1 b1 12 ![0,0,2,6] d27.2.1 0 d27.2.2.1 d27.2.2.2.1 [] d27.2.2.2.2 = true := by decide +kernel
theorem g27 : SliceGood 12 16 d27.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,6] [] [])) sl27
noncomputable def d28 : CData := (![0,0,2,7], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl28 : sliceCOK 12 16 d28.1 L1 b1 12 ![0,0,2,7] d28.2.1 0 d28.2.2.1 d28.2.2.2.1 [] d28.2.2.2.2 = true := by decide +kernel
theorem g28 : SliceGood 12 16 d28.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,7] [] [])) sl28
noncomputable def d29 : CData := (![0,0,2,8], [], [(t5, ⟨false, false, false, false, true, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t3857, ⟨false, false, false, true, true, true⟩), (t1263, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl29 : sliceCOK 12 16 d29.1 L1 b1 12 ![0,0,2,8] d29.2.1 0 d29.2.2.1 d29.2.2.2.1 [] d29.2.2.2.2 = true := by decide +kernel
theorem g29 : SliceGood 12 16 d29.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,8] [] [])) sl29
noncomputable def d30 : CData := (![0,0,2,9], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl30 : sliceCOK 12 16 d30.1 L1 b1 12 ![0,0,2,9] d30.2.1 0 d30.2.2.1 d30.2.2.2.1 [] d30.2.2.2.2 = true := by decide +kernel
theorem g30 : SliceGood 12 16 d30.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,9] [] [])) sl30
noncomputable def d31 : CData := (![0,0,2,10], [], [(t5, ⟨false, false, false, false, true, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t3857, ⟨false, false, false, true, true, true⟩), (t1263, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl31 : sliceCOK 12 16 d31.1 L1 b1 12 ![0,0,2,10] d31.2.1 0 d31.2.2.1 d31.2.2.2.1 [] d31.2.2.2.2 = true := by decide +kernel
theorem g31 : SliceGood 12 16 d31.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,10] [] [])) sl31
noncomputable def d32 : CData := (![0,0,2,11], [], [(t5, ⟨false, false, false, false, true, false⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t3824, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl32 : sliceCOK 12 16 d32.1 L1 b1 12 ![0,0,2,11] d32.2.1 0 d32.2.2.1 d32.2.2.2.1 [] d32.2.2.2.2 = true := by decide +kernel
theorem g32 : SliceGood 12 16 d32.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,2,11] [] [])) sl32
noncomputable def d33 : CData := (![0,0,3,3], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl33 : sliceCOK 12 16 d33.1 L2 b2 12 ![0,0,3,3] d33.2.1 0 d33.2.2.1 d33.2.2.2.1 [] d33.2.2.2.2 = true := by decide +kernel
theorem g33 : SliceGood 12 16 d33.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,3,3] [] [])) sl33
noncomputable def d34 : CData := (![0,0,3,4], [], [(t14, ⟨false, false, false, false, false, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t4836, ⟨false, false, false, true, false, true⟩)], [], [])
theorem sl34 : sliceCOK 12 16 d34.1 L1 b1 12 ![0,0,3,4] d34.2.1 0 d34.2.2.1 d34.2.2.2.1 [] d34.2.2.2.2 = true := by decide +kernel
theorem g34 : SliceGood 12 16 d34.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,4] [] [])) sl34
noncomputable def d35 : CData := (![0,0,3,5], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl35 : sliceCOK 12 16 d35.1 L1 b1 12 ![0,0,3,5] d35.2.1 0 d35.2.2.1 d35.2.2.2.1 [] d35.2.2.2.2 = true := by decide +kernel
theorem g35 : SliceGood 12 16 d35.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,5] [] [])) sl35
noncomputable def d36 : CData := (![0,0,3,6], [], [(t14, ⟨false, false, false, false, false, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t59, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl36 : sliceCOK 12 16 d36.1 L1 b1 12 ![0,0,3,6] d36.2.1 0 d36.2.2.1 d36.2.2.2.1 [] d36.2.2.2.2 = true := by decide +kernel
theorem g36 : SliceGood 12 16 d36.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,6] [] [])) sl36
noncomputable def d37 : CData := (![0,0,3,7], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl37 : sliceCOK 12 16 d37.1 L1 b1 12 ![0,0,3,7] d37.2.1 0 d37.2.2.1 d37.2.2.2.1 [] d37.2.2.2.2 = true := by decide +kernel
theorem g37 : SliceGood 12 16 d37.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,7] [] [])) sl37
noncomputable def d38 : CData := (![0,0,3,8], [], [(t14, ⟨false, false, false, false, false, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t59, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl38 : sliceCOK 12 16 d38.1 L1 b1 12 ![0,0,3,8] d38.2.1 0 d38.2.2.1 d38.2.2.2.1 [] d38.2.2.2.2 = true := by decide +kernel
theorem g38 : SliceGood 12 16 d38.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,8] [] [])) sl38
noncomputable def d39 : CData := (![0,0,3,9], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl39 : sliceCOK 12 16 d39.1 L1 b1 12 ![0,0,3,9] d39.2.1 0 d39.2.2.1 d39.2.2.2.1 [] d39.2.2.2.2 = true := by decide +kernel
theorem g39 : SliceGood 12 16 d39.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,9] [] [])) sl39
noncomputable def d40 : CData := (![0,0,3,10], [], [(t14, ⟨false, false, false, false, false, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t59, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl40 : sliceCOK 12 16 d40.1 L1 b1 12 ![0,0,3,10] d40.2.1 0 d40.2.2.1 d40.2.2.2.1 [] d40.2.2.2.2 = true := by decide +kernel
theorem g40 : SliceGood 12 16 d40.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,10] [] [])) sl40
noncomputable def d41 : CData := (![0,0,3,11], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl41 : sliceCOK 12 16 d41.1 L1 b1 12 ![0,0,3,11] d41.2.1 0 d41.2.2.1 d41.2.2.2.1 [] d41.2.2.2.2 = true := by decide +kernel
theorem g41 : SliceGood 12 16 d41.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,3,11] [] [])) sl41
noncomputable def d42 : CData := (![0,0,4,4], [], [(t5, ⟨false, false, false, false, false, false⟩), (t3874, ⟨false, false, false, false, false, true⟩), (t4836, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl42 : sliceCOK 12 16 d42.1 L2 b2 12 ![0,0,4,4] d42.2.1 0 d42.2.2.1 d42.2.2.2.1 [] d42.2.2.2.2 = true := by decide +kernel
theorem g42 : SliceGood 12 16 d42.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,4,4] [] [])) sl42
noncomputable def d43 : CData := (![0,0,4,5], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl43 : sliceCOK 12 16 d43.1 L1 b1 12 ![0,0,4,5] d43.2.1 0 d43.2.2.1 d43.2.2.2.1 [] d43.2.2.2.2 = true := by decide +kernel
theorem g43 : SliceGood 12 16 d43.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,4,5] [] [])) sl43
noncomputable def d44 : CData := (![0,0,4,6], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t9749, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl44 : sliceCOK 12 16 d44.1 L1 b1 12 ![0,0,4,6] d44.2.1 0 d44.2.2.1 d44.2.2.2.1 [] d44.2.2.2.2 = true := by decide +kernel
theorem g44 : SliceGood 12 16 d44.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,4,6] [] [])) sl44
noncomputable def d45 : CData := (![0,0,4,7], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl45 : sliceCOK 12 16 d45.1 L1 b1 12 ![0,0,4,7] d45.2.1 0 d45.2.2.1 d45.2.2.2.1 [] d45.2.2.2.2 = true := by decide +kernel
theorem g45 : SliceGood 12 16 d45.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,4,7] [] [])) sl45
noncomputable def d46 : CData := (![0,0,4,8], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t9749, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl46 : sliceCOK 12 16 d46.1 L1 b1 12 ![0,0,4,8] d46.2.1 0 d46.2.2.1 d46.2.2.2.1 [] d46.2.2.2.2 = true := by decide +kernel
theorem g46 : SliceGood 12 16 d46.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,4,8] [] [])) sl46
noncomputable def d47 : CData := (![0,0,4,9], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl47 : sliceCOK 12 16 d47.1 L1 b1 12 ![0,0,4,9] d47.2.1 0 d47.2.2.1 d47.2.2.2.1 [] d47.2.2.2.2 = true := by decide +kernel
theorem g47 : SliceGood 12 16 d47.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,4,9] [] [])) sl47
noncomputable def d48 : CData := (![0,0,4,10], [], [(t5, ⟨false, false, false, false, true, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t9749, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl48 : sliceCOK 12 16 d48.1 L1 b1 12 ![0,0,4,10] d48.2.1 0 d48.2.2.1 d48.2.2.2.1 [] d48.2.2.2.2 = true := by decide +kernel
theorem g48 : SliceGood 12 16 d48.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,4,10] [] [])) sl48
noncomputable def d49 : CData := (![0,0,4,11], [], [(t5, ⟨false, false, false, false, true, false⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t3824, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl49 : sliceCOK 12 16 d49.1 L1 b1 12 ![0,0,4,11] d49.2.1 0 d49.2.2.1 d49.2.2.2.1 [] d49.2.2.2.2 = true := by decide +kernel
theorem g49 : SliceGood 12 16 d49.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,4,11] [] [])) sl49
noncomputable def d50 : CData := (![0,0,5,5], [], [(t5, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl50 : sliceCOK 12 16 d50.1 L2 b2 12 ![0,0,5,5] d50.2.1 0 d50.2.2.1 d50.2.2.2.1 [] d50.2.2.2.2 = true := by decide +kernel
theorem g50 : SliceGood 12 16 d50.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,5,5] [] [])) sl50
noncomputable def d51 : CData := (![0,0,5,6], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t4836, ⟨false, false, false, true, false, true⟩)], [], [])
theorem sl51 : sliceCOK 12 16 d51.1 L1 b1 12 ![0,0,5,6] d51.2.1 0 d51.2.2.1 d51.2.2.2.1 [] d51.2.2.2.2 = true := by decide +kernel
theorem g51 : SliceGood 12 16 d51.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,5,6] [] [])) sl51
noncomputable def d52 : CData := (![0,0,5,7], [], [(t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl52 : sliceCOK 12 16 d52.1 L1 b1 12 ![0,0,5,7] d52.2.1 0 d52.2.2.1 d52.2.2.2.1 [] d52.2.2.2.2 = true := by decide +kernel
theorem g52 : SliceGood 12 16 d52.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,5,7] [] [])) sl52
noncomputable def d53 : CData := (![0,0,5,8], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t59, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl53 : sliceCOK 12 16 d53.1 L1 b1 12 ![0,0,5,8] d53.2.1 0 d53.2.2.1 d53.2.2.2.1 [] d53.2.2.2.2 = true := by decide +kernel
theorem g53 : SliceGood 12 16 d53.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,5,8] [] [])) sl53
noncomputable def d54 : CData := (![0,0,5,9], [], [(t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl54 : sliceCOK 12 16 d54.1 L1 b1 12 ![0,0,5,9] d54.2.1 0 d54.2.2.1 d54.2.2.2.1 [] d54.2.2.2.2 = true := by decide +kernel
theorem g54 : SliceGood 12 16 d54.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,5,9] [] [])) sl54
noncomputable def d55 : CData := (![0,0,5,10], [], [(t5, ⟨false, false, false, false, true, false⟩), (t10721, ⟨false, false, false, true, true, true⟩), (t59, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl55 : sliceCOK 12 16 d55.1 L1 b1 12 ![0,0,5,10] d55.2.1 0 d55.2.2.1 d55.2.2.2.1 [] d55.2.2.2.2 = true := by decide +kernel
theorem g55 : SliceGood 12 16 d55.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,5,10] [] [])) sl55
noncomputable def d56 : CData := (![0,0,5,11], [], [(t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl56 : sliceCOK 12 16 d56.1 L1 b1 12 ![0,0,5,11] d56.2.1 0 d56.2.2.1 d56.2.2.2.1 [] d56.2.2.2.2 = true := by decide +kernel
theorem g56 : SliceGood 12 16 d56.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,5,11] [] [])) sl56
noncomputable def d57 : CData := (![0,0,6,6], [], [(t5, ⟨false, false, false, false, false, false⟩), (t3874, ⟨false, false, false, false, false, true⟩), (t4836, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl57 : sliceCOK 12 16 d57.1 L2 b2 12 ![0,0,6,6] d57.2.1 0 d57.2.2.1 d57.2.2.2.1 [] d57.2.2.2.2 = true := by decide +kernel
theorem g57 : SliceGood 12 16 d57.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,6,6] [] [])) sl57
noncomputable def d58 : CData := (![0,0,6,7], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl58 : sliceCOK 12 16 d58.1 L1 b1 12 ![0,0,6,7] d58.2.1 0 d58.2.2.1 d58.2.2.2.1 [] d58.2.2.2.2 = true := by decide +kernel
theorem g58 : SliceGood 12 16 d58.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,6,7] [] [])) sl58
noncomputable def d59 : CData := (![0,0,6,8], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t9749, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl59 : sliceCOK 12 16 d59.1 L1 b1 12 ![0,0,6,8] d59.2.1 0 d59.2.2.1 d59.2.2.2.1 [] d59.2.2.2.2 = true := by decide +kernel
theorem g59 : SliceGood 12 16 d59.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,6,8] [] [])) sl59
noncomputable def d60 : CData := (![0,0,6,9], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl60 : sliceCOK 12 16 d60.1 L1 b1 12 ![0,0,6,9] d60.2.1 0 d60.2.2.1 d60.2.2.2.1 [] d60.2.2.2.2 = true := by decide +kernel
theorem g60 : SliceGood 12 16 d60.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,6,9] [] [])) sl60
noncomputable def d61 : CData := (![0,0,6,10], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t9749, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl61 : sliceCOK 12 16 d61.1 L1 b1 12 ![0,0,6,10] d61.2.1 0 d61.2.2.1 d61.2.2.2.1 [] d61.2.2.2.2 = true := by decide +kernel
theorem g61 : SliceGood 12 16 d61.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,6,10] [] [])) sl61
noncomputable def d62 : CData := (![0,0,6,11], [], [(t5, ⟨false, false, false, false, true, false⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t3824, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl62 : sliceCOK 12 16 d62.1 L1 b1 12 ![0,0,6,11] d62.2.1 0 d62.2.2.1 d62.2.2.2.1 [] d62.2.2.2.2 = true := by decide +kernel
theorem g62 : SliceGood 12 16 d62.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,6,11] [] [])) sl62
noncomputable def d63 : CData := (![0,0,7,7], [], [(t5, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl63 : sliceCOK 12 16 d63.1 L2 b2 12 ![0,0,7,7] d63.2.1 0 d63.2.2.1 d63.2.2.2.1 [] d63.2.2.2.2 = true := by decide +kernel
theorem g63 : SliceGood 12 16 d63.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,7,7] [] [])) sl63
noncomputable def d64 : CData := (![0,0,7,8], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t4836, ⟨false, false, false, true, false, true⟩)], [], [])
theorem sl64 : sliceCOK 12 16 d64.1 L1 b1 12 ![0,0,7,8] d64.2.1 0 d64.2.2.1 d64.2.2.2.1 [] d64.2.2.2.2 = true := by decide +kernel
theorem g64 : SliceGood 12 16 d64.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,7,8] [] [])) sl64
noncomputable def d65 : CData := (![0,0,7,9], [], [(t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl65 : sliceCOK 12 16 d65.1 L1 b1 12 ![0,0,7,9] d65.2.1 0 d65.2.2.1 d65.2.2.2.1 [] d65.2.2.2.2 = true := by decide +kernel
theorem g65 : SliceGood 12 16 d65.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,7,9] [] [])) sl65
noncomputable def d66 : CData := (![0,0,7,10], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t59, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl66 : sliceCOK 12 16 d66.1 L1 b1 12 ![0,0,7,10] d66.2.1 0 d66.2.2.1 d66.2.2.2.1 [] d66.2.2.2.2 = true := by decide +kernel
theorem g66 : SliceGood 12 16 d66.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,7,10] [] [])) sl66
noncomputable def d67 : CData := (![0,0,7,11], [], [(t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl67 : sliceCOK 12 16 d67.1 L1 b1 12 ![0,0,7,11] d67.2.1 0 d67.2.2.1 d67.2.2.2.1 [] d67.2.2.2.2 = true := by decide +kernel
theorem g67 : SliceGood 12 16 d67.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,7,11] [] [])) sl67
noncomputable def d68 : CData := (![0,0,8,8], [], [(t5, ⟨false, false, false, false, false, false⟩), (t3874, ⟨false, false, false, false, false, true⟩), (t4836, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl68 : sliceCOK 12 16 d68.1 L2 b2 12 ![0,0,8,8] d68.2.1 0 d68.2.2.1 d68.2.2.2.1 [] d68.2.2.2.2 = true := by decide +kernel
theorem g68 : SliceGood 12 16 d68.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,8,8] [] [])) sl68
noncomputable def d69 : CData := (![0,0,8,9], [], [(t2682, ⟨false, false, false, false, false, false⟩), (t5, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl69 : sliceCOK 12 16 d69.1 L1 b1 12 ![0,0,8,9] d69.2.1 0 d69.2.2.1 d69.2.2.2.1 [] d69.2.2.2.2 = true := by decide +kernel
theorem g69 : SliceGood 12 16 d69.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,8,9] [] [])) sl69
noncomputable def d70 : CData := (![0,0,8,10], [], [(t5, ⟨false, false, false, false, true, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t9749, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl70 : sliceCOK 12 16 d70.1 L1 b1 12 ![0,0,8,10] d70.2.1 0 d70.2.2.1 d70.2.2.2.1 [] d70.2.2.2.2 = true := by decide +kernel
theorem g70 : SliceGood 12 16 d70.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,8,10] [] [])) sl70
noncomputable def d71 : CData := (![0,0,8,11], [], [(t5, ⟨false, false, false, false, true, false⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t3824, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl71 : sliceCOK 12 16 d71.1 L1 b1 12 ![0,0,8,11] d71.2.1 0 d71.2.2.1 d71.2.2.2.1 [] d71.2.2.2.2 = true := by decide +kernel
theorem g71 : SliceGood 12 16 d71.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,8,11] [] [])) sl71
noncomputable def d72 : CData := (![0,0,9,9], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl72 : sliceCOK 12 16 d72.1 L2 b2 12 ![0,0,9,9] d72.2.1 0 d72.2.2.1 d72.2.2.2.1 [] d72.2.2.2.2 = true := by decide +kernel
theorem g72 : SliceGood 12 16 d72.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,9,9] [] [])) sl72
noncomputable def d73 : CData := (![0,0,9,10], [], [(t14, ⟨false, false, false, false, false, false⟩), (t8277, ⟨false, false, false, true, true, true⟩), (t4836, ⟨false, false, false, true, false, true⟩)], [], [])
theorem sl73 : sliceCOK 12 16 d73.1 L1 b1 12 ![0,0,9,10] d73.2.1 0 d73.2.2.1 d73.2.2.2.1 [] d73.2.2.2.2 = true := by decide +kernel
theorem g73 : SliceGood 12 16 d73.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,9,10] [] [])) sl73
noncomputable def d74 : CData := (![0,0,9,11], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl74 : sliceCOK 12 16 d74.1 L1 b1 12 ![0,0,9,11] d74.2.1 0 d74.2.2.1 d74.2.2.2.1 [] d74.2.2.2.2 = true := by decide +kernel
theorem g74 : SliceGood 12 16 d74.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,9,11] [] [])) sl74
noncomputable def d75 : CData := (![0,0,10,10], [], [(t5, ⟨false, false, false, false, false, false⟩), (t2422, ⟨false, false, false, false, false, false⟩), (t4836, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl75 : sliceCOK 12 16 d75.1 L2 b2 12 ![0,0,10,10] d75.2.1 0 d75.2.2.1 d75.2.2.2.1 [] d75.2.2.2.2 = true := by decide +kernel
theorem g75 : SliceGood 12 16 d75.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base2 (subM_zero (tgtM 12 16 ![0,0,10,10] [] [])) sl75
noncomputable def d76 : CData := (![0,0,10,11], [], [(t5, ⟨false, false, false, false, true, false⟩), (t4836, ⟨false, false, false, true, true, true⟩), (t9750, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl76 : sliceCOK 12 16 d76.1 L1 b1 12 ![0,0,10,11] d76.2.1 0 d76.2.2.1 d76.2.2.2.1 [] d76.2.2.2.2 = true := by decide +kernel
theorem g76 : SliceGood 12 16 d76.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base1 (subM_zero (tgtM 12 16 ![0,0,10,11] [] [])) sl76
noncomputable def d77 : CData := (![0,0,11,11], [], [(t14, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl77 : sliceCOK 12 16 d77.1 L3 b3 12 ![0,0,11,11] d77.2.1 0 d77.2.2.1 d77.2.2.2.1 [] d77.2.2.2.2 = true := by decide +kernel
theorem g77 : SliceGood 12 16 d77.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base3 (subM_zero (tgtM 12 16 ![0,0,11,11] [] [])) sl77
noncomputable def d78 : CData := (![0,1,0,1], [], [(t3742, ⟨false, false, false, false, false, true⟩), (t2457, ⟨false, false, false, false, false, false⟩), (t3881, ⟨false, false, false, true, true, true⟩), (t4054, ⟨false, false, false, false, false, false⟩), (t3808, ⟨false, false, false, true, false, false⟩), (t3235, ⟨false, false, false, false, false, false⟩), (t2295, ⟨false, false, false, false, false, false⟩), (t1614, ⟨false, false, false, false, false, false⟩), (t4, ⟨false, false, false, false, true, false⟩), (t2282, ⟨false, false, false, true, false, false⟩)], [(28560, 4369)], [])
theorem sl78 : sliceCOK 12 16 d78.1 L4 b4 12 ![0,1,0,1] d78.2.1 0 d78.2.2.1 d78.2.2.2.1 [] d78.2.2.2.2 = true := by decide +kernel
theorem g78 : SliceGood 12 16 d78.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base4 (subM_zero (tgtM 12 16 ![0,1,0,1] [] [])) sl78
noncomputable def d79 : CData := (![0,1,0,2], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t2459, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t4479, ⟨false, false, false, true, false, false⟩), (t1313, ⟨false, false, false, false, true, true⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t1867, ⟨false, false, false, false, false, false⟩), (t3771, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl79 : sliceCOK 12 16 d79.1 L5 b5 12 ![0,1,0,2] d79.2.1 0 d79.2.2.1 d79.2.2.2.1 [] d79.2.2.2.2 = true := by decide +kernel
theorem g79 : SliceGood 12 16 d79.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,2] [] [])) sl79
noncomputable def d80 : CData := (![0,1,0,3], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t2500, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩), (t6892, ⟨false, false, false, false, false, true⟩)], [(28560, 4369)], [])
theorem sl80 : sliceCOK 12 16 d80.1 L5 b5 12 ![0,1,0,3] d80.2.1 0 d80.2.2.1 d80.2.2.2.1 [] d80.2.2.2.2 = true := by decide +kernel
theorem g80 : SliceGood 12 16 d80.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,3] [] [])) sl80
noncomputable def d81 : CData := (![0,1,0,4], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t1867, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t3771, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl81 : sliceCOK 12 16 d81.1 L5 b5 12 ![0,1,0,4] d81.2.1 0 d81.2.2.1 d81.2.2.2.1 [] d81.2.2.2.2 = true := by decide +kernel
theorem g81 : SliceGood 12 16 d81.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,4] [] [])) sl81
noncomputable def d82 : CData := (![0,1,0,5], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t2500, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩), (t6892, ⟨false, false, false, false, false, true⟩)], [(28560, 4369)], [])
theorem sl82 : sliceCOK 12 16 d82.1 L5 b5 12 ![0,1,0,5] d82.2.1 0 d82.2.2.1 d82.2.2.2.1 [] d82.2.2.2.2 = true := by decide +kernel
theorem g82 : SliceGood 12 16 d82.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,5] [] [])) sl82
noncomputable def d83 : CData := (![0,1,0,6], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t1867, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t3771, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl83 : sliceCOK 12 16 d83.1 L5 b5 12 ![0,1,0,6] d83.2.1 0 d83.2.2.1 d83.2.2.2.1 [] d83.2.2.2.2 = true := by decide +kernel
theorem g83 : SliceGood 12 16 d83.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,6] [] [])) sl83
noncomputable def d84 : CData := (![0,1,0,7], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t2500, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩), (t6892, ⟨false, false, false, false, false, true⟩)], [(28560, 4369)], [])
theorem sl84 : sliceCOK 12 16 d84.1 L5 b5 12 ![0,1,0,7] d84.2.1 0 d84.2.2.1 d84.2.2.2.1 [] d84.2.2.2.2 = true := by decide +kernel
theorem g84 : SliceGood 12 16 d84.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,7] [] [])) sl84
noncomputable def d85 : CData := (![0,1,0,8], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t1867, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t3771, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl85 : sliceCOK 12 16 d85.1 L5 b5 12 ![0,1,0,8] d85.2.1 0 d85.2.2.1 d85.2.2.2.1 [] d85.2.2.2.2 = true := by decide +kernel
theorem g85 : SliceGood 12 16 d85.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,8] [] [])) sl85
noncomputable def d86 : CData := (![0,1,0,9], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t2500, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩), (t6892, ⟨false, false, false, false, false, true⟩)], [(28560, 4369)], [])
theorem sl86 : sliceCOK 12 16 d86.1 L5 b5 12 ![0,1,0,9] d86.2.1 0 d86.2.2.1 d86.2.2.2.1 [] d86.2.2.2.2 = true := by decide +kernel
theorem g86 : SliceGood 12 16 d86.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,9] [] [])) sl86
noncomputable def d87 : CData := (![0,1,0,10], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t1867, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t2491, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl87 : sliceCOK 12 16 d87.1 L5 b5 12 ![0,1,0,10] d87.2.1 0 d87.2.2.1 d87.2.2.2.1 [] d87.2.2.2.2 = true := by decide +kernel
theorem g87 : SliceGood 12 16 d87.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,10] [] [])) sl87
noncomputable def d88 : CData := (![0,1,0,11], [], [(t10, ⟨false, false, false, true, false, false⟩), (t1612, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t2507, ⟨false, false, false, false, false, false⟩), (t5338, ⟨false, false, false, true, true, true⟩), (t3793, ⟨false, false, false, true, false, false⟩)], [(3990, 4369), (12182, 4369), (28560, 4369), (28562, 4369)], [])
theorem sl88 : sliceCOK 12 16 d88.1 L5 b5 12 ![0,1,0,11] d88.2.1 0 d88.2.2.1 d88.2.2.2.1 [] d88.2.2.2.2 = true := by decide +kernel
theorem g88 : SliceGood 12 16 d88.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,0,11] [] [])) sl88
noncomputable def d89 : CData := (![0,1,1,1], [], [(t4, ⟨false, false, false, false, true, false⟩), (t2440, ⟨false, false, false, false, false, false⟩), (t5713, ⟨false, false, false, false, false, false⟩), (t3235, ⟨false, false, false, false, true, false⟩), (t3819, ⟨false, false, false, false, true, true⟩), (t3881, ⟨false, false, false, true, true, false⟩), (t3879, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl89 : sliceCOK 12 16 d89.1 L6 b6 12 ![0,1,1,1] d89.2.1 0 d89.2.2.1 d89.2.2.2.1 [] d89.2.2.2.2 = true := by decide +kernel
theorem g89 : SliceGood 12 16 d89.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,1,1] [] [])) sl89
noncomputable def d90 : CData := (![0,1,1,2], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t2463, ⟨false, false, false, false, false, false⟩), (t772, ⟨false, false, false, true, false, false⟩), (t4054, ⟨false, false, false, false, true, true⟩), (t3895, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl90 : sliceCOK 12 16 d90.1 L5 b5 12 ![0,1,1,2] d90.2.1 0 d90.2.2.1 d90.2.2.2.1 [] d90.2.2.2.2 = true := by decide +kernel
theorem g90 : SliceGood 12 16 d90.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,2] [] [])) sl90
noncomputable def d91 : CData := (![0,1,1,3], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩), (t6963, ⟨false, false, false, true, false, true⟩), (t2500, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl91 : sliceCOK 12 16 d91.1 L5 b5 12 ![0,1,1,3] d91.2.1 0 d91.2.2.1 d91.2.2.2.1 [] d91.2.2.2.2 = true := by decide +kernel
theorem g91 : SliceGood 12 16 d91.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,3] [] [])) sl91
noncomputable def d92 : CData := (![0,1,1,4], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t3936, ⟨false, false, false, true, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t10387, ⟨false, false, false, true, false, true⟩), (t3895, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl92 : sliceCOK 12 16 d92.1 L5 b5 12 ![0,1,1,4] d92.2.1 0 d92.2.2.1 d92.2.2.2.1 [] d92.2.2.2.2 = true := by decide +kernel
theorem g92 : SliceGood 12 16 d92.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,4] [] [])) sl92
noncomputable def d93 : CData := (![0,1,1,5], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t2507, ⟨false, false, false, false, false, false⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl93 : sliceCOK 12 16 d93.1 L5 b5 12 ![0,1,1,5] d93.2.1 0 d93.2.2.1 d93.2.2.2.1 [] d93.2.2.2.2 = true := by decide +kernel
theorem g93 : SliceGood 12 16 d93.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,5] [] [])) sl93
noncomputable def d94 : CData := (![0,1,1,6], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t3936, ⟨false, false, false, true, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t10387, ⟨false, false, false, true, false, true⟩), (t3895, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl94 : sliceCOK 12 16 d94.1 L5 b5 12 ![0,1,1,6] d94.2.1 0 d94.2.2.1 d94.2.2.2.1 [] d94.2.2.2.2 = true := by decide +kernel
theorem g94 : SliceGood 12 16 d94.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,6] [] [])) sl94
noncomputable def d95 : CData := (![0,1,1,7], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t2507, ⟨false, false, false, false, false, false⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl95 : sliceCOK 12 16 d95.1 L5 b5 12 ![0,1,1,7] d95.2.1 0 d95.2.2.1 d95.2.2.2.1 [] d95.2.2.2.2 = true := by decide +kernel
theorem g95 : SliceGood 12 16 d95.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,7] [] [])) sl95
noncomputable def d96 : CData := (![0,1,1,8], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t3936, ⟨false, false, false, true, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t10387, ⟨false, false, false, true, false, true⟩), (t3895, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl96 : sliceCOK 12 16 d96.1 L5 b5 12 ![0,1,1,8] d96.2.1 0 d96.2.2.1 d96.2.2.2.1 [] d96.2.2.2.2 = true := by decide +kernel
theorem g96 : SliceGood 12 16 d96.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,8] [] [])) sl96
noncomputable def d97 : CData := (![0,1,1,9], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t2507, ⟨false, false, false, false, false, false⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t3770, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl97 : sliceCOK 12 16 d97.1 L5 b5 12 ![0,1,1,9] d97.2.1 0 d97.2.2.1 d97.2.2.2.1 [] d97.2.2.2.2 = true := by decide +kernel
theorem g97 : SliceGood 12 16 d97.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,9] [] [])) sl97
noncomputable def d98 : CData := (![0,1,1,10], [], [(t3936, ⟨false, false, false, false, true, true⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t3936, ⟨false, false, false, true, true, true⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t6915, ⟨false, false, false, false, false, false⟩), (t10387, ⟨false, false, false, true, false, true⟩), (t3895, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl98 : sliceCOK 12 16 d98.1 L5 b5 12 ![0,1,1,10] d98.2.1 0 d98.2.2.1 d98.2.2.2.1 [] d98.2.2.2.2 = true := by decide +kernel
theorem g98 : SliceGood 12 16 d98.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,10] [] [])) sl98
noncomputable def d99 : CData := (![0,1,1,11], [], [(t2507, ⟨false, false, false, false, false, false⟩), (t2343, ⟨false, false, false, false, false, false⟩), (t3936, ⟨false, false, false, false, true, true⟩), (t2576, ⟨false, false, false, false, false, false⟩), (t5338, ⟨false, false, false, true, true, true⟩), (t3787, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl99 : sliceCOK 12 16 d99.1 L5 b5 12 ![0,1,1,11] d99.2.1 0 d99.2.2.1 d99.2.2.2.1 [] d99.2.2.2.2 = true := by decide +kernel
theorem g99 : SliceGood 12 16 d99.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,1,11] [] [])) sl99
noncomputable def d100 : CData := (![0,1,2,2], [], [(t5, ⟨false, false, false, false, false, false⟩), (t7005, ⟨false, false, false, true, true, false⟩), (t5595, ⟨false, false, false, false, false, true⟩), (t2661, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl100 : sliceCOK 12 16 d100.1 L6 b6 12 ![0,1,2,2] d100.2.1 0 d100.2.2.1 d100.2.2.2.1 [] d100.2.2.2.2 = true := by decide +kernel
theorem g100 : SliceGood 12 16 d100.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,2,2] [] [])) sl100
noncomputable def d101 : CData := (![0,1,2,3], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t4395, ⟨false, false, false, true, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl101 : sliceCOK 12 16 d101.1 L5 b5 12 ![0,1,2,3] d101.2.1 0 d101.2.2.1 d101.2.2.2.1 [] d101.2.2.2.2 = true := by decide +kernel
theorem g101 : SliceGood 12 16 d101.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,3] [] [])) sl101
noncomputable def d102 : CData := (![0,1,2,4], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t60, ⟨false, false, false, false, false, false⟩), (t4118, ⟨false, false, false, true, false, true⟩), (t4121, ⟨false, false, false, true, false, true⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t3912, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl102 : sliceCOK 12 16 d102.1 L5 b5 12 ![0,1,2,4] d102.2.1 0 d102.2.2.1 d102.2.2.2.1 [] d102.2.2.2.2 = true := by decide +kernel
theorem g102 : SliceGood 12 16 d102.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,4] [] [])) sl102
noncomputable def d103 : CData := (![0,1,2,5], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t4395, ⟨false, false, false, true, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl103 : sliceCOK 12 16 d103.1 L5 b5 12 ![0,1,2,5] d103.2.1 0 d103.2.2.1 d103.2.2.2.1 [] d103.2.2.2.2 = true := by decide +kernel
theorem g103 : SliceGood 12 16 d103.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,5] [] [])) sl103
noncomputable def d104 : CData := (![0,1,2,6], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t4597, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, false, true⟩), (t4121, ⟨false, false, false, true, false, true⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t3912, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl104 : sliceCOK 12 16 d104.1 L5 b5 12 ![0,1,2,6] d104.2.1 0 d104.2.2.1 d104.2.2.2.1 [] d104.2.2.2.2 = true := by decide +kernel
theorem g104 : SliceGood 12 16 d104.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,6] [] [])) sl104
noncomputable def d105 : CData := (![0,1,2,7], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t4395, ⟨false, false, false, true, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl105 : sliceCOK 12 16 d105.1 L5 b5 12 ![0,1,2,7] d105.2.1 0 d105.2.2.1 d105.2.2.2.1 [] d105.2.2.2.2 = true := by decide +kernel
theorem g105 : SliceGood 12 16 d105.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,7] [] [])) sl105
noncomputable def d106 : CData := (![0,1,2,8], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t4597, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, false, true⟩), (t4121, ⟨false, false, false, true, false, true⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t3912, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl106 : sliceCOK 12 16 d106.1 L5 b5 12 ![0,1,2,8] d106.2.1 0 d106.2.2.1 d106.2.2.2.1 [] d106.2.2.2.2 = true := by decide +kernel
theorem g106 : SliceGood 12 16 d106.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,8] [] [])) sl106
noncomputable def d107 : CData := (![0,1,2,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t4395, ⟨false, false, false, true, false, false⟩), (t4054, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl107 : sliceCOK 12 16 d107.1 L5 b5 12 ![0,1,2,9] d107.2.1 0 d107.2.2.1 d107.2.2.2.1 [] d107.2.2.2.2 = true := by decide +kernel
theorem g107 : SliceGood 12 16 d107.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,9] [] [])) sl107
noncomputable def d108 : CData := (![0,1,2,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2459, ⟨false, false, false, false, false, false⟩), (t1677, ⟨false, false, false, true, false, true⟩), (t4118, ⟨false, false, false, true, false, true⟩), (t4121, ⟨false, false, false, true, false, true⟩), (t10316, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl108 : sliceCOK 12 16 d108.1 L5 b5 12 ![0,1,2,10] d108.2.1 0 d108.2.2.1 d108.2.2.2.1 [] d108.2.2.2.2 = true := by decide +kernel
theorem g108 : SliceGood 12 16 d108.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,10] [] [])) sl108
noncomputable def d109 : CData := (![0,1,2,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩), (t7331, ⟨false, false, false, true, true, true⟩), (t3824, ⟨false, false, false, true, false, true⟩), (t5338, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl109 : sliceCOK 12 16 d109.1 L5 b5 12 ![0,1,2,11] d109.2.1 0 d109.2.2.1 d109.2.2.2.1 [] d109.2.2.2.2 = true := by decide +kernel
theorem g109 : SliceGood 12 16 d109.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,2,11] [] [])) sl109
noncomputable def d110 : CData := (![0,1,3,3], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl110 : sliceCOK 12 16 d110.1 L6 b6 12 ![0,1,3,3] d110.2.1 0 d110.2.2.1 d110.2.2.2.1 [] d110.2.2.2.2 = true := by decide +kernel
theorem g110 : SliceGood 12 16 d110.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,3,3] [] [])) sl110
noncomputable def d111 : CData := (![0,1,3,4], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t4827, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl111 : sliceCOK 12 16 d111.1 L5 b5 12 ![0,1,3,4] d111.2.1 0 d111.2.2.1 d111.2.2.2.1 [] d111.2.2.2.2 = true := by decide +kernel
theorem g111 : SliceGood 12 16 d111.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,4] [] [])) sl111
noncomputable def d112 : CData := (![0,1,3,5], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl112 : sliceCOK 12 16 d112.1 L5 b5 12 ![0,1,3,5] d112.2.1 0 d112.2.2.1 d112.2.2.2.1 [] d112.2.2.2.2 = true := by decide +kernel
theorem g112 : SliceGood 12 16 d112.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,5] [] [])) sl112
noncomputable def d113 : CData := (![0,1,3,6], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩), (t3850, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl113 : sliceCOK 12 16 d113.1 L5 b5 12 ![0,1,3,6] d113.2.1 0 d113.2.2.1 d113.2.2.2.1 [] d113.2.2.2.2 = true := by decide +kernel
theorem g113 : SliceGood 12 16 d113.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,6] [] [])) sl113
noncomputable def d114 : CData := (![0,1,3,7], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl114 : sliceCOK 12 16 d114.1 L5 b5 12 ![0,1,3,7] d114.2.1 0 d114.2.2.1 d114.2.2.2.1 [] d114.2.2.2.2 = true := by decide +kernel
theorem g114 : SliceGood 12 16 d114.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,7] [] [])) sl114
noncomputable def d115 : CData := (![0,1,3,8], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t3850, ⟨false, false, false, true, true, false⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl115 : sliceCOK 12 16 d115.1 L5 b5 12 ![0,1,3,8] d115.2.1 0 d115.2.2.1 d115.2.2.2.1 [] d115.2.2.2.2 = true := by decide +kernel
theorem g115 : SliceGood 12 16 d115.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,8] [] [])) sl115
noncomputable def d116 : CData := (![0,1,3,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl116 : sliceCOK 12 16 d116.1 L5 b5 12 ![0,1,3,9] d116.2.1 0 d116.2.2.1 d116.2.2.2.1 [] d116.2.2.2.2 = true := by decide +kernel
theorem g116 : SliceGood 12 16 d116.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,9] [] [])) sl116
noncomputable def d117 : CData := (![0,1,3,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t3850, ⟨false, false, false, true, true, false⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl117 : sliceCOK 12 16 d117.1 L5 b5 12 ![0,1,3,10] d117.2.1 0 d117.2.2.1 d117.2.2.2.1 [] d117.2.2.2.2 = true := by decide +kernel
theorem g117 : SliceGood 12 16 d117.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,10] [] [])) sl117
noncomputable def d118 : CData := (![0,1,3,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl118 : sliceCOK 12 16 d118.1 L5 b5 12 ![0,1,3,11] d118.2.1 0 d118.2.2.1 d118.2.2.2.1 [] d118.2.2.2.2 = true := by decide +kernel
theorem g118 : SliceGood 12 16 d118.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,3,11] [] [])) sl118
noncomputable def d119 : CData := (![0,1,4,4], [], [(t5, ⟨false, false, false, false, false, false⟩), (t9811, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, false, true⟩), (t9881, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl119 : sliceCOK 12 16 d119.1 L6 b6 12 ![0,1,4,4] d119.2.1 0 d119.2.2.1 d119.2.2.2.1 [] d119.2.2.2.2 = true := by decide +kernel
theorem g119 : SliceGood 12 16 d119.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,4,4] [] [])) sl119
noncomputable def d120 : CData := (![0,1,4,5], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t9750, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, true, false⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl120 : sliceCOK 12 16 d120.1 L5 b5 12 ![0,1,4,5] d120.2.1 0 d120.2.2.1 d120.2.2.2.1 [] d120.2.2.2.2 = true := by decide +kernel
theorem g120 : SliceGood 12 16 d120.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,4,5] [] [])) sl120
noncomputable def d121 : CData := (![0,1,4,6], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t60, ⟨false, false, false, false, false, false⟩), (t4123, ⟨false, false, false, false, false, false⟩), (t7012, ⟨false, false, false, false, false, false⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl121 : sliceCOK 12 16 d121.1 L5 b5 12 ![0,1,4,6] d121.2.1 0 d121.2.2.1 d121.2.2.2.1 [] d121.2.2.2.2 = true := by decide +kernel
theorem g121 : SliceGood 12 16 d121.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,4,6] [] [])) sl121
noncomputable def d122 : CData := (![0,1,4,7], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩), (t11, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl122 : sliceCOK 12 16 d122.1 L5 b5 12 ![0,1,4,7] d122.2.1 0 d122.2.2.1 d122.2.2.2.1 [] d122.2.2.2.2 = true := by decide +kernel
theorem g122 : SliceGood 12 16 d122.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,4,7] [] [])) sl122
noncomputable def d123 : CData := (![0,1,4,8], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t4597, ⟨false, false, false, false, true, true⟩), (t4123, ⟨false, false, false, false, false, false⟩), (t7012, ⟨false, false, false, false, false, false⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl123 : sliceCOK 12 16 d123.1 L5 b5 12 ![0,1,4,8] d123.2.1 0 d123.2.2.1 d123.2.2.2.1 [] d123.2.2.2.2 = true := by decide +kernel
theorem g123 : SliceGood 12 16 d123.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,4,8] [] [])) sl123
noncomputable def d124 : CData := (![0,1,4,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩), (t11, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl124 : sliceCOK 12 16 d124.1 L5 b5 12 ![0,1,4,9] d124.2.1 0 d124.2.2.1 d124.2.2.2.1 [] d124.2.2.2.2 = true := by decide +kernel
theorem g124 : SliceGood 12 16 d124.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,4,9] [] [])) sl124
noncomputable def d125 : CData := (![0,1,4,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2459, ⟨false, false, false, false, false, false⟩), (t4123, ⟨false, false, false, false, false, false⟩), (t7012, ⟨false, false, false, false, false, false⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl125 : sliceCOK 12 16 d125.1 L5 b5 12 ![0,1,4,10] d125.2.1 0 d125.2.2.1 d125.2.2.2.1 [] d125.2.2.2.2 = true := by decide +kernel
theorem g125 : SliceGood 12 16 d125.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,4,10] [] [])) sl125
noncomputable def d126 : CData := (![0,1,4,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t8710, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩), (t9812, ⟨false, false, false, true, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl126 : sliceCOK 12 16 d126.1 L5 b5 12 ![0,1,4,11] d126.2.1 0 d126.2.2.1 d126.2.2.2.1 [] d126.2.2.2.2 = true := by decide +kernel
theorem g126 : SliceGood 12 16 d126.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,4,11] [] [])) sl126
noncomputable def d127 : CData := (![0,1,5,5], [], [(t5, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl127 : sliceCOK 12 16 d127.1 L6 b6 12 ![0,1,5,5] d127.2.1 0 d127.2.2.1 d127.2.2.2.1 [] d127.2.2.2.2 = true := by decide +kernel
theorem g127 : SliceGood 12 16 d127.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,5,5] [] [])) sl127
noncomputable def d128 : CData := (![0,1,5,6], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩), (t4827, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl128 : sliceCOK 12 16 d128.1 L5 b5 12 ![0,1,5,6] d128.2.1 0 d128.2.2.1 d128.2.2.2.1 [] d128.2.2.2.2 = true := by decide +kernel
theorem g128 : SliceGood 12 16 d128.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,5,6] [] [])) sl128
noncomputable def d129 : CData := (![0,1,5,7], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl129 : sliceCOK 12 16 d129.1 L5 b5 12 ![0,1,5,7] d129.2.1 0 d129.2.2.1 d129.2.2.2.1 [] d129.2.2.2.2 = true := by decide +kernel
theorem g129 : SliceGood 12 16 d129.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,5,7] [] [])) sl129
noncomputable def d130 : CData := (![0,1,5,8], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩), (t3850, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl130 : sliceCOK 12 16 d130.1 L5 b5 12 ![0,1,5,8] d130.2.1 0 d130.2.2.1 d130.2.2.2.1 [] d130.2.2.2.2 = true := by decide +kernel
theorem g130 : SliceGood 12 16 d130.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,5,8] [] [])) sl130
noncomputable def d131 : CData := (![0,1,5,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl131 : sliceCOK 12 16 d131.1 L5 b5 12 ![0,1,5,9] d131.2.1 0 d131.2.2.1 d131.2.2.2.1 [] d131.2.2.2.2 = true := by decide +kernel
theorem g131 : SliceGood 12 16 d131.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,5,9] [] [])) sl131
noncomputable def d132 : CData := (![0,1,5,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t3850, ⟨false, false, false, true, true, false⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl132 : sliceCOK 12 16 d132.1 L5 b5 12 ![0,1,5,10] d132.2.1 0 d132.2.2.1 d132.2.2.2.1 [] d132.2.2.2.2 = true := by decide +kernel
theorem g132 : SliceGood 12 16 d132.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,5,10] [] [])) sl132
noncomputable def d133 : CData := (![0,1,5,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl133 : sliceCOK 12 16 d133.1 L5 b5 12 ![0,1,5,11] d133.2.1 0 d133.2.2.1 d133.2.2.2.1 [] d133.2.2.2.2 = true := by decide +kernel
theorem g133 : SliceGood 12 16 d133.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,5,11] [] [])) sl133
noncomputable def d134 : CData := (![0,1,6,6], [], [(t5, ⟨false, false, false, false, false, false⟩), (t9811, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, false, true⟩), (t9881, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl134 : sliceCOK 12 16 d134.1 L6 b6 12 ![0,1,6,6] d134.2.1 0 d134.2.2.1 d134.2.2.2.1 [] d134.2.2.2.2 = true := by decide +kernel
theorem g134 : SliceGood 12 16 d134.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,6,6] [] [])) sl134
noncomputable def d135 : CData := (![0,1,6,7], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t9750, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, true, false⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl135 : sliceCOK 12 16 d135.1 L5 b5 12 ![0,1,6,7] d135.2.1 0 d135.2.2.1 d135.2.2.2.1 [] d135.2.2.2.2 = true := by decide +kernel
theorem g135 : SliceGood 12 16 d135.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,6,7] [] [])) sl135
noncomputable def d136 : CData := (![0,1,6,8], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t60, ⟨false, false, false, false, false, false⟩), (t4123, ⟨false, false, false, false, false, false⟩), (t7012, ⟨false, false, false, false, false, false⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl136 : sliceCOK 12 16 d136.1 L5 b5 12 ![0,1,6,8] d136.2.1 0 d136.2.2.1 d136.2.2.2.1 [] d136.2.2.2.2 = true := by decide +kernel
theorem g136 : SliceGood 12 16 d136.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,6,8] [] [])) sl136
noncomputable def d137 : CData := (![0,1,6,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t3785, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩), (t11, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl137 : sliceCOK 12 16 d137.1 L5 b5 12 ![0,1,6,9] d137.2.1 0 d137.2.2.1 d137.2.2.2.1 [] d137.2.2.2.2 = true := by decide +kernel
theorem g137 : SliceGood 12 16 d137.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,6,9] [] [])) sl137
noncomputable def d138 : CData := (![0,1,6,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2459, ⟨false, false, false, false, false, false⟩), (t4123, ⟨false, false, false, false, false, false⟩), (t7012, ⟨false, false, false, false, false, false⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl138 : sliceCOK 12 16 d138.1 L5 b5 12 ![0,1,6,10] d138.2.1 0 d138.2.2.1 d138.2.2.2.1 [] d138.2.2.2.2 = true := by decide +kernel
theorem g138 : SliceGood 12 16 d138.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,6,10] [] [])) sl138
noncomputable def d139 : CData := (![0,1,6,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t8710, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩), (t9812, ⟨false, false, false, true, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl139 : sliceCOK 12 16 d139.1 L5 b5 12 ![0,1,6,11] d139.2.1 0 d139.2.2.1 d139.2.2.2.1 [] d139.2.2.2.2 = true := by decide +kernel
theorem g139 : SliceGood 12 16 d139.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,6,11] [] [])) sl139
noncomputable def d140 : CData := (![0,1,7,7], [], [(t5, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl140 : sliceCOK 12 16 d140.1 L6 b6 12 ![0,1,7,7] d140.2.1 0 d140.2.2.1 d140.2.2.2.1 [] d140.2.2.2.2 = true := by decide +kernel
theorem g140 : SliceGood 12 16 d140.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,7,7] [] [])) sl140
noncomputable def d141 : CData := (![0,1,7,8], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩), (t4827, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl141 : sliceCOK 12 16 d141.1 L5 b5 12 ![0,1,7,8] d141.2.1 0 d141.2.2.1 d141.2.2.2.1 [] d141.2.2.2.2 = true := by decide +kernel
theorem g141 : SliceGood 12 16 d141.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,7,8] [] [])) sl141
noncomputable def d142 : CData := (![0,1,7,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t11, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl142 : sliceCOK 12 16 d142.1 L5 b5 12 ![0,1,7,9] d142.2.1 0 d142.2.2.1 d142.2.2.2.1 [] d142.2.2.2.2 = true := by decide +kernel
theorem g142 : SliceGood 12 16 d142.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,7,9] [] [])) sl142
noncomputable def d143 : CData := (![0,1,7,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩), (t3850, ⟨false, false, false, true, true, false⟩)], [], [])
theorem sl143 : sliceCOK 12 16 d143.1 L5 b5 12 ![0,1,7,10] d143.2.1 0 d143.2.2.1 d143.2.2.2.1 [] d143.2.2.2.2 = true := by decide +kernel
theorem g143 : SliceGood 12 16 d143.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,7,10] [] [])) sl143
noncomputable def d144 : CData := (![0,1,7,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl144 : sliceCOK 12 16 d144.1 L5 b5 12 ![0,1,7,11] d144.2.1 0 d144.2.2.1 d144.2.2.2.1 [] d144.2.2.2.2 = true := by decide +kernel
theorem g144 : SliceGood 12 16 d144.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,7,11] [] [])) sl144
noncomputable def d145 : CData := (![0,1,8,8], [], [(t5, ⟨false, false, false, false, false, false⟩), (t9811, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, false, true⟩), (t9881, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl145 : sliceCOK 12 16 d145.1 L6 b6 12 ![0,1,8,8] d145.2.1 0 d145.2.2.1 d145.2.2.2.1 [] d145.2.2.2.2 = true := by decide +kernel
theorem g145 : SliceGood 12 16 d145.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,8,8] [] [])) sl145
noncomputable def d146 : CData := (![0,1,8,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2682, ⟨false, false, false, false, false, false⟩), (t9750, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, true, false⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl146 : sliceCOK 12 16 d146.1 L5 b5 12 ![0,1,8,9] d146.2.1 0 d146.2.2.1 d146.2.2.2.1 [] d146.2.2.2.2 = true := by decide +kernel
theorem g146 : SliceGood 12 16 d146.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,8,9] [] [])) sl146
noncomputable def d147 : CData := (![0,1,8,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9743, ⟨false, false, false, false, false, true⟩), (t4123, ⟨false, false, false, false, false, false⟩), (t7012, ⟨false, false, false, false, false, false⟩), (t10316, ⟨false, false, false, false, false, true⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl147 : sliceCOK 12 16 d147.1 L5 b5 12 ![0,1,8,10] d147.2.1 0 d147.2.2.1 d147.2.2.2.1 [] d147.2.2.2.2 = true := by decide +kernel
theorem g147 : SliceGood 12 16 d147.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,8,10] [] [])) sl147
noncomputable def d148 : CData := (![0,1,8,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t2382, ⟨false, false, false, false, false, false⟩), (t8710, ⟨false, false, false, false, true, true⟩), (t4118, ⟨false, false, false, true, true, true⟩), (t9812, ⟨false, false, false, true, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩)], [], [])
theorem sl148 : sliceCOK 12 16 d148.1 L5 b5 12 ![0,1,8,11] d148.2.1 0 d148.2.2.1 d148.2.2.2.1 [] d148.2.2.2.2 = true := by decide +kernel
theorem g148 : SliceGood 12 16 d148.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,8,11] [] [])) sl148
noncomputable def d149 : CData := (![0,1,9,9], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl149 : sliceCOK 12 16 d149.1 L6 b6 12 ![0,1,9,9] d149.2.1 0 d149.2.2.1 d149.2.2.2.1 [] d149.2.2.2.2 = true := by decide +kernel
theorem g149 : SliceGood 12 16 d149.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,9,9] [] [])) sl149
noncomputable def d150 : CData := (![0,1,9,10], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9750, ⟨false, false, false, false, true, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t9824, ⟨false, false, false, true, false, false⟩), (t4827, ⟨false, false, false, false, false, true⟩)], [], [])
theorem sl150 : sliceCOK 12 16 d150.1 L5 b5 12 ![0,1,9,10] d150.2.1 0 d150.2.2.1 d150.2.2.2.1 [] d150.2.2.2.2 = true := by decide +kernel
theorem g150 : SliceGood 12 16 d150.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,9,10] [] [])) sl150
noncomputable def d151 : CData := (![0,1,9,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t11, ⟨false, false, false, false, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩), (t9824, ⟨false, false, false, true, false, false⟩)], [], [])
theorem sl151 : sliceCOK 12 16 d151.1 L5 b5 12 ![0,1,9,11] d151.2.1 0 d151.2.2.1 d151.2.2.2.1 [] d151.2.2.2.2 = true := by decide +kernel
theorem g151 : SliceGood 12 16 d151.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,1,9,11] [] [])) sl151
noncomputable def d152 : CData := (![0,1,10,10], [], [(t5, ⟨false, false, false, false, false, false⟩), (t4827, ⟨false, false, false, false, false, true⟩), (t2401, ⟨false, false, false, true, false, false⟩), (t4118, ⟨false, false, false, true, true, true⟩)], [], [])
theorem sl152 : sliceCOK 12 16 d152.1 L6 b6 12 ![0,1,10,10] d152.2.1 0 d152.2.2.1 d152.2.2.2.1 [] d152.2.2.2.2 = true := by decide +kernel
theorem g152 : SliceGood 12 16 d152.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base6 (subM_zero (tgtM 12 16 ![0,1,10,10] [] [])) sl152
noncomputable def d153 : CData := (![0,1,10,11], [], [(t3821, ⟨false, false, false, false, false, true⟩), (t9812, ⟨false, false, false, true, false, false⟩), (t41, ⟨false, false, false, false, true, false⟩), (t4827, ⟨false, false, false, false, true, true⟩)], [], [])
theorem sl153 : sliceCOK 12 16 d153.1 L7 b7 12 ![0,1,10,11] d153.2.1 0 d153.2.2.1 d153.2.2.2.1 [] d153.2.2.2.2 = true := by decide +kernel
theorem g153 : SliceGood 12 16 d153.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base7 (subM_zero (tgtM 12 16 ![0,1,10,11] [] [])) sl153
noncomputable def d154 : CData := (![0,2,0,2], [], [(t226, ⟨false, false, false, false, false, false⟩), (t7130, ⟨false, false, false, true, false, true⟩), (t3874, ⟨false, false, false, false, false, true⟩), (t3808, ⟨false, false, false, true, false, false⟩), (t3879, ⟨false, false, false, true, true, false⟩), (t1950, ⟨false, false, false, false, false, false⟩), (t7371, ⟨false, false, false, false, false, true⟩), (t7121, ⟨false, false, false, false, false, false⟩), (t1955, ⟨false, false, false, false, false, false⟩), (t25, ⟨false, false, false, false, false, false⟩)], [(28560, 4369)], [])
theorem sl154 : sliceCOK 12 16 d154.1 L4 b4 12 ![0,2,0,2] d154.2.1 0 d154.2.2.1 d154.2.2.2.1 [] d154.2.2.2.2 = true := by decide +kernel
theorem g154 : SliceGood 12 16 d154.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base4 (subM_zero (tgtM 12 16 ![0,2,0,2] [] [])) sl154
noncomputable def d155 : CData := (![0,2,0,3], [], [(t2048, ⟨false, false, false, false, false, false⟩), (t2906, ⟨false, false, false, false, false, false⟩), (t3895, ⟨false, false, false, false, false, false⟩), (t2055, ⟨false, false, false, false, false, false⟩), (t3742, ⟨false, false, false, false, false, true⟩), (t30, ⟨false, false, false, false, false, false⟩), (t3764, ⟨false, false, false, true, false, false⟩), (t1950, ⟨false, false, false, false, false, false⟩), (t410, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl155 : sliceCOK 12 16 d155.1 L5 b5 12 ![0,2,0,3] d155.2.1 0 d155.2.2.1 d155.2.2.2.1 [] d155.2.2.2.2 = true := by decide +kernel
theorem g155 : SliceGood 12 16 d155.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,2,0,3] [] [])) sl155
noncomputable def d156 : CData := (![0,2,0,4], [], [(t2832, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t2, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t2835, ⟨false, false, false, false, false, false⟩), (t1626, ⟨false, false, false, false, false, false⟩), (t9699, ⟨false, false, false, true, true, false⟩), (t25, ⟨false, false, false, false, false, false⟩), (t410, ⟨false, false, false, false, false, false⟩)], [(28560, 4369)], [])
theorem sl156 : sliceCOK 12 16 d156.1 L5 b5 12 ![0,2,0,4] d156.2.1 0 d156.2.2.1 d156.2.2.2.1 [] d156.2.2.2.2 = true := by decide +kernel
theorem g156 : SliceGood 12 16 d156.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,2,0,4] [] [])) sl156
noncomputable def d157 : CData := (![0,2,0,5], [], [(t2832, ⟨false, false, false, false, false, false⟩), (t2048, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1439, ⟨false, false, false, false, false, false⟩), (t4176, ⟨false, false, false, true, false, false⟩), (t2, ⟨false, false, false, false, false, false⟩), (t410, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl157 : sliceCOK 12 16 d157.1 L5 b5 12 ![0,2,0,5] d157.2.1 0 d157.2.2.1 d157.2.2.2.1 [] d157.2.2.2.2 = true := by decide +kernel
theorem g157 : SliceGood 12 16 d157.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,2,0,5] [] [])) sl157
noncomputable def d158 : CData := (![0,2,0,6], [], [(t2832, ⟨false, false, false, false, false, false⟩), (t10, ⟨false, false, false, false, false, false⟩), (t2, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t2835, ⟨false, false, false, false, false, false⟩), (t1626, ⟨false, false, false, false, false, false⟩), (t9699, ⟨false, false, false, true, true, false⟩), (t25, ⟨false, false, false, false, false, false⟩), (t410, ⟨false, false, false, false, false, false⟩)], [(28560, 4369)], [])
theorem sl158 : sliceCOK 12 16 d158.1 L5 b5 12 ![0,2,0,6] d158.2.1 0 d158.2.2.1 d158.2.2.2.1 [] d158.2.2.2.2 = true := by decide +kernel
theorem g158 : SliceGood 12 16 d158.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,2,0,6] [] [])) sl158
noncomputable def d159 : CData := (![0,2,0,7], [], [(t2832, ⟨false, false, false, false, false, false⟩), (t2048, ⟨false, false, false, false, false, false⟩), (t3793, ⟨false, false, false, false, false, false⟩), (t1439, ⟨false, false, false, false, false, false⟩), (t4176, ⟨false, false, false, true, false, false⟩), (t2, ⟨false, false, false, false, false, false⟩), (t410, ⟨false, false, false, false, false, false⟩)], [], [])
theorem sl159 : sliceCOK 12 16 d159.1 L5 b5 12 ![0,2,0,7] d159.2.1 0 d159.2.2.1 d159.2.2.2.1 [] d159.2.2.2.2 = true := by decide +kernel
theorem g159 : SliceGood 12 16 d159.1 := sliceCOK_sound (by decide) (by decide) (by decide) (by decide) base5 (subM_zero (tgtM 12 16 ![0,2,0,7] [] [])) sl159
end BoxKGen.N12x16
