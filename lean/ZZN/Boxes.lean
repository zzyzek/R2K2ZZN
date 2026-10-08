-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Finite2
import ZZN.Box.B11_11
import ZZN.Box.B11_12
import ZZN.Box.B11_13
import ZZN.Box.B11_14
import ZZN.Box.B11_15
import ZZN.Box.B11_16
import ZZN.Box.B11_17
import ZZN.Box.B11_18
import ZZN.Box.B11_19
import ZZN.Box.B11_20
import ZZN.Box.B11_21
import ZZN.Box.B11_22
import ZZN.Box.B12_11
import ZZN.Box.B12_12
import ZZN.Box.B12_13
import ZZN.Box.B12_14
import ZZN.Box.B12_15
import ZZN.Box.B12_16
import ZZN.Box.B12_17
import ZZN.Box.B12_18
import ZZN.Box.B12_19
import ZZN.Box.B12_20
import ZZN.Box.B12_21
import ZZN.Box.B12_22
import ZZN.Box.B13_11
import ZZN.Box.B13_12
import ZZN.Box.B13_13
import ZZN.Box.B13_14
import ZZN.Box.B13_15
import ZZN.Box.B13_16
import ZZN.Box.B13_17
import ZZN.Box.B13_18
import ZZN.Box.B13_19
import ZZN.Box.B13_20
import ZZN.Box.B13_21
import ZZN.Box.B13_22
import ZZN.Box.B14_11
import ZZN.Box.B14_12
import ZZN.Box.B14_13
import ZZN.Box.B14_14
import ZZN.Box.B14_15
import ZZN.Box.B14_16
import ZZN.Box.B14_17
import ZZN.Box.B14_18
import ZZN.Box.B14_19
import ZZN.Box.B14_20
import ZZN.Box.B14_21
import ZZN.Box.B14_22
import ZZN.Box.B15_11
import ZZN.Box.B15_12
import ZZN.Box.B15_13
import ZZN.Box.B15_14
import ZZN.Box.B15_15
import ZZN.Box.B15_16
import ZZN.Box.B15_17
import ZZN.Box.B15_18
import ZZN.Box.B15_19
import ZZN.Box.B15_20
import ZZN.Box.B15_21
import ZZN.Box.B15_22
import ZZN.Box.B16_11
import ZZN.Box.B16_12
import ZZN.Box.B16_13
import ZZN.Box.B16_14
import ZZN.Box.B16_15
import ZZN.Box.B16_16
import ZZN.Box.B16_17
import ZZN.Box.B16_18
import ZZN.Box.B16_19
import ZZN.Box.B16_20
import ZZN.Box.B16_21
import ZZN.Box.B16_22
import ZZN.Box.B17_11
import ZZN.Box.B17_12
import ZZN.Box.B17_13
import ZZN.Box.B17_14
import ZZN.Box.B17_15
import ZZN.Box.B17_16
import ZZN.Box.B17_17
import ZZN.Box.B17_18
import ZZN.Box.B17_19
import ZZN.Box.B17_20
import ZZN.Box.B17_21
import ZZN.Box.B17_22
import ZZN.Box.B18_11
import ZZN.Box.B18_12
import ZZN.Box.B18_13
import ZZN.Box.B18_14
import ZZN.Box.B18_15
import ZZN.Box.B18_16
import ZZN.Box.B18_17
import ZZN.Box.B18_18
import ZZN.Box.B18_19
import ZZN.Box.B18_20
import ZZN.Box.B18_21
import ZZN.Box.B18_22
import ZZN.Box.B19_11
import ZZN.Box.B19_12
import ZZN.Box.B19_13
import ZZN.Box.B19_14
import ZZN.Box.B19_15
import ZZN.Box.B19_16
import ZZN.Box.B19_17
import ZZN.Box.B19_18
import ZZN.Box.B19_19
import ZZN.Box.B19_20
import ZZN.Box.B19_21
import ZZN.Box.B19_22
import ZZN.Box.B20_11
import ZZN.Box.B20_12
import ZZN.Box.B20_13
import ZZN.Box.B20_14
import ZZN.Box.B20_15
import ZZN.Box.B20_16
import ZZN.Box.B20_17
import ZZN.Box.B20_18
import ZZN.Box.B20_19
import ZZN.Box.B20_20
import ZZN.Box.B20_21
import ZZN.Box.B20_22
import ZZN.Box.B21_11
import ZZN.Box.B21_12
import ZZN.Box.B21_13
import ZZN.Box.B21_14
import ZZN.Box.B21_15
import ZZN.Box.B21_16
import ZZN.Box.B21_17
import ZZN.Box.B21_18
import ZZN.Box.B21_19
import ZZN.Box.B21_20
import ZZN.Box.B21_21
import ZZN.Box.B21_22
import ZZN.Box.B22_11
import ZZN.Box.B22_12
import ZZN.Box.B22_13
import ZZN.Box.B22_14
import ZZN.Box.B22_15
import ZZN.Box.B22_16
import ZZN.Box.B22_17
import ZZN.Box.B22_18
import ZZN.Box.B22_19
import ZZN.Box.B22_20
import ZZN.Box.B22_21
import ZZN.Box.B22_22

/-!
# Theorem A with no hypotheses

Every box check holds (`ZZN/Box/*`, by `native_decide`), so `finite` holds and Theorem A follows
(`theoremA_final`).
-/

namespace ZZN

theorem boxes_all (w h a : ℕ) (hw1 : 11 ≤ w) (hw2 : w ≤ 22) (hh1 : 11 ≤ h) (hh2 : h ≤ 22)
    (ha : a < w) : checkBoxC (ckBox w h) w h a = true := by
  have key : ∀ (w h : ℕ), 11 ≤ w → w ≤ 22 → 11 ≤ h → h ≤ 22 →
      (List.range w).all (checkBoxC (ckBox w h) w h) = true := by
    intro w h hw1 hw2 hh1 hh2
    interval_cases w <;> interval_cases h
    · exact box_11_11
    · exact box_11_12
    · exact box_11_13
    · exact box_11_14
    · exact box_11_15
    · exact box_11_16
    · exact box_11_17
    · exact box_11_18
    · exact box_11_19
    · exact box_11_20
    · exact box_11_21
    · exact box_11_22
    · exact box_12_11
    · exact box_12_12
    · exact box_12_13
    · exact box_12_14
    · exact box_12_15
    · exact box_12_16
    · exact box_12_17
    · exact box_12_18
    · exact box_12_19
    · exact box_12_20
    · exact box_12_21
    · exact box_12_22
    · exact box_13_11
    · exact box_13_12
    · exact box_13_13
    · exact box_13_14
    · exact box_13_15
    · exact box_13_16
    · exact box_13_17
    · exact box_13_18
    · exact box_13_19
    · exact box_13_20
    · exact box_13_21
    · exact box_13_22
    · exact box_14_11
    · exact box_14_12
    · exact box_14_13
    · exact box_14_14
    · exact box_14_15
    · exact box_14_16
    · exact box_14_17
    · exact box_14_18
    · exact box_14_19
    · exact box_14_20
    · exact box_14_21
    · exact box_14_22
    · exact box_15_11
    · exact box_15_12
    · exact box_15_13
    · exact box_15_14
    · exact box_15_15
    · exact box_15_16
    · exact box_15_17
    · exact box_15_18
    · exact box_15_19
    · exact box_15_20
    · exact box_15_21
    · exact box_15_22
    · exact box_16_11
    · exact box_16_12
    · exact box_16_13
    · exact box_16_14
    · exact box_16_15
    · exact box_16_16
    · exact box_16_17
    · exact box_16_18
    · exact box_16_19
    · exact box_16_20
    · exact box_16_21
    · exact box_16_22
    · exact box_17_11
    · exact box_17_12
    · exact box_17_13
    · exact box_17_14
    · exact box_17_15
    · exact box_17_16
    · exact box_17_17
    · exact box_17_18
    · exact box_17_19
    · exact box_17_20
    · exact box_17_21
    · exact box_17_22
    · exact box_18_11
    · exact box_18_12
    · exact box_18_13
    · exact box_18_14
    · exact box_18_15
    · exact box_18_16
    · exact box_18_17
    · exact box_18_18
    · exact box_18_19
    · exact box_18_20
    · exact box_18_21
    · exact box_18_22
    · exact box_19_11
    · exact box_19_12
    · exact box_19_13
    · exact box_19_14
    · exact box_19_15
    · exact box_19_16
    · exact box_19_17
    · exact box_19_18
    · exact box_19_19
    · exact box_19_20
    · exact box_19_21
    · exact box_19_22
    · exact box_20_11
    · exact box_20_12
    · exact box_20_13
    · exact box_20_14
    · exact box_20_15
    · exact box_20_16
    · exact box_20_17
    · exact box_20_18
    · exact box_20_19
    · exact box_20_20
    · exact box_20_21
    · exact box_20_22
    · exact box_21_11
    · exact box_21_12
    · exact box_21_13
    · exact box_21_14
    · exact box_21_15
    · exact box_21_16
    · exact box_21_17
    · exact box_21_18
    · exact box_21_19
    · exact box_21_20
    · exact box_21_21
    · exact box_21_22
    · exact box_22_11
    · exact box_22_12
    · exact box_22_13
    · exact box_22_14
    · exact box_22_15
    · exact box_22_16
    · exact box_22_17
    · exact box_22_18
    · exact box_22_19
    · exact box_22_20
    · exact box_22_21
    · exact box_22_22
  exact List.all_eq_true.mp (key w h hw1 hw2 hh1 hh2) a (List.mem_range.mpr ha)

/-- **Theorem A**: every well-formed instance with both sides ≥ 11 that passes the catalogue is
solvable. -/
theorem theoremA_final (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h)
    (hP : Passes I) : Solvable I :=
  theoremA_fin (finite_of_checkC ckBox hck_ckBox boxes_all) I hwf hw hh hP

end ZZN
