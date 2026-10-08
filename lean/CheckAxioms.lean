-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Thin.Decide

/-! Print the axioms of the main results. Run from `lean/` after building:
`lake env lean CheckAxioms.lean`. Expected: `propext`, `Classical.choice`, `Quot.sound`, plus,
for the first and third, the 154 `..._native.native_decide.ax_1_1` axioms (144 box checks and 10
window certificates); `ZZN.Thin.thinBF_iff` uses only the three standard axioms. -/

#print axioms ZZN.passes_iff_solvable
#print axioms ZZN.Thin.thinBF_iff
#print axioms ZZN.solvableB_iff
