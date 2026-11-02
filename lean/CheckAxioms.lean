-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Thin.Decide
import ZZN.Timed.Main
import ZZN.Timed.Construct

/-! Print the axioms of the main results. Run from `lean/` after building:
`lake env lean CheckAxioms.lean`. Expected: `propext`, `Classical.choice`, `Quot.sound`, plus,
for `passes_iff_solvable`, `solvableB_iff`, `solvableBT_main` and `solveZZN_complete`, the 154
`..._native.native_decide.ax_1_1` axioms (144 box checks and 10 window certificates). -/

#print axioms ZZN.passes_iff_solvable
#print axioms ZZN.Thin.thinBF_iff
#print axioms ZZN.solvableB_iff
#print axioms ZZN.T.solvableBT_time
#print axioms ZZN.T.solvableBT_main
#print axioms ZZN.solveZZN_sound
#print axioms ZZN.solveZZN_complete
#print axioms ZZN.T.solveZZNT_ret
#print axioms ZZN.T.solveZZNT_time
