/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Main
public import ZZN.Thin.Decide
public import ZZN.Constr.Main
public import ZZN.Timed.Main
public import ZZN.Timed.Construct

-- The axioms of the main results; expected: propext, Classical.choice, Quot.sound.
--
#print axioms ZZN.solvableB_iff
#print axioms ZZN.passes_iff_solvable
#print axioms ZZN.solveZZN_sound
#print axioms ZZN.solveZZN_complete
#print axioms ZZN.passes_iff_solvable_K
#print axioms ZZN.T.solvableBT_main
#print axioms ZZN.T.solveZZNT_time
#print axioms ZZN.T.solveZZNT_ret
#print axioms ZZN.T.solveZZNT_main
#print axioms ZZN.T.fires3T_iff_solvable
