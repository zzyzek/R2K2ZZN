/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Main
public import ZZN.Thin.Decide
public import ZZN.Constr.Main
public import ZZN.Timed.DecideR
public import ZZN.Timed.RoundTimeR
public import ZZN.Look.Main
public import ZZN.Look.RoundTimeL

-- The axioms of the main results; expected: propext, Classical.choice, Quot.sound.
--
-- Registered with Palomar (ChallengeDecide, ChallengeConstruct).
--
#print axioms ZZN.T.solvableBRT_main
#print axioms ZZN.T.fires3T_iff_solvable
#print axioms ZZN.T.solveZ3RT_main

-- The construction with lookup leaves (its statement holds the lookup tables, too large for a
-- Palomar challenge).
--
#print axioms ZZN.T.solveZ3LT_main
#print axioms ZZN.solveZ3L_main

-- The plain statements.
--
#print axioms ZZN.solvableB_iff
#print axioms ZZN.passes_iff_solvable
#print axioms ZZN.passes_iff_solvable_K
#print axioms ZZN.solveZZN_sound
#print axioms ZZN.solveZZN_complete
