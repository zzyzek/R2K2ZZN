/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Timed.Band
public import ZZN.Timed.CatalogueCost

@[expose] public section

/-!
# The time of the counted stretch

`stretchT_time`: stretching a path of `n` cells takes at most `3 n + 1` steps.
-/

namespace ZZN.T

open ZZN GridHam

/-! ### Time of the stretch -/

lemma stretchT_time (r : ℕ) : ∀ l : List Coord, (stretchT r l).time ≤ 3 * l.length + 1
  | [] => by simp [stretchT]
  | [_] => by simp [stretchT]
  | a :: b :: l => by
    have := stretchT_time r (b :: l)
    simp only [stretchT, time_bind, List.length_cons] at *
    omega

end ZZN.T
