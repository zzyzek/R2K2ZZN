/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.TimedStatement
public import ZZN.Constr.Band
public import ZZN.Timed.TimeM

@[expose] public section

/-!
# The counted band extension

`stretchT` is `stretch` written with the counted operations (`stretchT_ret`). The band extension
itself is counted in one pass by `bandExtLT` (`ZZN/Timed/BandL.lean`).

Constant-time helpers used directly: arithmetic and comparisons, `shiftAt`, `gap` (at most two
cells), building lists of at most four cells, pattern matches on options and on list heads.
-/

namespace ZZN.T

open ZZN GridHam

/-! ### Stretch -/

@[simp] lemma stretchT_ret (r : ℕ) : ∀ l : List Coord, (stretchT r l).ret = stretch r l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by simp only [stretchT, stretch, ret_bind, stretchT_ret r (b :: l)]

end ZZN.T
