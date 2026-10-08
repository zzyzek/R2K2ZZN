-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Final
import ZZN.Boxes

/-!
# The characterization

On rectangles with both sides at least 11, an instance of two-color Zig-Zag Numberlink is
solvable exactly when it passes the forbidden-pattern catalogue. The catalogue test `Passes` is a
polynomial-time computation, so this gives the polynomial-time algorithm on this domain.
-/

namespace ZZN

/-- **Passing the catalogue is equivalent to solvability**, for both sides at least 11. -/
theorem passes_iff_solvable (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h) :
    Passes I ↔ Solvable I :=
  ⟨theoremA_final I hwf hw hh, Win.theoremB_final ⟨hw, hh, hwf⟩⟩

end ZZN
