/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import FinalN

@[expose] public section

/-!
# The characterization

On rectangles with both sides at least 11, an instance of two-color Zig-Zag Numberlink is
solvable exactly when it passes the forbidden-pattern catalogue. The proof is
`passes_iff_solvable_K` (`FinalN.lean`): Theorem A over the boxes (`BoxKGen`) and Theorem B over
the windows (`WinKU`), every certificate checked by the kernel.
-/

namespace ZZN

/-- **Passing the catalogue is equivalent to solvability**, for both sides at least 11. -/
theorem passes_iff_solvable (I : Inst) (hwf : I.WellFormed) (hw : 11 ≤ I.w) (hh : 11 ≤ I.h) :
    Passes I ↔ Solvable I :=
  passes_iff_solvable_K I hwf hw hh

end ZZN
