-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import ZZN.Statement
import GridHam.Basic

/-!
# Two-color Zig-Zag Numberlink on rectangles: the problem statement

This file is the part of the formalization that has to be read and trusted: everything else is
checked by Lean against these definitions.

Conventions follow `GridHam` (the Itai–Papadimitriou–Szwarcfiter formalization): a cell is a
`Coord = ℕ × ℕ`, the grid is `w × h` with `InBounds w h v ↔ v.1 < w ∧ v.2 < h`, and two cells
are `Adjacent` when they differ by 1 in exactly one coordinate.

An instance has endpoints `s0, t0` (color 0) and `s1, t1` (color 1). A solution is a pair of
vertex-disjoint paths, `s0 → t0` and `s1 → t1`, that together visit every cell.
-/

namespace ZZN

open GridHam






end ZZN
