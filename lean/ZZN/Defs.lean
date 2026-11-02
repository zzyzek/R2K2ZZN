-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
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

/-- `p` is a simple path in the `w × h` grid from `s` to `t`: it starts at `s`, ends at `t`, has no
repeated cell, stays in bounds, and consecutive cells are adjacent. -/
def IsPath (w h : ℕ) (s t : Coord) (p : List Coord) : Prop :=
  p.head? = some s ∧
  p.getLast? = some t ∧
  p.Nodup ∧
  (∀ v ∈ p, InBounds w h v) ∧
  chainAdjacent p = true

/-- An instance: a `w × h` grid with the endpoints of the two colors. -/
structure Inst where
  w  : ℕ
  h  : ℕ
  s0 : Coord
  t0 : Coord
  s1 : Coord
  t1 : Coord

/-- The instance is well formed: the four endpoints are distinct cells of the grid. -/
def Inst.WellFormed (I : Inst) : Prop :=
  InBounds I.w I.h I.s0 ∧ InBounds I.w I.h I.t0 ∧
  InBounds I.w I.h I.s1 ∧ InBounds I.w I.h I.t1 ∧
  I.s0 ≠ I.t0 ∧ I.s0 ≠ I.s1 ∧ I.s0 ≠ I.t1 ∧
  I.t0 ≠ I.s1 ∧ I.t0 ≠ I.t1 ∧ I.s1 ≠ I.t1

/-- `p, q` solve `I`: `p` is a path `s0 → t0`, `q` a path `s1 → t1`, they share no cell, and every
cell of the grid is on one of them. -/
def IsSolution (I : Inst) (p q : List Coord) : Prop :=
  IsPath I.w I.h I.s0 I.t0 p ∧
  IsPath I.w I.h I.s1 I.t1 q ∧
  (∀ v ∈ p, v ∉ q) ∧
  (∀ v, InBounds I.w I.h v → v ∈ p ∨ v ∈ q)

/-- The instance has a solution. -/
def Solvable (I : Inst) : Prop :=
  ∃ p q, IsSolution I p q

end ZZN
