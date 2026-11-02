/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import ZZN.Statement
public import Mathlib

@[expose] public section

/-!
# Basic definitions for Hamiltonian paths in rectangular grid graphs

See the module docstring in the original version of this file for the
overall intent. This revision fixes three build errors reported against the
first version:

* `And.decidable` / `Or.decidable` are not real constant names in this
  Lean/Mathlib version -- replaced with `infer_instance`, which doesn't
  require knowing the exact instance name, only that Lean's typeclass
  search can find *some* `Decidable` instance for the (very standard)
  pieces involved (`<`, `=`, `∧`, `∨` on `ℕ`).
* `List.Chain'` isn't found -- rather than chase down which Mathlib module
  it currently lives in (this has moved across versions), the
  "consecutive-adjacent" check is now defined directly by recursion on the
  list as a plain `Bool`-valued function, sidestepping the question
  entirely. This also makes the later `decide`-based proofs in
  `PrimeCases.lean` more robust (pure `Bool` computation, not a derived
  typeclass instance for an externally-defined relation).
-/

namespace GridHam



instance : DecidablePred (fun v => InBounds width height v) :=
  fun v => by unfold InBounds; infer_instance





/-- Every coordinate of a `width × height` grid, as a flat list (used to
state "covers every vertex" as a decidable `List` membership check rather
than a nested bounded quantifier over `ℕ`). -/
def allCoords (width height : ℕ) : List Coord :=
  (List.range width).flatMap (fun x => (List.range height).map (fun y => (x, y)))

/-- `p` is a genuine Hamiltonian path from `s` to `t` in the `width × height`
grid graph:

* it has exactly `width * height` vertices (one for every grid vertex),
* it starts at `s` and ends at `t`,
* it has no repeated vertex,
* every vertex it contains is in bounds,
* every in-bounds vertex is contained in it (together with the previous two
  conditions, this pins `p` down to being a permutation of the whole grid),
* every consecutive pair is grid-adjacent.
-/
def ValidPath (width height : ℕ) (s t : Coord) (p : List Coord) : Prop :=
  p.length = width * height ∧
  p.head? = some s ∧
  p.getLast? = some t ∧
  p.Nodup ∧
  (∀ v ∈ p, InBounds width height v) ∧
  (∀ v ∈ allCoords width height, v ∈ p) ∧
  chainAdjacent p = true

/-- A Hamiltonian path exists between `s` and `t` in the `width × height`
grid graph. This is the existential IPS's theorem characterizes. -/
def HasHamPath (width height : ℕ) (s t : Coord) : Prop :=
  ∃ p, ValidPath width height s t p

instance : DecidablePred (fun p => ValidPath width height s t p) :=
  fun p => by unfold ValidPath; infer_instance

end GridHam
