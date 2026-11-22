/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import Lean

/-!
A fingerprint of the declarations the registered statements depend on, to compare a Palomar
challenge with its solution before running the comparator. Starting from the theorem types, it
follows every constant in the `ZZN` and `GridHam` namespaces (auxiliary matchers included)
through types, definition values and constructors, and prints one line per constant: its name,
kind and the hashes of its type and value. The challenge and the solution must print the same
lines.

usage (from proof/): lake env lean --run ../certgen/tools/HashDump.lean MODULE THEOREM...
-/

open Lean

def ours (n : Name) : Bool :=
  (`ZZN).isPrefixOf n || (`GridHam).isPrefixOf n

def main (args : List String) : IO Unit := do
  let mod :: roots := args | throw (IO.userError "usage: MODULE THEOREM...")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod.toName }] {}
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  for r in roots do
    let some ci := env.find? r.toName | throw (IO.userError s!"missing {r}")
    todo := todo ++ ci.type.getUsedConstants
  let mut out : Array String := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !ours n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    todo := todo ++ ci.type.getUsedConstants
    let (kind, v) := match ci with
      | .defnInfo d => ("def", hash d.value)
      | .thmInfo _ => ("thm", 0)
      | .opaqueInfo d => ("opaque", hash d.value)
      | .inductInfo _ => ("induct", 0)
      | .ctorInfo _ => ("ctor", 0)
      | .recInfo _ => ("rec", 0)
      | .axiomInfo _ => ("axiom", 0)
      | .quotInfo _ => ("quot", 0)
    match ci with
    | .defnInfo d => todo := todo ++ d.value.getUsedConstants
    | .inductInfo i => todo := todo ++ i.ctors.toArray
    | .ctorInfo c => todo := todo.push c.induct
    | _ => pure ()
    out := out.push s!"{n} {kind} {ci.levelParams} {hash ci.type} {v}"
  for l in out.qsort (· < ·) do IO.println l
