/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ZZN.Timed.DecideR
import ZZN.Timed.RoundTimeR

/-!
The project declarations the registered statements depend on: the constants in the theorem
types, then, transitively, in the types and values of definitions and in the constructors of
inductive types (not in proofs). Prints `DECL module start end name` per declaration with a source
range; auxiliary constants (matchers, equation lemmas) are followed but not printed.

usage (from proof/): ROOTS="ZZN.T.a ZZN.T.b" lake env lean ../certgen/tools/Closure.lean
-/

open Lean


def inProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`ZZN).isPrefixOf m || (`GridHam).isPrefixOf m
  | none => false

#eval show CoreM Unit from do
  let env ← getEnv
  -- The roots: the theorem names in the environment variable ROOTS, separated by spaces.
  --
  let roots := ((← IO.getEnv "ROOTS").getD "").splitOn " " |>.filter (· ≠ "") |>.map String.toName
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  for r in roots do
    let some ci := env.find? r | throwError "missing {r}"
    todo := todo ++ ci.type.getUsedConstants
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !inProject env n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    todo := todo ++ ci.type.getUsedConstants
    -- An auxiliary constant (a matcher, `_f`, `_unary`, ...) has no source range. Its owner is
    -- copied too: a definition may reuse a matcher made for an earlier definition, and the copy
    -- reuses it only if that definition comes first in the challenge as well.
    --
    if (← findDeclarationRanges? n).isNone then todo := todo.push n.getPrefix
    match ci with
    | .defnInfo d => todo := todo ++ d.value.getUsedConstants
    | .inductInfo i => todo := todo ++ i.ctors.toArray
    | .ctorInfo c => todo := todo.push c.induct
    | _ => pure ()
  -- Modules in import order (the environment lists every module after its imports).
  --
  let mods := seen.toList.filterMap fun n => env.getModuleIdxFor? n |>.map (·.toNat)
  for i in (mods.eraseDups.toArray.qsort (· < ·)) do
    IO.println s!"MOD {env.header.moduleNames[i]!}"
  let mut out : Array String := #[]
  for n in seen.toList do
    let some i := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[i.toNat]!
    if let some r ← findDeclarationRanges? n then
      out := out.push s!"DECL {m} {r.range.pos.line} {r.range.endPos.line} {n}"
  for l in out.qsort (· < ·) do IO.println l
