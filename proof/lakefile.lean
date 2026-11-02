/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import Lake
open Lake DSL

package «r2k2zzn» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- The main results; their imports bring in the generated certificate modules.
--
@[default_target]
lean_lib «Results» where
  roots := #[`ZZN.Main, `ZZN.Thin.Decide, `ZZN.Constr.Main, `ZZN.Timed.Main, `ZZN.Timed.Construct]
  precompileModules := false

lean_lib «FinalN» where
  precompileModules := false

lean_lib «BoxKGen» where
  globs := #[.submodules `BoxKGen]
  precompileModules := false

lean_lib «GridHam» where
  globs := #[.submodules `GridHam]
  precompileModules := false

lean_lib «WinKU» where
  globs := #[.submodules `WinKU]
  precompileModules := false

lean_lib «ZZN» where
  globs := #[.submodules `ZZN]
  precompileModules := false

-- The Palomar registry statement (`Challenge`, imports only Mathlib) and its solution.
--
lean_lib «Challenge» where

lean_lib «Solution» where
