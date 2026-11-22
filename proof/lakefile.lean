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
  roots := #[`ZZN.Main, `ZZN.Thin.Decide, `ZZN.Constr.Main, `ZZN.Timed.DecideR,
    `ZZN.Timed.RoundTimeR, `ZZN.Look.Main, `ZZN.Look.RoundTimeL]
  precompileModules := false

@[default_target]
lean_lib «FinalN» where
  precompileModules := false

@[default_target]
lean_lib «BoxKGen» where
  globs := #[.submodules `BoxKGen]
  precompileModules := false

@[default_target]
lean_lib «GridHam» where
  globs := #[.submodules `GridHam]
  precompileModules := false

@[default_target]
lean_lib «WinKU» where
  globs := #[.submodules `WinKU]
  precompileModules := false

@[default_target]
lean_lib «ZZN» where
  globs := #[.submodules `ZZN]
  precompileModules := false

-- The Palomar registrations: each challenge imports only Mathlib; each solution imports the
-- library modules that prove its theorems.
--
lean_lib «ChallengeDecide» where

@[default_target]
lean_lib «SolutionDecide» where

lean_lib «ChallengeConstruct» where

@[default_target]
lean_lib «SolutionConstruct» where
