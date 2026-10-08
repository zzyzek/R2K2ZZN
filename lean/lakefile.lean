-- SPDX-License-Identifier: CC0-1.0
-- To the extent possible under law, the author has waived all copyright and related or
-- neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).
import Lake
open Lake DSL

package «r2k2zzn» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- A copy of the IPS proof (GridHam2D-Lean), used for one-path pieces.
lean_lib «GridHam» where
  precompileModules := true

@[default_target]
lean_lib «ZZN» where
  precompileModules := true

lean_exe catcheck where
  root := `CatCheck.Main

lean_exe movecheck where
  root := `MoveCheck.Main

lean_exe movetime where
  root := `MoveTime.Main

lean_lib «MoveCheck» where

lean_exe soltime where
  root := `SolveTime.Main

lean_exe symcheck where
  root := `SymCheck.Main

lean_exe boxcheck where
  root := `BoxCheck.Main

lean_exe thintime where
  root := `ThinTime.Main

lean_exe statecount where
  root := `StateCount.Main
