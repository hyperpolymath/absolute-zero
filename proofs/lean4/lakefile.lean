import Lake
open Lake DSL

package cno where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

lean_lib CNO where
  -- Core CNO library

@[default_target]
lean_exe absolute_zero where
  root := `CNO
