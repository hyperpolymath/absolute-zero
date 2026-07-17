import Lake
open Lake DSL

package cno where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

-- Each proof file is exposed as its own library so `lake build` covers them
-- all. The `lean_exe absolute_zero` target was dropped — CNO.lean defines no
-- `main`, and the project's surface is theorem verification, not a binary.

@[default_target]
lean_lib CNO

@[default_target]
lean_lib CNOCategory

@[default_target]
lean_lib FilesystemCNO

@[default_target]
lean_lib LambdaCNO

@[default_target]
lean_lib QuantumCNO

@[default_target]
lean_lib StatMech

@[default_target]
lean_lib OND

-- Reversibility ↔ CNO bridge (mirror of the Coq A2 development). Deliberately
-- NOT a @[default_target]: it was authored where the Lean toolchain could not be
-- fetched (egress policy blocked the GitHub release, HTTP 403), so it is
-- unverified in that environment and must not gate the standard `lake build`.
-- Build/verify explicitly with `lake build CNOBridge`.
lean_lib CNOBridge
