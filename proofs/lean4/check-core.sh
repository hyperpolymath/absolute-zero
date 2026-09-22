#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Build the six Mathlib-free Lean 4 modules with the toolchain pinned in
# `lean-toolchain` and run the axiom audit (AxiomAudit.lean). This is the
# CI-side Lean gate (job `lean` in .github/workflows/proofs.yml); the two
# Mathlib-dependent modules (QuantumCNO, StatMech) stay on `lake build` in the
# local/container gate `proofs/verify-all-provers.sh`.
#
# Exit status is non-zero if any module fails to compile or if any
# `#guard_msgs` in AxiomAudit.lean does not match Lean's actual output.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
if [ -z "$toolchain" ]; then
  echo "::error::lean-toolchain is empty" >&2
  exit 1
fi
# `elan toolchain install` exits non-zero when the toolchain is already present
# (measured: "error: 'leanprover/lean4:v4.16.0' is already installed"), so
# install only when it is absent; `elan run` below fails loudly if it is unusable.
if ! elan toolchain list | awk '{print $1}' | grep -qxF -- "$toolchain"; then
  elan toolchain install "$toolchain"
fi
echo "toolchain: $toolchain"
elan run "$toolchain" lean --version

out="${LEAN_CORE_OUT:-$here/_out}"
if [ "$out" = "$here/_out" ]; then
  rm -rf -- "$out"
fi
mkdir -p "$out"

# Dependency order: CNOCategory and CNOBridge import CNO. The rest are leaves.
modules=(CNO OND CNOCategory CNOBridge FilesystemCNO LambdaCNO)
for m in "${modules[@]}"; do
  echo "== lean $m"
  LEAN_PATH="$out" elan run "$toolchain" lean --root=. -o "$out/$m.olean" "$m.lean"
done

echo "== axiom audit: every #guard_msgs in AxiomAudit.lean must match"
guards="$(grep -c '^#guard_msgs' AxiomAudit.lean)"
LEAN_PATH="$out" elan run "$toolchain" lean --root=. AxiomAudit.lean
echo "✓ Lean core: ${#modules[@]} modules compiled, $guards guards matched (toolchain $toolchain)"
