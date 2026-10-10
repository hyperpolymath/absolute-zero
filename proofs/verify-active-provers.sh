#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — reproduce the ACTIVE machine-checked verification.
#
# Owner ruling 2026-10-10: the active proof stack is Idris 2 (ABI) and Agda
# (CNO + OND). Z3 remains as bounded, expect-annotated checks. Coq, Lean 4,
# Isabelle/HOL and Mizar are retired from the active gate; their trees and their
# six-prover gate are archived under archive/proofs/ (see archive/README.adoc).
#
# Every active prover is REQUIRED: an absent toolchain is a failure, never a skip.
# Needs on PATH: agda, z3, idris2. The Agda standard library is registered via
# ~/.agda/libraries (see .github/workflows/proofs.yml for the pinned setup).
set -uo pipefail
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
HERE="$(cd "$(dirname "$0")" && pwd)"
fail=0
say() { printf '\n\033[1m== %s ==\033[0m\n' "$1"; }

# ---- Agda (CNO + OND + EchoBridge) ----------------------------------------
say "Agda — CNO + OND + EchoBridge"
if command -v agda >/dev/null; then
  ( cd "$HERE/agda" && for m in CNO OND EchoBridgeScaffold EchoBridgeCNO; do
      [ -f "$m.agda" ] || { echo "$m.agda MISSING"; exit 1; }
      echo "checking $m"; agda --safe --without-K "$m.agda" || exit 1
    done ) || { echo "AGDA FAILED"; fail=1; }
else echo "agda missing"; fail=1; fi

# ---- Z3 (bounded instances, expect-checked) --------------------------------
say "Z3 — expect-checked bounded instances (proofs/z3/verify.sh)"
if command -v z3 >/dev/null; then
  bash "$HERE/z3/verify.sh" || { echo "Z3 FAILED"; fail=1; }
else echo "z3 missing"; fail=1; fi

# ---- Idris 2 (ABI boundary) ------------------------------------------------
say "Idris 2 — ABI"
if command -v idris2 >/dev/null; then
  ( cd "$HERE/.." && idris2 --build absolute-zero-abi.ipkg ) \
     || { echo "IDRIS FAILED"; fail=1; }
else echo "idris2 missing"; fail=1; fi

echo
if [ "$fail" -eq 0 ]; then echo "ACTIVE-PROVERS-GREEN"; else echo "SOME ACTIVE PROVERS FAILED"; fi
exit "$fail"
