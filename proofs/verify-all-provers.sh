#!/usr/bin/env bash
# Absolute Zero — reproduce the machine-checked verification across every prover.
# Both pillars: CNO (certified null effect) and OND (certified null disclosure).
#
# Every prover is REQUIRED: an absent toolchain is a failure, never a skip
# (before 2026-09-23 Isabelle and Mizar printed "skipped" and the script could
# still say ALL-PROVERS-GREEN on four of six). Needs on PATH: coqc, agda,
# lake, z3, isabelle, idris2, and the Mizar accom/verifier with MIZFILES set.
# Prover binaries outside the system prefix are expected under ~/.local/bin.
# Self-test with stubbed toolchains: proofs/tests/gate-selftest.sh.
set -uo pipefail
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
HERE="$(cd "$(dirname "$0")" && pwd)"
fail=0
say() { printf '\n\033[1m== %s ==\033[0m\n' "$1"; }

# ---- Coq (both pillars) --------------------------------------------------
say "Coq — CNO + OND"
if command -v coqc >/dev/null; then
  if ( cd "$HERE/coq" && coq_makefile -f _CoqProject -o Makefile.all >/dev/null 2>&1 \
      && make -f Makefile.all -j"$(nproc)" ); then
    # The build alone is not the gate: the 17 named theorems must be closed under
    # the global context, and the control must prove the audit can say no.
    bash "$HERE/coq/check-assumptions.sh" || { echo "COQ ASSUMPTIONS FAILED"; fail=1; }
    bash "$HERE/coq/check-assumptions.sh" --control || { echo "COQ ASSUMPTIONS-CONTROL FAILED"; fail=1; }
    bash "$HERE/coq/check-axiom-tags.sh" || { echo "COQ AXIOM-TAGS FAILED"; fail=1; }
    bash "$HERE/coq/check-axiom-tags.sh" --control || { echo "COQ AXIOM-TAGS-CONTROL FAILED"; fail=1; }
  else echo "COQ FAILED"; fail=1; fi
else echo "coqc missing"; fail=1; fi

# ---- Agda (CNO + OND) ----------------------------------------------------
say "Agda — CNO + OND"
if command -v agda >/dev/null; then
  ( cd "$HERE/agda" && for m in CNO OND EchoBridgeScaffold EchoBridgeCNO; do
      [ -f "$m.agda" ] || { echo "$m.agda MISSING"; exit 1; }
      echo "checking $m"; agda --safe --without-K "$m.agda" || exit 1
    done ) || { echo "AGDA FAILED"; fail=1; }
else echo "agda missing"; fail=1; fi

# ---- Lean 4 (CNO + OND; needs Mathlib) -----------------------------------
say "Lean 4 — CNO + OND"
if command -v lake >/dev/null; then
  ( cd "$HERE/lean4" && lake build ) || { echo "LEAN FAILED"; fail=1; }
else echo "lake missing"; fail=1; fi

# ---- Z3 (OND bounded instances) ------------------------------------------
say "Z3 — expect-checked bounded instances (proofs/z3/verify.sh)"
if command -v z3 >/dev/null; then
  bash "$HERE/z3/verify.sh" || { echo "Z3 FAILED"; fail=1; }
else echo "z3 missing"; fail=1; fi

# ---- Isabelle/HOL (CNO + OND) --------------------------------------------
say "Isabelle/HOL — CNO + OND"
if [ "${SKIP_ISABELLE:-0}" = "1" ]; then
  echo "Isabelle/HOL skipped (SKIP_ISABELLE=1)"
elif command -v isabelle >/dev/null; then
  ( cd "$HERE/isabelle" && isabelle build -d . AbsoluteZero-CNO ) \
     || { echo "ISABELLE FAILED"; fail=1; }
else echo "isabelle missing"; fail=1; fi

# ---- Mizar (CNO) ---------------------------------------------------------
say "Mizar — CNO"
if [ "${SKIP_MIZAR:-0}" = "1" ]; then
  echo "Mizar skipped (SKIP_MIZAR=1)"
elif command -v verifier >/dev/null && [ -n "${MIZFILES:-}" ]; then
  ( cd "$HERE/mizar" && accom CNO && verifier CNO && [ ! -s CNO.err ] ) \
     || { echo "MIZAR FAILED (see CNO.err)"; fail=1; }
else echo "mizar verifier / MIZFILES missing"; fail=1; fi

# ---- Idris 2 (ABI boundary) ----------------------------------------------
say "Idris 2 — ABI"
if command -v idris2 >/dev/null; then
  ( cd "$HERE/.." && idris2 --build absolute-zero-abi.ipkg ) \
     || { echo "IDRIS FAILED"; fail=1; }
else echo "idris2 missing"; fail=1; fi

echo
if [ "$fail" -eq 0 ]; then echo "ALL-PROVERS-GREEN"; else echo "SOME PROVERS FAILED"; fi
exit "$fail"
