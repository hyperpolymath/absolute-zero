#!/usr/bin/env bash
# Absolute Zero — reproduce the machine-checked verification across every prover.
# Both pillars: CNO (certified null effect) and OND (certified null disclosure).
#
# Exit non-zero on the first prover that fails. Requires the toolchains on PATH
# (coqc, agda, lean/lake, z3, isabelle, idris2, mizar verifier). Prover binaries
# installed outside the system prefix are expected under ~/.local/bin.
set -uo pipefail
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
HERE="$(cd "$(dirname "$0")" && pwd)"
fail=0
say() { printf '\n\033[1m== %s ==\033[0m\n' "$1"; }

# ---- Coq (both pillars) --------------------------------------------------
say "Coq — CNO + OND"
if command -v coqc >/dev/null; then
  ( cd "$HERE/coq" && coq_makefile -f _CoqProject -o Makefile.all >/dev/null 2>&1 \
      && make -f Makefile.all -j"$(nproc)" ) || { echo "COQ FAILED"; fail=1; }
else echo "coqc missing"; fail=1; fi

# ---- Agda (CNO + OND) ----------------------------------------------------
say "Agda — CNO + OND"
if command -v agda >/dev/null; then
  ( cd "$HERE/agda" && for m in CNO OND EchoBridgeCNO; do
      [ -f "$m.agda" ] && { echo "checking $m"; agda --safe --without-K "$m.agda" || exit 1; }
    done ) || { echo "AGDA FAILED"; fail=1; }
else echo "agda missing"; fail=1; fi

# ---- Lean 4 (CNO + OND; needs Mathlib) -----------------------------------
say "Lean 4 — CNO + OND"
if command -v lake >/dev/null; then
  ( cd "$HERE/lean4" && lake build ) || { echo "LEAN FAILED"; fail=1; }
else echo "lake missing"; fail=1; fi

# ---- Z3 (OND bounded instances) ------------------------------------------
say "Z3 — OND bounded checks"
if command -v z3 >/dev/null; then
  z3 "$HERE/z3/ond/OND_checks.smt2" || { echo "Z3 FAILED"; fail=1; }
else echo "z3 missing"; fail=1; fi

# ---- Isabelle/HOL (CNO + OND) --------------------------------------------
say "Isabelle/HOL — CNO + OND"
if command -v isabelle >/dev/null; then
  ( cd "$HERE/isabelle" && isabelle build -d . AbsoluteZero-CNO ) \
     || { echo "ISABELLE FAILED"; fail=1; }
else echo "isabelle missing (skipped)"; fi

# ---- Mizar (CNO) ---------------------------------------------------------
say "Mizar — CNO"
if command -v verifier >/dev/null && [ -n "${MIZFILES:-}" ]; then
  ( cd "$HERE/mizar" && accom CNO && verifier CNO && [ ! -s CNO.err ] ) \
     || { echo "MIZAR FAILED (see CNO.err)"; fail=1; }
else echo "mizar verifier / MIZFILES not set (skipped)"; fi

# ---- Idris 2 (ABI boundary) ----------------------------------------------
say "Idris 2 — ABI"
if command -v idris2 >/dev/null; then
  ( cd "$HERE/.." && idris2 --build absolute-zero-abi.ipkg ) \
     || { echo "IDRIS FAILED"; fail=1; }
else echo "idris2 missing"; fail=1; fi

echo
if [ "$fail" -eq 0 ]; then echo "ALL-PROVERS-GREEN"; else echo "SOME PROVERS FAILED"; fi
exit "$fail"
