#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — self-test for the prover gate.
#
# Proves that proofs/verify-all-provers.sh and proofs/z3/verify.sh turn RED when
# they should, using a stub toolchain on a private PATH (no real prover needed),
# plus two mutants under a REAL z3 (required on PATH). Every negative case must
# fail with the expected reason string, not merely a non-zero exit — a parse
# error would otherwise pass as a kill.
# HOME is overridden because the gate prepends $HOME/.local/bin:$HOME/.elan/bin.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PROOFS="$(cd "$HERE/.." && pwd)"
GATE="$PROOFS/verify-all-provers.sh"
Z3CHECK="$PROOFS/z3/verify.sh"
REAL_SMT2="$PROOFS/z3/ond/OND_checks.smt2"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/az-gate-selftest.XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT
STUB="$SCRATCH/bin"; mkdir -p "$STUB" "$SCRATCH/home"
cases=0; fails=0
# pass <label>: record and report a successful test case.
pass()  { cases=$((cases+1)); echo "PASS: $1"; }
# flunk <label>: record and report a failed test case.
flunk() { cases=$((cases+1)); fails=$((fails+1)); echo "FAIL: $1"; }

for s in "$GATE" "$Z3CHECK"; do bash -n "$s" || { echo "FAIL: $s does not parse"; exit 1; }; done

# mkstub <tool> [body]: create an executable stub, defaulting to success.
mkstub() { printf '#!/bin/sh\n%s\n' "${2:-exit 0}" > "$STUB/$1"; chmod +x "$STUB/$1"; }
for t in coqc coq_makefile make agda lake isabelle accom verifier idris2; do mkstub "$t"; done
# z3_stub <verdicts>: replace the z3 stub with the supplied solver output.
z3_stub() { mkstub z3 "case \"\${1:-}\" in --version) echo \"Z3 version stub\";; *) printf '$1';; esac"; }
z3_stub 'sat\nunsat\nsat\n'
# coqc must answer `Print Assumptions` faithfully, or the audit inside the gate
# (proofs/coq/check-assumptions.sh) cannot be exercised: one "Closed under the
# global context" per Print Assumptions line, except the control's target
# (landauer_limit_positive), which rests on the tagged axiom kB_positive.
# COQC_STUB_MODE=axioms  -> every theorem reports an axiom (case O)
# COQC_STUB_MODE=closed  -> every theorem reports closed, control included (case P)
cat > "$STUB/coqc" <<'COQC'
#!/bin/sh
f=""; for a in "$@"; do case "$a" in *.v) f=$a;; esac; done
[ -n "$f" ] && [ -r "$f" ] || exit 0
grep '^Print Assumptions' "$f" | while IFS= read -r line; do
  id=${line#Print Assumptions }; id=${id%.}
  case "${COQC_STUB_MODE:-}:$id" in
    axioms:*|:*landauer_limit_positive*) printf 'Axioms:\nPhysicsConstants.kB_positive : (0 < kB)%%R\n';;
    *) echo "Closed under the global context";;
  esac
done
exit 0
COQC
chmod +x "$STUB/coqc"
for s in "$STUB"/*; do sh -n "$s" || { echo "FAIL: stub $s does not parse"; exit 1; }; done

OUT=""; RC=0
# run_gate: capture the gate's output and exit status with the stub toolchain.
run_gate() { OUT="$(HOME="$SCRATCH/home" PATH="$STUB:/usr/bin:/bin" MIZFILES="${MIZ-$SCRATCH/miz}" SKIP_ISABELLE="${SKIP_ISABELLE:-0}" SKIP_MIZAR="${SKIP_MIZAR:-0}" bash "$GATE" 2>&1)"; RC=$?; }
# expect <label> <exit-wanted> <must-contain> <must-not-contain>
expect() {
  local label=$1 want=$2 must=$3 mustnot=$4
  if [ "$RC" -ne "$want" ]; then flunk "$label — exit $RC, wanted $want"; printf '%s\n' "$OUT" | tail -6 | sed 's/^/    /'; return; fi
  if [ -n "$must" ] && ! printf '%s\n' "$OUT" | grep -qF -- "$must"; then flunk "$label — output lacks '$must'"; printf '%s\n' "$OUT" | tail -6 | sed 's/^/    /'; return; fi
  if [ -n "$mustnot" ] && printf '%s\n' "$OUT" | grep -qF -- "$mustnot"; then flunk "$label — output contains '$mustnot'"; return; fi
  pass "$label"
}

# A. positive control: every stub present and green
run_gate; expect "A all provers present -> ALL-PROVERS-GREEN" 0 "ALL-PROVERS-GREEN" "SOME PROVERS FAILED"
# B. isabelle absent must FAIL (pre-2026-09-23: printed 'skipped', stayed green)
mv "$STUB/isabelle" "$SCRATCH/isabelle.off"; run_gate
expect "B isabelle absent -> fail" 1 "isabelle missing" "ALL-PROVERS-GREEN"
# B2. isabelle absent with SKIP_ISABELLE=1 succeeds (issue #161)
SKIP_ISABELLE=1 run_gate
expect "B2 isabelle absent with SKIP_ISABELLE=1 -> pass" 0 "Isabelle/HOL skipped (SKIP_ISABELLE=1)" "SOME PROVERS FAILED"
unset SKIP_ISABELLE
mv "$SCRATCH/isabelle.off" "$STUB/isabelle"
# C. mizar verifier absent must FAIL
mv "$STUB/verifier" "$SCRATCH/verifier.off"; run_gate
expect "C mizar verifier absent -> fail" 1 "mizar verifier / MIZFILES missing" "ALL-PROVERS-GREEN"
# C2. mizar absent with SKIP_MIZAR=1 succeeds (issue #161)
SKIP_MIZAR=1 run_gate
expect "C2 mizar absent with SKIP_MIZAR=1 -> pass" 0 "Mizar skipped (SKIP_MIZAR=1)" "SOME PROVERS FAILED"
unset SKIP_MIZAR
mv "$SCRATCH/verifier.off" "$STUB/verifier"
# D. MIZFILES unset must FAIL
MIZ="" run_gate; expect "D MIZFILES unset -> fail" 1 "mizar verifier / MIZFILES missing" "ALL-PROVERS-GREEN"
# E. z3 verdict drift (second verdict sat instead of unsat) must FAIL
z3_stub 'sat\nsat\nsat\n'; run_gate
expect "E z3 verdict mismatch -> fail" 1 "verdicts differ from annotations" "ALL-PROVERS-GREEN"
# F. z3 (error ...) line must FAIL even when the verdicts match
z3_stub 'sat\n(error "boom")\nunsat\nsat\n'; run_gate
expect "F z3 (error line -> fail" 1 "z3 reported an error" "ALL-PROVERS-GREEN"
# G. z3 'unknown' must FAIL
z3_stub 'sat\nunknown\nsat\n'; run_gate
expect "G z3 unknown verdict -> fail" 1 "verdicts differ from annotations" "ALL-PROVERS-GREEN"
z3_stub 'sat\nunsat\nsat\n'
# H. a prover that runs but fails must FAIL
mkstub idris2 'exit 3'; run_gate; expect "H idris2 exit 3 -> fail" 1 "IDRIS FAILED" "ALL-PROVERS-GREEN"; mkstub idris2
# O. Coq builds but a theorem rests on an axiom: the audit must turn the gate red
#    (pre-2026-09-23 the canonical gate never ran the audit, so this was green)
export COQC_STUB_MODE=axioms; run_gate; unset COQC_STUB_MODE
expect "O coq audit sees Axioms: -> fail" 1 "COQ ASSUMPTIONS FAILED" "ALL-PROVERS-GREEN"
# P. an audit that calls EVERYTHING closed, the control's target included, must FAIL
export COQC_STUB_MODE=closed; run_gate; unset COQC_STUB_MODE
expect "P coq control passes wrongly -> fail" 1 "COQ ASSUMPTIONS-CONTROL FAILED" "ALL-PROVERS-GREEN"
# I. after the mutants, the positive control is green again (no state leaked)
run_gate; expect "I positive control repeats green" 0 "ALL-PROVERS-GREEN" "SOME PROVERS FAILED"

# ---- the expect-checker under a REAL z3 ------------------------------------
if ! command -v z3 >/dev/null; then flunk "J-M need a real z3 on PATH"; else
  # J. positive control: the committed file matches its annotations
  OUT="$(bash "$Z3CHECK" 2>&1)"; RC=$?; expect "J real z3, committed OND_checks.smt2 -> OK" 0 "Z3-CHECK OK" "Z3-CHECK FAILED"
  # K. expect-flipped mutant: 'expect unsat' -> 'expect sat' must FAIL
  mkdir -p "$SCRATCH/k"; sed 's/; expect unsat/; expect sat/' "$REAL_SMT2" > "$SCRATCH/k/mutant.smt2"
  grep -q '; expect unsat' "$SCRATCH/k/mutant.smt2" && flunk "K mutant not applied"
  OUT="$(bash "$Z3CHECK" "$SCRATCH/k" 2>&1)"; RC=$?; expect "K real z3, expect-flipped mutant -> fail" 1 "verdicts differ from annotations" "Z3-CHECK OK"
  # L. an unannotated (check-sat) must FAIL
  mkdir -p "$SCRATCH/l"; sed 's/; expect .*$//' "$REAL_SMT2" > "$SCRATCH/l/bare.smt2"
  OUT="$(bash "$Z3CHECK" "$SCRATCH/l" 2>&1)"; RC=$?; expect "L real z3, (check-sat) without expect -> fail" 1 "without an '; expect sat|unsat' annotation" "Z3-CHECK OK"
  # M. a root with no .smt2 must FAIL (vacuous)
  mkdir -p "$SCRATCH/m"; OUT="$(bash "$Z3CHECK" "$SCRATCH/m" 2>&1)"; RC=$?; expect "M no .smt2 files -> fail" 1 "no .smt2 files" "Z3-CHECK OK"
  # N. a file whose assertions are unsatisfiable where 'sat' is expected: z3 says unsat -> FAIL
  mkdir -p "$SCRATCH/n"; printf '(declare-const x Int)\n(assert (< x 0))\n(assert (> x 0))\n(check-sat) ; expect sat\n' > "$SCRATCH/n/contra.smt2"
  OUT="$(bash "$Z3CHECK" "$SCRATCH/n" 2>&1)"; RC=$?; expect "N real z3, contradictory assertions vs expect sat -> fail" 1 "verdicts differ from annotations" "Z3-CHECK OK"
fi

echo
if [ "$fails" -eq 0 ]; then echo "GATE-SELFTEST OK: $cases/$cases cases"; exit 0; fi
echo "GATE-SELFTEST FAILED: $fails of $cases cases"; exit 1
