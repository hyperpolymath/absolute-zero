#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Unit tests for verify-active-provers.sh, plus its Z3 checker integration.
# Run: bash proofs/tests/gate-selftest.sh (no real provers or network needed).
# All mutations are confined to a disposable fixture; archived proofs are unused.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
PROOFS="$(cd "$HERE/.." && pwd)"
BASH_BIN="$(command -v bash)"
ENV_BIN="$(command -v env)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/az-active-gate-selftest.XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT
# Spaces exercise quoting in the gate's path resolution and subprocess calls.
FIXTURE="$SCRATCH/repo with spaces"
STUB="$SCRATCH/bin"
TRACE="$SCRATCH/trace"
mkdir -p "$STUB" "$SCRATCH/home" "$SCRATCH/unrelated cwd" "$FIXTURE/proofs"
cp "$PROOFS/verify-active-provers.sh" "$FIXTURE/proofs/"

# No system PATH fallback: missing-prover cases must stay missing even on a
# developer's machine with all provers installed. Only checker utilities escape.
for utility in bash dirname find sort awk grep diff sed tail tr; do
  ln -s "$(command -v "$utility")" "$STUB/$utility"
done

cat > "$STUB/agda" <<'AGDA'
#!/bin/sh
printf 'agda|%s|%s\n' "$PWD" "$*" >> "$TRACE"
[ "$#" -eq 3 ] && [ "$1" = --safe ] && [ "$2" = --without-K ] || exit 90
[ -f "$3" ] || exit 91
[ "$3" != "$AGDA_FAIL" ] || exit 7
AGDA
cat > "$STUB/idris2" <<'IDRIS'
#!/bin/sh
printf 'idris2|%s|%s\n' "$PWD" "$*" >> "$TRACE"
[ "$#" -eq 2 ] && [ "$1" = --build ] && [ "$2" = absolute-zero-abi.ipkg ] || exit 90
[ -f "$2" ] || exit 91
exit "$IDRIS_RC"
IDRIS
cat > "$STUB/z3" <<'Z3'
#!/bin/sh
printf 'z3|%s|%s\n' "$PWD" "$*" >> "$TRACE"
[ "$#" -eq 1 ] || exit 90
if [ "$1" = --version ]; then
  echo 'Z3 version stub'
  exit 0
fi
[ -f "$1" ] || exit 91
printf '%s\n' "$Z3_OUTPUT"
exit "$Z3_RC"
Z3
# Retirement is a behavior: even available archived tools must never be called.
for retired in coqc coq_makefile make lake lean isabelle accom verifier; do
  cat > "$STUB/$retired" <<'RETIRED'
#!/bin/sh
printf 'ARCHIVED TOOL CALLED: %s\n' "$0" >> "$TRACE"
exit 99
RETIRED
done
chmod +x "$STUB/"{agda,idris2,z3,coqc,coq_makefile,make,lake,lean,isabelle,accom,verifier}

MODULES=(CNO OND EchoBridgeScaffold EchoBridgeCNO)
cases=0
fails=0

reset_fixture() {
  local module
  rm -rf "$FIXTURE/proofs/agda" "$FIXTURE/proofs/z3"
  mkdir -p "$FIXTURE/proofs/agda" "$FIXTURE/proofs/z3/ond"
  for module in "${MODULES[@]}"; do
    cp "$PROOFS/agda/$module.agda" "$FIXTURE/proofs/agda/"
  done
  cp "$PROOFS/z3/verify.sh" "$FIXTURE/proofs/z3/"
  cp "$PROOFS/../absolute-zero-abi.ipkg" "$FIXTURE/"
  # The solver is stubbed, so a small annotated fixture is sufficient to test
  # the gate/checker boundary without coupling it to theorem contents.
  printf '(check-sat) ; expect sat\n(check-sat) ; expect unsat\n(check-sat) ; expect sat\n' \
    > "$FIXTURE/proofs/z3/ond/checks.smt2"
  AGDA_FAIL=''
  IDRIS_RC=0
  Z3_RC=0
  Z3_OUTPUT=$'sat\nunsat\nsat'
  EXPECTED=''
}

expect_agda() {
  local module
  for module in "$@"; do
    EXPECTED+="agda|$FIXTURE/proofs/agda|--safe --without-K $module.agda"$'\n'
  done
}
expect_z3() {
  EXPECTED+="z3|$SCRATCH/unrelated cwd|--version"$'\n'
  EXPECTED+="z3|$SCRATCH/unrelated cwd|$FIXTURE/proofs/z3/ond/checks.smt2"$'\n'
}
expect_idris() {
  EXPECTED+="idris2|$FIXTURE|--build absolute-zero-abi.ipkg"$'\n'
}
expect_all() { expect_agda "${MODULES[@]}"; expect_z3; expect_idris; }

run_gate() {
  : > "$TRACE"
  RC=0
  # A clean child environment also removes exported shell functions, BASH_ENV,
  # user-local toolchains, and legacy skip flags from the host test environment.
  OUT="$(cd "$SCRATCH/unrelated cwd" && "$ENV_BIN" -i \
    HOME="$SCRATCH/home" PATH="$STUB" LC_ALL=C TRACE="$TRACE" \
    AGDA_FAIL="$AGDA_FAIL" IDRIS_RC="$IDRIS_RC" Z3_RC="$Z3_RC" Z3_OUTPUT="$Z3_OUTPUT" \
    "$BASH_BIN" "$FIXTURE/proofs/verify-active-provers.sh" 2>&1)" || RC=$?
}

# Require the specific failure diagnostic AND final status AND exact tool
# invocations: an unrelated shell error must never satisfy a negative case.
expect() {
  local label=$1 want=$2 reason problem='' actual
  shift 2
  cases=$((cases + 1))
  [ "$RC" -eq "$want" ] || problem+="exit $RC, wanted $want; "
  for reason in "$@"; do
    [[ "$OUT" == *"$reason"* ]] || problem+="missing '$reason'; "
  done
  if [ "$want" -eq 0 ]; then
    [[ "$OUT" == *ACTIVE-PROVERS-GREEN ]] || problem+='missing green summary; '
    [[ "$OUT" != *'SOME ACTIVE PROVERS FAILED'* ]] || problem+='failure on success; '
  else
    [[ "$OUT" == *'SOME ACTIVE PROVERS FAILED' ]] || problem+='missing failure summary; '
    [[ "$OUT" != *ACTIVE-PROVERS-GREEN* ]] || problem+='false green; '
  fi
  actual="$(cat "$TRACE")"
  [[ "$actual" == "${EXPECTED%$'\n'}" ]] || problem+='tool calls differ; '
  if [ -z "$problem" ]; then
    printf 'PASS: %s\n' "$label"
  else
    fails=$((fails + 1))
    printf 'FAIL: %s — %s\n%s\nExpected calls:\n%sActual calls:\n%s\n' \
      "$label" "$problem" "$OUT" "$EXPECTED" "$actual"
  fi
}

reset_fixture; expect_all; run_gate
expect 'all active provers pass; archived tools unused; cwd and flags correct' 0 'Z3-CHECK OK'

for tool in agda z3 idris2; do
  reset_fixture
  mv "$STUB/$tool" "$SCRATCH/$tool.off"
  if [ "$tool" != agda ]; then expect_agda "${MODULES[@]}"; fi
  if [ "$tool" != z3 ]; then expect_z3; fi
  if [ "$tool" != idris2 ]; then expect_idris; fi
  run_gate
  expect "$tool missing fails while other provers still run" 1 "$tool missing"
  mv "$SCRATCH/$tool.off" "$STUB/$tool"
done

reset_fixture
for tool in agda z3 idris2; do mv "$STUB/$tool" "$SCRATCH/$tool.off"; done
run_gate
expect 'all missing provers are reported together' 1 'agda missing' 'z3 missing' 'idris2 missing'
for tool in agda z3 idris2; do mv "$SCRATCH/$tool.off" "$STUB/$tool"; done

for index in "${!MODULES[@]}"; do
  module=${MODULES[$index]}
  reset_fixture
  AGDA_FAIL="$module.agda"
  expect_agda "${MODULES[@]:0:index+1}"; expect_z3; expect_idris
  run_gate
  expect "$module rejects: stop Agda at that module, continue other provers" 1 'AGDA FAILED'

  reset_fixture
  rm "$FIXTURE/proofs/agda/$module.agda"
  expect_agda "${MODULES[@]:0:index}"; expect_z3; expect_idris
  run_gate
  expect "$module missing: never invoke Agda on a missing module" 1 "$module.agda MISSING"
done

reset_fixture
rm -rf "$FIXTURE/proofs/agda"
expect_z3; expect_idris; run_gate
expect 'missing Agda directory fails without checking from the wrong cwd' 1 'AGDA FAILED'

reset_fixture
IDRIS_RC=3
expect_all; run_gate
expect 'Idris build failure normalizes to gate exit 1' 1 'IDRIS FAILED'

reset_fixture
rm "$FIXTURE/absolute-zero-abi.ipkg"
expect_all; run_gate
expect 'missing ABI package propagates the build failure' 1 'IDRIS FAILED'

# These are integration cases for the new gate's delegation to the existing
# expect-checker; a solver exiting zero alone must never make the gate green.
for mode in mismatch unknown error nonzero empty truncated extra; do
  reset_fixture
  reason='verdicts differ from annotations'
  case "$mode" in
    mismatch) Z3_OUTPUT=$'sat\nsat\nsat';;
    unknown) Z3_OUTPUT=$'sat\nunknown\nsat';;
    error) Z3_OUTPUT=$'sat\n(error "boom")\nunsat\nsat'; reason='z3 reported an error';;
    nonzero) Z3_RC=4; reason='z3 exit 4';;
    empty) Z3_OUTPUT='';;
    truncated) Z3_OUTPUT=$'sat\nunsat';;
    extra) Z3_OUTPUT=$'sat\nunsat\nsat\nsat';;
  esac
  expect_all; run_gate
  expect "Z3 $mode fails the active gate and still runs Idris" 1 "$reason" 'Z3 FAILED'
done

reset_fixture
rm "$FIXTURE/proofs/z3/ond/checks.smt2"
expect_agda "${MODULES[@]}"
EXPECTED+="z3|$SCRATCH/unrelated cwd|--version"$'\n'
expect_idris; run_gate
expect 'empty solver fixture cannot pass vacuously' 1 'no .smt2 files'

reset_fixture
rm "$FIXTURE/proofs/z3/verify.sh"
expect_agda "${MODULES[@]}"; expect_idris; run_gate
expect 'missing delegated checker fails even with z3 available' 1 'Z3 FAILED'

reset_fixture
AGDA_FAIL=CNO.agda; Z3_RC=4; IDRIS_RC=3
expect_agda CNO; expect_z3; expect_idris; run_gate
expect 'multiple failures preserve a failing result after every prover runs' 1 \
  'AGDA FAILED' 'Z3 FAILED' 'IDRIS FAILED'

reset_fixture; expect_all; run_gate
expect 'positive control after negative cases: no fixture state leaks' 0 'Z3-CHECK OK'

if [ "$fails" -eq 0 ]; then
  printf 'GATE-SELFTEST OK: %s/%s cases\n' "$cases" "$cases"
  exit 0
fi
printf 'GATE-SELFTEST FAILED: %s failures in %s cases\n' "$fails" "$cases"
exit 1
