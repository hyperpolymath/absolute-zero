#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Acceptance checks for the documentation added by PR #188. No prover runs.
# Usage: bash tests/check-policy-records.sh (bash/awk only; finishes in seconds).
# These check references and factual claims, not prose or proof correctness.
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"
export LC_ALL=C
failures=0
cases=0

expect() {
  local label=$1
  shift
  cases=$((cases + 1))
  if "$@"; then
    printf 'PASS: %s\n' "$label"
  else
    printf 'FAIL: %s\n' "$label" >&2
    failures=$((failures + 1))
  fi
}

exception=docs/EXCEPTION-T1-2026-10-12.adoc
decision=docs/DECISION-T7-2026-10-12.adoc
for document in README.adoc "$exception" "$decision"; do
  # Missing input must fail before extraction, never yield an empty passing loop.
  if [[ ! -s "$document" ]]; then
    printf 'FAIL: missing or empty document: %s\n' "$document" >&2
    exit 1
  fi
done

# Resolve the actual link in the new README note, relative to the README.
mapfile -t links < <(awk '
  {
    while (match($0, /link:[^[:space:][]*EXCEPTION-T1[^[:space:][]*\[/)) {
      print substr($0, RSTART + 5, RLENGTH - 6)
      $0 = substr($0, RSTART + RLENGTH)
    }
  }
' README.adoc)
expect 'README has one T1 exception link' test "${#links[@]}" -eq 1
for target in "${links[@]}"; do
  expect "README exception link resolves: $target" test -s "$target"
done

# Extract the named modules rather than duplicating the exception's inventory.
mapfile -t modules < <(awk '
  {
    while (match($0, /[[:alnum:]_]+[.]agda/)) {
      print substr($0, RSTART, RLENGTH)
      $0 = substr($0, RSTART + RLENGTH)
    }
  }
' "$exception")
expect 'T1 names at least one proof module' test "${#modules[@]}" -gt 0
for module in "${modules[@]}"; do
  expect "T1 module exists: $module" test -s "proofs/agda/$module"
  for flag in --safe --without-K; do
    expect "$module declares the T1 safety condition $flag" awk -v flag="$flag" '
      /^[[:space:]]*\{-# OPTIONS / {
        for (i = 3; i <= NF; i++) if ($i == flag) found = 1
      }
      END { exit !found }
    ' "proofs/agda/$module"
  done
done

# The archive claim must not silently point readers back to an active tree.
for prover in coq lean4 isabelle mizar; do
  expect "archived $prover tree exists" test -d "archive/proofs/$prover"
  expect "$prover has no active proof tree" test ! -e "proofs/$prover"
done
expect 'T7 proof-contract destination exists' test -d proofs/agda
expect 'T1 ABI package exists' test -s absolute-zero-abi.ipkg
expect 'T1 ABI directory matches the package source directory' awk '
  /^[[:space:]]*sourcedir[[:space:]]*=[[:space:]]*"src\/abi"[[:space:]]*$/ { found = 1 }
  END { exit !found }
' absolute-zero-abi.ipkg
expect 'T1 ABI source directory exists' test -d src/abi

# Negative/regression case: documentation and line comments are not live
# escape hatches. Follow scripts/check-proof-patterns.sh counting semantics;
# count occurrences (including multiple on one line), not matching lines.
documented_count=$(awk '
  match($0, /[0-9]+[[:space:]]+`believe_me`/) {
    print substr($0, RSTART, RLENGTH) + 0
  }
' "$decision")
shopt -s globstar nullglob
abi_sources=(src/abi/**/*.idr)
expect 'ABI census has source inputs' test "${#abi_sources[@]}" -gt 0
if ((${#abi_sources[@]} > 0)); then
  live_count=$(awk '
    /^[[:space:]]*\|\|\|/ { next }
    {
      sub(/--.*/, "")
      while (match($0, /believe_me/)) {
        count++
        $0 = substr($0, RSTART + RLENGTH)
      }
    }
    END { print count + 0 }
  ' "${abi_sources[@]}")
  expect "T7 live believe_me count: documented=$documented_count, actual=$live_count" \
    test "$documented_count" = "$live_count"
fi

printf 'POLICY-RECORDS: %s checks, %s failures\n' "$cases" "$failures"
test "$failures" -eq 0
