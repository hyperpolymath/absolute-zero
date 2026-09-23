#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — Z3 expect-checker (CNO + OND bounded instances).
#
# For every *.smt2 under the given root (default: this directory), read the
# `; expect sat` / `; expect unsat` annotation on each (check-sat) line and
# compare it, IN ORDER, with the verdict z3 actually prints. The run FAILS on:
#   - a verdict that differs from its annotation, or an `unknown`;
#   - an `(error ...)` line anywhere in z3's output;
#   - a (check-sat) line without an `; expect sat|unsat` annotation;
#   - a file with no (check-sat), a root with no *.smt2, or z3 exit != 0.
# Exit 0 (printing Z3-CHECK OK) only when every file matches exactly.
#
# Before 2026-09-23 this script ran `z3 cno_properties.smt2` (a file that did
# not exist), CI wrapped it in `|| true`, and the only other check was z3's
# exit code — which is 0 for sat AND unsat, so a broken theorem never failed.
# Self-test (mutants that must turn this red): proofs/tests/gate-selftest.sh.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="${1:-$HERE}"

command -v z3 >/dev/null || { echo "Z3-CHECK FAILED: z3 not on PATH"; exit 1; }
z3 --version

files=()
while IFS= read -r f; do files+=("$f"); done < <(find "$ROOT" -type f -name '*.smt2' | LC_ALL=C sort)
[ "${#files[@]}" -gt 0 ] || { echo "Z3-CHECK FAILED: no .smt2 files under $ROOT"; exit 1; }

fail=0
for f in "${files[@]}"; do
  rel="${f#"$ROOT"/}"
  expected="$(awk '/\(check-sat\)/ {
      if (match($0, /; *expect +(sat|unsat)([^a-z]|$)/)) {
        s = substr($0, RSTART, RLENGTH); sub(/^; *expect +/, "", s); sub(/[^a-z].*$/, "", s); print s
      } else print "MISSING" }' "$f")"
  n_expected=$(printf '%s\n' "$expected" | grep -c .)
  if [ "$n_expected" -eq 0 ]; then
    echo "Z3-CHECK FAILED: $rel has no (check-sat)"; fail=1; continue
  fi
  if printf '%s\n' "$expected" | grep -qx MISSING; then
    echo "Z3-CHECK FAILED: $rel has a (check-sat) without an '; expect sat|unsat' annotation"; fail=1; continue
  fi
  out="$(z3 "$f" 2>&1)"; rc=$?
  if printf '%s\n' "$out" | grep -q '(error'; then
    echo "Z3-CHECK FAILED: $rel — z3 reported an error:"; printf '%s\n' "$out" | grep '(error' | sed 's/^/  /'
    fail=1; continue
  fi
  if [ "$rc" -ne 0 ]; then
    echo "Z3-CHECK FAILED: $rel — z3 exit $rc"; printf '%s\n' "$out" | tail -5 | sed 's/^/  /'; fail=1; continue
  fi
  got="$(printf '%s\n' "$out" | grep -xE 'sat|unsat|unknown')"
  if [ "$expected" != "$got" ]; then
    echo "Z3-CHECK FAILED: $rel — verdicts differ from annotations (< expected, > got):"
    diff <(printf '%s\n' "$expected") <(printf '%s\n' "$got") | sed 's/^/  /'
    fail=1; continue
  fi
  echo "ok: $rel — $n_expected (check-sat) verdict(s) match: $(printf '%s' "$expected" | tr '\n' ' ')"
done
if [ "$fail" -eq 0 ]; then echo "Z3-CHECK OK: ${#files[@]} file(s) under $ROOT"; else echo "Z3-CHECK FAILED"; fi
exit "$fail"
