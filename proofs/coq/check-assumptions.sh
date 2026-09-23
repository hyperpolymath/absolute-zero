#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — Print Assumptions gate for the Coq pillar.
#
# Compiles audit/Assumptions.v (or the file given as $1) against the built
# theories, using the -R roots from _CoqProject, and FAILS unless every
# `Print Assumptions` line answers "Closed under the global context":
#   - any "Axioms:" block            -> FAIL (the block is printed);
#   - closed-count != line-count     -> FAIL (a theorem silently missing);
#   - coqc exit != 0                 -> FAIL (a renamed/removed theorem);
#   - a file with no Print Assumptions lines -> FAIL (vacuous gate).
# `--control` proves the gate bites: it audits CNO.StatMech.landauer_limit_positive,
# which rests on the tagged axiom PhysicsConstants.kB_positive, and requires
# the gate to REJECT it naming that axiom.
# Run after `coq_makefile -f _CoqProject -o Makefile.all && make -f Makefile.all`.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"

command -v coqc >/dev/null || { echo "ASSUMPTIONS-CHECK FAILED: coqc not on PATH"; exit 1; }
RFLAGS=()
while read -r flag dir ns; do
  [ "$flag" = "-R" ] && RFLAGS+=("-R" "$HERE/$dir" "$ns")
done < "$HERE/_CoqProject"
[ "${#RFLAGS[@]}" -gt 0 ] || { echo "ASSUMPTIONS-CHECK FAILED: no -R roots in _CoqProject"; exit 1; }

# check_file <file.v>: 0 iff every Print Assumptions line is closed.
check_file() {
  local file=$1 base dir out rc expected closed axioms
  base="$(basename "${file%.v}")"; dir="$(dirname "$file")"
  expected=$(grep -c '^Print Assumptions' "$file")
  if [ "$expected" -eq 0 ]; then
    echo "ASSUMPTIONS-CHECK FAILED: $file has no 'Print Assumptions' lines (vacuous)"; return 1
  fi
  out="$(coqc "${RFLAGS[@]}" "$file" 2>&1)"; rc=$?
  rm -f "$dir/$base.vo" "$dir/$base.vos" "$dir/$base.vok" "$dir/$base.glob" "$dir/.$base.aux"
  printf '%s\n' "$out"
  if [ "$rc" -ne 0 ]; then echo "ASSUMPTIONS-CHECK FAILED: coqc exit $rc on $file"; return 1; fi
  closed=$(printf '%s\n' "$out" | grep -c '^Closed under the global context')
  axioms=$(printf '%s\n' "$out" | grep -c '^Axioms:')
  if [ "$axioms" -ne 0 ] || [ "$closed" -ne "$expected" ]; then
    echo "ASSUMPTIONS-CHECK FAILED: $file — expected $expected closed, got closed=$closed axiom-blocks=$axioms"
    return 1
  fi
  echo "ASSUMPTIONS-CHECK OK: $expected/$expected theorems closed under the global context ($file)"
}

if [ "${1:-}" = "--control" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/az-assumptions-control.XXXXXX")"
  trap 'rm -rf "$tmp"' EXIT
  printf 'Require CNO.StatMech.\nPrint Assumptions CNO.StatMech.landauer_limit_positive.\n' > "$tmp/Control.v"
  if check_file "$tmp/Control.v" > "$tmp/control.log" 2>&1; then
    echo "ASSUMPTIONS-CONTROL FAILED: landauer_limit_positive (rests on kB_positive) PASSED the gate"
    cat "$tmp/control.log"; exit 1
  fi
  if ! grep -q 'kB_positive' "$tmp/control.log"; then
    echo "ASSUMPTIONS-CONTROL FAILED: the rejection did not name PhysicsConstants.kB_positive"
    cat "$tmp/control.log"; exit 1
  fi
  echo "ASSUMPTIONS-CONTROL OK: landauer_limit_positive rejected, naming kB_positive (the gate bites)"
  exit 0
fi

check_file "${1:-$HERE/audit/Assumptions.v}"
