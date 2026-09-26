#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — Unified axiom-tag grammar checker for Coq proofs.
#
# Verifies that every top-level Axiom, Parameter, or Hypothesis across the
# 14 Coq theories is immediately preceded by exactly one tag matching the
# fixed grammar:
#   (* AXIOM[CLASS]: <reason> *)   or   (* AXIOM: [CLASS] <reason> *)
# where CLASS is one of:
#   METAL-BOUNDARY | CLASS-A | STDLIB-CLASSICAL
#
# Usage:
#   bash proofs/coq/check-axiom-tags.sh            # Check all theories
#   bash proofs/coq/check-axiom-tags.sh --control  # Test that untagged/bad tags fail
#
# Requirements from issue #171: bash/awk only, zero Python/Deno dependencies.
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
FAIL=0

check_file() {
  local f="$1"
  local errors
  errors="$(awk '
    BEGIN {
      in_str = 0
      in_comment = 0
      prev_line = ""
      prev_prev = ""
      errs = 0
      known_classes = "^(METAL-BOUNDARY|CLASS-A|STDLIB-CLASSICAL)$"
    }

    # Track comment and string state across lines (simplified top-level scanner)
    {
      raw = $0
      line = $0
      sub(/^[[:space:]]+/, "", line)

      # Check if this line declares a top-level Axiom, Parameter, or Hypothesis
      if (line ~ /^(Axiom|Parameter|Hypothesis)[[:space:]]+[A-Za-z0-9_]+/) {
        # Check if the preceding non-empty line was a valid tag
        tag = ""
        candidate = prev_line
        if (candidate == "" && prev_prev != "") candidate = prev_prev

        # Format 1: (* AXIOM[CLASS]: reason *)
        # Format 2: (* AXIOM: [CLASS] reason *)
        class_name = ""
        if (match(candidate, /\(\*[[:space:]]*AXIOM\[([A-Za-z0-9_-]+)\]:[[:space:]]*.*[[:space:]]*\*\)/)) {
          # Extract class from candidate
          s = candidate
          sub(/^[^(]*\(\*[[:space:]]*AXIOM\[/, "", s)
          sub(/\].*$/, "", s)
          class_name = s
        } else if (match(candidate, /\(\*[[:space:]]*AXIOM:[[:space:]]*\[([A-Za-z0-9_-]+)\][[:space:]]*.*[[:space:]]*\*\)/)) {
          s = candidate
          sub(/^[^(]*\(\*[[:space:]]*AXIOM:[[:space:]]*\[/, "", s)
          sub(/\].*$/, "", s)
          class_name = s
        }

        if (class_name == "") {
          printf "%s:%d: UNTAGGED declaration: %s\n", FILENAME, NR, line
          printf "  preceding line: \"%s\"\n", candidate
          printf "  Expected: (* AXIOM[CLASS]: <reason> *) with CLASS in {METAL-BOUNDARY, CLASS-A, STDLIB-CLASSICAL}\n"
          errs++
        } else if (class_name !~ known_classes) {
          printf "%s:%d: UNKNOWN AXIOM CLASS \"%s\" in declaration: %s\n", FILENAME, NR, class_name, line
          printf "  Valid classes: METAL-BOUNDARY, CLASS-A, STDLIB-CLASSICAL\n"
          errs++
        }
      }

      if (raw ~ /[^[:space:]]/) {
        prev_prev = prev_line
        prev_line = raw
      }
    }

    END {
      exit errs > 0 ? 1 : 0
    }
  ' "$f")"
  local rc=$?
  if [ $rc -ne 0 ]; then
    printf '%s\n' "$errors"
    return 1
  fi
  return 0
}

# Positive control mode: test that untagged axiom turns the checker red
if [ "${1:-}" = "--control" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/az-axiom-tags-control.XXXXXX")"
  trap 'rm -rf "$tmp"' EXIT

  # Test 1: untagged Axiom fails
  cat > "$tmp/Untagged.v" <<'EOF'
Require Import Coq.Reals.Reals.
Axiom bad_axiom : 0 = 1.
EOF
  if check_file "$tmp/Untagged.v" > "$tmp/control1.log" 2>&1; then
    echo "AXIOM-TAGS-CONTROL FAILED: untagged Axiom passed the tag checker"
    exit 1
  fi
  if ! grep -q "UNTAGGED declaration" "$tmp/control1.log"; then
    echo "AXIOM-TAGS-CONTROL FAILED: untagged error message did not contain expected text"
    cat "$tmp/control1.log"
    exit 1
  fi

  # Test 2: unknown class fails
  cat > "$tmp/UnknownClass.v" <<'EOF'
Require Import Coq.Reals.Reals.
(* AXIOM[UNSOUND-CLASS]: bad tag *)
Axiom bad_axiom : 0 = 1.
EOF
  if check_file "$tmp/UnknownClass.v" > "$tmp/control2.log" 2>&1; then
    echo "AXIOM-TAGS-CONTROL FAILED: unknown axiom class passed the tag checker"
    exit 1
  fi
  if ! grep -q "UNKNOWN AXIOM CLASS" "$tmp/control2.log"; then
    echo "AXIOM-TAGS-CONTROL FAILED: unknown class error message did not contain expected text"
    cat "$tmp/control2.log"
    exit 1
  fi

  # Test 3: valid tag passes
  cat > "$tmp/ValidTag.v" <<'EOF'
Require Import Coq.Reals.Reals.
(* AXIOM[METAL-BOUNDARY]: empirical constant. *)
Parameter kB : R.
(* AXIOM[CLASS-A]: provable in principle. *)
Axiom test_class_a : True.
EOF
  if ! check_file "$tmp/ValidTag.v" > "$tmp/control3.log" 2>&1; then
    echo "AXIOM-TAGS-CONTROL FAILED: valid tags failed the tag checker"
    cat "$tmp/control3.log"
    exit 1
  fi

  echo "AXIOM-TAGS-CONTROL OK: untagged axioms and invalid classes turn red, valid tags pass"
  exit 0
fi

# Normal mode: check all Coq source files (excluding audit directory)
checked_files=0
while IFS= read -r f; do
  checked_files=$((checked_files + 1))
  if ! check_file "$f"; then
    FAIL=1
  fi
done < <(find "$HERE" -name "*.v" -not -path "*/audit/*" | sort)

if [ "$FAIL" -ne 0 ]; then
  echo "AXIOM-TAGS-CHECK FAILED: some declarations are untagged or have invalid classes"
  exit 1
fi

echo "AXIOM-TAGS-CHECK OK: all declarations across $checked_files theories tagged with unified grammar"
exit 0
