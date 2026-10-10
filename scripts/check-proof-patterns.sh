#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Text gate for active source. Issue #27 approves at most five ABI believe_me
# occurrences, not a general allowance for escape hatches elsewhere.
set -euo pipefail
cd "$(dirname "$0")/.."
test -d src/abi
shopt -s globstar nullglob dotglob
sources=(src/**/*.idr src/**/*.ml src/**/*.hs src/**/*.rs)
if ((${#sources[@]} == 0)); then
  echo "No source files found" >&2
  exit 1
fi

awk '
  {
    code = $0
    # Ignore Idris documentation and line comments, retaining code before --.
    if (FILENAME ~ /[.]idr$/) {
      if (code ~ /^[[:space:]]*\|\|\|/) next
      sub(/--.*/, "", code)
    }
    if (code ~ /assert_total|unsafeCoerce|Obj[.]magic/) {
      print FILENAME ":" FNR ": forbidden proof escape hatch"
      failed = 1
    }
    while (match(code, /believe_me/)) {
      if (FILENAME ~ /^src\/abi\/.*[.]idr$/) count++
      else {
        print FILENAME ":" FNR ": believe_me outside the approved ABI scope"
        failed = 1
      }
      code = substr(code, RSTART + RLENGTH)
    }
  }
  END {
    printf "ABI believe_me occurrences: %d (maximum 5; issue #27)\n", count
    exit (failed || count > 5)
  }
' "${sources[@]}"
