#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — AsciiDoc PSV-table structural check (bash/awk only; no
# Python/Deno per the estate language policy).
#
# Every row in a |=== table block must carry exactly the number of cells its
# cols= spec declares, once escaped pipes (\|) are treated as literal content
# (asciidoctor behaviour). Guards the docs/proof-debt.adoc fix for issue #166.
# Mutant control: a bare | inside a table cell re-creates the cell-count
# mismatch that makes asciidoctor "drop cells from incomplete row".
#
# Usage: check-adoc-tables.sh FILE...   (exit non-zero on any problem)
set -uo pipefail
[ "$#" -ge 1 ] || { echo "usage: $0 FILE.adoc..." >&2; exit 2; }

fail=0
for f in "$@"; do
  [ -r "$f" ] || { echo "ADOC-TABLES FAILED: $f not readable"; fail=1; continue; }
  out="$(awk '
    function colcount(spec,   n, arr) { n = split(spec, arr, ","); return n }
    BEGIN { inblk = 0; errors = 0 }
    # remember the most recent attribute line ([...]) seen outside a table
    !inblk && /^\[.*\][ \t]*$/ { attr = $0; next }
    !inblk && /^\|[ \t]*===[ \t]*$/ {
      inblk = 1; start = NR; cells = 0; expected = 0
      if (match(attr, /cols="[^"]+"/)) {
        spec = substr(attr, RSTART + 6, RLENGTH - 7)
        expected = colcount(spec)
      }
      attr = ""
      next
    }
    inblk && /^\|[ \t]*===[ \t]*$/ {
      if (expected > 0 && cells > 0 && cells % expected != 0) {
        printf "%s:%d: table has %d cells, not a multiple of %d (cols spec) — asciidoctor would drop cells from an incomplete row\n", FILENAME, start, cells, expected
        errors++
      }
      inblk = 0
      next
    }
    inblk {
      line = $0
      # drop escaped pipes (\| is literal content), then count cell separators
      gsub(/\\[|]/, "", line)
      n = gsub(/[|]/, "|", line)
      cells += n
      next
    }
    !inblk { attr = "" }
    END {
      if (inblk) { printf "%s:%d: unterminated table block\n", FILENAME, start; errors++ }
      exit errors > 0 ? 1 : 0
    }
  ' "$f")"; rc=$?
  if [ "$rc" -ne 0 ]; then
    printf '%s\n' "$out"
    echo "ADOC-TABLES FAILED: $f"
    fail=1
  else
    echo "ADOC-TABLES OK: $f"
  fi
done
exit "$fail"
