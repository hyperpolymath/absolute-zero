#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Exercise the gate with synthetic mutations, without changing actual proofs.
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/src/abi"
cp "$repo_root/scripts/check-proof-patterns.sh" "$fixture/scripts/"

expect() {
  local expected=$1 label=$2 status
  if bash "$fixture/scripts/check-proof-patterns.sh" > "$fixture/result" 2>&1; then
    status=0
  else
    status=$?
  fi
  if [[ "$status" != "$expected" ]]; then
    cat "$fixture/result"
    echo "FAIL: $label (expected $expected, got $status)" >&2
    exit 1
  fi
  echo "PASS: $label"
}

printf 'proof = believe_me ()\n%.0s' {1..5} > "$fixture/src/abi/Baseline.idr"
cat >> "$fixture/src/abi/Baseline.idr" <<'EOF'
-- believe_me in a comment
||| believe_me in documentation
EOF
expect 0 'five approved sites plus comments'
printf 'sixth = believe_me () -- inline comment\n' > "$fixture/src/abi/Extra.idr"
expect 1 'sixth site with inline comment'
rm "$fixture/src/abi/Extra.idr"
printf 'pair = (believe_me (), believe_me ())\n%.0s' {1..3} > "$fixture/src/abi/Baseline.idr"
expect 1 'multiple occurrences on one line'
: > "$fixture/src/abi/Baseline.idr"
expect 0 'baseline can decrease to zero'
printf 'escape = believe_me ()\n' > "$fixture/src/Outside.idr"
expect 1 'believe_me outside ABI even below baseline'
rm "$fixture/src/Outside.idr"
for pattern in assert_total unsafeCoerce Obj.magic; do
  printf 'escape = %s\n' "$pattern" > "$fixture/src/abi/Extra.idr"
  expect 1 "$pattern is never allowed in ABI"
  rm "$fixture/src/abi/Extra.idr"
done
for extension in rs ml hs; do
  printf 'Obj.magic\n' > "$fixture/src/Outside.$extension"
  expect 1 "forbidden pattern in $extension source"
  rm "$fixture/src/Outside.$extension"
done
rm "$fixture/src/abi/Baseline.idr"
expect 1 'empty source fails closed'
rmdir "$fixture/src/abi"
expect 1 'missing ABI directory fails closed'
