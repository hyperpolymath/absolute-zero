#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — reproducible Agda standard-library registration.
#
# The Agda proofs (proofs/agda/, absolute-zero.agda-lib) `depend: standard-library`.
# This script fetches ONE pinned agda-stdlib release, checks that the tag still
# resolves to the pinned commit, and registers it for Agda. CI
# (.github/workflows/proofs.yml, `agda` job) and local runs use this same script,
# so both type-check against the same library bytes.
#
# Pin: agda-stdlib v1.7.3 (the release that matches Agda 2.6.3, the version
# Ubuntu 24.04 ships and CI installs). Tag v1.7.3 -> commit STDLIB_COMMIT below,
# read with `git ls-remote https://github.com/agda/agda-stdlib.git refs/tags/v1.7.3^{}`
# on 2026-11-09. If the tag is ever moved, this script fails rather than
# silently using different sources.
#
# Usage:
#   bash scripts/provision-agda-stdlib.sh
# Environment (all optional):
#   AGDA_DIR           Agda's config directory (Agda's own variable; default ~/.agda).
#                      `libraries` and `defaults` are written here.
#   AGDA_STDLIB_DIR    Where to put the checkout (default $AGDA_DIR/agda-stdlib-v1.7.3).
#
# Idempotent: an existing checkout at the pinned commit is reused. The
# `libraries` / `defaults` files are OVERWRITTEN to name exactly this library,
# so run it with a dedicated AGDA_DIR if you keep other Agda libraries in ~/.agda.
set -euo pipefail

STDLIB_REPO="https://github.com/agda/agda-stdlib.git"
STDLIB_TAG="v1.7.3"
STDLIB_COMMIT="0817da6877aa045932221134913d8511caa78d97"

AGDA_DIR="${AGDA_DIR:-$HOME/.agda}"
AGDA_STDLIB_DIR="${AGDA_STDLIB_DIR:-$AGDA_DIR/agda-stdlib-$STDLIB_TAG}"

mkdir -p "$AGDA_DIR"

if [ -d "$AGDA_STDLIB_DIR/.git" ]; then
  echo "reusing checkout $AGDA_STDLIB_DIR"
else
  git -c advice.detachedHead=false clone -q --depth 1 --branch "$STDLIB_TAG" "$STDLIB_REPO" "$AGDA_STDLIB_DIR"
fi

have="$(git -C "$AGDA_STDLIB_DIR" rev-parse HEAD)"
if [ "$have" != "$STDLIB_COMMIT" ]; then
  echo "PROVISION FAILED: $AGDA_STDLIB_DIR is at $have, expected $STDLIB_TAG = $STDLIB_COMMIT" >&2
  exit 1
fi

# absolute-zero.agda-lib depends on the unversioned name `standard-library`;
# the upstream manifest calls itself `standard-library-1.7.3`. Rename in place
# (the only local modification to the checkout).
lib="$AGDA_STDLIB_DIR/standard-library.agda-lib"
[ -f "$lib" ] || { echo "PROVISION FAILED: $lib missing" >&2; exit 1; }
sed -i 's/^name: .*/name: standard-library/' "$lib"

printf '%s\n' "$lib" > "$AGDA_DIR/libraries"
printf '%s\n' "standard-library" > "$AGDA_DIR/defaults"

echo "registered standard-library ($STDLIB_TAG @ $STDLIB_COMMIT)"
echo "  libraries: $AGDA_DIR/libraries -> $lib"
echo "  defaults:  $AGDA_DIR/defaults"
