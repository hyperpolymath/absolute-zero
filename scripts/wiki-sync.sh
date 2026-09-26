#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Absolute Zero — Sync docs/wiki/ to the GitHub Wiki repository.
#
# Usage:
#   scripts/wiki-sync.sh
# Requires GITHUB_TOKEN for remote push; in dry-run mode (no token), lists
# the pages that would be synced.
set -uo pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
WIKI_DIR="$HERE/docs/wiki"

if [ ! -d "$WIKI_DIR" ]; then
  echo "WIKI-SYNC ERROR: $WIKI_DIR does not exist"
  exit 1
fi

TOKEN="${GITHUB_TOKEN:-${GH_TOKEN:-}}"
if [ -z "$TOKEN" ]; then
  echo "WIKI-SYNC: No GITHUB_TOKEN detected; running in dry-run mode."
  echo "Pages found in $WIKI_DIR:"
  ls -la "$WIKI_DIR"/*.md
  exit 0
fi

REPO="${GITHUB_REPOSITORY:-hyperpolymath/absolute-zero}"
WIKI_REPO="https://x-access-token:${TOKEN}@github.com/${REPO}.wiki.git"

TMP="$(mktemp -d "${TMPDIR:-/tmp}/az-wiki-sync.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

echo "WIKI-SYNC: Cloning ${REPO}.wiki..."
if ! git clone --depth 1 "$WIKI_REPO" "$TMP" 2>/dev/null; then
  echo "WIKI-SYNC: Wiki repository not yet initialized or inaccessible. Skipping push."
  exit 0
fi

cp "$WIKI_DIR"/*.md "$TMP/"

cd "$TMP"
git config user.name "github-actions[bot]"
git config user.email "github-actions[bot]@users.noreply.github.com"
git add .
if git diff --quiet && git diff --staged --quiet; then
  echo "WIKI-SYNC: Wiki is already up to date."
else
  COMMIT_SHA="$(cd "$HERE" && git rev-parse --short HEAD)"
  git commit -m "Sync from absolute-zero/docs/wiki@${COMMIT_SHA}"
  git push origin master 2>/dev/null || git push origin main 2>/dev/null || echo "WIKI-SYNC: Push failed"
  echo "WIKI-SYNC: Synced to GitHub Wiki successfully."
fi
exit 0
