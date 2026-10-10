# Absolute Zero Build Automation
#
# Modern build automation using `just` (https://github.com/casey/just)
# Install: cargo install just
#
# Author: Jonathan D. A. Jewell
# Project: Absolute Zero

# Default recipe (show help)
default:
    @just --list

# ============================================================================
# Build Commands
# ============================================================================
# Active proof stack (owner ruling 2026-10-10): Idris 2 (ABI) and Agda (CNO +
# OND), plus Z3 bounded checks. Coq, Lean 4, Isabelle/HOL and Mizar are archived
# under archive/proofs/ and are not built or gated here.

# Build the active provers and the Idris ABI
build-all: build-agda build-idris
    @echo "✓ All builds complete"

# Build Agda proofs (CNO + OND + EchoBridge, 4 modules, --safe --without-K)
build-agda:
    @echo "Building Agda proofs..."
    cd proofs/agda && agda --safe --without-K CNO.agda && agda --safe --without-K OND.agda && agda --safe --without-K EchoBridgeScaffold.agda && agda --safe --without-K EchoBridgeCNO.agda

# Build the Idris 2 ABI package
build-idris:
    @echo "Building Idris 2 ABI..."
    idris2 --build absolute-zero-abi.ipkg

# ============================================================================
# Verification Commands
# ============================================================================

# Canonical gate: Agda + Z3 + Idris 2 ABI. Prints ACTIVE-PROVERS-GREEN on success.
verify:
    @proofs/verify-active-provers.sh

# Verify all active proofs (per-prover targets; `just verify` is the canonical one-shot)
verify-all: verify-z3 verify-agda verify-idris
    @echo "✓ All verifications complete"

# Verify Z3 SMT properties: every (check-sat) verdict must match its `; expect` annotation (no skip-as-pass)
verify-z3:
    @echo "Verifying Z3 SMT properties..."
    @command -v z3 >/dev/null 2>&1 || { echo "✗ z3 not found (required, not skipped)"; exit 1; }
    bash proofs/z3/verify.sh
    @echo "✓ Z3 verification complete"

# Verify Agda proofs
verify-agda: build-agda
    @echo "✓ Agda proofs verified"

# Verify the Idris 2 ABI package
verify-idris: build-idris
    @echo "✓ Idris ABI verified"

# ============================================================================
# Testing Commands
# ============================================================================

# Run all tests
test-all: test-proofs
    @echo "✓ All tests passed"

# Test proofs
test-proofs:
    @echo "Testing proof verification..."
    just verify-z3

# ============================================================================
# Documentation
# ============================================================================

# Generate documentation
docs:
    @echo "Generating documentation..."
    @echo "Theoretical foundations: docs/theory.md"
    @echo "Examples: docs/examples.md"
    @echo "Proof guide: docs/proofs-guide.md"
    @echo "Philosophy: docs/philosophy.md"

# View documentation
view-docs:
    @echo "Documentation files:"
    @ls -lh docs/

# Sync docs/wiki to GitHub Wiki repository (issue #80)
wiki-sync:
    @echo "Syncing docs/wiki to GitHub wiki..."
    bash scripts/wiki-sync.sh

# ============================================================================
# Cleanup
# ============================================================================

# Clean all build artifacts
clean: clean-coq clean-lean
    @echo "✓ All build artifacts cleaned"

# Clean Coq artifacts
clean-coq:
    @echo "Cleaning Coq artifacts..."
    find archive/proofs/coq -name "*.vo" -delete
    find archive/proofs/coq -name "*.vok" -delete
    find archive/proofs/coq -name "*.vos" -delete
    find archive/proofs/coq -name "*.glob" -delete
    find archive/proofs/coq -name ".*.aux" -delete

# Clean Lean artifacts
clean-lean:
    @echo "Cleaning Lean artifacts..."
    cd archive/proofs/lean4 && lake clean

# ============================================================================
# Development
# ============================================================================

# Format code — no formatter is configured: the AffineScript/TypeScript tree it
# targeted was removed (#75). Fails loudly rather than reporting a no-op as success.
format:
    @echo "format: no formatter configured for this repository (see #75)" >&2; exit 1

# Lint code — no linter is configured: `npm run lint || true` targeted a package.json
# that does not exist and could never fail (#75). Fails loudly instead.
lint:
    @echo "lint: no linter configured for this repository (see #75)" >&2; exit 1

# ============================================================================
# CI/CD
# ============================================================================

# Run CI pipeline locally
ci: build-all test-all verify-all
    @echo "✓ CI pipeline completed successfully"

# ============================================================================
# Installation
# ============================================================================

# ============================================================================
# Container (Podman/Docker)
# ============================================================================

# Build container image (Podman preferred)
container-build:
    @echo "Building container image..."
    podman build -t absolute-zero:latest .

# Run verification in container
container-verify:
    @echo "Running verification in container..."
    podman run --rm absolute-zero:latest just verify-all

# Run container interactively
container-shell:
    @echo "Starting interactive shell..."
    podman run --rm -it absolute-zero:latest /bin/bash

# Run all language examples in container
container-test-all:
    @echo "Testing all languages in container..."
    podman run --rm absolute-zero:latest just test-all

# Docker compatibility aliases
docker-build: container-build
docker-verify: container-verify

# ============================================================================
# Research
# ============================================================================

# Generate LaTeX paper
paper:
    @echo "Generating research paper..."
    cd papers && pdflatex main.tex

# Count lines of code
stats:
    @echo "Project statistics:"
    @echo ""
    @echo "Proof code:"
    @find proofs -name "*.v" -o -name "*.lean" -o -name "*.agda" -o -name "*.thy" -o -name "*.miz" -o -name "*.smt2" | xargs wc -l | tail -1
    @echo ""
    @echo "Documentation:"
    @find docs -name "*.md" | xargs wc -l | tail -1
    @echo ""
    @echo "Total:"
    @find . -name "*.v" -o -name "*.lean" -o -name "*.agda" -o -name "*.thy" -o -name "*.miz" -o -name "*.smt2" -o -name "*.res" -o -name "*.py" -o -name "*.ts" -o -name "*.md" | xargs wc -l | tail -1

# Check proof completion status
proof-status:
    @echo "=== Proof Completion Status ==="
    @echo ""
    @echo "Coq proofs:"
    @admitted=$$(grep -r "Admitted\." archive/proofs/coq/ 2>/dev/null | wc -l); \
    total=$$(grep -r "Theorem\|Lemma\|Corollary" archive/proofs/coq/ 2>/dev/null | wc -l); \
    if [ $$total -gt 0 ]; then \
        complete=$$((total - admitted)); \
        percent=$$((complete * 100 / total)); \
        echo "  Theorems: $$total"; \
        echo "  Complete: $$complete"; \
        echo "  Admitted: $$admitted"; \
        echo "  Completion: $$percent%"; \
    else \
        echo "  No Coq files found"; \
    fi
    @echo ""
    @echo "Lean 4 proofs:"
    @sorry=$$(grep -r "sorry" archive/proofs/lean4/ 2>/dev/null | wc -l); \
    total=$$(grep -r "theorem\|lemma" archive/proofs/lean4/ 2>/dev/null | wc -l); \
    if [ $$total -gt 0 ]; then \
        complete=$$((total - sorry)); \
        percent=$$((complete * 100 / total)); \
        echo "  Theorems: $$total"; \
        echo "  Complete: $$complete"; \
        echo "  Sorry: $$sorry"; \
        echo "  Completion: $$percent%"; \
    else \
        echo "  No Lean files found"; \
    fi
    @echo ""
    @echo "Z3 SMT specifications:"
    @theorems=$$(grep -c "assert.*theorem" proofs/z3/cno_properties.smt2 2>/dev/null || echo 0); \
    echo "  Theorems: $$theorems"

# ============================================================================
# Help
# ============================================================================

# Show detailed help
help:
    @echo "Absolute Zero - Build Automation"
    @echo ""
    @echo "Common commands:"
    @echo "  just build-all       - Build everything"
    @echo "  just verify-all      - Verify all proofs"
    @echo "  just test-all        - Run all tests"
    @echo "  just clean           - Clean build artifacts"
    @echo "  just ci              - Run full CI pipeline"
    @echo ""
    @echo "For all commands: just --list"

# ============================================================================
# Elm GUI Playground
# ============================================================================

# Build Elm playground
build-elm:
    @echo "Building Elm playground..."
    @if command -v elm >/dev/null 2>&1; then \
        cd elm && elm make src/Main.elm --output=dist/main.js && echo "✓ Elm compiled"; \
    else \
        echo "⚠ elm not found, skipping Elm build"; \
    fi

# Run Elm playground (opens in browser)
run-elm: build-elm
    @echo "Opening Elm playground..."
    @python3 -m http.server 8000 &
    @sleep 2
    @xdg-open http://localhost:8000/elm-playground.html || open http://localhost:8000/elm-playground.html

# Clean Elm artifacts
clean-elm:
    @echo "Cleaning Elm artifacts..."
    rm -rf elm/dist elm/elm-stuff

# ============================================================================
# ECHIDNA Integration (Neurosymbolic Proof Assistant)
# ============================================================================

# List all Admitted proofs needing completion
echidna-list:
    @./scripts/use-echidna.sh list-admitted

# Get tactic suggestions for a proof file
echidna-suggest FILE:
    @./scripts/use-echidna.sh suggest {{FILE}}

# Attempt to auto-complete proofs in a file
echidna-complete FILE:
    @./scripts/use-echidna.sh complete {{FILE}}

# Verify all proofs with multi-prover consensus
echidna-verify:
    @./scripts/use-echidna.sh verify-all

# Start ECHIDNA interactive REPL
echidna-repl:
    @./scripts/use-echidna.sh repl

# Check ECHIDNA installation
echidna-check:
    @echo "Checking ECHIDNA installation..."
    @if [ -x ~/Documents/hyperpolymath-repos/echidna/target/release/echidna ]; then \
        echo "✓ ECHIDNA binary found"; \
        ~/Documents/hyperpolymath-repos/echidna/target/release/echidna --version; \
    else \
        echo "❌ ECHIDNA not built. Run:"; \
        echo "   cd ~/Documents/hyperpolymath-repos/echidna && cargo build --release"; \
    fi

