<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Roadmap

Short summary; the authoritative version is [`ROADMAP.adoc`](../../ROADMAP.adoc) at the root.

## Now (post v1.0.0-alpha)

* ✅ Both pillars machine-checked across six provers + Idris (PR #100) — via `proofs/verify-all-provers.sh`, now archived as `archive/proofs/verify-all-provers.six-prover.sh`; since 2026-10-10 the active gate is `proofs/verify-active-provers.sh` (Agda + Z3 bounded + Idris 2 ABI)
* ✅ OND pillar authored (OND-1..5 proved, zero axioms); ✅ Idris ABI builds; ✅ Isabelle + Mizar verified (2026-07-07; both archived under `archive/proofs/` since 2026-10-10)
* Wire proof verification into CI (`.github/workflows/proofs.yml` runs the `agda`, `z3` and `idris` jobs; the Coq and Lean 4 jobs were dropped when those trees were archived on 2026-10-10)
* Discharge the class-A remainder (needs finite-dim/tensor QM + coinductive-β machinery) — optional
* Prove **OND-6** (conditional composition) — the research capstone

## Next (v0.9 → v1.0 milestones)

* `v0.9.0` — Container / CI proof verification: Containerfile with all six provers, cross-arch CI
* `v1.0.0` — Publication: paper (both pillars, six-prover story), industrial CNO/OND examples

## Long horizon (v2 → v12)

7-year vision: language expansion, AI-assisted proving, quantum verification,
standardisation. Detailed phase decomposition in [`ROADMAP.adoc`](../../ROADMAP.adoc).

## How decisions are recorded

* Forward-looking architectural choices → ADRs in
  [`.machine_readable/descriptiles/META.a2ml`](../../.machine_readable/descriptiles/META.a2ml)
  `architecture-decisions` section
* Backward-looking audit events → [`AUDIT.adoc`](../../AUDIT.adoc)
* Live phase / progress → [`.machine_readable/descriptiles/STATE.a2ml`](../../.machine_readable/descriptiles/STATE.a2ml)
