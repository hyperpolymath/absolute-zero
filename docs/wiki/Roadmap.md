<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Roadmap

Short summary; the authoritative version is [`ROADMAP.adoc`](../../ROADMAP.adoc) at the root.

## Now (post v1.0.0-alpha)

* ✅ Both pillars machine-checked across six provers + Idris (PR #100) — `proofs/verify-all-provers.sh`
* ✅ OND pillar authored (OND-1..5 proved, zero axioms); ✅ Idris ABI builds; ✅ Isabelle + Mizar verify
* Wire proof verification into CI (`.github/workflows/proofs.yml` runs Coq + Z3; extend to more provers)
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
  [`.machine_readable/6a2/META.a2ml`](../../.machine_readable/6a2/META.a2ml)
  `architecture-decisions` section
* Backward-looking audit events → [`AUDIT.adoc`](../../AUDIT.adoc)
* Live phase / progress → [`.machine_readable/6a2/STATE.a2ml`](../../.machine_readable/6a2/STATE.a2ml)
