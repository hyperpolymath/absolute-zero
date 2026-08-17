// SPDX-License-Identifier: MPL-2.0
= Absolute Zero — Certified Null Operations and Observational Null Disclosure
:toc: preamble
:toc-title: Contents
:icons: font
:doctype: article

image:https://img.shields.io/badge/OpenSSF-BestPractices-green[link="https://www.bestpractices.dev/projects/XXXX"]

Multi-prover formal verification of programs that provably compute nothing (CNO) and programs that provably reveal nothing (OND). Two co-equal pillars: Certified Null Effect and Certified Null Disclosure.

== Overview

Absolute Zero formalises two kinds of computational nothingness:

CNO (Certified Null Effect)::
  A program that does nothing to the world: it terminates, maps input state to identical output state, is pure, and is thermodynamically reversible. The conserved quantity is state.

OND (Observational Null Disclosure)::
  A program that reveals nothing about its secret input to a declared observer: its observable trace is constant over the secret, relative to a declared observation model `O`. The conserved quantity is the secret-to-observable channel. Every OND claim ships a residue list of out-of-scope observables: the honest boundary between the proof and the physical metal.

The two pillars are logically independent (a proved theorem, with witnesses). They are connected by a coupling dial between a thing and the trace it casts to an observer—this dial is framing, not theorem.

== The two pillars

[cols="1,2,2", options="header"]
|===
| Pillar | Certifies | Conserved quantity

| CNO
| Null *effect*: operation leaves state identical, is pure, and is thermodynamically reversible
| State

| OND
| Null *disclosure*: observable trace is constant over the secret input, relative to observation model `O`
| Secret→observable channel
|===

Both pillars are machine-checked. OND obligations OND-1..5 are proved with zero axioms in Coq, mirrored in Lean 4, Agda, and Z3. The independence theorem is anchored to `is_CNO`. OND-6 (conditional composition, the research capstone) remains open by design.

== What is standard and what is ours

[cols="1,2,2", options="header"]
|===
| Concept | Status | Home

| Landauer's principle / reversible computing
| Standard (Landauer 1961, Bennett 1973)
| `proofs/coq/physics/`, `proofs/lean4/StatMech.lean`

| Non-interference / observational determinism
| Standard (security literature)
| OND pillar

| Identity morphisms in category theory
| Standard
| `proofs/coq/category/`

| Multi-prover cross-validation
| Standard methodology
| `proofs/verify-all-provers.sh`

| CNO formalisation (termination + state preservation + purity + reversibility)
| **Novel assembly**
| `proofs/coq/common/CNO.v`

| OND formalisation with declared `O` and residue lists
| **Novel formalisation**
| `proofs/coq/ond/OND.v`

| CNO ↔ OND independence proof
| **Novel theorem**
| Core proofs

| Malbolge / Brainfuck / Whitespace CNO verification
| **Novel application**
| `interpreters/`, `proofs/coq/malbolge/`
|===

== Multi-prover verification

[cols="1,2,2,2", options="header"]
|===
| Prover | Foundation | CNO Status | OND Status

| Coq 8.19
| Constructive type theory
| 115 Qed, 0 Admitted, 61 Axioms
| OND-1..5: zero axioms

| Lean 4
| Dependent type theory + Mathlib
| Phases 1–4 complete, 52 Axioms
| Mirrored

| Agda 2.6
| Dependent types
| Phase 1 complete
| Mirrored

| Z3 4.13
| SMT solving
| 10 theorems encoded
| Mirrored

| Isabelle/HOL
| Higher-order logic
| Phase 1 complete
| Mirrored

| Mizar
| Set theory
| Phase 1 complete
| Mirrored
|===

[CAUTION]
====
**Axioms are unproven assumptions, not theorems.** The Coq CNO development rests on 61 axioms (e.g., quantum-gate unitarity, complex-analysis identities, Shannon-entropy non-negativity, filesystem inverse laws). "Machine-checked" means checked *relative to those axioms*—not an axiom-free proof. The OND pillar (OND-1..5) is axiom-free. Discharging the CNO axioms is the next major obligation.
====

[CAUTION]
====
**Z3, Isabelle, and Mizar are generated but not yet run.** The artefacts exist in-tree but are not part of the CI gate. Only Coq, Lean 4, and Agda are machine-checked in CI.
====

== Known scope boundaries

[CAUTION]
====
**OND-6 (conditional composition) is open.** OND obligations 1–5 are proved. OND-6, the research capstone for composing OND-certified operations under conditions, remains open by design.
====

[CAUTION]
====
**OND claims are conditional on the declared observation model `O`.** An OND proof certifies non-disclosure *relative to `O`*. It ships a residue list of out-of-scope observables (timing, power, cache). The proof does not cover observables not in `O`.
====

[CAUTION]
====
**CNO verification is undecidable in general** (reduction from the halting problem). The formalisations here verify specific programs or finite-state classes, not arbitrary programs.
====

== Repository Layout

[cols="1,3", options="header"]
|===
| Path | Purpose

| `proofs/coq/`
| Coq proofs: CNO framework, Malbolge, physics, category theory, lambda, quantum, filesystem, OND

| `proofs/lean4/`
| Lean 4 mirrors of CNO and OND modules

| `proofs/agda/`, `proofs/z3/`, `proofs/isabelle/`, `proofs/mizar/`
| Additional prover artefacts (Agda checked in CI; others generated but not yet run)

| `proofs/ond/`
| OND Coq module (OND-1..5 proved, zero axioms)

| `proofs/observation-models/`
| Declared observation models `O` (proof inputs for OND)

| `proofs/residue/`
| OND residue lists (model-vs-metal gap)

| `interpreters/`
| Malbolge (ReScript), Brainfuck (Python), Whitespace (Python) with CNO detection

| `proofs/verify-all-provers.sh`
| One-shot gate: both pillars, all six provers + Idris ABI
|===

== Build

[source,bash]
----
# One-shot: both pillars, all provers
proofs/verify-all-provers.sh

# Or via task runner
just verify

# Individual provers
just build-coq
just verify-agda
----

== Documentation

* link:EXPLAINME.adoc[EXPLAINME] — claim-by-claim receipts and known gaps
* link:Glossary.adoc[Glossary] — terminology reference
* `docs/TWO-PILLARS.adoc` — narrative description of CNO and OND
* `docs/OND-ROADMAP.adoc` — prioritised OND obligations
* `PROOF-STATUS.adoc` — per-prover verification status

== License

SPDX-License-Identifier: MPL-2.0 — see link:LICENSE[LICENSE].

Prose documentation is licensed under CC-BY-SA-4.0; see `LICENSES/`.====

== Repository Layout

[cols="1,3", options="header"]
|===
| Path | Purpose

| `proofs/coq/`
