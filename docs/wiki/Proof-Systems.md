<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Proof Systems

## Why six?

Each prover trades off three axes:

| | Constructive | Automated | Mathlib |
|---|---|---|---|
| Coq         | ✅ | ⚪ | ⚪ |
| Lean 4      | ✅ | ⚪ | ✅ |
| Agda        | ✅ | ⚪ | ⚪ |
| Isabelle    | ⚪ | ⚪ | ✅ |
| Mizar       | ⚪ | ⚪ | ✅ |
| Z3          | ⚪ | ✅ | ⚪ |

A property proved in **all six** is robust against any single backend's
foundational quirks. A property proved in *some but not others*
flags a foundational dependency worth understanding.

## What lives where

Since the 2026-10-10 archive ruling the active stack is Agda (`proofs/agda/`),
Z3 bounded checks (`proofs/z3/`) and the Idris 2 ABI. The Coq, Lean 4,
Isabelle/HOL and Mizar trees below are archived under `archive/proofs/` and are
no longer built or gated; their status lines are historical receipts.

### `archive/proofs/coq/` (archived; formerly the load-bearing system)
* `common/CNO.v` — core CNO definitions and properties
* `physics/StatMech.v` — Landauer bound axiomatised
* `physics/LandauerDerivation.v` — Landauer bound derived (the two
  together form ADR-002's "dual formalisation")
* `category/CNOCategory.v` — CNOs as identity morphisms
* `lambda/LambdaCNO.v` — lambda calculus CNOs
* `quantum/QuantumCNO.v` — quantum CNOs
* `quantum/QuantumMechanicsExact.v` — exact QM formulation
* `malbolge/MalbolgeCore.v` — Malbolge VM semantics
* `filesystem/FilesystemCNO.v` — filesystem CNOs

Status (PR #100, 2026-07-06): **14/14 theories compiled, 0 Admitted**, now
including `ond/OND.v` (the OND pillar, OND-1..5, zero axioms). CNO axioms cut
98→small classified remainder: filesystem/category/QuantumMechanicsExact fully
discharged; genuine physical postulates kept as tagged `METAL-BOUNDARY`; a few
class-A items openly labelled; three unsound axioms removed/corrected. See
[`PROOF-STATUS.adoc`](../../PROOF-STATUS.adoc) and
[`docs/PROOF-CLASSIFICATION.adoc`](../PROOF-CLASSIFICATION.adoc).

### `archive/proofs/lean4/` (archived)
* `CNO.lean`, `StatMech.lean`, `CNOCategory.lean`, `LambdaCNO.lean`,
  `QuantumCNO.lean`, `FilesystemCNO.lean`
* Was built with `lake build`; mathlib + 6 lean_lib targets;
  1631/1632 green (verified 2026-05-20).

### `proofs/z3/`
SMT proofs of decidable fragments. Fast counterexample search for
candidate CNO claims before committing to a constructive proof.

### `proofs/agda/`
Type-level CNO certificates exploiting dependent types.

### `archive/proofs/isabelle/`, `archive/proofs/mizar/` (archived)
Cross-validation. Catches Coq-specific tactic quirks; connects
Mizar's standard maths library.

## Reproducible build

```bash
just build-agda     # agda --safe --without-K on the four Agda modules
just build-idris    # idris2 --build absolute-zero-abi.ipkg
just verify-z3      # bash proofs/z3/verify.sh (expect-annotated)
just verify         # proofs/verify-active-provers.sh → ACTIVE-PROVERS-GREEN
```

The former `build-coq`, `build-lean`, `build-isabelle` and `build-z3` recipes no
longer exist in the Justfile.

## Discharged axioms (recent)

* **ADR-007** (2026-05-20, PR #24): `eval_deterministic`
  Axiom → Theorem via `step_deterministic_strong`
* **ADR-008** (2026-05-20, PR #32): deleted unsound
  `eval_respects_state_eq_{left,right}` axioms; weakened
  `logically_reversible` to observational reversibility (`=st=`)
* **ADR-009** (2026-05-25, PR #41 / #40):
  deleted unsound Idris2 `alignmentMatchesPlatformWord` postulate;
  consolidated div/mod axioms into shared
  `AbsoluteZero.ABI.Proofs.DivMod`

See [Audit Trail](Audit-Trail.md) for the full ledger.

## Idris2 ABI (the seventh)

The Idris2 surface in `src/abi/` isn't a proof system per se, but
carries formal alignment + size proofs for the C FFI boundary. See
[ABI](ABI.md).
