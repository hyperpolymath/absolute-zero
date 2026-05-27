<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
-->

# Proof Debt — absolute-zero

**Schema**: [hyperpolymath/standards `TRUSTED-BASE-REDUCTION-POLICY.adoc`](https://github.com/hyperpolymath/standards/blob/main/docs/TRUSTED-BASE-REDUCTION-POLICY.adoc) (standards#203).

## Initial inventory

The 2026-05-26 estate proof-debt audit
([standards#195](https://github.com/hyperpolymath/standards/pull/195))
detected **129 soundness-relevant escape hatches** in this repo (now
**124** after intervening closures). Markers were originally seeded
in §(d) DEBT pending classification.

## Phase 1 triage — 72 Coq Axioms (2026-05-27, [#58](https://github.com/hyperpolymath/absolute-zero/pull/58))

The per-marker classification for every Coq `Axiom` lives in
[`docs/proof-debt-triage.md`](./proof-debt-triage.md). Summary:

| Disposition | Count |
|-------------|------:|
| §(c) AXIOM (TRUSTED-BASE) | 52 |
| §(a) DISCHARGE backlog    | 17 |
| §(b) PROPERTY-TEST        |  3 |
| **Total Coq Axioms**      | **72** |

Out of scope for Phase 1 (still in §(d) pending future triage):
52 Lean 4 `axiom` declarations and the 7 Idris2 postulates tracked by
[#27](https://github.com/hyperpolymath/absolute-zero/issues/27).

## Phase 2a triage — Lean Lambda cluster (2026-05-27)

Per-cluster Lean triage rolling out 2026-05-27 in cluster-sized PRs.
First cluster: `proofs/lean4/LambdaCNO.lean` (3 axioms).

| Line | Identifier | Disposition | Justification |
|-----:|------------|-------------|---------------|
| 183  | `subst_closed_term`        | §(d) DEBT   | Standard metatheoretic property of lambda calculus; provable by induction on `t` once the substitution-on-closed-terms lemma is mechanised. |
| 232  | `y_combinator_not_identity` | §(c) AXIOM | Non-termination claim about Y combinator; requires step-indexed semantics or coinduction (same justification as Coq `y_not_cno`). |
| 258  | `eta_equivalence`           | §(c) AXIOM | η-equivalence is not derivable under β-only reduction (same justification as Coq `eta_equivalence` at LambdaCNO.v:376). |

The two §(c) entries are annotated inline with `-- AXIOM:` leading
comments. The §(d) entry below has an owner + deadline.

## (a) DISCHARGE backlog (Coq, 17)

Provable propositions currently stated as `Axiom`. Enumerated in
[`docs/proof-debt-triage.md`](./proof-debt-triage.md) — each row marked
`DISCHARGE` is a candidate for a future proof PR.

## (b) BUDGETED — tested with a refutation budget (3)

Decidability claims over opaque types: `fs_eq_dec`, `state_dec`,
`state_eq_dec`. Belong to §(b) once a §(b) property-test budget is
attached; otherwise treat as §(c).

## (c) NECESSARY AXIOM (Coq, 52)

Physics constants, quantum gate primitives, POSIX semantics,
Kolmogorov + Shannon entropy core inequalities, complex exponential
algebra, and fundamental physical laws (second law, Landauer, no-cloning).
Full enumeration in [`docs/proof-debt-triage.md`](./proof-debt-triage.md).

## (d) DEBT — actively to be closed

After Phase 1, the §(d) bucket contains only the Lean axioms and 7
Idris2 postulates that have not yet been triaged. Coq markers are
no longer in §(d).

### Lean — provable, awaiting proof

- `proofs/lean4/LambdaCNO.lean:183` — `subst_closed_term`
  - **Owner**: @hyperpolymath
  - **Plan**: discharge by induction on `t : LambdaTerm`; closed-term
    invariant carries through `LVar`, `LAbs`, `LApp` cases. Sibling to
    Coq's `subst` lemmas in `proofs/coq/lambda/LambdaCNO.v`.
  - **Deadline**: INDEFINITE (no proof-PR scheduled yet — provable;
    awaits Lean-side discharge push).

### Lean — pending triage

49 Lean axioms remain to be triaged (FilesystemCNO 21, QuantumCNO 14,
StatMech 14). Triage planned in cluster-sized PRs through
2026-06 — see this file's status block at the bottom.

### Idris2 — pending triage

7 Idris2 postulates in `src/abi/Layout.idr`. Tracked by
[#27](https://github.com/hyperpolymath/absolute-zero/issues/27).

```
(Coq markers no longer in §(d) post Phase 1; see triage doc for §a/§b/§c.)
```

> If `129` > 30, the list above shows the first 30 only.
> The full list is reproducible via:
>
> ```bash
> bash /path/to/standards/scripts/check-trusted-base.sh .
> ```

## Suggested triage process

1. Run `scripts/check-trusted-base.sh` locally; it lists every marker
   with file:line.
2. For each marker, decide:
   - Can this be proven? → §(a) DISCHARGED via a PR that adds the proof.
   - Is this at an FFI / extraction / opaque-primitive boundary? →
     §(b) or §(c). Add a property test and document the refutation
     budget for §(b), or cite the metatheoretic justification for §(c).
   - Is this temporary debt? → §(d) with a deadline.
3. Update this file in the same PR that lands the disposition.
4. The `check-trusted-base` CI job (standards#211) ensures markers
   are never un-annotated AND un-enumerated simultaneously.

## Companion documents

- [standards#195](https://github.com/hyperpolymath/standards/pull/195) — estate proof-debt audit.
- [standards#203](https://github.com/hyperpolymath/standards/pull/203) — trusted-base reduction policy (the schema this file follows).
- [standards#211](https://github.com/hyperpolymath/standards/pull/211) — `check-trusted-base.sh` CI enforcement.

---

🤖 Initial seed by Claude Code, 2026-05-26.
