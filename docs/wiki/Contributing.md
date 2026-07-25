<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Contributing

Short summary; the authoritative version is [`CONTRIBUTING.adoc`](../../CONTRIBUTING.adoc) at the root.

## Language policy (hard rule)

Read [`docs/CLAUDE.adoc`](../CLAUDE.adoc) Language Policy section first.
TL;DR:

* **Allowed**: AffineScript, Deno, Rust, Tauri, Dioxus, Gleam, Bash, JavaScript
  (where AffineScript cannot reach), Nickel, Guile Scheme, Julia, OCaml, Ada, Idris2
* **Banned**: TypeScript, ReScript (banned 2026-04-30 — replaced by
  AffineScript), Node.js, npm/Bun/pnpm/yarn, Go, Python, Java/Kotlin,
  Swift, React Native, Flutter/Dart, Ruby, Perl

`.github/workflows/language-policy.yml` blocks new banned-language files at CI.

## Commit conventions

Conventional commits. Examples:

```
proof(coq): discharge eval_deterministic via step_deterministic_strong
proof(idris2/abi): port to Idris2 0.8.0 syntax (#27)
chore(docs): reconcile and tidy root
ci(codeql): cron weekly→monthly (cut 3, standards#233 Option B) (#71)
```

* Never amend published commits.
* Hook bypass (`--no-verify`, `--no-gpg-sign`) only with explicit owner approval.

## Verify before pushing

```bash
just verify       # full suite
just lint
just fmt
```

## ADR / Audit trail

* If your change is an **architectural decision** going forward, add an ADR
  entry to [`.machine_readable/descriptiles/META.a2ml`](../../.machine_readable/descriptiles/META.a2ml)
  (next ADR-NNN).
* If your change **discharges a postulate / deletes unsound code**, add an
  AUDIT entry to [`AUDIT.adoc`](../../AUDIT.adoc).

## PR checklist

* [ ] SPDX-License-Identifier on all new files (`MPL-2.0` — PMPL identifiers are banned by repo policy)
* [ ] No new banned-language files
* [ ] Tests / proofs updated where relevant
* [ ] If you touched workflows, all `uses:` references pinned to commit SHAs
* [ ] If you added a new top-level dir, it's listed in
  [`RSR_COMPLIANCE.adoc`](../../RSR_COMPLIANCE.adoc)
