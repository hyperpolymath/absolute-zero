K9!
# SPDX-License-Identifier: MPL-2.0
# trust.k9.ncl — K9 contractile component: TRUST (trust boundaries and integrity invariants)
# Repo: absolute-zero
#
# Migrated from archive/a2ml-v1/contractiles-Trustfile.a2ml.txt (2026-10-10,
# a2ml retirement: D99, D269c, D312, D313; envelope per MIGRATION-1058 M1 and
# the K9 contract spec v1.0.0).
#
# Leash / authority: 'Hunt / blocking (hard gate). The leash is the estate
# template canon for the trust verb. The source Trustfile declares no leash.
#
# Runner: DISABLED in the source ([runner] enabled = false). It stays disabled here.
#
# Signature: NONE. K9-S009 requires a signature block at 'Hunt. No signing
# ceremony has run, and this sandbox has no signing key. This contract is NOT
# authorised to run as 'Hunt until the owner signs it. Ledger row K-1.
#
# Probes are the source `run` strings with TOML escapes decoded, except for the
# dangerous-patterns probe below. Its shared script is enforced separately in
# proofs.yml, independently of this disabled contract runner.
#
# Adaptations (ledger rows A-T1, A-T2): the Lean and Coq "bounded" checks point
# at archive/proofs/ because those provers are archived (2026-10-10).

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:trust",
    semantics = "invariant",

    security = {
      leash = 'Hunt,
      trust_level = "maximal",
      signature_required = true,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = true,
      capabilities = [ "process.spawn" ],
    },

    metadata = {
      name = "absolute-zero-trust",
      version = "1.0.0",
      description = "Trust boundaries for AI agents plus integrity invariants: no committed secrets, traceable provenance, and dangerous proof patterns held at the verified baselines.",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    side_effects = [
      "runs read-only shell probes (test, grep, find, git log) from the repository root; one subprocess per invariant",
      "writes nothing; no network access",
    ],
  },

  declaration = {
    abstract = "Trust boundaries for AI agents plus integrity invariants: no committed secrets, traceable provenance, and dangerous proof patterns held at the verified baselines.",
    last_updated = "2026-10-10",

    runner = {
      enabled = false,
      command = "just trust-check",
      on_push = false,
      on_pr = false,
      note = "Scaffold only. Do not activate until the maintainer has reviewed.",
    },

    trust = {
      level = "maximal",
      definition = "Agents may read, build, test, lint and format freely. Destructive or external actions, and edits to the protected paths below, require maintainer approval.",
      protected_paths = [
        ".claude/CLAUDE.md",
        ".github/workflows/",
        "proofs/",
        "src/abi/",
        "LICENSE",
        "TOPOLOGY.adoc",
        "coordination.k9",
      ],
    },

    invariants = [
      {
        id = "no-secrets-committed",
        section = "secrets",
        description = "No credential files in repo",
        probe = "test ! -f .env && test ! -f credentials.json && test ! -f .env.local && test ! -f .env.production",
        severity = "critical",
      },
      {
        id = "no-private-keys",
        section = "secrets",
        description = "No private key files committed",
        probe = "! find . -name '*.pem' -o -name '*.key' -o -name 'id_rsa' -o -name 'id_ed25519' 2>/dev/null | grep -v node_modules | head -1 | grep -q .",
        severity = "critical",
      },
      {
        id = "no-tokens-in-source",
        section = "secrets",
        description = "No hardcoded API tokens in source files",
        probe = "! grep -rE '(api[_-]?key|secret|token|password)[[:space:]]*[:=][[:space:]]*[\\\"'\\\\''][A-Za-z0-9]{16,}' --include='*.js' --include='*.res' --include='*.py' --include='*.rs' . 2>/dev/null | grep -v node_modules | head -1 | grep -q .",
        severity = "critical",
      },
      {
        id = "author-correct",
        section = "provenance",
        description = "Git author matches expected identity",
        probe = "git log -1 --format='%ae' | grep -qE '(hyperpolymath|j\\\\.d\\\\.a\\\\.jewell)'",
        severity = "warning",
      },
      {
        id = "license-content",
        section = "provenance",
        description = "LICENSE contains the MPL identifier (repo policy: MPL-2.0 only, PMPL banned)",
        probe = "grep -q 'Mozilla Public License' LICENSE",
        severity = "warning",
      },
      {
        id = "container-images-pinned",
        section = "container-security",
        description = "Containerfile uses pinned/Chainguard base images",
        probe = "test ! -f Containerfile || grep -q 'cgr.dev\\\\|@sha256:' Containerfile",
        severity = "warning",
      },
      {
        id = "no-dockerfile",
        section = "container-security",
        description = "No Dockerfile (use Containerfile)",
        probe = "test ! -f Dockerfile",
        severity = "warning",
      },
      {
        id = "no-dangerous-proof-patterns",
        section = "dangerous-patterns",
        description = "At most five believe_me code occurrences in src/abi Idris files; none elsewhere in src. No assert_total, unsafeCoerce or Obj.magic in src",
        probe = "bash scripts/check-proof-patterns.sh",
        baseline = 5,
        baseline_note = "Issue #27: four sites in Proofs/DivMod.idr and one in Layout.idr. Enforced by the shared script in CI even while this runner is disabled.",
        severity = "critical",
      },
      {
        id = "lean4-sorry-bounded",
        section = "dangerous-patterns",
        description = "Lean 4 sorry count does not exceed baseline (0). Archived prover; path adapted to archive/proofs/lean4/ (A-T1)",
        probe = "count=$(grep -rn 'sorry' archive/proofs/lean4/ 2>/dev/null | grep -v '^[[:space:]]*--' | wc -l); test \"$count\" -le 0",
        severity = "high",
        baseline = 0,
        baseline_note = "Refreshed 2026-06-12 from a verified grep (0 hits). Lean is archived under archive/proofs/lean4/ as of 2026-10-10; the check is retained for reference.",
      },
      {
        id = "coq-admitted-bounded",
        section = "dangerous-patterns",
        description = "Coq Admitted count does not exceed baseline (0). Archived prover; path adapted to archive/proofs/coq/ (A-T2)",
        probe = "count=$(grep -rn 'Admitted' archive/proofs/coq/ 2>/dev/null | wc -l); test \"$count\" -le 0",
        severity = "high",
        baseline = 0,
        baseline_note = "Refreshed 2026-06-12 from a verified grep (0 hits). Coq is archived under archive/proofs/coq/ as of 2026-10-10; the check is retained for reference.",
      },
      {
        id = "no-unsafe-rust-without-comment",
        section = "dangerous-patterns",
        description = "All unsafe blocks in Rust must have SAFETY comments",
        probe = "! grep -B1 'unsafe {' --include='*.rs' -r . 2>/dev/null | grep -v SAFETY | grep 'unsafe {' | head -1 | grep -q .",
        severity = "warning",
      },
      {
        id = "localhost-only-bindings",
        section = "service-security",
        description = "No wildcard service bindings in source (n/a: research repo; kept for estate consistency)",
        probe = "! grep -rE 'bind\\\\(\\\"0\\\\.0\\\\.0\\\\.0' --include='*.rs' --include='*.ex' --include='*.res' . 2>/dev/null | head -1 | grep -q .",
        severity = "critical",
      },
    ],
  },
}
