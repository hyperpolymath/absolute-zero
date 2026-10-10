K9!
# SPDX-License-Identifier: MPL-2.0
# bust.k9.ncl — K9 contractile component: BUST (breakage and failure-recovery)
# Repo: absolute-zero
#
# Migrated from archive/a2ml-v1/contractiles-Bustfile.a2ml.txt (2026-10-10,
# a2ml retirement: D99, D269c, D312, D313; envelope per MIGRATION-1058 M1 and
# the K9 contract spec v1.0.0). Source semantics: every declared failure mode
# must have a recovery path that has been exercised.
#
# Leash / authority: 'Hunt / blocking (hard gate). Estate template canon for
# the bust verb.
#
# Runner: NOT ENABLED (runner-semantics.enabled = false in the source). The old
# runner (bust.ncl) was never present in this repo, and D187/#81 rule on whether
# it is dropped. Ledger row B-5.
#
# Signature: NONE. K9-S009 requires a signature block at 'Hunt. No signing
# ceremony has run. Not authorised to run as 'Hunt until the owner signs it
# (ledger row K-1).

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:bust",
    semantics = "recovery-drill",

    security = {
      leash = 'Hunt,
      trust_level = "blocking (hard gate)",
      signature_required = true,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = true,
      capabilities = [ "process.spawn" ],
      injection_scope = "system-under-test-only",
    },

    metadata = {
      name = "absolute-zero-bust",
      version = "1.1.0",
      description = "Rollback procedures when something breaks: revert-first escalation, secret-leak response, proof-suite breakage recovery.",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    side_effects = [
      "drill mode would inject declared failures into the system under test; the runner is NOT enabled, so no drill runs today",
      "writes nothing; no network access",
    ],
  },

  declaration = {
    abstract = "Rollback procedures when something breaks: revert-first escalation, secret-leak response, proof-suite breakage recovery.",
    last_updated = "2026-10-10",

    runner_semantics = {
      enabled = false,
      verb = "bust",
      gate = "hard gate on any failure mode with missing or broken recovery",
      injection_scope = "system-under-test-only",
      allow_network = false,
      record_recovery_times = true,
    },

    scenarios = [
      {
        id = "bad-merge-or-bump",
        description = "A bad commit (merge, pointer/pin bump, metadata sweep) lands on main",
        recovery = "git revert <commit>: reversible, low blast radius; child/upstream repos untouched",
        status = "verified",
        notes = "Generalised from the ported 'bad-pointer-bump' scenario; exercised routinely via PR reverts.",
      },
      {
        id = "secret-leaked-to-public-history",
        description = "Secret or private content committed to public history",
        recovery = "Hard-rotate the leaked secret IMMEDIATELY; then git-filter-repo or BFG on the affected history; public re-publication only after rotation completes",
        status = "declared",
        notes = "Ported in substance from the nested Bustfile, generalised from submodule to any public history. Rotation before rewrite, always.",
      },
      {
        id = "proof-suite-breakage",
        description = "Proof suite goes red systemically (toolchain or keystone regression)",
        recovery = "Revert to last CI-green; for keystone damage use the rescue-branch pattern (re-prove on a branch, land via reviewed PR)",
        status = "verified",
        notes = "Exercised: Tier-0 rescue 2026-05-18 (docs/archive/PROOF-STATUS-2026-05-18.md); rescue branch rebased and landed 2026-05-20 (PR #24). The active proof stack is now Agda, Z3 and Idris 2; archived provers are under archive/proofs/.",
      },
      {
        id = "submodule-pointer-points-at-missing-sha",
        description = "Submodule pointer references a SHA missing from the child remote",
        recovery = "git submodule update --init --checkout <path>; or revert the stale bump commit",
        status = "not-applicable",
        reason = "absolute-zero has no git submodules (no .gitmodules). Preserved from the ported meta-repo-flavoured Bustfile so its content is not lost.",
      },
      {
        id = "submodule-orphan-after-local-only-commit",
        description = "Local-only submodule commit stranded after parent reset",
        recovery = "git reset to before the stranded commit; fix the remote situation before re-attempting",
        status = "not-applicable",
        reason = "absolute-zero has no git submodules (no .gitmodules). Preserved from the ported meta-repo-flavoured Bustfile so its content is not lost.",
      },
    ],

    escalation_ladder = [
      "1. revert the offending commit (reversible, low blast radius)",
      "2. reset the local clone / working tree (affects only local workspace)",
      "3. force-push to main: PROHIBITED without explicit user confirmation (violates branch protection)",
      "4. registry-level action (delete/archive the GitHub repo): human-only, never by AI",
    ],

    backup_points = [
      "GitHub (origin) serves as the durable backup for the full history",
      "CI-green commits on origin/main are the durable rollback targets for the proof suite",
      "Local backup tags (backup/pre-<operation>-<date>) retained on risky rewrites",
    ],
  },
}
