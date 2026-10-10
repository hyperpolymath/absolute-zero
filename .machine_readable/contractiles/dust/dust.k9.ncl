K9!
# SPDX-License-Identifier: MPL-2.0
# dust.k9.ncl — K9 contractile component: DUST (recovery and rollback semantics)
# Repo: absolute-zero
#
# Migrated from archive/a2ml-v1/contractiles-Dustfile.a2ml.txt (2026-10-10,
# a2ml retirement: D99, D269c, D312, D313; envelope per MIGRATION-1058 M1 and
# the K9 contract spec v1.0.0). Every asset that can degrade declares a
# reversible recovery path.
#
# Leash / authority: 'Yard / advisory (continue-with-warnings). Estate template
# canon for the dust verb.
#
# Grants: NONE. At 'Yard the spec permits no filesystem, network or subprocess
# access. The source's recovery handlers are text for humans and agents, not
# executed by this component. Ledger row D-1.
#
# Adaptations (ledger rows A-D1, A-D2): the proof-suite asset now names the
# active and archived proof trees; the machine-metadata asset names the deed,
# the K9 contracts and coordination.k9 in place of the retired .a2ml set.

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:dust",
    semantics = "recovery-paths",

    security = {
      leash = 'Yard,
      trust_level = "advisory (continue-with-warnings)",
      signature_required = false,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
      capabilities = [],
    },

    metadata = {
      name = "absolute-zero-dust",
      version = "1.0.0",
      description = "Reversible recovery paths for absolute-zero: git-revert-first discipline, proof-suite rescue precedent, append-only archives, and pinned-workflow rollback.",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  declaration = {
    abstract = "Reversible recovery paths for absolute-zero: git-revert-first discipline, proof-suite rescue precedent, append-only archives, and pinned-workflow rollback.",
    last_updated = "2026-10-10",

    recoveries = [
      {
        id = "bad-commit-on-main",
        asset = "main branch history",
        reversible = true,
        handler = "git revert <sha>: origin/main on GitHub is the durable history; never force-push main",
        notes = "First rung for any regression: revert, do not rewrite.",
      },
      {
        id = "proof-suite-regression",
        asset = "proofs/ (agda, z3, observation-models, residue) + src/abi/; archive/proofs/ (coq, lean4, isabelle, mizar) is reference-only since 2026-10-10 (A-D1)",
        reversible = true,
        handler = "Revert the offending commit to the last CI-green state; for systemic breakage follow the rescue-branch pattern",
        notes = "Exercised precedent: Tier-0 rescue of 2026-05-18 (ledger archived at docs/archive/PROOF-STATUS-2026-05-18.md).",
      },
      {
        id = "ci-workflow-regression",
        asset = ".github/workflows/ (thin wrappers over hyperpolymath/standards reusables)",
        reversible = true,
        handler = "Revert the pin bump; workflows are SHA-pinned to the standards reusables, so rollback = restoring the previous pinned SHA",
        notes = "Exercised precedent: PR #69 repinned orphan reusable SHAs (97df7621/4fdf4314 to live).",
      },
      {
        id = "stale-machine-metadata",
        asset = "machine-readable metadata: absolute-zero_chora.deed, .machine_readable/contractiles/ K9 set, coordination.k9, .machine_readable/bot_directives/ (A-D2)",
        reversible = true,
        handler = "Regenerate from repo facts (git log since the last deed date + repo docs); prior states are recoverable from git history and from archive/a2ml-v1/",
        notes = "Deed updates are additive; never invent facts; omit unknown keys.",
      },
      {
        id = "dated-doc-supersession",
        asset = "docs/archive/",
        reversible = true,
        handler = "Append-only: supersede by adding a new dated snapshot; consult docs/archive/README.adoc for the live counterpart of each archived file",
        notes = "Do not edit archived snapshots in place.",
      },
      {
        id = "github-wiki-divergence",
        asset = "GitHub Wiki (mirror of docs/wiki/)",
        reversible = true,
        handler = "docs/wiki/ in-repo is canonical; re-run the sync procedure in docs/wiki/README.md to overwrite the wiki copy",
        notes = "Wiki divergence is always resolvable in favour of the in-repo source.",
      },
      {
        id = "template-dust-handlers",
        asset = "decision-log replay / policy rollback / gateway deployment undo (from the removed root template)",
        reversible = false,
        status = "not-applicable",
        reason = "Template placeholders from contractiles/dust/Dustfile (generic gateway repo shape: logs/decisions.json, policy/policy.ncl, kubectl rollout undo). absolute-zero has no such gateway, deployment, or decision-log assets; recorded here so the removed template's content is accounted for rather than lost.",
      },
    ],
  },
}
