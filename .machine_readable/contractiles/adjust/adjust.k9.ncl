K9!
# SPDX-License-Identifier: MPL-2.0
# adjust.k9.ncl — K9 contractile component: ADJUST (drift tolerance)
# Repo: absolute-zero
#
# Migrated from archive/a2ml-v1/contractiles-Adjustfile.a2ml.txt (2026-10-10,
# a2ml retirement: D99, D269c, D312, D313; envelope per MIGRATION-1058 M1 and
# the K9 contract spec v1.0.0). Cumulative-drift catchment: tolerance bands and
# corrective actions. Advisory only: it warns and trends and does not block.
#
# Leash / authority: 'Yard / advisory (continue-with-warnings). Estate template
# canon for the adjust verb.
#
# Grants: NONE. The source's `adjust fix` deterministic auto-fix would write
# files, which 'Yard does not permit. Under this grant `adjust fix` is NOT
# operative; the corrective actions below are for humans and agents. Ledger row D-1.
#
# Adaptations (ledger rows A-A1, A-A2): the Coq-sourced tolerances are marked
# archived because Coq is archived under archive/proofs/ (2026-10-10).

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:adjust",
    semantics = "drift-tolerance",

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
      name = "absolute-zero-adjust",
      version = "1.0.0",
      description = "Drift tolerances for absolute-zero's proof-debt figures, language-policy surface, and documentation sync. Advisory only.",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  declaration = {
    abstract = "Drift tolerances for absolute-zero's proof-debt figures, language-policy surface, and documentation sync. Advisory only.",
    last_updated = "2026-10-10",

    tolerances = [
      {
        id = "coq-axiom-count",
        description = "Coq Axiom count must not exceed the Phase-1 triage baseline",
        tolerance = "<= 72 Axioms (counting method = docs/proof-debt-triage.md, PR #58, 2026-05-27)",
        corrective = "Any NEW axiom requires a triage entry (TRUSTED-BASE / DISCHARGE / PROPERTY-TEST) in docs/proof-debt-triage.md before merge; trend the count DOWN by discharging the 17-item DISCHARGE backlog",
        severity = "advisory",
        status = "archived",
        status_note = "Coq is archived under archive/proofs/coq/ (2026-10-10). Not gated; kept for reference. Note: the cited file docs/proof-debt-triage.md is .adoc in the repo (stale path in the source).",
      },
      {
        id = "coq-parameter-count",
        description = "Coq Parameter count stays at the model-layer baseline",
        tolerance = "<= 42 Parameters (baseline of 2026-05-27)",
        corrective = "New Parameters need the same triage discipline as Axioms",
        severity = "advisory",
        status = "archived",
        status_note = "Coq is archived under archive/proofs/coq/ (2026-10-10). Not gated; kept for reference.",
      },
      {
        id = "escape-hatch-total",
        description = "Total escape hatches across all proof languages must not increase",
        tolerance = "<= 124 (canonical figure per the standards#195 counting method; was 129, reduced to 124 as of the 2026-05-27 STATE entry)",
        corrective = "Decrement by discharge; any increment needs a documented rationale in docs/proof-debt-triage.md",
        severity = "advisory",
        status = "active",
        status_note = "The count baseline predates archiving; recount on the active tree plus archive/proofs/ before relying on it.",
      },
      {
        id = "physics-constant-duplication",
        description = "Physics constants should be declared once, not per-file",
        tolerance = "Known duplication: kB_positive/temperature_positive declared 3x across QuantumCNO/StatMech/LandauerDerivation (surfaced by the Phase-1 triage)",
        corrective = "Deduplicate into a shared constants module (already on the STATE this-week actions; those are now archived)",
        severity = "advisory",
        status = "archived",
        status_note = "The duplicated declarations live in archived Coq sources (archive/proofs/coq/). Not gated.",
      },
      {
        id = "banned-language-surface",
        description = "Banned-language files stay confined to the demonstration surface",
        tolerance = "Banned-language files only under examples/ or enumerated in .hypatia-ignore; zero NEW banned-language files elsewhere",
        corrective = "Move demonstration files under examples/; anything load-bearing gets rewritten per the language policy (Python to Julia/Rust, etc.)",
        severity = "advisory",
        status = "active",
      },
      {
        id = "wiki-sync-drift",
        description = "docs/wiki/ (canonical, in-repo) vs the GitHub Wiki copy",
        tolerance = "GitHub Wiki may lag docs/wiki/ between manual syncs (sync is a manual cp + push, see docs/wiki/README.md)",
        corrective = "Run the sync procedure in docs/wiki/README.md; automation (just wiki-sync + workflow) is a tracked TODO",
        severity = "advisory",
        status = "active",
      },
      {
        id = "stale-dated-docs",
        description = "Dated snapshots belong in docs/archive/",
        tolerance = "0 dated status/roadmap snapshots outside docs/archive/",
        corrective = "Move superseded dated documents into docs/archive/ and add them to docs/archive/README.adoc",
        severity = "advisory",
        status = "active",
      },
    ],
  },
}
