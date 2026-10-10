K9!
# SPDX-License-Identifier: MPL-2.0
# intend.k9.ncl — K9 contractile component: INTEND (north-star intents and wishes)
# Repo: absolute-zero
#
# Migrated from archive/a2ml-v1/contractiles-Intentfile.a2ml.txt (2026-10-10,
# a2ml retirement: D99, D269c, D312, D313; envelope per MIGRATION-1058 M1 and
# the K9 contract spec v1.0.0). Non-gating: this is a report, not a gate.
#
# Leash / authority: 'Hunt / reporting (log drift, never fail). The leash is the
# estate template canon for the intend verb. The source Intentfile has no
# runner and no probes, so this component requests no grants.
#
# Signature: NONE. K9-S009 requires a signature block at 'Hunt. No signing
# ceremony has run. Not authorised to run as 'Hunt until the owner signs it
# (ledger row K-1). Its authority is 'reporting, so an unsigned run can only
# log drift.
#
# Adaptations (ledger rows A-I1..A-I3): the purpose statement now names the
# ACTIVE prover set (Idris 2, Agda, Z3) after the owner's 2026-10-10 ruling.
# Intents and wishes tied to archived provers stay listed, marked parked
# (never silently dropped).

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:intend",
    semantics = "north-star",

    security = {
      leash = 'Hunt,
      trust_level = "reporting (log drift, never fail)",
      signature_required = true,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
      capabilities = [],
    },

    metadata = {
      name = "absolute-zero-intend",
      version = "1.0.0",
      description = "North star for absolute-zero: machine-checked proofs that Certified Null Operations do nothing, en route to a publication release.",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    side_effects = [
      "reads the repository's declarations; writes nothing; no subprocess; no network",
    ],
  },

  declaration = {
    abstract = "North star for absolute-zero: machine-checked proofs that Certified Null Operations (CNOs) do nothing, en route to a publication release.",
    last_updated = "2026-10-10",

    purpose = {
      statement = "Formal verification of Certified Null Operations (programs provably having zero net computational effect), with an Idris 2 ABI and Agda and Z3 proof surfaces, and cross-language demonstration examples. Coq, Lean 4, Isabelle/HOL and Mizar are archived under archive/proofs/ (owner ruling 2026-10-10).",
      supersedes = "The six-prover statement (Coq, Lean 4, Z3, Agda, Isabelle, Mizar), adaptation A-I1.",
    },

    anti_purpose = {
      not = [
        "A production runtime or deployed service (research repo; service-security checks are kept only for estate consistency)",
        "A general-purpose proof framework: the subject is CNOs and their thermodynamic/categorical meaning",
        "A language-advocacy showcase: banned-language files under examples/ exist to demonstrate cross-language nop semantics, not to endorse those languages",
      ],
    },

    if_in_doubt = {
      sensitive_areas = [ "proofs/", "src/abi/", ".github/workflows/", ".claude/CLAUDE.md", "LICENSE", "TOPOLOGY.adoc" ],
      guidance = "Proof semantics and licensing are maintainer-gated; ask before touching.",
    },

    intents = [
      {
        id = "phase-2-triage",
        description = "Phase 2 proof-debt triage of the Idris 2 postulates (#27), following the Phase-1 triage discipline (PR #58). The Lean 52-axiom item is parked: Lean is archived (A-I2).",
        status = "declared",
      },
      {
        id = "discharge-coq-backlog",
        description = "Discharge the 17 DISCHARGE-class Coq axioms from the Phase-1 triage (lowest-hanging: cno_zero_energy_dissipation_derived, fidelity_bound, unitary_inverse_property, *_not_identity existence pair)",
        status = "declared",
        parked = "Coq is archived under archive/proofs/coq/ (2026-10-10). Parked, not abandoned; needs an owner ruling (Coq is also in the D204 Coq Module Type CNO interface).",
      },
      {
        id = "physics-constant-dedup",
        description = "Deduplicate kB_positive/temperature_positive (declared 3x across QuantumCNO/StatMech/LandauerDerivation)",
        status = "declared",
        parked = "The duplicates are in archived Coq sources. Parked.",
      },
      {
        id = "migrate-python-to-rust",
        description = "Migrate Python interpreters to Rust (RSR language-policy blocker recorded in STATE)",
        status = "declared",
      },
      {
        id = "v0-8-compliance-sprint",
        description = "v0.8 milestone: compliance sprint (RSR/estate alignment)",
        status = "in_progress",
        progress = "estate-standardization merged + governance checkpoint 2026-06-12; STATE put route-to-mvp completion at 40 as of 2026-05-27",
      },
      {
        id = "v0-9-container-verification",
        description = "v0.9 milestone: container verification pipeline (active gate: proofs/verify-active-provers.sh; proofs.yml runs Agda, Z3 and Idris 2)",
        status = "declared",
      },
      {
        id = "v1-0-publication-release",
        description = "v1.0 milestone: publication release + paper draft. The paper's six-prover story is out of date (A-I3); the Coq, Lean 4, Isabelle and Mizar results are archived.",
        status = "declared",
      },
    ],

    wishes = [
      {
        id = "wiki-sync-automation",
        horizon = "near",
        description = "Automated docs/wiki to GitHub Wiki sync (just wiki-sync recipe + push workflow), replacing the manual procedure in docs/wiki/README.md",
        status = "declared",
      },
      {
        id = "landauer-measure-theory",
        horizon = "mid",
        description = "LandauerDerivation.v upgraded with real measure theory (current blocker recorded in STATE)",
        status = "declared",
        parked = "Coq is archived under archive/proofs/coq/ (2026-10-10). Parked.",
      },
      {
        id = "mizar-beyond-stub",
        horizon = "far",
        description = "Mizar track beyond stub (needs installation per STATE components)",
        status = "declared",
        parked = "Mizar is archived under archive/proofs/mizar/ (2026-10-10). Parked.",
      },
      {
        id = "y-not-cno-nontermination",
        horizon = "far",
        description = "y_not_cno non-termination proof (low-priority blocker in STATE)",
        status = "declared",
        parked = "The open axiom lives in the archived Coq/Lean sources. Parked.",
      },
    ],
  },
}
