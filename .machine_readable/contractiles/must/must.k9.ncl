K9!
# SPDX-License-Identifier: MPL-2.0
# must.k9.ncl — K9 contractile component: MUST (invariant assertion, release-blocking)
# Repo: absolute-zero
#
# Migrated from archive/a2ml-v1/contractiles-Mustfile.a2ml.txt (2026-10-10,
# a2ml retirement: D99, D269c, D312, D313; envelope per MIGRATION-1058 M1 and
# the K9 contract spec v1.0.0).
#
# Leash / authority: 'Hunt / blocking (hard gate). The leash is the estate
# template canon for the must verb (rsr-template-repo must.k9.ncl). The source
# Mustfile declares no leash itself.
#
# Signature: NONE. K9-S009 requires a signature block at 'Hunt. No signing
# ceremony has run, and this sandbox has no signing key. A block would be a
# claim, not a fact, so none is written. This contract is therefore NOT
# authorised to run as 'Hunt until the owner signs it. Ledger row K-1.
#
# Adaptations to source checks (ledger rows A-M1..A-M7):
#   proofs-tree-present       -> active proof tree + archive/proofs
#   six-a2ml-present          -> deed-and-coordination-present
#   contractiles-flat-complete -> contractiles-k9-complete
#   a2ml-parses-as-toml       -> retired; replaced by no-live-a2ml
#   anchor-directory          -> anchor-clause-present (ANCHOR is a deed clause)
#   bot-directives-present    -> clause check against the deed
#   ai-manifest               -> manifest clause in the deed (root 0-AI-MANIFEST retired)

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:must",
    semantics = "invariant",

    security = {
      leash = 'Hunt,
      trust_level = "blocking (hard gate)",
      signature_required = true,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = true,
      capabilities = [ "process.spawn" ],
    },

    metadata = {
      name = "absolute-zero-must",
      version = "1.0.0",
      description = "Physical-state invariants for absolute-zero: required governance files, the K9 contractile set, the deed, and the absence of retired a2ml metadata.",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    side_effects = [
      "runs read-only shell probes (test, grep, find) from the repository root, one subprocess per invariant",
      "writes nothing; no network access",
    ],
  },

  declaration = {
    abstract = "Physical-state invariants for absolute-zero: required governance files, the K9 contractile set, the deed, and the absence of retired a2ml metadata.",
    last_updated = "2026-10-10",

    invariants = [
      {
        id = "license-present",
        description = "LICENSE file must exist (MPL-2.0)",
        probe = "test -f LICENSE && grep -q 'Mozilla Public License' LICENSE",
        severity = "critical",
      },
      {
        id = "readme-canonical",
        description = "README.adoc (canonical) must exist; README.md is a pointer only",
        probe = "test -f README.adoc",
        severity = "critical",
      },
      {
        id = "security-policy",
        description = "SECURITY.md must exist",
        probe = "test -f SECURITY.md",
        severity = "critical",
      },
      {
        id = "ai-manifest",
        description = "AI manifest clause must be present in the repo deed (retired root 0-AI-MANIFEST.a2ml, adaptation A-M6)",
        probe = "test -f absolute-zero_chora.deed && grep -q '(manifest' absolute-zero_chora.deed",
        severity = "critical",
      },
      {
        id = "governance-docs",
        description = "GOVERNANCE.adoc, MAINTAINERS.adoc, .github/CODEOWNERS must exist (estate wave 2026-06)",
        probe = "test -f GOVERNANCE.adoc && test -f MAINTAINERS.adoc && test -f .github/CODEOWNERS",
        severity = "critical",
      },
      {
        id = "contractiles-k9-complete",
        description = "All six contractile K9 components exist at .machine_readable/contractiles/<verb>/<verb>.k9.ncl (adaptation A-M3: replaces the flat .a2ml check)",
        probe = "test -f .machine_readable/contractiles/must/must.k9.ncl && test -f .machine_readable/contractiles/trust/trust.k9.ncl && test -f .machine_readable/contractiles/dust/dust.k9.ncl && test -f .machine_readable/contractiles/bust/bust.k9.ncl && test -f .machine_readable/contractiles/adjust/adjust.k9.ncl && test -f .machine_readable/contractiles/intend/intend.k9.ncl",
        severity = "critical",
      },
      {
        id = "deed-and-coordination-present",
        description = "The repo deed and coordination.k9 exist (adaptation A-M2: replaces the six-a2ml check)",
        probe = "test -f absolute-zero_chora.deed && grep -q '(repo-deed' absolute-zero_chora.deed && test -f coordination.k9",
        severity = "critical",
      },
      {
        id = "anchor-clause-present",
        description = "The ANCHOR realignment record is present as a deed clause (adaptation A-M4)",
        probe = "grep -q '(anchor' absolute-zero_chora.deed",
        severity = "warning",
      },
      {
        id = "bot-directives-present",
        description = "bot_directives/ README exists and the deed carries the bot-directives clause (adaptation A-M5)",
        probe = "test -f .machine_readable/bot_directives/README.adoc && grep -q '(bot-directives' absolute-zero_chora.deed",
        severity = "warning",
      },
      {
        id = "self-validating-present",
        description = "self-validating/ (renamed from svc/k9) exists with the k9 template set",
        probe = "test -d .machine_readable/self-validating && test -f .machine_readable/self-validating/template-kennel.k9.ncl",
        severity = "warning",
      },
      {
        id = "no-duplicate-root-scm",
        description = "No duplicate root .machine_readable/*.scm set (removed by estate wave 2026-06; the deed is canonical)",
        probe = "test -z \"$(ls .machine_readable/*.scm 2>/dev/null)\"",
        severity = "critical",
      },
      {
        id = "no-live-a2ml",
        description = "No live .a2ml files outside archive/ (added by the 2026-10-10 migration; replaces the a2ml-parses-as-toml check, adaptation A-M7)",
        probe = "test -z \"$(find . -name '*.a2ml' -not -path './archive/*' -not -path './.git/*' 2>/dev/null | head -1)\"",
        severity = "critical",
      },
      {
        id = "proofs-tree-present",
        description = "The active proof tree exists (agda, z3, observation-models, residue) and the archived provers are under archive/proofs (adaptation A-M1)",
        probe = "test -d proofs/agda && test -d proofs/z3 && test -d proofs/observation-models && test -d proofs/residue && test -d archive/proofs/coq && test -d archive/proofs/lean4 && test -d archive/proofs/isabelle && test -d archive/proofs/mizar",
        severity = "critical",
      },
      {
        id = "root-mustfile-buildgate",
        description = "Repo-root Mustfile (build-gate: just lint/test/fmt) and Justfile exist",
        probe = "test -f Mustfile && test -f Justfile",
        severity = "warning",
      },
      {
        id = "no-dockerfile",
        description = "No Dockerfile (use Containerfile)",
        probe = "test ! -f Dockerfile",
        severity = "warning",
      },
    ],
  },
}
