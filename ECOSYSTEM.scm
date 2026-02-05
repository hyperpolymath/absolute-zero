;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Project relationship mapping

(ecosystem
  (version "1.0")
  (name "absolute-zero")
  (type "research-project")
  (purpose "Formal verification of Certified Null Operations (CNOs) —
    programs proven to compute nothing. Establishes CNO theory as a
    universal concept across computational models via Coq proofs in
    category theory, lambda calculus, quantum computing, statistical
    mechanics, and filesystem operations.")

  (position-in-ecosystem
    (role "foundational-theory")
    (layer "verification")
    (category "formal-methods")
    (subcategory "program-verification")
    (unique-value
      ("First formal treatment of computational nullity"
       "Multi-prover verification (6 proof systems)"
       "Thermodynamic foundations via Landauer/Bennett"
       "Category-theoretic model independence"
       "81 completed Coq proofs across 10 modules")))

  (related-projects
    ((name . "echidna")
     (relationship . "sibling-standard")
     (description . "Security scanning framework. Could use CNO theory
       for verifying sandboxed code inertness. CI/CD integration target
       for automated proof checking.")
     (integration-points
       . ("echidna could verify CNO properties of scanned code"
          "absolute-zero proofs could run in echidna CI pipeline"
          "Shared Julia layer for batch analysis")))

    ((name . "echidnabot")
     (relationship . "potential-consumer")
     (description . "GitHub bot for echidna. Could automate CNO
       verification as part of PR review workflow."))

    ((name . "valence-shell")
     (relationship . "integration-target")
     (description . "Filesystem operations library. FilesystemCNO.v
       proves properties of valence-shell operations.")
     (integration-points
       . ("FilesystemCNO.v proves read-only ops are CNOs"
          "Valence Shell reversibility connects to thermodynamic proofs")))

    ((name . "rsr-template-repo")
     (relationship . "infrastructure")
     (description . "Repository template. Absolute-zero should conform
       to RSR standards (workflows, checkpoint files, license headers).")))

  (what-this-is
    ("Formal verification research project"
     "Multi-prover theorem proving (Coq, Lean 4, Z3, Agda, Isabelle)"
     "Theoretical computer science contribution"
     "Bridge between computation theory and thermodynamics"
     "Educational resource for proof engineering"))

  (what-this-is-not
    ("A runtime library or framework"
     "A programming language"
     "A security tool (though it has security applications)"
     "Production software (it is a research artifact)")))
