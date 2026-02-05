;; SPDX-License-Identifier: PMPL-1.0-or-later
;; META.scm - Project metadata and architectural decisions

(define project-meta
  `((version . "1.0.0-alpha")

    (architecture-decisions
      . (((id . "ADR-001")
          (title . "ProofIrrelevance for morphism equality")
          (status . "accepted")
          (date . "2026-02-05")
          (context . "Category theory proofs need morphism equality.
            ProgramMorphism wraps a Program with an eval witness.
            Two morphisms with same program must be equal.")
          (decision . "Import Coq.Logic.ProofIrrelevance and use
            morph_eq_ext lemma to reduce morphism equality to
            program equality (list equality).")
          (consequences . "Category laws become list append properties.
            Standard axiom accepted by most Coq developments."))

         ((id . "ADR-002")
          (title . "Landauer axiomatization vs derivation")
          (status . "accepted")
          (date . "2026-02-05")
          (context . "Landauer's Principle is a physical law.
            StatMech.v axiomatizes it directly. LandauerDerivation.v
            attempts to derive it from statistical mechanics.")
          (decision . "Keep both approaches. StatMech.v is the primary
            (complete, all proofs done). LandauerDerivation.v is
            aspirational (needs measure theory, 3 proofs remaining).")
          (consequences . "Dual formalization captures both physics
            (axiom from experiment) and mathematics (derivation)."))

         ((id . "ADR-003")
          (title . "Lambda CNO definition: identity only, no termination")
          (status . "accepted")
          (date . "2026-02-05")
          (context . "Original is_lambda_CNO required normalization
            for ALL arguments, but identity applied to divergent terms
            gives divergent terms (no normal form). Definition was false.")
          (decision . "CNO in lambda calculus = identity property only:
            forall arg, beta_reduce_star (LApp t arg) arg.
            Termination for normalizing args is a separate theorem.")
          (consequences . "Cleaner definition. Composition theorem
            needs closedness hypotheses for de Bruijn substitution."))

         ((id . "ADR-004")
          (title . "post_execution_dist specialized for CNOs")
          (status . "accepted")
          (date . "2026-02-05")
          (context . "General post_execution_dist needs measure theory.
            For CNOs, f_p = id, so P_final = P_initial.")
          (decision . "StatMech.v uses CNO-specialized identity.
            Document explicitly why this is mathematically correct.
            LandauerDerivation.v keeps general definition as future work.")
          (consequences . "Thermodynamic proofs in StatMech.v are
            trivially correct. General case deferred to v1.0."))

         ((id . "ADR-005")
          (title . "Quantum Cexp bug: real vs complex exponential")
          (status . "proposed")
          (date . "2026-02-05")
          (context . "QuantumCNO.v uses Cexp(RtoC theta) which gives
            e^theta (real exponential), not e^{i*theta} (phase factor).
            Global phase requires the complex exponential.")
          (decision . "Fix to Cexp(Ci * RtoC theta) for proper phase.
            Add complex exponential axioms from Coquelicot.")
          (consequences . "quantum_state_eq proofs become completable.
            global_phase_is_cno proof becomes straightforward."))))

    (development-practices
      ((code-style . "Coq proof engineering best practices")
       (security . "openssf-scorecard")
       (versioning . "semver")
       (documentation . "asciidoc")
       (branching . "trunk-based")
       (proof-methodology
         . ("Prefer Qed over Admitted"
            "Axiomatize physical laws and well-known results"
            "Document every Admitted with rationale"
            "Use proof irrelevance for propositional equality"
            "Separate infrastructure lemmas into helper files"))))

    (design-rationale
      . ("CNOs as identity morphisms in arbitrary categories"
         "Multi-prover verification for maximum confidence"
         "Thermodynamic grounding via Landauer and Bennett"
         "Model independence via category theory functors"
         "Progressive formalization: axiom -> theorem -> verified"))))
