/- Reversibility ↔ CNO Bridge — Lean 4 mirror of the Coq A2 development

   Mirrors the theorems added to proofs/coq/common/CNO.v (the "reversibility
   ↔ CNO bridge" the MAA framework / aletheia cites). See PROOF-STATUS.adoc.

   ┌─ VERIFICATION STATUS ──────────────────────────────────────────────────┐
   │ NOT machine-checked in the environment where this file was written:     │
   │ the Lean toolchain and Mathlib cache download from GitHub release        │
   │ assets, which the egress policy blocked (HTTP 403). This file is a       │
   │ best-effort transcription against the CNO.lean API and is registered in  │
   │ lakefile.lean as a NON-default `lean_lib`, so the standard `lake build`  │
   │ is unaffected by it. To verify:                                          │
   │     cd proofs/lean4 && lake exe cache get && lake build CNOBridge        │
   │ and `#print axioms` on each theorem. Treat as unverified until then.     │
   └─────────────────────────────────────────────────────────────────────────┘

   Modelling note (honest cross-prover difference): Lean's `eval` is a TOTAL
   FUNCTION and `ProgramState.eq` INCLUDES the program counter, whereas Coq's
   `eval` is a relation and `=st=` EXCLUDES the PC. So this Lean mirror states
   the bridge with SYNTACTIC equality of evaluated states — a stronger, cleaner
   form that needs no determinism lemma (free for a function) and no
   "up-to-=st=" slack on the backward direction. It is therefore not a literal
   transcription of the Coq statement but its functional-model analogue,
   consistent with the repo's "each prover checks its own formalisation" stance.

   Author: Jonathan D. A. Jewell
   Project: Absolute Zero
   License: MPL-2.0
-/

import CNO

namespace CNOBridge

open CNO

/-- `reverses p p_inv`: `p_inv` undoes `p` on every state. In Lean's functional
    model this is `∀ s, eval p_inv (eval p s) = s` — the body of `CNO.reversible`. -/
def reverses (p p_inv : Program) : Prop :=
  ∀ s, eval p_inv (eval p s) = s

/-- The repo's `reversible` is exactly "there exists a (one-sided) left inverse". -/
theorem reversible_iff_exists_reverses (p : Program) :
    reversible p ↔ ∃ p_inv, reverses p p_inv := Iff.rfl

/-- CNO-equivalence to the no-op, functional form: the two programs evaluate to
    the same state from every start state. -/
def cnoEquiv (p1 p2 : Program) : Prop :=
  ∀ s, eval p1 s = eval p2 s

/-- Core lemma: a left inverse sequenced after `p` computes the identity on
    every state. Uses only `eval_seqComp` (Coq needed `eval_app` +
    `eval_deterministic`; determinism is free here because `eval` is a function). -/
theorem reverses_seq_computes_identity {p p_inv : Program}
    (h : reverses p p_inv) : ∀ s, eval (seqComp p p_inv) s = s := by
  intro s
  rw [eval_seqComp]
  exact h s

/-- Repackaged as CNO-equivalence to the empty program (the canonical no-op). -/
theorem cnoEquiv_seq_empty_of_reverses {p p_inv : Program}
    (h : reverses p p_inv) : cnoEquiv (seqComp p p_inv) [] := by
  intro s
  show eval (seqComp p p_inv) s = eval [] s
  have hnil : eval [] s = s := rfl
  rw [hnil]
  exact reverses_seq_computes_identity h s

/-- Forward bridge (the faithful direction of the aletheia contract): a
    two-sided inverse makes BOTH composites CNO-equivalent to the no-op. -/
theorem reversible_bridge_forward {p : Program}
    (h : ∃ p_inv, reverses p p_inv ∧ reverses p_inv p) :
    ∃ p_inv, cnoEquiv (seqComp p p_inv) [] ∧ cnoEquiv (seqComp p_inv p) [] := by
  obtain ⟨p_inv, hpp, hpi⟩ := h
  exact ⟨p_inv, cnoEquiv_seq_empty_of_reverses hpp,
               cnoEquiv_seq_empty_of_reverses hpi⟩

/-- Backward bridge: from "the composite is a no-op" recover the inverse. In
    Lean's functional/PC-inclusive model this is exact (SYNTACTIC), with no
    up-to-`=st=` slack and no termination hypothesis — the two facts Coq needed
    (its `reversible_bridge_backward_upto`) because its `eval` is relational and
    `=st=` drops the PC. -/
theorem reversible_bridge_backward {p p_inv : Program}
    (h : cnoEquiv (seqComp p p_inv) []) : reverses p p_inv := by
  intro s
  have hs := h s
  rw [eval_seqComp] at hs
  -- hs : eval p_inv (eval p s) = eval [] s, and eval [] s = s definitionally
  exact hs

/-- Corollary: in the functional model the forward and backward directions
    combine into a genuine biconditional for a single inverse `p_inv`. -/
theorem reverses_iff_cnoEquiv_seq_empty (p p_inv : Program) :
    reverses p p_inv ↔ cnoEquiv (seqComp p p_inv) [] :=
  ⟨cnoEquiv_seq_empty_of_reverses, reversible_bridge_backward⟩

end CNOBridge
