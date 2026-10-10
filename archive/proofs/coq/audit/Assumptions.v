(* SPDX-License-Identifier: MPL-2.0 *)
(* Print Assumptions audit over the theorems PROOF-STATUS.adoc names.

   NOT listed in _CoqProject: proofs/coq/check-assumptions.sh compiles this file
   after the theories are built and FAILS unless every line below prints
   "Closed under the global context" (no stdlib axiom, no project axiom).
   Add a line here whenever PROOF-STATUS starts naming a theorem; the checker
   counts the "Print Assumptions" lines, so a theorem cannot be dropped silently.
   Measured 2026-09-23: 17/17 closed (Coq 8.18). *)
Require CNO.CNO.
Require CNO.FilesystemCNO.
Require CNO.LambdaCNO.
Require CNO.OND.
Print Assumptions CNO.CNO.cno_equiv_seq_empty_of_reverses.
Print Assumptions CNO.FilesystemCNO.create_unlink_inverse.
Print Assumptions CNO.LambdaCNO.eta_equivalence.
Print Assumptions CNO.CNO.eval_app.
Print Assumptions CNO.CNO.eval_deterministic.
Print Assumptions CNO.FilesystemCNO.mkdir_idempotent.
Print Assumptions CNO.FilesystemCNO.mkdir_not_identity.
Print Assumptions CNO.FilesystemCNO.mkdir_rmdir_inverse.
Print Assumptions CNO.FilesystemCNO.rename_inverse.
Print Assumptions CNO.CNO.reverses_seq_computes_identity.
Print Assumptions CNO.CNO.reversible_bridge_backward_upto.
Print Assumptions CNO.CNO.reversible_bridge_forward.
Print Assumptions CNO.CNO.reversible_iff_exists_reverses.
Print Assumptions CNO.OND.skip_program_is_core_CNO.
Print Assumptions CNO.FilesystemCNO.snapshot_restore_identity.
Print Assumptions CNO.FilesystemCNO.transaction_cno.
Print Assumptions CNO.OND.writer_program_not_core_CNO.
