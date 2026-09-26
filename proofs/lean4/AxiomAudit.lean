import Lean
import CNO
import OND
import CNOCategory
import CNOBridge
import FilesystemCNO
import LambdaCNO

/-!
# Axiom audit for the Mathlib-free Lean core (issue #125)

Every `#guard_msgs` below pins the EXACT output Lean produces, so this file is a
regression test on the axiom surface of the six core modules:

* Section A — the signature of every declared axiom, with the preconditions that
  issue #125 showed to be necessary (`noDirAt`, `noFileAt`, `noEntryAt`,
  `noLambda`). Dropping a precondition changes the printed signature and turns
  this file red.
* Section B — the occupancy predicates, printed in full, so they cannot be
  weakened to `True` silently.
* Section C — the #125 derivations of `False`, verbatim, as NEGATIVE controls:
  each must fail to typecheck with exactly the recorded error.
* Section D — pinned `#print axioms` output for named theorems, followed by an
  environment-wide check of every theorem in the six modules (including private
  declarations). Only the recorded axioms are allowed; `sorryAx` never appears.

Run with `proofs/lean4/check-core.sh` (CI job `lean` in
`.github/workflows/proofs.yml`). Whitespace is compared laxly so a change in the
pretty-printer's line width cannot cause a spurious failure; any change in the
TEXT of a signature or axiom list does.
-/

/-! ## Section A — axiom signatures -/
section
open FilesystemCNO

/--
info: mkdir : Path → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @mkdir

/--
info: rmdir : Path → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @rmdir

/--
info: create : Path → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @create

/--
info: unlink : Path → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @unlink

/--
info: readFile : Path → Filesystem → Option FileContent
-/
#guard_msgs (whitespace := lax) in #check @readFile

/--
info: writeFile : Path → FileContent → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @writeFile

/--
info: stat : Path → Filesystem → Option FileMetadata
-/
#guard_msgs (whitespace := lax) in #check @stat

/--
info: chmod : Path → PermSet → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @chmod

/--
info: chown : Path → Nat → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @chown

/--
info: rename : Path → Path → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @rename

/--
info: mkdir_rmdir_inverse : ∀ (p : Path) (fs : Filesystem), noDirAt p fs → rmdir p (mkdir p fs) = fs
-/
#guard_msgs (whitespace := lax) in #check @mkdir_rmdir_inverse

/--
info: create_unlink_inverse : ∀ (p : Path) (fs : Filesystem), noFileAt p fs → unlink p (create p fs) = fs
-/
#guard_msgs (whitespace := lax) in #check @create_unlink_inverse

/--
info: read_write_identity : ∀ (p : Path) (fs : Filesystem) (content : FileContent),
  readFile p fs = some content → writeFile p content fs = fs
-/
#guard_msgs (whitespace := lax) in #check @read_write_identity

/--
info: chmod_identity : ∀ (p : Path) (fs : Filesystem) (meta : FileMetadata),
  stat p fs = some meta → chmod p meta.permissions fs = fs
-/
#guard_msgs (whitespace := lax) in #check @chmod_identity

/--
info: rename_identity : ∀ (p : Path) (fs : Filesystem), rename p p fs = fs
-/
#guard_msgs (whitespace := lax) in #check @rename_identity

/--
info: rename_inverse : ∀ (p1 p2 : Path) (fs : Filesystem), p1 ≠ p2 → noEntryAt p2 fs → rename p2 p1 (rename p1 p2 fs) = fs
-/
#guard_msgs (whitespace := lax) in #check @rename_inverse

/--
info: mkdir_not_identity : ∃ p fs, mkdir p fs ≠ fs
-/
#guard_msgs (whitespace := lax) in #check @mkdir_not_identity

/--
info: snapshot : Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @snapshot

/--
info: restore : Filesystem → Filesystem → Filesystem
-/
#guard_msgs (whitespace := lax) in #check @restore

/--
info: snapshot_restore_identity : ∀ (fs : Filesystem), restore (snapshot fs) fs = fs
-/
#guard_msgs (whitespace := lax) in #check @snapshot_restore_identity

/--
info: mkdir_idempotent : ∀ (p : Path), isIdempotent fun fs => mkdir p fs
-/
#guard_msgs (whitespace := lax) in #check @mkdir_idempotent
end

section
open LambdaCNO

/--
info: y_combinator_not_identity : ¬BetaReduceStar (y_combinator.LApp lambda_id) lambda_id
-/
#guard_msgs (whitespace := lax) in #check @y_combinator_not_identity

/--
info: noLambda : LambdaTerm → Bool
-/
#guard_msgs (whitespace := lax) in #check @noLambda
end

/-! ## Section B — the occupancy predicates, in full -/
section
open FilesystemCNO

/--
info: def FilesystemCNO.noDirAt : Path → Filesystem → Prop :=
fun p fs =>
  ∀ (e : FileEntry),
    e ∈ fs →
      match e with
      | FileEntry.Directory p' a a_1 => p ≠ p'
      | x => True
-/
#guard_msgs (whitespace := lax) in #print noDirAt

/--
info: def FilesystemCNO.noFileAt : Path → Filesystem → Prop :=
fun p fs =>
  ∀ (e : FileEntry),
    e ∈ fs →
      match e with
      | FileEntry.File p' a a_1 => p ≠ p'
      | x => True
-/
#guard_msgs (whitespace := lax) in #print noFileAt

/--
info: def FilesystemCNO.noEntryAt : Path → Filesystem → Prop :=
fun p fs =>
  ∀ (e : FileEntry),
    e ∈ fs →
      match e with
      | FileEntry.File p' a a_1 => p ≠ p'
      | FileEntry.Directory p' a a_1 => p ≠ p'
      | FileEntry.Symlink p' a a_1 => p ≠ p'
-/
#guard_msgs (whitespace := lax) in #print noEntryAt
end

/-! ## Section C — the #125 derivations must NOT typecheck (negative controls)

Each `example` below is the pre-fix use of a law axiom, i.e. the step of the
#125 `False` proof that the missing precondition made possible. The recorded
error is the precondition being demanded. If any of these ever elaborates,
the axiom has lost its precondition. -/
section
open FilesystemCNO

/--
error: type mismatch
  mkdir_rmdir_inverse p fs
has type
  noDirAt p fs → rmdir p (mkdir p fs) = fs : Prop
but is expected to have type
  rmdir p (mkdir p fs) = fs : Prop
-/
#guard_msgs (whitespace := lax) in
example (p : Path) (fs : Filesystem) : rmdir p (mkdir p fs) = fs :=
  mkdir_rmdir_inverse p fs

/--
error: type mismatch
  create_unlink_inverse p fs
has type
  noFileAt p fs → unlink p (create p fs) = fs : Prop
but is expected to have type
  unlink p (create p fs) = fs : Prop
-/
#guard_msgs (whitespace := lax) in
example (p : Path) (fs : Filesystem) : unlink p (create p fs) = fs :=
  create_unlink_inverse p fs

/--
error: type mismatch
  rename_inverse p1 p2 fs h
has type
  noEntryAt p2 fs → rename p2 p1 (rename p1 p2 fs) = fs : Prop
but is expected to have type
  rename p2 p1 (rename p1 p2 fs) = fs : Prop
-/
#guard_msgs (whitespace := lax) in
example (p1 p2 : Path) (fs : Filesystem) (h : p1 ≠ p2) :
    rename p2 p1 (rename p1 p2 fs) = fs :=
  rename_inverse p1 p2 fs h

/--
error: type mismatch
  mkdir_rmdir_inverse p (mkdir p fs)
has type
  noDirAt p (mkdir p fs) → rmdir p (mkdir p (mkdir p fs)) = mkdir p fs : Prop
but is expected to have type
  rmdir p (mkdir p (mkdir p fs)) = mkdir p fs : Prop
---
error: unsolved goals
case intro.intro
p : Path
fs : Filesystem
hne : mkdir p fs ≠ fs
h1 : rmdir p (mkdir p fs) = mkdir p fs
h2 : mkdir p (mkdir p fs) = mkdir p fs
⊢ noDirAt p fs
-/
#guard_msgs (whitespace := lax) in
example : False := by
  obtain ⟨p, fs, hne⟩ := mkdir_not_identity
  have h1 : rmdir p (mkdir p (mkdir p fs)) = mkdir p fs := mkdir_rmdir_inverse p (mkdir p fs)
  have h2 : mkdir p (mkdir p fs) = mkdir p fs := mkdir_idempotent p fs
  rw [h2, mkdir_rmdir_inverse p fs] at h1
  exact hne h1.symm
end

section
open LambdaCNO LambdaCNO.LambdaTerm

/--
error: type mismatch
  eta_equivalence f
has type
  noLambda f = true → BetaReduceStar (f.LAbs.LApp (LVar 0)).LAbs f.LAbs : Prop
but is expected to have type
  BetaReduceStar (f.LApp (LVar 0)).LAbs f : Prop
-/
#guard_msgs (whitespace := lax) in
example (f : LambdaTerm) : BetaReduceStar (LAbs (LApp f (LVar 0))) f :=
  eta_equivalence f

/--
error: application type mismatch
  eta_general_claim_is_false (eta_equivalence (LVar 5))
argument
  eta_equivalence (LVar 5)
has type
  noLambda (LVar 5) = true → BetaReduceStar ((LVar 5).LAbs.LApp (LVar 0)).LAbs (LVar 5).LAbs : Prop
but is expected to have type
  BetaReduceStar ((LVar 5).LApp (LVar 0)).LAbs (LVar 5) : Prop
-/
#guard_msgs (whitespace := lax) in
example : False :=
  eta_general_claim_is_false (eta_equivalence (LVar 5))
end

/-! ## Section D — the axiom list of every theorem in the six modules -/

section
open CNO

/--
info: 'CNO.terminates_always' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms terminates_always

/--
info: 'CNO.empty_is_cno' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms empty_is_cno

/--
info: 'CNO.nop_preserves_most_state' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms nop_preserves_most_state

/--
info: 'CNO.halt_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms halt_is_cno

/--
info: 'CNO.cno_terminates' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cno_terminates

/--
info: 'CNO.cno_preserves_state' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cno_preserves_state

/--
info: 'CNO.cno_pure' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cno_pure

/--
info: 'CNO.cno_reversible' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cno_reversible

/--
info: 'CNO.eval_seqComp' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms eval_seqComp

/--
info: 'CNO.state_eq_trans' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms state_eq_trans

/--
info: 'CNO.pure_trans' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms pure_trans

/--
info: 'CNO.cno_composition' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cno_composition

/--
info: 'CNO.crazy_op_zero' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in #print axioms crazy_op_zero

/--
info: 'CNO.triple_rotation_identity' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms triple_rotation_identity

/--
info: 'CNO.loadStore_preserves_memory' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms loadStore_preserves_memory

/--
info: 'CNO.nop_minimal_complexity' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms nop_minimal_complexity

/--
info: 'CNO.halt_minimal_complexity' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms halt_minimal_complexity

/--
info: 'CNO.absoluteZero_is_cno' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms absoluteZero_is_cno
end

section
open OND

/--
info: 'OND.OND2_skip_is_OND' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms OND2_skip_is_OND

/--
info: 'OND.leaky_cno_is_null' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms leaky_cno_is_null

/--
info: 'OND.leaky_cno_not_OND_time' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms leaky_cno_not_OND_time

/--
info: 'OND.writer_is_OND_all' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms writer_is_OND_all

/--
info: 'OND.writer_not_null' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms writer_not_null

/--
info: 'OND.OND3_cno_ond_independent' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms OND3_cno_ond_independent

/--
info: 'OND.OND4_ct_select_is_OND_all' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms OND4_ct_select_is_OND_all

/--
info: 'OND.p_op_is_OND_all' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms p_op_is_OND_all

/--
info: 'OND.q_op_is_OND_all' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms q_op_is_OND_all

/--
info: 'OND.OND5_composition_leaks' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms OND5_composition_leaks

/--
info: 'OND.OND5_non_composition' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms OND5_non_composition
end

section
open CNOCategory

/--
info: 'CNOCategory.cno_categorical_equiv' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cno_categorical_equiv

/--
info: 'CNOCategory.functor_preserves_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms functor_preserves_cno

/--
info: 'CNOCategory.cno_model_independent' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cno_model_independent

/--
info: 'CNOCategory.yoneda_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms yoneda_cno
end

section
open CNOBridge

/--
info: 'CNOBridge.reversible_iff_exists_reverses' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms reversible_iff_exists_reverses

/--
info: 'CNOBridge.reverses_seq_computes_identity' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms reverses_seq_computes_identity

/--
info: 'CNOBridge.cnoEquiv_seq_empty_of_reverses' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms cnoEquiv_seq_empty_of_reverses

/--
info: 'CNOBridge.reversible_bridge_forward' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms reversible_bridge_forward

/--
info: 'CNOBridge.reversible_bridge_backward' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms reversible_bridge_backward

/--
info: 'CNOBridge.reverses_iff_cnoEquiv_seq_empty' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms reverses_iff_cnoEquiv_seq_empty
end

section
open FilesystemCNO

/--
info: 'FilesystemCNO.fs_nop_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms fs_nop_is_cno

/--
info: 'FilesystemCNO.mkdir_rmdir_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms mkdir_rmdir_is_cno

/--
info: 'FilesystemCNO.create_unlink_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms create_unlink_is_cno

/--
info: 'FilesystemCNO.read_write_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms read_write_is_cno

/--
info: 'FilesystemCNO.chmod_nop_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms chmod_nop_is_cno

/--
info: 'FilesystemCNO.rename_nop_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms rename_nop_is_cno

/--
info: 'FilesystemCNO.fs_cno_composition' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms fs_cno_composition

/--
info: 'FilesystemCNO.mkdir_alone_not_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms mkdir_alone_not_cno

/--
info: 'FilesystemCNO.valence_reversible_pair_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms valence_reversible_pair_is_cno

/--
info: 'FilesystemCNO.snapshot_restore_is_cno' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms snapshot_restore_is_cno

/--
info: 'FilesystemCNO.unconditional_mkdir_rmdir_inverse_is_false' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms unconditional_mkdir_rmdir_inverse_is_false
end

section
open LambdaCNO

/--
info: 'LambdaCNO.lambda_id_is_cno_weak' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lambda_id_is_cno_weak

/--
info: 'LambdaCNO.lambda_id_normal_form' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms lambda_id_normal_form

/--
info: 'LambdaCNO.lambda_id_is_cno' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lambda_id_is_cno

/--
info: 'LambdaCNO.BetaReduceStar_app_right' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms BetaReduceStar_app_right

/--
info: 'LambdaCNO.BetaReduceStar_app_left' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms BetaReduceStar_app_left

/--
info: 'LambdaCNO.BetaReduceStar_trans' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms BetaReduceStar_trans

/--
info: 'LambdaCNO.subst_closed_term' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms subst_closed_term

/--
info: 'LambdaCNO.lambda_cno_composition' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lambda_cno_composition

/--
info: 'LambdaCNO.y_not_cno' depends on axioms: [LambdaCNO.y_combinator_not_identity]
-/
#guard_msgs (whitespace := lax) in #print axioms y_not_cno

/--
info: 'LambdaCNO.eta_general_claim_is_false' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms eta_general_claim_is_false

/--
info: 'LambdaCNO.unrestricted_eta_equivalence_is_false' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms unrestricted_eta_equivalence_is_false

/--
info: 'LambdaCNO.subst_noLambda_self' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms subst_noLambda_self

/--
info: 'LambdaCNO.eta_equivalence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms eta_equivalence

/--
info: 'LambdaCNO.eta_expanded_id_is_cno' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms eta_expanded_id_is_cno
end

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`CNO, `OND, `CNOCategory, `CNOBridge, `FilesystemCNO, `LambdaCNO]
  let allowed : Array Name := #[
    `propext, `Quot.sound,
    `LambdaCNO.y_combinator_not_identity
  ]
  let mut checked := 0
  for moduleName in modules do
    let some moduleIdx := env.getModuleIdx? moduleName
      | throwError "axiom audit: missing module {moduleName}"
    let theorems := env.constants.toList.filterMap fun (name, info) =>
      if info.isTheorem && env.getModuleIdxFor? name == some moduleIdx then
        some name
      else
        none
    if theorems.isEmpty then
      throwError "axiom audit: no theorems found in {moduleName}"
    for name in theorems.toArray.qsort Name.lt do
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "axiom audit: {name} depends on unexpected axiom {axiomName}"
      logInfo m!"axiom audit: {name} depends on {axioms.qsort Name.lt |>.toList}"
      checked := checked + 1
  logInfo m!"axiom audit: checked {checked} theorems in {modules.size} modules"
