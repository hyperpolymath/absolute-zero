(** * Statistical Mechanics Basis — Shared Probability + Entropy Axioms

    Single source of truth for the Kolmogorov-style probability axioms,
    state-equality decision procedure, point distribution, Shannon
    entropy parameter, and the two core Shannon-entropy inequalities
    used by both [StatMech.v] and [LandauerDerivation.v].
    Consolidates duplicated declarations (Follow-up 3 of
    [docs/proof-debt-triage.md]).

    Author: Jonathan D. A. Jewell
    Project: Absolute Zero
    License: MPL-2.0
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import CNO.CNO.
Import ListNotations.

Open Scope R_scope.

(** ** Probability distributions over [ProgramState] *)

Definition StateDistribution : Type := ProgramState -> R.

(* DISCHARGED/DELETED AXIOM (issue #171): prob_nonneg and prob_normalized
   were formerly declared as axioms over raw [StateDistribution := ProgramState -> R].
   Because an unconstrained function [ProgramState -> R] can be negative (e.g. fun _ => -1)
   or have sum != 1 (e.g. fun _ => 0), those statements were contradictory over
   the raw function type. A full census (issue #171) confirmed that ZERO theorems
   in the repository depend on either declaration. They have been deleted to restore
   unconditional soundness, pending a future bundled-distribution refactor where
   distributions carry proofs of non-negativity and normalization by construction. *)

(** ** Decidable equality on [ProgramState] *)

(* NOT-YET-DISCHARGED (class A) — decidability axiom, not a physical one.
   [ProgramState] (CNO.v) is a record whose [state_memory] field has type
   [Memory := nat -> nat] (a function). Leibniz equality [s1 = s2] on a record
   containing a function field is NOT decidable in Coq's constructive logic
   (it would require deciding pointwise equality of arbitrary [nat -> nat]
   functions and functional extensionality). Hence this cannot be discharged
   as stated. The mathematically clean fix is to decide the observational
   equality [=st=] (which compares memory pointwise via [mem_eq]) instead of
   Leibniz [=]; but [=st=] is a [Prop] over a [nat -> nat] pointwise predicate,
   still not decidable without extra hypotheses. Kept as an axiom asserting
   classical/decidable equality on the state type (used only to define the
   Dirac [point_dist]). BLOCKER: undecidable function-equality on the
   [Memory : nat -> nat] field.
   Consolidated from StatMech.v:51 (`state_dec`) and LandauerDerivation.v:48
   (`state_eq_dec`); canonical name `state_dec` (Follow-up 3). *)
(* AXIOM: [CLASS-A] classical decidable equality for states containing function fields. *)
Axiom state_dec :
  forall s1 s2 : ProgramState, {s1 = s2} + {s1 <> s2}.

(** Point distribution (Dirac delta) over [ProgramState]. *)
Definition point_dist (s0 : ProgramState) : StateDistribution :=
  fun s => if state_dec s s0 then 1 else 0.

(** ** Shannon entropy *)

(** Shannon entropy: [H(P) = -Σ p(s) log₂ p(s)], measured in bits.

    Kept as an opaque [Parameter]: the two axioms below act as its defining
    specification. Giving it a concrete summation definition is the intended
    class-A discharge route, but it is coupled to the distribution-type refactor
    and a finite-carrier / measure treatment (see the
    per-axiom BLOCKER notes), so it is left abstract for now. *)
(* AXIOM: [CLASS-A] opaque Shannon entropy functional over StateDistribution. *)
Parameter shannon_entropy : StateDistribution -> R.

(* NOT-YET-DISCHARGED (class A). Shannon non-negativity H(P) >= 0. This is a
   true mathematical fact for genuine probability distributions, but proving it
   requires (a) a concrete definition [H(P) = -Σ p log₂ p] over a finite carrier,
   and (b) the per-state bound [0 <= p(s) <= 1] — the upper bound comes only from
   normalization, which is not available while [StateDistribution] is an
   unconstrained function type. Without the
   upper bound the term [-p·log₂ p] is not sign-definite. BLOCKER: concrete
   entropy definition + normalized distribution type.
   Consolidated from StatMech.v:67 and LandauerDerivation.v:63 (Follow-up 3). *)
(* AXIOM: [CLASS-A] Shannon entropy non-negativity pending concrete finite carrier definition. *)
Axiom shannon_entropy_nonneg :
  forall P : StateDistribution, shannon_entropy P >= 0.

(* NOT-YET-DISCHARGED (class A). H(δ_x) = 0 for the point (Dirac) distribution.
   This IS provable once [shannon_entropy] is defined concretely as
   [-Σ_{s∈carrier} p(s)·log₂ p(s)] : every summand of [point_dist s0] is either
   [1·log₂ 1 = 0] or [0·log₂ 0 = 0], so the sum is 0 regardless of the carrier.
   It is left abstract only because concretizing [shannon_entropy] simultaneously
   exposes [shannon_entropy_nonneg] (above), which is NOT cleanly provable here;
   an [Axiom] about a concretely-defined function would be unsound if left
   unproved, so both stay abstract together. BLOCKER: coupled to the
   [shannon_entropy] concrete-definition step.
   Consolidated from StatMech.v:72 and LandauerDerivation.v:67 (Follow-up 3). *)
(* AXIOM: [CLASS-A] zero Shannon entropy on Dirac delta point distribution. *)
Axiom shannon_entropy_point_zero :
  forall s : ProgramState, shannon_entropy (point_dist s) = 0.
