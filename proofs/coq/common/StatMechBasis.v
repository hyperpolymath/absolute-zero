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

(* NOT-YET-DISCHARGED (class A) + SOUNDNESS WARNING.
   This is intended as the Kolmogorov non-negativity axiom, but as *stated*
   it quantifies over ALL [StateDistribution]s, and [StateDistribution] is a
   raw function [ProgramState -> R] with no non-negativity constraint. The
   statement is therefore FALSE (counterexample: [P := fun _ => -1]); since
   [ProgramState] is inhabited it is in fact inconsistent. The honest class-A
   discharge is to make "distribution" a concrete constrained type (a sigma
   bundling the function with proofs of non-negativity and normalization), after
   which this becomes a trivial projection lemma. That refactor changes the type
   of [StateDistribution] and every [P s] application site, so it is deferred.
   BLOCKER: requires replacing [StateDistribution := ProgramState -> R] with a
   bundled distribution type across StatMech.v / LandauerDerivation.v.
   NOTE: this axiom is currently UNUSED in any proof (dead), so removing or
   fixing it cannot break existing results — recommend the type refactor.
   Consolidated from StatMech.v:39 and LandauerDerivation.v:40 (Follow-up 3). *)
Axiom prob_nonneg :
  forall (P : StateDistribution) (s : ProgramState),
    P s >= 0.

(* NOT-YET-DISCHARGED (class A) + SOUNDNESS WARNING.
   Intended as the Kolmogorov normalization axiom (Σp = 1), but as stated it
   asserts that EVERY [StateDistribution] (i.e. every function [ProgramState -> R])
   admits a finite list summing to 1. This is FALSE (counterexample: the zero
   function [P := fun _ => 0] sums to 0 over any list, never 1). Same root cause
   and same class-A fix as [prob_nonneg]: normalization must be a defining
   property of a constrained distribution type, not an axiom over raw functions.
   BLOCKER: requires the bundled distribution type refactor (see [prob_nonneg]).
   NOTE: currently UNUSED in any proof (dead).
   Consolidated from StatMech.v:45 and LandauerDerivation.v:43 (Follow-up 3);
   the [map P] form was picked over the equivalent fold_right/lambda form. *)
Axiom prob_normalized :
  forall (P : StateDistribution),
    exists (states : list ProgramState),
      fold_right Rplus 0 (map P states) = 1.

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
    (see [prob_nonneg]) and a finite-carrier / measure treatment (see the
    per-axiom BLOCKER notes), so it is left abstract for now. *)
Parameter shannon_entropy : StateDistribution -> R.

(* NOT-YET-DISCHARGED (class A). Shannon non-negativity H(P) >= 0. This is a
   true mathematical fact for genuine probability distributions, but proving it
   requires (a) a concrete definition [H(P) = -Σ p log₂ p] over a finite carrier,
   and (b) the per-state bound [0 <= p(s) <= 1] — the upper bound comes only from
   normalization, which is not available while [StateDistribution] is an
   unconstrained function type (see [prob_nonneg]/[prob_normalized]). Without the
   upper bound the term [-p·log₂ p] is not sign-definite. BLOCKER: concrete
   entropy definition + normalized distribution type.
   Consolidated from StatMech.v:67 and LandauerDerivation.v:63 (Follow-up 3). *)
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
Axiom shannon_entropy_point_zero :
  forall s : ProgramState, shannon_entropy (point_dist s) = 0.
