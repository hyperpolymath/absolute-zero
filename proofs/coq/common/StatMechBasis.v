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

(* AXIOM: prob_nonneg; Kolmogorov probability axiom (non-negativity).
   Consolidated from StatMech.v:39 and LandauerDerivation.v:40
   (Follow-up 3 of docs/proof-debt-triage.md).
   §(c) per docs/proof-debt.md. *)
Axiom prob_nonneg :
  forall (P : StateDistribution) (s : ProgramState),
    P s >= 0.

(* Consolidated from StatMech.v:45 and LandauerDerivation.v:43
   (Follow-up 3). Picked the `map P` form from StatMech.v; the
   LandauerDerivation form (fold_right with explicit lambda) is
   equivalent. AXIOM: prob_normalized; Kolmogorov axiom (Σp = 1).
   §(c) per docs/proof-debt.md. *)
Axiom prob_normalized :
  forall (P : StateDistribution),
    exists (states : list ProgramState),
      fold_right Rplus 0 (map P states) = 1.

(** ** Decidable equality on [ProgramState] *)

(* Consolidated from StatMech.v:51 (`state_dec`) and
   LandauerDerivation.v:48 (`state_eq_dec`); canonical name picked:
   `state_dec` (Follow-up 3). AXIOM: state_dec; decidable equality
   over opaque `ProgramState`; PROPERTY-TEST (§(b)) — treated as §(c)
   until a property-test budget is attached. *)
Axiom state_dec :
  forall s1 s2 : ProgramState, {s1 = s2} + {s1 <> s2}.

(** Point distribution (Dirac delta) over [ProgramState]. *)
Definition point_dist (s0 : ProgramState) : StateDistribution :=
  fun s => if state_dec s s0 then 1 else 0.

(** ** Shannon entropy *)

(** Shannon entropy: [H(P) = -Σ p(s) log₂ p(s)], measured in bits. *)
Parameter shannon_entropy : StateDistribution -> R.

(* AXIOM: shannon_entropy_nonneg; Shannon entropy core inequality.
   Consolidated from StatMech.v:67 and LandauerDerivation.v:63
   (Follow-up 3 of docs/proof-debt-triage.md).
   §(c) per docs/proof-debt.md. *)
Axiom shannon_entropy_nonneg :
  forall P : StateDistribution, shannon_entropy P >= 0.

(* AXIOM: shannon_entropy_point_zero; H(δ_x) = 0. Consolidated from
   StatMech.v:72 and LandauerDerivation.v:67 (Follow-up 3 of
   docs/proof-debt-triage.md).
   §(c) per docs/proof-debt.md. *)
Axiom shannon_entropy_point_zero :
  forall s : ProgramState, shannon_entropy (point_dist s) = 0.
