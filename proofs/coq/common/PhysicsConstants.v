(** * Physical Constants — Shared Across CNO Theory

    Single source of truth for the [kB] (Boltzmann constant) and
    [temperature] parameters that show up in the quantum and statistical
    mechanics modules. Consolidates triplicated declarations from
    [QuantumCNO.v], [StatMech.v], and [LandauerDerivation.v] (Follow-up 1
    of [docs/proof-debt-triage.md]).

    Author: Jonathan D. A. Jewell
    Project: Absolute Zero
    License: MPL-2.0
*)

Require Import Coq.Reals.Reals.

Open Scope R_scope.

(** ** Boltzmann constant *)

(** Boltzmann constant [k_B] (J/K). In SI units:
    [kB ≈ 1.380649 × 10^{-23} J/K]. *)
(* METAL-BOUNDARY AXIOM (kept): kB is the Boltzmann constant, a measured
   physical constant of nature (SI-fixed value 1.380649e-23 J/K). It is not
   a mathematical object derivable from other definitions — it is an empirical
   input to the theory. Left as an opaque [Parameter] (its numeric value is
   never used, only its positivity). *)
Parameter kB : R.

(* METAL-BOUNDARY AXIOM (kept): kB > 0. The positivity of the Boltzmann
   constant is an empirical physical fact (kB is a strictly positive measured
   quantity). It cannot be derived because kB is an opaque parameter standing
   for a measured constant. This is a legitimate physical postulate.
   Consolidated from QuantumCNO.v:31, StatMech.v:25,
   LandauerDerivation.v:28 (Follow-up 1 of docs/proof-debt-triage.md). *)
Axiom kB_positive : kB > 0.

(** ** Temperature *)

(** Temperature in Kelvin (must be positive). Room temperature ≈ 300 K. *)
(* METAL-BOUNDARY AXIOM (kept): [temperature] is the absolute (Kelvin)
   temperature at which the process runs — an empirical physical parameter of
   the scenario, not a derivable mathematical constant. Opaque [Parameter]. *)
Parameter temperature : R.

(* METAL-BOUNDARY AXIOM (kept): temperature > 0. Absolute temperature is
   strictly positive by the third law / definition of the Kelvin scale; this
   is a physical precondition of every thermodynamic statement here, not a
   theorem. Kept as a physical postulate on the opaque [temperature] parameter.
   Consolidated from QuantumCNO.v:35, StatMech.v:30,
   LandauerDerivation.v:32 (Follow-up 1 of docs/proof-debt-triage.md). *)
Axiom temperature_positive : temperature > 0.
