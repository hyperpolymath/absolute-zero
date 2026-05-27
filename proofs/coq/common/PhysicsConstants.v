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
Parameter kB : R.

(* AXIOM: kB_positive; Boltzmann constant — physical constant.
   Consolidated from QuantumCNO.v:31, StatMech.v:25,
   LandauerDerivation.v:28 (Follow-up 1 of docs/proof-debt-triage.md).
   §(c) per docs/proof-debt.md. *)
Axiom kB_positive : kB > 0.

(** ** Temperature *)

(** Temperature in Kelvin (must be positive). Room temperature ≈ 300 K. *)
Parameter temperature : R.

(* AXIOM: temperature_positive; Temperature scalar — physical precondition.
   Consolidated from QuantumCNO.v:35, StatMech.v:30,
   LandauerDerivation.v:32 (Follow-up 1 of docs/proof-debt-triage.md).
   §(c) per docs/proof-debt.md. *)
Axiom temperature_positive : temperature > 0.
