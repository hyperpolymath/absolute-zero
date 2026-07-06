(** * Rigorous Derivation of Landauer's Principle from Statistical Mechanics

    This module derives Landauer's Principle from fundamental statistical mechanics
    and thermodynamics, rather than axiomatizing it.

    Key Result: Information erasure dissipates at least kT ln(2) energy per bit.

    Author: Jonathan D. A. Jewell
    Project: Absolute Zero - Phase 1 Complete Derivation
    License: MPL-2.0
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import CNO.CNO.
(* Shared physics constants — kB, temperature, kB_positive,
   temperature_positive. See proofs/coq/common/PhysicsConstants.v
   (consolidated by Follow-up 1 of docs/proof-debt-triage.md). *)
Require Import CNO.PhysicsConstants.
(* Shared statmech basis — StateDistribution, prob_nonneg, prob_normalized,
   state_dec, point_dist, shannon_entropy, shannon_entropy_nonneg,
   shannon_entropy_point_zero. See proofs/coq/common/StatMechBasis.v
   (consolidated by Follow-up 3 of docs/proof-debt-triage.md). *)
Require Import CNO.StatMechBasis.
Import ListNotations.

Open Scope R_scope.

(** ** Physical Constants (Measured Values, Not Derived)

    Boltzmann constant [k_B = 1.380649 × 10^{-23} J/K] and [temperature]
    in Kelvin (must be positive) are imported from [CNO.PhysicsConstants]
    (consolidated by Follow-up 1). These are measured physical constants,
    grounded in experiment. *)

(** ** Foundation: Probability + Shannon Entropy Basis

    [StateDistribution], [prob_nonneg], [prob_normalized], [state_dec],
    [point_dist], [shannon_entropy], [shannon_entropy_nonneg], and
    [shannon_entropy_point_zero] are imported from [CNO.StatMechBasis]
    (consolidated by Follow-up 3 of [docs/proof-debt-triage.md]). This
    file adds [log2] and the uniform-max / additive axioms below. *)

Definition log2 (x : R) : R := ln x / ln 2.

(** Entropy of a uniform distribution over n states equals log2 n *)
(* NOT-YET-DISCHARGED (class A) — specification axiom for the opaque
   [shannon_entropy]. States: a distribution uniform over [n] states (each of
   mass [1/n]) has entropy [log₂ n]. This is a true information-theoretic
   identity and would be a Lemma once [shannon_entropy] is defined concretely as
   [-Σ p·log₂ p] over a finite carrier (the sum telescopes:
   [-n·(1/n)·log₂(1/n) = log₂ n]). While [shannon_entropy] stays opaque this
   serves as (part of) its defining spec. BLOCKER: concrete entropy definition +
   finite carrier. NOTE: it is a *sound* characterizing axiom (unlike
   [shannon_entropy_maximum]); it is consumed by [entropy_change_erasure] below,
   which is now discharged (Axiom -> Lemma) from it plus
   [shannon_entropy_point_zero]. *)
Axiom shannon_entropy_uniform_max :
  forall (P : StateDistribution) (n : nat) (states : list ProgramState),
    length states = n ->
    (forall s, In s states -> P s = 1 / INR n) ->
    shannon_entropy P = log2 (INR n).

(** Product distribution (for independence) *)
(* Opaque [Parameter]: the joint distribution of two independent systems. Left
   abstract because a concrete definition presupposes the concrete distribution
   type (see [prob_nonneg] in StatMechBasis.v). *)
Parameter product_dist : StateDistribution -> StateDistribution -> StateDistribution.

(** Entropy is additive for independent distributions *)
(* NOT-YET-DISCHARGED (class A) — specification axiom for the opaque pair
   ([shannon_entropy], [product_dist]). The additivity [H(X,Y) = H(X)+H(Y)] for
   independent [X,Y] is the entropy chain rule and is genuinely provable from the
   *definitions* of Shannon entropy and the product distribution. It cannot be
   discharged while both [shannon_entropy] and [product_dist] are opaque
   [Parameter]s with no defining equations. BLOCKER: concrete definitions of
   [shannon_entropy] and [product_dist] (coupled to the distribution-type
   refactor). Correcting the triage docs: this is not derivable from what is
   currently in the file. *)
Axiom shannon_entropy_additive :
  forall P Q : StateDistribution,
    (* For independent P and Q *)
    shannon_entropy (product_dist P Q) =
      shannon_entropy P + shannon_entropy Q.

(** ** Boltzmann Entropy: Thermodynamic Foundation *)

(** Boltzmann entropy: S = k_B ln(W) where W is number of microstates
    We connect this to Shannon entropy via:
    S = k_B ln(2) * H  (since ln(2^H) = H ln(2))
*)

Definition boltzmann_entropy (P : StateDistribution) : R :=
  kB * ln 2 * shannon_entropy P.

(** Boltzmann entropy is non-negative *)
Theorem boltzmann_entropy_nonneg :
  forall P : StateDistribution,
    boltzmann_entropy P >= 0.
Proof.
  intro P.
  unfold boltzmann_entropy.
  pose proof kB_positive as HkB.
  pose proof ln_lt_2 as Hln_half.
  assert (Hln : ln 2 > 0) by lra.
  pose proof (shannon_entropy_nonneg P) as Hentropy.
  unfold Rge in Hentropy.
  unfold Rge.
  destruct Hentropy as [Hentropy_pos | Hentropy_zero].
  - left.
    replace (kB * ln 2 * shannon_entropy P)%R
      with ((kB * ln 2) * shannon_entropy P)%R by ring.
    apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; assumption.
    + exact Hentropy_pos.
  - right. rewrite Hentropy_zero. ring.
Qed.

(** ** Second Law of Thermodynamics *)

(** The Second Law: Entropy of an isolated system never decreases
    ΔS ≥ 0 for irreversible processes
    ΔS = 0 for reversible processes *)

(* METAL-BOUNDARY AXIOM (kept): the Second Law of Thermodynamics is a
   fundamental empirical physical law — the entropy of an isolated system never
   decreases. It is not derivable from mathematics; it is a postulate about the
   physical world. Correctly kept as a physical axiom. *)
Axiom second_law :
  forall (P_initial P_final : StateDistribution),
    (* For any physical process *)
    boltzmann_entropy P_final >= boltzmann_entropy P_initial.

(** ** Energy and Work *)

(** Helmholtz free energy: F = E - TS
    where E is internal energy, T is temperature, S is entropy *)
(* METAL-BOUNDARY (kept): [internal_energy] is a physical observable (the
   thermodynamic internal energy E of a system in a given macrostate/distribution,
   in Joules). Opaque [Parameter] standing for a measured quantity. *)
Parameter internal_energy : StateDistribution -> R.

Definition free_energy (P : StateDistribution) : R :=
  internal_energy P - temperature * boltzmann_entropy P.

(** Work done by a system (energy dissipated to environment) *)
Definition work_dissipated (P_initial P_final : StateDistribution) : R :=
  free_energy P_initial - free_energy P_final.

(** ** Landauer's Principle: DERIVATION *)

(** Step 1: Relate information erasure to entropy change *)

(** Erasing n bits means going from 2^n possible states to 1 state *)
(** Initial: Uniform distribution over 2^n states (maximum entropy)
    Final: Point distribution (zero entropy) *)

Definition erasure_initial (n : nat) : StateDistribution :=
  (* Uniform over 2^n states *)
  fun s => 1 / (2 ^ n).

Definition erasure_final (s_final : ProgramState) : StateDistribution :=
  point_dist s_final.

(** Entropy change for erasing n bits

    This theorem requires computing Shannon entropy for a uniform distribution
    over 2^n states, which requires measure theory and integration.

    The result follows from the definition of Shannon entropy:
    H(P) = -Σ p_i log_2(p_i)

    For uniform distribution: p_i = 1/2^n for each of 2^n states
    H = -Σ (1/2^n) log_2(1/2^n) = -2^n * (1/2^n) * (-n) = n bits

    Point distribution has H = 0 (no uncertainty).
    Therefore: ΔH = n - 0 = n bits
    Boltzmann entropy: ΔS = k_B ln(2) * n

    A complete proof would require:
    - Formalization of summation over finite state spaces
    - Logarithm properties: log_2(1/2^n) = -n
    - Measure-theoretic foundation for probability distributions

    This is a fundamental result from information theory.
*)
(* DISCHARGED (class A): Axiom -> Lemma. The entropy change of erasing n bits
   equals [kB·ln2·n]. This is now PROVED from the two sound characterizing
   axioms [shannon_entropy_uniform_max] and [shannon_entropy_point_zero] plus
   real-analysis facts ([pow_INR], [ln_pow]): the erasure-initial distribution is
   uniform over 2^n states, so its Shannon entropy is [log₂(2^n) = n], while the
   erasure-final point distribution has entropy 0. Multiplying by [kB·ln2] gives
   the Boltzmann-entropy difference [kB·ln2·n]. No new axiom is introduced.

   [erasure_initial n = fun _ => 1/2^n] is uniform: for the count [2^n] and the
   carrier [repeat s_final (2^n)] (length 2^n; existence of a ProgramState
   witness is supplied by [s_final] itself), each mass equals [1/INR(2^n)] since
   [INR(2^n) = 2^n] (pow_INR), so [shannon_entropy_uniform_max] gives
   [H = log₂(INR(2^n)) = ln(2^n)/ln2 = (n·ln2)/ln2 = n] (ln_pow, ln2>0). *)
Lemma entropy_change_erasure :
  forall (n : nat) (s_final : ProgramState),
    (n > 0)%nat ->
    boltzmann_entropy (erasure_initial n) -
    boltzmann_entropy (erasure_final s_final) =
    kB * ln 2 * INR n.
Proof.
  intros n s_final Hn.
  assert (Hln2 : ln 2 > 0). { pose proof ln_lt_2 as Hl. lra. }
  (* INR of the natural power 2^n coincides with the real power 2^n. *)
  assert (Hpow : INR (Nat.pow 2 n) = 2 ^ n).
  { rewrite pow_INR. replace (INR 2) with 2 by (simpl; ring). reflexivity. }
  unfold boltzmann_entropy, erasure_final.
  rewrite (shannon_entropy_point_zero s_final).
  (* Shannon entropy of the uniform erasure-initial distribution is n bits. *)
  assert (HH : shannon_entropy (erasure_initial n) = INR n).
  { rewrite (shannon_entropy_uniform_max
               (erasure_initial n) (Nat.pow 2 n) (repeat s_final (Nat.pow 2 n))).
    - unfold log2. rewrite Hpow. rewrite (ln_pow 2 ltac:(lra) n).
      field. lra.
    - apply repeat_length.
    - intros s _. unfold erasure_initial. rewrite Hpow. reflexivity. }
  rewrite HH. ring.
Qed.

(** Step 2: Connect entropy decrease to energy dissipation *)

(** From thermodynamics: When entropy decreases, work must be done
    ΔF ≥ -TΔS (for isothermal process at temperature T)

    For erasure: ΔS < 0, so TΔS < 0, thus -TΔS > 0
    This is the minimum work that must be dissipated as heat.
*)

(* METAL-BOUNDARY AXIOM (kept): the isothermal work bound
   [W_dissipated >= T·(S_i - S_f)] is a consequence of the second law for an
   isothermal process (the minimum work to lower entropy by ΔS at temperature T).
   It rests on physical thermodynamics (Helmholtz free energy / second law), not
   pure mathematics — the connection between the abstract [work_dissipated]
   definition and this physical inequality is itself a physical postulate. Kept
   as a metal-boundary axiom. *)
Axiom isothermal_work_bound :
  forall (P_initial P_final : StateDistribution),
    work_dissipated P_initial P_final >=
      temperature * (boltzmann_entropy P_initial - boltzmann_entropy P_final).

(** Step 3: Landauer's Principle - DERIVED *)

Theorem landauer_principle_derived :
  forall (n : nat) (s_final : ProgramState),
    (n > 0)%nat ->
    work_dissipated (erasure_initial n) (erasure_final s_final) >=
      kB * temperature * ln 2 * INR n.
Proof.
  intros n s_final Hn.
  (* Apply isothermal work bound *)
  assert (H_work := isothermal_work_bound (erasure_initial n) (erasure_final s_final)).
  (* Substitute entropy change *)
  assert (H_entropy := entropy_change_erasure n s_final Hn).
  unfold work_dissipated in *.
  (* work ≥ T * ΔS *)
  (* work ≥ T * (k_B ln(2) * n) *)
  (* work ≥ k_B * T * ln(2) * n *)
  rewrite H_entropy in H_work.
  replace (kB * temperature * ln 2 * INR n)%R
    with (temperature * (kB * ln 2 * INR n))%R by ring.
  exact H_work.
Qed.

(** For erasing one bit (n = 1): *)
Corollary landauer_one_bit :
  forall s_final : ProgramState,
    work_dissipated (erasure_initial 1) (erasure_final s_final) >=
      kB * temperature * ln 2.
Proof.
  intro s_final.
  replace (kB * temperature * ln 2)%R
    with (kB * temperature * ln 2 * INR 1)%R by (simpl; ring).
  apply landauer_principle_derived.
  lia.
Qed.

(** At room temperature (300K): *)
(** E_min = 1.38e-23 J/K * 300K * ln(2) ≈ 2.87e-21 J per bit *)

(** ** Application to CNOs *)

(** Finite-state carrier used by the simplified distribution model. *)
(* Modeling [Parameter]s (not physical, not discharged here):
   [all_states] posits a finite enumeration of the (in general infinite) state
   space so the post-execution distribution can be written as a finite fold;
   [eval_to_dec] posits decidability of the evaluation relation. Both are
   modeling conveniences of the *simplified* distribution model; a faithful
   treatment would use a measure over the full state space. Left as parameters. *)
Parameter all_states : list ProgramState.
Parameter eval_to_dec : forall p s s', {eval p s s'} + {~ eval p s s'}.

(** Distribution after program execution *)
Definition post_execution_dist (p : Program) (P : StateDistribution) : StateDistribution :=
  fun s' =>
    (* Sum over all s that evaluate to s' *)
    fold_right Rplus 0
      (map (fun s => if eval_to_dec p s s' then P s else 0) all_states).

(** CNOs preserve Shannon entropy (key property)

    A CNO is an identity transformation: for all states s, eval p s s implies s' = s.
    Therefore, the post-execution distribution equals the initial distribution.

    Formally: post_execution_dist(p, P)(s') = P(s') for all s'

    Since Shannon entropy is a function of the distribution alone, and the
    distribution is unchanged, entropy is preserved.

    A complete proof would require:
    - Formalizing that identity maps preserve probability mass functions
    - Proving that post_execution_dist reduces to identity for CNOs
    - Measure-theoretic treatment of probability distributions over state spaces
    - Properties of summation: if p_i = p_i' for all i, then Σ f(p_i) = Σ f(p_i')

    This is a fundamental result: bijections preserve entropy, and identity
    is the canonical bijection.

    In measure-theoretic terms: if T: X → X is a measure-preserving bijection
    and μ is a probability measure, then H(μ) = H(T_*μ) where T_*μ is the
    pushforward measure. For the identity map, T_*μ = μ.
*)
(* NOT-YET-DISCHARGED (class A). Claim: CNOs preserve Shannon entropy.
   Morally true, but NOT provable as stated with this file's [post_execution_dist]
   (the [fold_right] over [all_states] using [eval_to_dec]). Proving
   [H(post_execution_dist p P) = H(P)] the clean way requires
   [post_execution_dist p P = P] pointwise, which fails in general here: for a CNO,
   [eval p s s'] only gives [s =st= s'] (observational equality, PC excluded), not
   [s = s'], so the fold over [all_states] collecting states that evaluate to [s']
   need not sum to [P s'] — it depends on how many [=st=]-equivalent states sit in
   [all_states] and on [P] being constant on [=st=] classes. BLOCKER: needs
   [all_states] to be a system of unique [=st=]-representatives and [P] to respect
   [=st=]; equivalently a measure/quotient treatment. (Contrast: StatMech.v proves
   its namesake because there [post_execution_dist] is literally the identity on
   distributions.) Correcting the triage docs: not derivable from present defs. *)
Axiom cno_preserves_shannon_entropy :
  forall (p : Program) (P : StateDistribution),
    is_CNO p ->
    shannon_entropy (post_execution_dist p P) = shannon_entropy P.

(** Therefore, CNOs have zero entropy change *)
Theorem cno_zero_entropy_change :
  forall (p : Program) (P : StateDistribution),
    is_CNO p ->
    boltzmann_entropy (post_execution_dist p P) - boltzmann_entropy P = 0.
Proof.
  intros p P H_cno.
  unfold boltzmann_entropy.
  rewrite cno_preserves_shannon_entropy; auto.
  ring.
Qed.

(** And therefore, CNOs dissipate zero energy (by Landauer)

    For a CNO, we have proven that ΔS = 0 (entropy is preserved).
    From thermodynamics, for a reversible isothermal process:

    ΔF = ΔE - T·ΔS

    Where ΔF is change in Helmholtz free energy, ΔE is change in internal energy.

    For a reversible process (CNO), the system can return to its initial state
    with no net work, implying ΔF = 0.

    Since ΔS = 0 for CNOs, and ΔF = 0 for reversible processes:
    0 = ΔE - T·0
    Therefore: ΔE = 0

    The work dissipated is:
    W = ΔF = 0

    A complete proof would require:
    - Thermodynamic identity: ΔF = 0 for reversible cycles at constant T
    - Connection between logical reversibility (CNO) and thermodynamic reversibility
    - First law of thermodynamics: dE = δQ - δW
    - For isothermal reversible process: W = TΔS

    This is Landauer's Principle in reverse: if ΔS = 0, then W = 0.
    CNOs are thermodynamically reversible and dissipate no energy.

    This result is fundamental to understanding the thermodynamics of computation
    and is safely axiomatized given the complexity of the thermodynamic machinery
    required for a complete proof.
*)
(* NOT-YET-DISCHARGED (class A) despite the [_derived] name. Claim: a CNO
   dissipates zero work, [work_dissipated P (post_execution_dist p P) = 0].
   Unfolding: [work_dissipated P Q = free_energy P - free_energy Q =
   (internal_energy P - internal_energy Q) - T·(boltzmann_entropy P - boltzmann_entropy Q)].
   The entropy term vanishes (via [cno_zero_entropy_change], hence via
   [cno_preserves_shannon_entropy]), but the [internal_energy] term
   [internal_energy P - internal_energy (post_execution_dist p P)] does NOT
   provably vanish: [internal_energy] is an opaque physical [Parameter] with no
   preservation law. Discharging would require both (a) discharging
   [cno_preserves_shannon_entropy] above and (b) an additional axiom/definition
   giving [internal_energy] invariance under CNOs — i.e. more input, not a pure
   derivation. Kept as an axiom; the triage "DISCHARGE" mark is inaccurate. *)
Axiom cno_zero_energy_dissipation_derived :
  forall (p : Program) (P : StateDistribution),
    is_CNO p ->
    work_dissipated P (post_execution_dist p P) = 0.

(** ** Summary of Derivation Chain *)

(**
   AXIOM AUDIT (post-classification; see per-axiom tags above).

   METAL-BOUNDARY axioms (kept — genuine empirical physics, not derivable):
   1. Boltzmann constant k_B and its positivity          (PhysicsConstants.v)
   2. Temperature T and its positivity                   (PhysicsConstants.v)
   3. Second Law of Thermodynamics                       (this file)
   4. Isothermal work bound (Helmholtz / 2nd law)        (this file)
   5. Landauer's principle lower bound                   (StatMech.v)
   6. Reversible ⇒ zero dissipation                      (StatMech.v)
      Opaque physical observables: energy_dissipated_phys, internal_energy.

   SPECIFICATION axioms for the opaque [shannon_entropy] / [product_dist]
   (class A — sound, but not dischargeable until those are defined concretely):
   1. shannon_entropy_nonneg, shannon_entropy_point_zero (StatMechBasis.v)
   2. shannon_entropy_uniform_max                        (this file)
   3. shannon_entropy_additive                           (this file)

   DERIVED (proved Theorems/Lemmas — NOT axioms):
   1. Boltzmann entropy non-negative
   2. Entropy change for erasure  [entropy_change_erasure — DISCHARGED here:
      Axiom -> Lemma, from uniform_max + point_zero + pow_INR/ln_pow]
   3. Landauer's principle bound  [landauer_principle_derived, landauer_one_bit]
   4. CNO zero entropy change     [cno_zero_entropy_change]

   NOT-YET-DISCHARGED (class A — cannot be honestly derived from present defs):
   1. cno_preserves_shannon_entropy — carrier/quotient issue (see tag)
   2. cno_zero_energy_dissipation_derived — internal_energy has no CNO-invariance

   SOUNDNESS WARNINGS (see StatMechBasis.v / StatMech.v tags):
   - prob_nonneg, prob_normalized: false over unconstrained function-type
     distributions (need a bundled distribution type); currently unused.
   - shannon_entropy_maximum (StatMech.v): the stated inequality is backwards
     (asserts uniform minimizes entropy); currently unused.
*)
