(** * Quantum CNOs: Certified Null Operations in Quantum Computing

    This module extends CNO theory to quantum computation, proving that
    the identity gate is the canonical quantum CNO and establishing
    connections between quantum reversibility and classical CNOs.

    Key Results:
    - Identity gate I is a quantum CNO
    - Quantum CNOs preserve quantum information
    - Unitary operations with trivial action are CNOs
    - Connection to no-cloning theorem

    Author: Jonathan D. A. Jewell
    Project: Absolute Zero
    License: MPL-2.0
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
(* Self-contained complex numbers (proofs/coq/common/Complex.v). *)
Require Import CNO.Complex.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CNO.CNO.
(* Shared physics constants — kB, temperature, kB_positive,
   temperature_positive. See proofs/coq/common/PhysicsConstants.v
   (consolidated by Follow-up 1 of docs/proof-debt-triage.md). *)
Require Import CNO.PhysicsConstants.

Open Scope R_scope.
Open Scope C_scope.

(** ** Physical Constants (for Landauer principle)

    [kB], [temperature], [kB_positive], and [temperature_positive] are
    imported from [CNO.PhysicsConstants] (consolidated by Follow-up 1). *)

(** ** Quantum State Representation *)

(** A quantum state is a unit vector in a Hilbert space.
    For simplicity, we work with finite-dimensional systems (qubits).
*)

(** Dimension of Hilbert space (2^n for n qubits).

    DISCHARGED (was Parameter dim + Axiom dim_positive). We fix a concrete
    single-qubit Hilbert space, dim = 2 = 2^1. Nothing in this development
    relies on [dim] being abstract, so pinning it to a concrete positive
    value both preserves every downstream statement and lets us *prove*
    [dim_positive] instead of postulating it. *)
Definition dim : nat := 2.

(** DISCHARGED (was Axiom dim_positive). *)
Lemma dim_positive : (dim > 0)%nat.
Proof. unfold dim; lia. Qed.

(** Complex vector representing quantum state *)
Definition QuantumState : Type := nat -> C.

(** Inner product for finite-dimensional quantum states.

    The inner product ⟨ψ|φ⟩ is defined as:
    ⟨ψ|φ⟩ = Σᵢ (ψᵢ)* × φᵢ

    where (ψᵢ)* is the complex conjugate of ψᵢ.

    For a rigorous treatment of infinite-dimensional Hilbert spaces,
    we would need measure theory (Lebesgue integration).
    Here we use an axiomatized version that captures the key properties.
*)

(** DISCHARGED (was Parameter inner_product + 3 axioms). We give the inner
    product its concrete finite-dimensional definition
    ⟨ψ|φ⟩ = Σ_{k<dim} conj(ψ_k)·φ_k, so the three Hilbert-space "axioms"
    (conjugate symmetry, linearity, positive definiteness) become *proved*
    lemmas rather than postulates. *)

(** Partial sum Σ_{i<k} conj(ψ_i)·φ_i. *)
Fixpoint ip_sum (ψ φ : QuantumState) (k : nat) : C :=
  match k with
  | O => C0
  | S k' => Cplus (ip_sum ψ φ k') (Cmult (Cconj (ψ k')) (φ k'))
  end.

(** Concrete inner product: the finite sum over the [dim] basis indices. *)
Definition inner_product (ψ φ : QuantumState) : C :=
  ip_sum ψ φ dim.

(** Conjugate symmetry (helper on partial sums, then the headline lemma). *)
Lemma ip_sum_conj_sym :
  forall (f g : QuantumState) (k : nat),
    ip_sum f g k = Cconj (ip_sum g f k).
Proof.
  intros f g k. induction k as [|k IH]; simpl.
  - unfold C0, Cconj; apply Cpair_eq; simpl; ring.
  - rewrite IH.
    destruct (ip_sum g f k) as [pr pi].
    destruct (f k) as [fr fi]; destruct (g k) as [gr gi].
    unfold Cplus, Cmult, Cconj; apply Cpair_eq; simpl; ring.
Qed.

(** DISCHARGED (was Axiom inner_product_conj_sym): ⟨ψ|φ⟩ = (⟨φ|ψ⟩)*. *)
Lemma inner_product_conj_sym :
  forall ψ φ : QuantumState,
    inner_product ψ φ = Cconj (inner_product φ ψ).
Proof. intros ψ φ; unfold inner_product; apply ip_sum_conj_sym. Qed.

(** DISCHARGED (was Axiom inner_product_linear). The original statement was
    literally [True] (a placeholder, since the model lacks state arithmetic),
    so it is proved trivially — no content is lost, and it leaves the trust
    base rather than sitting in it. *)
Lemma inner_product_linear :
  forall ψ φ1 φ2 : QuantumState,
  forall a b : C,
    True.
Proof. intros; exact I. Qed.

(** Positive definiteness (real part of Σ conj(ψ_i)·ψ_i is a sum of |ψ_i|²). *)
Lemma ip_sum_pos_re :
  forall (f : QuantumState) (k : nat),
    (Re (ip_sum f f k) >= 0)%R.
Proof.
  intros f k. induction k as [|k IH]; simpl.
  - unfold C0, Re; simpl; lra.
  - destruct (f k) as [fr fi].
    unfold Re, Cplus, Cmult, Cconj in *; simpl in *. nra.
Qed.

(** DISCHARGED (was Axiom inner_product_pos_def): Re⟨ψ|ψ⟩ ≥ 0. *)
Lemma inner_product_pos_def :
  forall ψ : QuantumState,
    (Re (inner_product ψ ψ) >= 0)%R.
Proof. intros ψ; unfold inner_product; apply ip_sum_pos_re. Qed.

(** Normalization: |ψ⟩ is normalized if ⟨ψ|ψ⟩ = 1 *)

Definition is_normalized (ψ : QuantumState) : Prop :=
  inner_product ψ ψ = C1.

(** ** Quantum Gates as Unitary Operators *)

(** A quantum gate is a unitary matrix U where U† U = I *)
Definition QuantumGate : Type := QuantumState -> QuantumState.

(** Unitary property: preserves inner products *)
Definition is_unitary (U : QuantumGate) : Prop :=
  forall ψ φ : QuantumState,
    inner_product (U ψ) (U φ) = inner_product ψ φ.

(** Identity gate *)
Definition I_gate : QuantumGate := fun ψ => ψ.

Theorem I_gate_unitary : is_unitary I_gate.
Proof.
  unfold is_unitary, I_gate.
  intros ψ φ.
  reflexivity.
Qed.

(** ** Common Quantum Gates *)

(** DISCHARGED gate concretisations. With the single-qubit model ([dim] = 2)
    and the concrete [inner_product] above, the Pauli X, Y, Z and Hadamard
    gates have honest matrix actions on the amplitude vector (ψ_0, ψ_1), and
    their unitarity becomes a *proved* per-component real identity rather than
    a postulate. (CNOT is a genuine two-qubit gate and cannot be hosted
    faithfully in a single-qubit space — see its note below.) *)

(** Pauli X (NOT gate): X = [[0,1],[1,0]], i.e. it swaps ψ_0 and ψ_1. *)
Definition X_gate : QuantumGate :=
  fun ψ n => match n with
             | 0%nat => ψ 1%nat
             | 1%nat => ψ 0%nat
             | _ => ψ n
             end.

(** DISCHARGED (was Axiom X_gate_unitary). *)
Lemma X_gate_unitary : is_unitary X_gate.
Proof.
  unfold is_unitary, inner_product, dim, X_gate. intros ψ φ. simpl.
  destruct (ψ 0%nat) as [a0r a0i]; destruct (ψ 1%nat) as [a1r a1i].
  destruct (φ 0%nat) as [b0r b0i]; destruct (φ 1%nat) as [b1r b1i].
  unfold Cplus, Cmult, Cconj, C0; apply Cpair_eq; simpl; ring.
Qed.

(** Pauli Y: Y = [[0,-i],[i,0]], i.e. ψ_0 ↦ -i·ψ_1, ψ_1 ↦ i·ψ_0. *)
Definition Y_gate : QuantumGate :=
  fun ψ n => match n with
             | 0%nat => Cmult (Copp Ci) (ψ 1%nat)
             | 1%nat => Cmult Ci (ψ 0%nat)
             | _ => ψ n
             end.

(** DISCHARGED (was Axiom Y_gate_unitary). *)
Lemma Y_gate_unitary : is_unitary Y_gate.
Proof.
  unfold is_unitary, inner_product, dim, Y_gate. intros ψ φ. simpl.
  destruct (ψ 0%nat) as [a0r a0i]; destruct (ψ 1%nat) as [a1r a1i].
  destruct (φ 0%nat) as [b0r b0i]; destruct (φ 1%nat) as [b1r b1i].
  unfold Cplus, Cmult, Cconj, Copp, Ci, C0; apply Cpair_eq; simpl; ring.
Qed.

(** Pauli Z: Z = [[1,0],[0,-1]], i.e. ψ_1 ↦ -ψ_1. *)
Definition Z_gate : QuantumGate :=
  fun ψ n => match n with
             | 1%nat => Copp (ψ 1%nat)
             | _ => ψ n
             end.

(** DISCHARGED (was Axiom Z_gate_unitary). *)
Lemma Z_gate_unitary : is_unitary Z_gate.
Proof.
  unfold is_unitary, inner_product, dim, Z_gate. intros ψ φ. simpl.
  destruct (ψ 0%nat) as [a0r a0i]; destruct (ψ 1%nat) as [a1r a1i].
  destruct (φ 0%nat) as [b0r b0i]; destruct (φ 1%nat) as [b1r b1i].
  unfold Cplus, Cmult, Cconj, Copp, C0; apply Cpair_eq; simpl; ring.
Qed.

(** Hadamard: H = (1/√2)·[[1,1],[1,-1]]. *)
Definition H_gate : QuantumGate :=
  fun ψ n => match n with
             | 0%nat => Cmult (RtoC (1 / sqrt 2)) (Cplus (ψ 0%nat) (ψ 1%nat))
             | 1%nat => Cmult (RtoC (1 / sqrt 2)) (Cminus (ψ 0%nat) (ψ 1%nat))
             | _ => ψ n
             end.

(** DISCHARGED (was Axiom H_gate_unitary). The (1/√2)² factor collapses to
    1/2 via [sqrt_sqrt], leaving each component identity 2·(1/2)·⟨·|·⟩. *)
Lemma H_gate_unitary : is_unitary H_gate.
Proof.
  unfold is_unitary, inner_product, dim, H_gate. intros ψ φ. simpl.
  assert (Hn : (sqrt 2 <> 0)%R) by (apply Rgt_not_eq, sqrt_lt_R0; lra).
  assert (Hs : (sqrt 2 * sqrt 2 = 2)%R) by (apply sqrt_sqrt; lra).
  (* The normalisation squares to 1/2. *)
  assert (Ht : (1 / sqrt 2 * (1 / sqrt 2) = / 2)%R).
  { replace (1 / sqrt 2 * (1 / sqrt 2))%R with (/ (sqrt 2 * sqrt 2))%R
      by (field; exact Hn). rewrite Hs; reflexivity. }
  set (t := (1 / sqrt 2)%R) in *.
  assert (Ht2 : (t ^ 2 = / 2)%R) by (rewrite <- Ht; ring).
  destruct (ψ 0%nat) as [a0r a0i]; destruct (ψ 1%nat) as [a1r a1i].
  destruct (φ 0%nat) as [b0r b0i]; destruct (φ 1%nat) as [b1r b1i].
  unfold Cplus, Cminus, Cmult, Cconj, Copp, RtoC, C0; apply Cpair_eq; simpl;
    ring_simplify; rewrite ?Ht2; ring_simplify; lra.
Qed.

(** CNOT gate (two-qubit).

    NOT-YET-DISCHARGED (class A, provable in principle): CNOT is a genuine
    two-qubit gate (a 4×4 permutation matrix acting on the |q1 q0⟩ basis).
    The [dim] = 2 single-qubit model here cannot host it *faithfully* (a flat
    [nat -> C] space with one global [dim] has no tensor-product structure).
    Its faithful concrete matrix [CNOT_matrix] lives in QuantumMechanicsExact.v;
    discharging its unitarity requires a genuine 2-qubit (4-dimensional,
    tensor-structured) state space, which this module deliberately does not
    build. Kept as an abstract primitive so downstream statements type-check.
    (This is the ONLY gate-unitarity claim in this file left undischarged.) *)
Parameter CNOT_gate : QuantumGate.
(* NOT-YET-DISCHARGED (class A): unitarity of the abstract CNOT primitive.
   See the note above — needs a 4-dimensional tensor-product model. *)
Axiom CNOT_gate_unitary : is_unitary CNOT_gate.

(** ** Quantum State Equality *)

(** DISCHARGED (was Parameter Cexp + 4 axioms). The phase used throughout
    this development is only ever applied to a real argument [RtoC θ], where
    it denotes the unit phase e^{iθ}. We give it that concrete meaning:
    [Cexp z = (cos (Re z), sin (Re z))], i.e. e^{i·Re z}. This is faithful to
    every use site (all of the form [Cexp (RtoC θ)] = (cos θ, sin θ)), and it
    turns the "complex exponential algebra" axioms below into proved lemmas
    (follow-up 4 of docs/proof-debt-triage.md). *)
Definition Cexp (z : C) : C := (cos (Re z), sin (Re z)).

(** Two quantum states are equal up to global phase *)
Definition quantum_state_eq (ψ φ : QuantumState) : Prop :=
  exists θ : R, forall n, ψ n = Cexp (RtoC θ) * φ n.

Notation "ψ =q= φ" := (quantum_state_eq ψ φ) (at level 70).

(** DISCHARGED (was Axiom Cexp_zero): e^{i·0} = 1. *)
Lemma Cexp_zero : Cexp (RtoC 0) = C1.
Proof.
  unfold Cexp, RtoC, Re, C1; simpl.
  rewrite cos_0, sin_0; reflexivity.
Qed.

(** DISCHARGED (was Axiom Cexp_neg): e^{-iθ} = (e^{iθ})^{-1}. Uses the
    Pythagorean identity cos²θ + sin²θ = 1 so the modulus is 1. *)
Lemma Cexp_neg : forall x : R, Cexp (RtoC (-x)) = Cinv (Cexp (RtoC x)).
Proof.
  intros x. unfold Cexp, RtoC, Cinv, Re, Cnorm2; simpl.
  assert (Hpy : (cos x * cos x + sin x * sin x = 1)%R).
  { pose proof (sin2_cos2 x) as H. unfold Rsqr in H. lra. }
  apply Cpair_eq; simpl.
  - rewrite cos_neg, Hpy; field.
  - rewrite sin_neg, Hpy; field.
Qed.

(** DISCHARGED (was Axiom Cexp_add): e^{iθ}·e^{iφ} = e^{i(θ+φ)}. Uses the
    angle-addition formulas for cos and sin. *)
Lemma Cexp_add : forall x y : R, Cexp (RtoC x) * Cexp (RtoC y) = Cexp (RtoC (x + y)).
Proof.
  intros x y. unfold Cexp, RtoC, Cmult, Re; simpl.
  rewrite cos_plus, sin_plus. apply Cpair_eq; simpl; ring.
Qed.

(* Cmult_1_l, Cmult_assoc, Cconj_RtoC, Cconj_mult are PROVED lemmas in
   CNO.Complex — no longer axioms. *)

(* REMOVED (was Axiom Cconj_Cexp : forall x:C, Cconj (Cexp x) = Cexp (Cconj x)).
   This axiom was DEAD CODE (no proof in this file referenced it) AND FALSE
   for a genuine phase: for the phase e^{iθ} one has (e^{iθ})* = e^{-iθ},
   whereas the axiom asserts (e^{iθ})* = e^{iθ} (Cconj (RtoC θ) = RtoC θ),
   which forces sin θ = 0. Had [Cexp] ever been given the concrete phase
   definition while this axiom stood, the development would have been
   inconsistent. It is removed here (reported as a latent-unsoundness find). *)

(* `global_phase_unitary` (now proved) appears below, after
   `global_phase_gate` is defined. *)

(** Reflexivity, symmetry, transitivity *)
Lemma quantum_state_eq_refl : forall ψ, ψ =q= ψ.
Proof.
  intros ψ.
  unfold quantum_state_eq.
  exists 0.
  intros n.
  (* e^0 = 1, so e^0 × ψ_n = 1 × ψ_n = ψ_n *)
  rewrite Cexp_zero.
  rewrite Cmult_1_l.
  reflexivity.
Qed.

Lemma quantum_state_eq_sym : forall ψ φ, ψ =q= φ -> φ =q= ψ.
Proof.
  intros ψ φ [θ H].
  exists (-θ)%R.
  intros n.
  (* ψ_n = e^θ × φ_n, so φ_n = e^{-θ} × ψ_n *)
  specialize (H n).
  rewrite H.
  (* e^{-θ} × (e^θ × φ_n) = (e^{-θ} × e^θ) × φ_n *)
  rewrite Cmult_assoc.
  (* e^{-θ} × e^θ = e^{-θ + θ} = e^0 = 1 *)
  assert (Cexp (RtoC (-θ)) * Cexp (RtoC θ) = C1) as Hinv.
  { rewrite Cexp_add.
    replace (-θ + θ)%R with 0%R by ring.
    apply Cexp_zero. }
  rewrite Hinv.
  rewrite Cmult_1_l.
  reflexivity.
Qed.

Lemma quantum_state_eq_trans : forall ψ φ χ,
  ψ =q= φ -> φ =q= χ -> ψ =q= χ.
Proof.
  intros ψ φ χ [θ1 H1] [θ2 H2].
  exists (θ1 + θ2)%R.
  intros n.
  (* ψ_n = e^{θ1} × φ_n and φ_n = e^{θ2} × χ_n *)
  (* So ψ_n = e^{θ1} × (e^{θ2} × χ_n) = e^{θ1 + θ2} × χ_n *)
  specialize (H1 n).
  specialize (H2 n).
  rewrite H1.
  rewrite H2.
  rewrite Cmult_assoc.
  rewrite Cexp_add.
  reflexivity.
Qed.

(** ** Quantum CNO Definition *)

(** A quantum gate is a CNO if:
    1. It's unitary (reversible)
    2. It acts as identity (up to global phase)
    3. No measurement (preserves quantum information)
*)

Definition is_quantum_CNO (U : QuantumGate) : Prop :=
  (** Unitary (reversible) *)
  is_unitary U /\
  (** Identity action *)
  (forall ψ : QuantumState, U ψ =q= ψ) /\
  (** No measurement - implicit in gate model *)
  True.

(** ** Main Theorem: Identity Gate is CNO *)

Theorem I_gate_is_quantum_cno : is_quantum_CNO I_gate.
Proof.
  unfold is_quantum_CNO, I_gate.
  split.
  - (* Unitary *)
    apply I_gate_unitary.
  - split.
    + (* Identity *)
      intros ψ.
      apply quantum_state_eq_refl.
    + (* No measurement *)
      trivial.
Qed.

(** ** Trivial Global Phase Gates *)

(** A gate that only adds global phase is a CNO *)
Definition global_phase_gate (θ : R) : QuantumGate :=
  fun ψ n => Cexp (RtoC θ) * ψ n.

(** Helper: scaling both arguments of the inner-product sum by a common
    unit-modulus constant (cr, ci) with cr² + ci² = 1 leaves the sum
    unchanged, because conj(c)·c = |c|² = 1. *)
Lemma ip_sum_scale :
  forall (cr ci : R) (ψ φ : QuantumState) (k : nat),
    (cr * cr + ci * ci = 1)%R ->
    ip_sum (fun n => Cmult (cr, ci) (ψ n)) (fun n => Cmult (cr, ci) (φ n)) k
    = ip_sum ψ φ k.
Proof.
  intros cr ci ψ φ k Hc.
  assert (Hcr : (cr ^ 2 = 1 - ci ^ 2)%R).
  { replace (cr ^ 2)%R with (cr * cr)%R by ring.
    replace (ci ^ 2)%R with (ci * ci)%R by ring. lra. }
  induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite IH. f_equal.
    destruct (ψ k) as [xr xi]; destruct (φ k) as [yr yi].
    unfold Cmult, Cconj; apply Cpair_eq; simpl;
      ring_simplify; rewrite ?Hcr; ring.
Qed.

(** DISCHARGED (was Axiom global_phase_unitary). A global phase multiplies
    every amplitude by the unit-modulus scalar e^{iθ} = (cos θ, sin θ); since
    |e^{iθ}|² = cos²θ + sin²θ = 1, the inner product is preserved. *)
Lemma global_phase_unitary :
  forall θ : R, is_unitary (global_phase_gate θ).
Proof.
  intros θ. unfold is_unitary. intros ψ φ. unfold inner_product.
  assert (Hgp : forall χ : QuantumState,
            global_phase_gate θ χ = (fun n => Cmult (cos θ, sin θ) (χ n))).
  { intro χ. unfold global_phase_gate, Cexp, RtoC, Re. simpl. reflexivity. }
  rewrite (Hgp ψ), (Hgp φ).
  apply ip_sum_scale.
  pose proof (sin2_cos2 θ) as H. unfold Rsqr in H. lra.
Qed.

Theorem global_phase_is_cno :
  forall θ : R, is_quantum_CNO (global_phase_gate θ).
Proof.
  intros θ.
  unfold is_quantum_CNO.
  split.
  - (* Unitary *)
    apply global_phase_unitary.
  - split.
    + (* Identity up to phase *)
      intros ψ.
      unfold quantum_state_eq.
      exists θ.
      intros n.
      unfold global_phase_gate.
      reflexivity.
    + trivial.
Qed.

(** ** Non-CNO Gates *)

(** DISCHARGED (was Axiom X_gate_not_identity). X flips |0⟩ ↔ |1⟩, so with the
    witness |0⟩ = (1,0,0,…) we have (X|0⟩)_0 = 0 while (e^{iθ}|0⟩)_0 = e^{iθ},
    forcing e^{iθ} = 0 — impossible since |e^{iθ}| = 1. *)
Lemma X_gate_not_identity : exists ψ, ~ (X_gate ψ =q= ψ).
Proof.
  exists (fun n => match n with O => C1 | _ => C0 end).
  intros [θ H]. specialize (H 0%nat).
  unfold X_gate in H. simpl in H.
  unfold Cexp, RtoC, Re, Cmult, C0, C1 in H. simpl in H.
  injection H as H1 H2.
  pose proof (sin2_cos2 θ) as Hpy. unfold Rsqr in Hpy. nra.
Qed.

Theorem X_gate_not_cno : ~ is_quantum_CNO X_gate.
Proof.
  unfold is_quantum_CNO.
  intro H.
  destruct H as [_ [H_id _]].
  destruct X_gate_not_identity as [ψ H_neq].
  specialize (H_id ψ).
  contradiction.
Qed.

(** DISCHARGED (was Axiom H_gate_not_identity). With witness |0⟩, the Hadamard
    output has (H|0⟩)_1 = 1/√2 ≠ 0, while (e^{iθ}|0⟩)_1 = e^{iθ}·0 = 0; equality
    up to phase would force 1/√2 = 0, contradicting 1/√2 > 0. *)
Lemma H_gate_not_identity : exists ψ, ~ (H_gate ψ =q= ψ).
Proof.
  exists (fun n => match n with O => C1 | _ => C0 end).
  intros [θ H]. specialize (H 1%nat).
  unfold H_gate in H. simpl in H.
  unfold Cexp, RtoC, Re, Cmult, Cminus, Cplus, Copp, C0, C1 in H. simpl in H.
  injection H as H1 H2.
  assert (Hpos : (1 / sqrt 2 > 0)%R)
    by (apply Rlt_gt, Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0; lra]).
  nra.
Qed.

Theorem H_gate_not_cno : ~ is_quantum_CNO H_gate.
Proof.
  unfold is_quantum_CNO.
  intro H.
  destruct H as [_ [H_id _]].
  destruct H_gate_not_identity as [ψ H_neq].
  specialize (H_id ψ).
  contradiction.
Qed.

(** ** Gate Composition *)

(** Composition of quantum gates *)
Definition gate_compose (U V : QuantumGate) : QuantumGate :=
  fun ψ => U (V ψ).

Notation "U ⊗ V" := (gate_compose U V) (at level 40, left associativity).

(** Composition of unitary gates is unitary *)
Theorem unitary_compose :
  forall U V : QuantumGate,
    is_unitary U -> is_unitary V -> is_unitary (U ⊗ V).
Proof.
  intros U V HU HV.
  unfold is_unitary in *.
  intros ψ φ.
  unfold gate_compose.
  rewrite HU.
  rewrite HV.
  reflexivity.
Qed.

(** Composition of quantum CNOs yields a CNO *)
Theorem quantum_cno_composition :
  forall U V : QuantumGate,
    is_quantum_CNO U ->
    is_quantum_CNO V ->
    is_quantum_CNO (U ⊗ V).
Proof.
  intros U V [HU_unitary [HU_id _]] [HV_unitary [HV_id _]].
  unfold is_quantum_CNO.
  split.
  - (* Unitary *)
    apply unitary_compose; assumption.
  - split.
    + (* Identity *)
      intros ψ.
      unfold gate_compose.
      (* U(V ψ) =q= ψ via transitivity through V ψ *)
      (* U(V ψ) =q= V ψ (by HU_id) and V ψ =q= ψ (by HV_id) *)
      apply quantum_state_eq_trans with (V ψ).
      * (* U(V ψ) =q= V ψ *)
        apply HU_id.
      * (* V ψ =q= ψ *)
        apply HV_id.
    + trivial.
Qed.

(** ** Quantum Information Theory *)

(** Von Neumann entropy (quantum analog of Shannon entropy).

    DISCHARGED (was Parameter von_neumann_entropy + 3 axioms). This module,
    like QuantumMechanicsExact.v (which also sets [von_neumann_entropy := 0]),
    works in the PURE-STATE fragment: every state vector is a pure state, and
    a pure state |ψ⟩ has S(|ψ⟩⟨ψ|) = 0. We therefore give the entropy its
    concrete pure-state value, 0.

    HONEST DISCLOSURE: because of this modelling choice the three lemmas below
    hold *trivially* (0 ≥ 0, 0 = 0). They are genuine consequences of working
    in the pure-state fragment — not deep theorems — and are reported as
    "trivial-by-model" rather than as substantive content. The non-trivial
    physics (mixed-state entropy, strict subadditivity, etc.) is outside the
    scope of this module and would require a density-matrix formalisation. *)
Definition von_neumann_entropy (ψ : QuantumState) : R := 0%R.

(** DISCHARGED (was Axiom von_neumann_nonneg): S ≥ 0. Trivial in the pure model. *)
Lemma von_neumann_nonneg :
  forall ψ : QuantumState,
    von_neumann_entropy ψ >= 0.
Proof. intros ψ; unfold von_neumann_entropy; lra. Qed.

(** DISCHARGED (was Axiom von_neumann_pure_zero): pure states have zero entropy. *)
Lemma von_neumann_pure_zero :
  forall ψ : QuantumState,
    is_normalized ψ ->
    von_neumann_entropy ψ = 0.
Proof. intros ψ _; unfold von_neumann_entropy; reflexivity. Qed.

(** DISCHARGED (was Axiom unitary_preserves_entropy): S(Uψ) = S(ψ). Trivial in
    the pure model (both sides are 0). *)
Lemma unitary_preserves_entropy :
  forall (U : QuantumGate) (ψ : QuantumState),
    is_unitary U ->
    von_neumann_entropy (U ψ) = von_neumann_entropy ψ.
Proof. intros U ψ _; unfold von_neumann_entropy; reflexivity. Qed.

(** Quantum CNOs preserve information (trivially, since they're identity) *)
Theorem quantum_cno_preserves_information :
  forall (U : QuantumGate) (ψ : QuantumState),
    is_quantum_CNO U ->
    von_neumann_entropy (U ψ) = von_neumann_entropy ψ.
Proof.
  intros U ψ [H_unitary _].
  apply unitary_preserves_entropy.
  assumption.
Qed.

(** ** No-Cloning Theorem *)

(** The no-cloning theorem states you cannot copy arbitrary quantum states.

    REMOVED (was Axiom no_cloning), reported as a LATENT-UNSOUNDNESS find.
    The former "simplified" statement was

        ~ exists U, forall ψ, exists basis, U ψ = ψ /\ U ψ = ψ

    whose body [exists basis, U ψ = ψ /\ U ψ = ψ] is just [U ψ = ψ] (the
    [basis] witness and the duplicated conjunct are inert). So the axiom
    asserts ~ (exists U, forall ψ, U ψ = ψ) — but that existential is WITNESSED
    by [I_gate] (fun ψ => ψ), which satisfies [forall ψ, I_gate ψ = ψ]. The
    axiom was therefore provably FALSE and made the development inconsistent
    (one could derive [False] from it). It was also dead code — no proof in
    this file referenced it (the [cno_respects_no_cloning] result below does
    not use it). A faithful no-cloning theorem needs a tensor-product state
    space, which this flat single-register model does not provide; it is left
    unstated here rather than restated in a degenerate (and unsound) form. *)

(** CNOs respect no-cloning (they don't clone, they preserve) *)
Theorem cno_respects_no_cloning :
  forall U : QuantumGate,
    is_quantum_CNO U ->
    forall ψ : QuantumState, U ψ =q= ψ.
Proof.
  intros U [_ [H_id _]] ψ.
  apply H_id.
Qed.

(** ** Connection to Classical CNOs *)

(** Measurement in the computational basis.

    Measurement collapses a quantum state |ψ⟩ = Σᵢ αᵢ|i⟩ to a classical
    outcome i with probability |αᵢ|².

    This is modeled as a function from QuantumState to ProgramState,
    representing the expected (deterministic) behavior when post-selecting
    on the measurement outcome, or the most likely outcome.
*)
Parameter measure : QuantumState -> ProgramState.

(** DISCHARGED (was Axiom measure_identity_commutes). Since [I_gate] is the
    identity function ([fun ψ => ψ]), [I_gate ψ] is definitionally [ψ], so
    measuring after the identity gate equals measuring before — by reflexivity,
    independent of what [measure] does. ([measure] itself stays an abstract
    operation, not an axiom.) *)
Lemma measure_identity_commutes :
  forall (ψ : QuantumState),
    measure (I_gate ψ) = measure ψ.
Proof. intros ψ; unfold I_gate; reflexivity. Qed.

(** A quantum gate induces a classical transformation via measurement.

    For a quantum CNO (which acts as identity), the induced classical
    program is the empty program (also a CNO).

    The correspondence is:
    - Quantum identity I → Classical empty program []
    - Both preserve their respective state types
    - Both dissipate zero energy (thermodynamically reversible)
*)
Definition quantum_to_classical (U : QuantumGate) : Program :=
  (* For a quantum CNO, the induced classical program is empty.
     This is because:
     1. CNO: U|ψ⟩ = |ψ⟩ (up to global phase)
     2. Measurement outcomes unchanged: measure(U|ψ⟩) = measure(|ψ⟩)
     3. Classical program does nothing to measurement statistics
     4. Empty program [] is the minimal classical CNO
  *)
  nil.

(** Theorem: Quantum CNOs induce classical CNOs via measurement *)
Theorem quantum_cno_induces_classical :
  forall U : QuantumGate,
    is_quantum_CNO U ->
    is_CNO (quantum_to_classical U).
Proof.
  intros U H_qcno.
  unfold quantum_to_classical.
  (* The empty program is a CNO - proved in CNO.v *)
  apply empty_is_cno.
Qed.

(** ** Quantum Circuit Model *)

(** A quantum circuit is a sequence of gates *)
Inductive QuantumCircuit : Type :=
  | QEmpty : QuantumCircuit
  | QGate : QuantumGate -> QuantumCircuit -> QuantumCircuit.

(** Circuit evaluation *)
Fixpoint eval_circuit (circ : QuantumCircuit) (ψ : QuantumState) : QuantumState :=
  match circ with
  | QEmpty => ψ
  | QGate U rest => eval_circuit rest (U ψ)
  end.

(** A circuit is a CNO if its evaluation is identity *)
Definition is_circuit_CNO (circ : QuantumCircuit) : Prop :=
  forall ψ : QuantumState, eval_circuit circ ψ =q= ψ.

(** Empty circuit is a CNO *)
Theorem empty_circuit_is_cno : is_circuit_CNO QEmpty.
Proof.
  unfold is_circuit_CNO.
  intros ψ.
  simpl.
  apply quantum_state_eq_refl.
Qed.

(** U followed by U† is a CNO (unitary inverse) *)
Parameter unitary_inverse : QuantumGate -> QuantumGate.

(* NOT-YET-DISCHARGED (class A, provable in principle): the inverse property
   unitary_inverse U (U ψ) =q= ψ. This does NOT follow merely from the
   [is_unitary] definition here (which is inner-product preservation): from
   "U preserves ⟨·|·⟩" alone one cannot *constructively exhibit* an inverse
   FUNCTION for an arbitrary endomap of the infinite [nat -> C] space. A real
   discharge needs finite-dimensional linear-algebra machinery (a unitary is
   invertible with U^{-1} = U†) over a proper matrix representation — absent
   from this abstract model. Kept as an axiom; it is load-bearing only for
   [gate_followed_by_inverse_is_cno] and [quantum_cno_reversible] below. *)
Axiom unitary_inverse_property :
  forall (U : QuantumGate) (ψ : QuantumState),
    is_unitary U ->
    unitary_inverse U (U ψ) =q= ψ.

Theorem gate_followed_by_inverse_is_cno :
  forall U : QuantumGate,
    is_unitary U ->
    is_circuit_CNO (QGate U (QGate (unitary_inverse U) QEmpty)).
Proof.
  intros U H_unitary.
  unfold is_circuit_CNO.
  intros ψ.
  simpl.
  apply unitary_inverse_property.
  assumption.
Qed.

(** ** Thermodynamics of Quantum CNOs *)

(** Quantum operations preserve unitarity, hence are reversible *)
Theorem quantum_cno_reversible :
  forall U : QuantumGate,
    is_quantum_CNO U ->
    exists U_inv : QuantumGate,
      forall ψ, U_inv (U ψ) =q= ψ.
Proof.
  intros U [H_unitary _].
  exists (unitary_inverse U).
  intros ψ.
  apply unitary_inverse_property.
  assumption.
Qed.

(** ** Quantum Landauer Principle

    The quantum generalization of Landauer's principle states:
    - Unitary operations are thermodynamically reversible (ΔS = 0)
    - Non-unitary operations (measurement, decoherence) can increase entropy
    - Energy dissipation is bounded by: E ≥ kT × ΔS

    For quantum CNOs:
    - They are unitary by definition
    - Von Neumann entropy is preserved
    - Therefore: E_dissipated = 0
*)

(** Physical energy dissipation for quantum operations *)
Parameter quantum_energy_dissipated : QuantumGate -> QuantumState -> R.

(** Landauer bound for quantum operations. *)
(* METAL-BOUNDARY AXIOM (kept): the quantum Landauer bound
   E_dissipated ≥ k_B·T·(-ΔS) when entropy decreases. This is a genuine
   PHYSICAL postulate relating an empirical energy quantity
   [quantum_energy_dissipated] (an abstract, unmodelled physical observable)
   to entropy change and temperature. It is NOT a mathematical consequence of
   the definitions — deliberately NOT discharged by setting energy ≡ 0, which
   would falsify the bound for genuinely dissipative (non-unitary) operations.
   It is the substantive thermodynamic input of this section. *)
Axiom quantum_landauer_bound :
  forall (U : QuantumGate) (ψ : QuantumState),
    let ΔS := (von_neumann_entropy (U ψ) - von_neumann_entropy ψ)%R in
    (ΔS <= 0)%R ->  (* Entropy decreased (information erased) *)
    (quantum_energy_dissipated U ψ >= kB * temperature * (-ΔS))%R.

(** DISCHARGED (was Axiom unitary_zero_entropy_change): unitary evolution
    leaves von Neumann entropy unchanged. In the pure-state model both sides
    are 0. (Same statement as [unitary_preserves_entropy]; kept as a distinct
    name because downstream code refers to it.) *)
Lemma unitary_zero_entropy_change :
  forall (U : QuantumGate) (ψ : QuantumState),
    is_unitary U ->
    von_neumann_entropy (U ψ) = von_neumann_entropy ψ.
Proof. intros U ψ _; unfold von_neumann_entropy; reflexivity. Qed.

(** Reversible quantum operations dissipate zero energy. *)
(* METAL-BOUNDARY AXIOM (kept): a thermodynamically reversible (entropy-
   preserving) operation dissipates exactly zero energy. This is a PHYSICAL
   idealisation about the abstract observable [quantum_energy_dissipated]; the
   Landauer bound above only gives a LOWER bound (≥ 0), so E = 0 for the
   reversible case is an independent physical postulate, not a mathematical
   consequence. (Not discharged via energy ≡ 0 — see the Landauer note.) *)
Axiom reversible_quantum_zero_dissipation :
  forall (U : QuantumGate) (ψ : QuantumState),
    is_unitary U ->
    von_neumann_entropy (U ψ) = von_neumann_entropy ψ ->
    quantum_energy_dissipated U ψ = 0%R.

(** Theorem: Quantum CNOs dissipate zero energy *)
Theorem quantum_cno_zero_dissipation :
  forall (U : QuantumGate) (ψ : QuantumState),
    is_quantum_CNO U ->
    quantum_energy_dissipated U ψ = 0%R.
Proof.
  intros U ψ [H_unitary [H_id _]].
  apply reversible_quantum_zero_dissipation.
  - (* U is unitary *)
    assumption.
  - (* Entropy preserved *)
    apply unitary_preserves_entropy.
    assumption.
Qed.

(** ** Decoherence and Noise *)

(** In reality, quantum gates experience decoherence.
    A perfect quantum CNO is an idealization.
*)

(** Noisy quantum channel *)
Parameter noisy_channel : QuantumGate -> QuantumGate.

(** Fidelity: how close is noisy gate to ideal gate *)
Parameter fidelity : QuantumGate -> QuantumGate -> R.

(* NOT-YET-DISCHARGED (class A, provable in principle): 0 ≤ fidelity U V ≤ 1.
   For a genuinely-defined fidelity this follows from [inner_product_pos_def]
   and Cauchy–Schwarz. Here [fidelity] is an abstract [Parameter] with no
   definition, so the bound cannot be proved without first giving fidelity a
   concrete construction (an operator-norm / overlap definition), which this
   module does not build. Kept as an axiom. *)
Axiom fidelity_bound : forall U V, 0 <= fidelity U V <= 1.

(** Even with noise, approximate CNOs preserve high fidelity *)
(* NOT-YET-DISCHARGED (class A / definitional): for any CNO U and ε > 0 there
   is a noisy gate within fidelity 1 - ε. With a concrete fidelity satisfying
   fidelity U U = 1 this is immediate (take U_noisy := U); but [fidelity] is
   abstract here, so it cannot be discharged without that concrete definition.
   Kept as an axiom. *)
Axiom approximate_cno :
  forall U : QuantumGate,
    is_quantum_CNO U ->
    forall ε : R, ε > 0 ->
      exists U_noisy,
        fidelity U U_noisy >= 1 - ε.

(** ** Summary *)

(** This module proves:

    1. Identity gate I is a quantum CNO
    2. Global phase gates are CNOs
    3. Non-trivial gates (X, H) are NOT CNOs
    4. Quantum CNOs compose
    5. Quantum CNOs preserve quantum information (entropy)
    6. Connection to no-cloning theorem
    7. Quantum CNOs are thermodynamically reversible
    8. U U† circuits are CNOs

    PHYSICAL INTERPRETATION:
    - Quantum CNOs are unitary operations that act as identity
    - They preserve quantum coherence
    - They dissipate zero energy (reversible)
    - They respect fundamental quantum limits (no-cloning)

    CONNECTION TO CLASSICAL CNOs:
    - Classical CNOs are measurement-free quantum CNOs
    - Both preserve information (different notions of entropy)
    - Both are thermodynamically reversible (Landauer's principle)

    PRACTICAL QUANTUM COMPUTING:
    - Calibration: ensuring gates approximate identity when needed
    - Error correction: detecting when gates deviate from CNO behavior
    - Optimization: removing CNO subcircuits from quantum algorithms
*)
