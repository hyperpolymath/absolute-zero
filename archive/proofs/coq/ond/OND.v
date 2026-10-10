(** * Observational Null Operations (OND): The Disclosure Pillar

    This file formalises the SECOND pillar of Absolute Zero: Observational
    Null Disclosure. Where a Certified Null Operation (CNO, see [CNO.CNO])
    certifies that an operation does *nothing to the world* (state identity),
    an Observational Null Operation certifies that an operation *reveals
    nothing about its secret input* to a declared observation model [O].

    The two pillars are siblings of equal weight, not parent and extension.
    This module discharges roadmap obligations OND-1 .. OND-5 (see
    docs/OND-ROADMAP.adoc) with real, machine-checked proofs and ZERO axioms.

    THE LOAD-BEARING DESIGN DECISION (OND-1).
    A CNO leaves *all state observables* unchanged, so anything an observer
    reconstructs purely from final state is automatically secret-independent
    whenever the output channel starts secret-independent. Consequently a CNO
    can leak *only* through a channel that is NOT a function of state — timing,
    energy, EM. That is exactly why the observation model here carries a
    [tm] (timing) component the pure-state CNO model deliberately lacks, and
    exactly why the two pillars are logically independent (OND-3). The observer
    sees the produced execution ([out] on a declared output channel, plus [tm]),
    NOT the raw secret input — so the empty operation is OND under *any* model
    (OND-2).

    Author: Jonathan D. A. Jewell (formalisation by Absolute Zero proof effort)
    Project: Absolute Zero
    License: MPL-2.0
*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import CNO.CNO.
Import ListNotations.

(** ** Memory, inputs, and the secret/public split *)

(** We reuse the core [Memory] model ([nat -> nat], see [CNO.CNO]).
    By convention cell 0 holds the SECRET input, cell 1 holds the PUBLIC
    input, and cell 2 is the declared OUTPUT channel (initialised to 0). *)

Definition secret_cell : nat := 0.
Definition public_cell : nat := 1.
Definition output_cell : nat := 2.

(** Inject a (secret, public) pair into an initial memory. The output cell
    and all other cells start at the secret-independent constant 0. *)
Definition inj (s p : nat) : Memory :=
  fun a => match a with
           | 0 => s
           | 1 => p
           | _ => 0
           end.

Lemma inj_secret : forall s p, inj s p secret_cell = s.
Proof. reflexivity. Qed.
Lemma inj_public : forall s p, inj s p public_cell = p.
Proof. reflexivity. Qed.
Lemma inj_output : forall s p, inj s p output_cell = 0.
Proof. reflexivity. Qed.

(** ** Operations and their observable executions *)

(** An operation has a semantic effect on memory ([op_step]) and an
    observable timing cost ([op_time]) that may itself depend on memory
    (this is the channel a CNO can leak through). *)
Record Op : Type := mkOp {
  op_step : Memory -> Memory;
  op_time : Memory -> nat
}.

(** What an observer can actually see of one run: the value on the declared
    output channel and the elapsed time. Crucially it does NOT expose the raw
    input memory, so the observer cannot read the secret cell directly. *)
Record Exec : Type := mkExec {
  ex_out : nat;
  ex_time : nat
}.

(** Run an operation on an injected (secret, public) input. *)
Definition run (o : Op) (s p : nat) : Exec :=
  mkExec (op_step o (inj s p) output_cell) (op_time o (inj s p)).

(** ** OND-1 — The definition, parameterised by an observation model [O] *)

(** An observation model [O] maps an execution to whatever trace the observer
    can see. [is_OND O o] says: fixing the public input, the observed trace is
    constant across every pair of secrets — the observer learns nothing about
    the secret. *)
Definition is_OND {Obs : Type} (O : Exec -> Obs) (o : Op) : Prop :=
  forall (s1 s2 pub : nat), O (run o s1 pub) = O (run o s2 pub).

(** Three canonical, concrete observation models. *)
Definition O_out  (e : Exec) : nat := ex_out e.
Definition O_time (e : Exec) : nat := ex_time e.
Definition O_all  (e : Exec) : nat * nat := (ex_out e, ex_time e).

(** The CNO-analogue at the operation level: a *null* operation preserves
    state. This is the [is_CNO] notion (state identity) transported to [Op];
    the bridge to the core [is_CNO] over [Program] is made explicit below. *)
Definition is_null (o : Op) : Prop :=
  forall m, mem_eq (op_step o m) m.

(** ** Canonical operations (witnesses) *)

(** The empty / skip operation: no effect, constant (zero) time. *)
Definition skip_op : Op := mkOp (fun m => m) (fun _ => 0).

(** A CERTIFIED NULL OP THAT LEAKS VIA TIMING. Its effect is the identity
    (so it is a genuine null op / CNO), but its running time equals the secret.
    This is the "constant-result early-exit whose iteration count tracks the
    secret" of the roadmap: unchanged state, data-dependent timing. It has NO
    counterpart in the pure-state core [Program] model — that is the honest
    reason the timing channel must be modelled explicitly. *)
Definition leaky_cno : Op := mkOp (fun m => m) (fun m => m secret_cell).

(** A STATE-CHANGING OP THAT DISCLOSES NOTHING. It overwrites the secret cell
    with a fixed constant (so it is NOT a null op), while its observable
    output and timing are constant. *)
Definition writer_op : Op := mkOp (fun m => mem_update m secret_cell 7) (fun _ => 1).

(** A real constant-time operation for the OND-4 template: copy the PUBLIC
    input to the OUTPUT channel in constant time. Output depends only on public
    data; timing is constant. *)
Definition ct_select : Op := mkOp (fun m => mem_update m output_cell (m public_cell)) (fun _ => 1).

(** ** OND-2 — Trivial-case satisfiability *)

(** The skip operation is OND under ANY observation model whatsoever, because
    its entire observable execution is secret-independent. This is the
    smoke-test that [is_OND] is non-vacuous / well-formed. *)
Theorem OND2_skip_is_OND :
  forall (Obs : Type) (O : Exec -> Obs), is_OND O skip_op.
Proof.
  intros Obs O s1 s2 pub.
  (* run skip_op s pub = mkExec 0 0, independent of s. *)
  unfold is_OND, run, skip_op; simpl.
  reflexivity.
Qed.

(** ** OND-3 — CNO ⊥ OND independence *)

(** Direction 1: a null op (CNO) that is NOT OND — [leaky_cno] preserves state
    but its timing channel reveals the secret. *)
Lemma leaky_cno_is_null : is_null leaky_cno.
Proof. intros m a. reflexivity. Qed.

Lemma leaky_cno_not_OND_time : ~ is_OND O_time leaky_cno.
Proof.
  intros H.
  (* is_OND would force time on secret 0 to equal time on secret 1. *)
  specialize (H 0 1 0).
  unfold O_time, run, leaky_cno in H; simpl in H.
  (* H : 0 = 1 *)
  discriminate H.
Qed.

(** Direction 2: an OND op that is NOT a null op — [writer_op] changes state
    but discloses nothing on (output, timing). *)
Lemma writer_is_OND_all : is_OND O_all writer_op.
Proof.
  intros s1 s2 pub.
  unfold O_all, run, writer_op; simpl.
  (* output cell 2 is untouched by an update to cell 0, so out = 0; time = 1. *)
  reflexivity.
Qed.

Lemma writer_not_null : ~ is_null writer_op.
Proof.
  intros H.
  specialize (H (fun _ => 0) secret_cell).
  unfold writer_op, mem_update in H; simpl in H.
  (* H : 7 = 0 *)
  discriminate H.
Qed.

(** The headline theorem: the two pillars are logically independent. Neither
    [is_null] (the CNO notion) nor [is_OND O] entails the other. *)
Theorem OND3_cno_ond_independent :
  (exists o, is_null o /\ ~ is_OND O_time o) /\
  (exists o, is_OND O_all o /\ ~ is_null o).
Proof.
  split.
  - exists leaky_cno. split.
    + apply leaky_cno_is_null.
    + apply leaky_cno_not_OND_time.
  - exists writer_op. split.
    + apply writer_is_OND_all.
    + apply writer_not_null.
Qed.

(** *** Bridge to the core [is_CNO] over [Program] *)

(** The [is_null] predicate is the operation-level image of the core
    state-preservation notion. We anchor the independence to the *actual*
    core [is_CNO] on real [Program]s in both honest directions.

    OND ∧ ¬CNO, at the core level: a program that stores a register into a
    memory cell genuinely changes state, so it is not a core CNO — witnessing
    the second independence direction against the real [is_CNO]. *)
Theorem writer_program_not_core_CNO : ~ is_CNO [Store secret_cell 0].
Proof.
  intros Hcno.
  destruct Hcno as [_ [Hid _]].
  (* Choose a state whose register 0 holds 5 and whose memory cell 0 holds 0.
     The Store writes 5 into cell 0, so the resulting state differs. *)
  set (s0 := mkState (fun _ => 0) [5] [] 0).
  set (s1 := mkState (mem_update (fun _ => 0) secret_cell 5) [5] [] 1).
  assert (Heval : eval [Store secret_cell 0] s0 s1).
  { eapply eval_step.
    - eapply step_store. simpl. reflexivity.
    - apply eval_empty. }
  specialize (Hid s0 s1 Heval).
  destruct Hid as [Hmem _].
  unfold mem_eq in Hmem.
  specialize (Hmem secret_cell).
  unfold s0, s1, mem_update in Hmem; simpl in Hmem.
  (* Hmem : 0 = 5 *)
  discriminate Hmem.
Qed.

(** CNO ∧ ¬OND, honestly stated: the empty program IS a core CNO
    ([empty_is_cno]) and its operation image [skip_op] is a null op; the
    leak witness [leaky_cno] shows that adding a timing observation to a
    state-identity operation breaks OND. The core [Program] model, having no
    timing channel, cannot express [leaky_cno] — which is precisely why the
    disclosure pillar needs its own observable-execution model. *)
Theorem skip_program_is_core_CNO : is_CNO [].
Proof. exact empty_is_cno. Qed.

Lemma skip_op_is_null : is_null skip_op.
Proof. intros m a. reflexivity. Qed.

(** ** OND-4 — Conditional template for one real operation *)

(** For the concrete constant-time operation [ct_select] we prove [is_OND]
    under the explicitly declared observation model [O_all] = (output, timing).
    The CONSEQUENT is proved here; the ANTECEDENT — that real hardware exposes
    only [O_all] and nothing else — is the operation's METAL-DISCHARGED
    obligation, enumerated in its residue list (see docs/OND-PILLAR-STRUCTURE
    and proofs/residue), NOT proved in Coq. *)
Theorem OND4_ct_select_is_OND_all : is_OND O_all ct_select.
Proof.
  intros s1 s2 pub.
  unfold O_all, run, ct_select; simpl.
  (* output = public input (cell 1); timing = 1; both secret-independent. *)
  reflexivity.
Qed.

(** The declared observation model for [ct_select] is [O_all]. Its residue
    list (channels OUTSIDE O_all, hence NOT covered by the theorem above) is:
    power draw, electromagnetic emanation, data/instruction cache residency,
    DRAM row-buffer timing, speculative-execution side effects, and micro-
    architectural port contention. See proofs/residue/ct_select.residue. *)

(** ** OND-5 — Non-composition counterexample *)

(** Sequential composition: run [o1] then [o2]. The composite's effect is the
    functional composite of the effects; its time is the sum. *)
Definition seq_op (o1 o2 : Op) : Op :=
  mkOp (fun m => op_step o2 (op_step o1 m))
       (fun m => op_time o1 m + op_time o2 (op_step o1 m)).

(** [p_op]: copy the secret cell into the (public) intermediate cell 1. Its own
    declared output (cell 2) and timing are constant, so it is OND. *)
Definition p_op : Op := mkOp (fun m => mem_update m public_cell (m secret_cell)) (fun _ => 1).

(** [q_op]: copy the intermediate cell 1 into the output cell 2. Over q's OWN
    secret input (cell 0) its output depends only on cell 1 (public to q), so
    it too is OND. *)
Definition q_op : Op := mkOp (fun m => mem_update m output_cell (m public_cell)) (fun _ => 1).

Lemma p_op_is_OND_all : is_OND O_all p_op.
Proof.
  intros s1 s2 pub.
  unfold O_all, run, p_op; simpl.
  (* output cell 2 is untouched by writing cell 1; time = 1. Both constant. *)
  reflexivity.
Qed.

Lemma q_op_is_OND_all : is_OND O_all q_op.
Proof.
  intros s1 s2 pub.
  unfold O_all, run, q_op; simpl.
  (* output cell 2 := cell 1 = public input; independent of the secret cell. *)
  reflexivity.
Qed.

(** Yet the composite p;q leaks the secret onto the output channel: p folds the
    secret into cell 1, which q — treating cell 1 as public — copies to the
    observed output. Neither operation is at fault alone; the leak is created
    by the state-chaining hand-off. This is the roadmap's mechanism (1). *)
Theorem OND5_composition_leaks : ~ is_OND O_all (seq_op p_op q_op).
Proof.
  intros H.
  specialize (H 0 1 0).
  unfold O_all, run, seq_op, p_op, q_op, mem_update in H; simpl in H.
  (* out(comp,secret=0) = 0, out(comp,secret=1) = 1: (0,_) = (1,_) is absurd. *)
  inversion H.
Qed.

(** Both parts are individually OND under [O_all], but their composite is not:
    observational nullity does NOT compose cleanly (unlike CNO's clean
    composition, [CNO.cno_composition]). The negative result is first-class. *)
Theorem OND5_non_composition :
  is_OND O_all p_op /\ is_OND O_all q_op /\ ~ is_OND O_all (seq_op p_op q_op).
Proof.
  split; [ apply p_op_is_OND_all | split ].
  - apply q_op_is_OND_all.
  - apply OND5_composition_leaks.
Qed.
