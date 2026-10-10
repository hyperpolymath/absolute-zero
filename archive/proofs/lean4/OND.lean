/- Observational Null Operations (OND): The Disclosure Pillar — Lean 4

   Second pillar of Absolute Zero. Mirrors proofs/coq/ond/OND.v: a CNO leaves
   all STATE observables unchanged, so it can leak only through a non-state
   channel (timing). Hence the observation model carries a `time` component the
   pure-state CNO model lacks — which is exactly why the two pillars are
   independent (OND-3). Discharges OND-1..5 with zero axioms (core Lean only).

   Author: Jonathan D. A. Jewell
   Project: Absolute Zero
   License: MPL-2.0
-/

namespace OND

/-! ## Memory, inputs, and the secret/public split -/

abbrev Memory : Type := Nat → Nat

def Memory.update (m : Memory) (addr val : Nat) : Memory :=
  fun a => if a == addr then val else m a

def secret_cell : Nat := 0
def public_cell : Nat := 1
def output_cell : Nat := 2

/-- Inject (secret, public) into an initial memory; output cell and the rest
    start at the secret-independent constant 0. -/
def inj (s p : Nat) : Memory :=
  fun a => match a with
           | 0 => s
           | 1 => p
           | _ => 0

/-! ## Operations and their observable executions -/

structure Op where
  step : Memory → Memory
  time : Memory → Nat

/-- What an observer sees of one run: the declared output-channel value and the
    elapsed time — NOT the raw input memory. -/
structure Exec where
  out : Nat
  time : Nat

def run (o : Op) (s p : Nat) : Exec :=
  ⟨o.step (inj s p) output_cell, o.time (inj s p)⟩

/-! ## OND-1 — the definition, parameterised by an observation model -/

def is_OND {Obs : Type} (O : Exec → Obs) (o : Op) : Prop :=
  ∀ s1 s2 pub : Nat, O (run o s1 pub) = O (run o s2 pub)

def O_out  (e : Exec) : Nat := e.out
def O_time (e : Exec) : Nat := e.time
def O_all  (e : Exec) : Nat × Nat := (e.out, e.time)

/-- CNO-analogue at the operation level: state preservation. -/
def is_null (o : Op) : Prop := ∀ m : Memory, ∀ a : Nat, o.step m a = m a

/-! ## Witnesses -/

def skip_op   : Op := ⟨fun m => m, fun _ => 0⟩
def leaky_cno : Op := ⟨fun m => m, fun m => m secret_cell⟩          -- null, but time = secret
def writer_op : Op := ⟨fun m => Memory.update m secret_cell 7, fun _ => 1⟩
def ct_select : Op := ⟨fun m => Memory.update m output_cell (m public_cell), fun _ => 1⟩
def p_op      : Op := ⟨fun m => Memory.update m public_cell (m secret_cell), fun _ => 1⟩
def q_op      : Op := ⟨fun m => Memory.update m output_cell (m public_cell), fun _ => 1⟩

def seq_op (o1 o2 : Op) : Op :=
  ⟨fun m => o2.step (o1.step m), fun m => o1.time m + o2.time (o1.step m)⟩

/-! ## OND-2 — trivial-case satisfiability (skip is OND under ANY model) -/

theorem OND2_skip_is_OND {Obs : Type} (O : Exec → Obs) : is_OND O skip_op := by
  intro s1 s2 pub; rfl

/-! ## OND-3 — CNO ⊥ OND independence -/

theorem leaky_cno_is_null : is_null leaky_cno := by
  intro m a; rfl

theorem leaky_cno_not_OND_time : ¬ is_OND O_time leaky_cno := by
  intro h; exact absurd (h 0 1 0) (by decide)

theorem writer_is_OND_all : is_OND O_all writer_op := by
  intro s1 s2 pub; rfl

theorem writer_not_null : ¬ is_null writer_op := by
  intro h; exact absurd (h (fun _ => 0) 0) (by decide)

/-- The two pillars are logically independent. -/
theorem OND3_cno_ond_independent :
    (∃ o, is_null o ∧ ¬ is_OND O_time o) ∧
    (∃ o, is_OND O_all o ∧ ¬ is_null o) := by
  refine ⟨⟨leaky_cno, leaky_cno_is_null, leaky_cno_not_OND_time⟩,
          ⟨writer_op, writer_is_OND_all, writer_not_null⟩⟩

/-! ## OND-4 — conditional template for one real constant-time operation -/

theorem OND4_ct_select_is_OND_all : is_OND O_all ct_select := by
  intro s1 s2 pub; rfl
-- Declared O = O_all; residue list in proofs/residue/ct_select.residue.

/-! ## OND-5 — non-composition counterexample -/

theorem p_op_is_OND_all : is_OND O_all p_op := by
  intro s1 s2 pub; rfl

theorem q_op_is_OND_all : is_OND O_all q_op := by
  intro s1 s2 pub; rfl

theorem OND5_composition_leaks : ¬ is_OND O_all (seq_op p_op q_op) := by
  intro h; exact absurd (h 0 1 0) (by decide)

theorem OND5_non_composition :
    is_OND O_all p_op ∧ is_OND O_all q_op ∧ ¬ is_OND O_all (seq_op p_op q_op) :=
  ⟨p_op_is_OND_all, q_op_is_OND_all, OND5_composition_leaks⟩

end OND
