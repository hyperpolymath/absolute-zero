theory OND
  imports Main
begin

section \<open>Observational Null Operations (OND): The Disclosure Pillar\<close>

text \<open>
  This theory formalises the SECOND pillar of Absolute Zero: Observational
  Null Disclosure. Where a Certified Null Operation (CNO, see @{file "CNO.thy"})
  certifies that an operation does \<^emph>\<open>nothing to the world\<close> (state identity),
  an Observational Null Operation certifies that an operation \<^emph>\<open>reveals nothing
  about its secret input\<close> to a declared observation model \<open>O\<close>.

  The two pillars are siblings of equal weight, not parent and extension. This
  module discharges roadmap obligations OND-1 .. OND-5 with real, machine-checked
  proofs and ZERO axioms (no \<open>sorry\<close>, no \<open>oops\<close>, no \<open>axiomatization\<close>). It is a
  faithful port of proofs/coq/ond/OND.v.

  THE LOAD-BEARING DESIGN DECISION (OND-1).
  A CNO leaves \<^emph>\<open>all state observables\<close> unchanged, so anything an observer
  reconstructs purely from final state is automatically secret-independent
  whenever the output channel starts secret-independent. Consequently a CNO can
  leak \<^emph>\<open>only\<close> through a channel that is NOT a function of state — timing,
  energy, EM. That is exactly why the observation model here carries a \<open>tm\<close>
  (timing) component the pure-state CNO model deliberately lacks, and exactly why
  the two pillars are logically independent (OND-3). The observer sees the
  produced execution (\<open>out\<close> on a declared output channel, plus \<open>tm\<close>), NOT the raw
  secret input — so the empty operation is OND under \<^emph>\<open>any\<close> model (OND-2).

  Author: Jonathan D. A. Jewell
  Project: Absolute Zero
  License: MPL-2.0
\<close>

subsection \<open>Memory, inputs, and the secret/public split\<close>

text \<open>
  This theory is self-contained (imports @{theory Main} only). Memory is the
  same core model used by the CNO development — a total function from
  addresses to values. By convention cell 0 holds the SECRET input, cell 1 the
  PUBLIC input, and cell 2 is the declared OUTPUT channel (initialised to 0).
\<close>

type_synonym memory = "nat \<Rightarrow> nat"

definition mem_update :: "memory \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory" where
  "mem_update m addr val = (\<lambda>a. if a = addr then val else m a)"

definition mem_eq :: "memory \<Rightarrow> memory \<Rightarrow> bool" where
  "mem_eq m1 m2 = (\<forall>a. m1 a = m2 a)"

definition secret_cell :: nat where "secret_cell = 0"
definition public_cell :: nat where "public_cell = 1"
definition output_cell :: nat where "output_cell = 2"

text \<open>Inject a \<open>(secret, public)\<close> pair into an initial memory. The output cell
  and all other cells start at the secret-independent constant 0.\<close>
definition inj_mem :: "nat \<Rightarrow> nat \<Rightarrow> memory" where
  "inj_mem s p = (\<lambda>a. if a = secret_cell then s
                      else if a = public_cell then p else 0)"

lemma inj_secret: "inj_mem s p secret_cell = s"
  by (simp add: inj_mem_def)
lemma inj_public: "inj_mem s p public_cell = p"
  by (simp add: inj_mem_def secret_cell_def public_cell_def)
lemma inj_output: "inj_mem s p output_cell = 0"
  by (simp add: inj_mem_def secret_cell_def public_cell_def output_cell_def)

subsection \<open>Operations and their observable executions\<close>

text \<open>An operation has a semantic effect on memory (\<open>op_step\<close>) and an observable
  timing cost (\<open>op_time\<close>) that may itself depend on memory (this is the channel
  a CNO can leak through).\<close>
record Op =
  op_step :: "memory \<Rightarrow> memory"
  op_time :: "memory \<Rightarrow> nat"

text \<open>What an observer can actually see of one run: the value on the declared
  output channel and the elapsed time. Crucially it does NOT expose the raw
  input memory, so the observer cannot read the secret cell directly.\<close>
record Exec =
  ex_out :: nat
  ex_time :: nat

text \<open>Run an operation on an injected \<open>(secret, public)\<close> input.\<close>
definition run :: "Op \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Exec" where
  "run opr s p = \<lparr> ex_out = op_step opr (inj_mem s p) output_cell,
                   ex_time = op_time opr (inj_mem s p) \<rparr>"

subsection \<open>OND-1 — The definition, parameterised by an observation model\<close>

text \<open>An observation model \<open>M\<close> maps an execution to whatever trace the observer
  can see. \<open>is_OND M opr\<close> says: fixing the public input, the observed trace is
  constant across every pair of secrets — the observer learns nothing about the
  secret.\<close>
definition is_OND :: "(Exec \<Rightarrow> 'obs) \<Rightarrow> Op \<Rightarrow> bool" where
  "is_OND M opr = (\<forall>s1 s2 pub. M (run opr s1 pub) = M (run opr s2 pub))"

text \<open>Three canonical, concrete observation models.\<close>
definition O_out  :: "Exec \<Rightarrow> nat" where "O_out e = ex_out e"
definition O_time :: "Exec \<Rightarrow> nat" where "O_time e = ex_time e"
definition O_all  :: "Exec \<Rightarrow> nat \<times> nat" where "O_all e = (ex_out e, ex_time e)"

text \<open>The CNO-analogue at the operation level: a \<^emph>\<open>null\<close> operation preserves
  state. This is the \<open>is_CNO\<close> notion (state identity) transported to \<open>Op\<close>.\<close>
definition is_null :: "Op \<Rightarrow> bool" where
  "is_null opr = (\<forall>m. mem_eq (op_step opr m) m)"

subsection \<open>Canonical operations (witnesses)\<close>

text \<open>The empty / skip operation: no effect, constant (zero) time.\<close>
definition skip_op :: Op where
  "skip_op = \<lparr> op_step = (\<lambda>m. m), op_time = (\<lambda>_. 0) \<rparr>"

text \<open>A CERTIFIED NULL OP THAT LEAKS VIA TIMING. Its effect is the identity (so
  it is a genuine null op / CNO), but its running time equals the secret. This
  is the "constant-result early-exit whose iteration count tracks the secret" of
  the roadmap: unchanged state, data-dependent timing. It has NO counterpart in
  the pure-state core \<open>Program\<close> model — the honest reason the timing channel
  must be modelled explicitly.\<close>
definition leaky_cno :: Op where
  "leaky_cno = \<lparr> op_step = (\<lambda>m. m), op_time = (\<lambda>m. m secret_cell) \<rparr>"

text \<open>A STATE-CHANGING OP THAT DISCLOSES NOTHING. It overwrites the secret cell
  with a fixed constant (so it is NOT a null op), while its observable output and
  timing are constant.\<close>
definition writer_op :: Op where
  "writer_op = \<lparr> op_step = (\<lambda>m. mem_update m secret_cell 7), op_time = (\<lambda>_. 1) \<rparr>"

text \<open>A real constant-time operation for the OND-4 template: copy the PUBLIC
  input to the OUTPUT channel in constant time. Output depends only on public
  data; timing is constant.\<close>
definition ct_select :: Op where
  "ct_select = \<lparr> op_step = (\<lambda>m. mem_update m output_cell (m public_cell)),
                 op_time = (\<lambda>_. 1) \<rparr>"

subsection \<open>OND-2 — Trivial-case satisfiability\<close>

text \<open>The skip operation is OND under ANY observation model whatsoever, because
  its entire observable execution is secret-independent. This is the smoke-test
  that \<open>is_OND\<close> is non-vacuous / well-formed. The free \<open>M :: Exec \<Rightarrow> 'obs\<close> is the
  Isabelle idiom for "for any observation model".\<close>
theorem OND2_skip_is_OND: "is_OND (M :: Exec \<Rightarrow> 'obs) skip_op"
  by (simp add: is_OND_def run_def skip_op_def inj_mem_def
                secret_cell_def public_cell_def output_cell_def)

subsection \<open>OND-3 — CNO \<open>\<bottom>\<close> OND independence\<close>

text \<open>Direction 1: a null op (CNO) that is NOT OND — \<open>leaky_cno\<close> preserves state
  but its timing channel reveals the secret.\<close>
lemma leaky_cno_is_null: "is_null leaky_cno"
  by (simp add: is_null_def leaky_cno_def mem_eq_def)

lemma leaky_cno_not_OND_time: "\<not> is_OND O_time leaky_cno"
proof
  assume "is_OND O_time leaky_cno"
  \<comment> \<open>\<open>is_OND\<close> would force the time on secret 0 to equal the time on secret 1.\<close>
  then have "O_time (run leaky_cno 0 0) = O_time (run leaky_cno (Suc 0) 0)"
    unfolding is_OND_def by blast
  then show False
    by (simp add: O_time_def run_def leaky_cno_def inj_mem_def secret_cell_def)
qed

text \<open>Direction 2: an OND op that is NOT a null op — \<open>writer_op\<close> changes state but
  discloses nothing on \<open>(output, timing)\<close>.\<close>
lemma writer_is_OND_all: "is_OND O_all writer_op"
  \<comment> \<open>output cell 2 is untouched by an update to cell 0, so \<open>out = 0\<close>; \<open>time = 1\<close>.\<close>
  by (simp add: is_OND_def O_all_def run_def writer_op_def inj_mem_def
                mem_update_def secret_cell_def public_cell_def output_cell_def)

lemma writer_not_null: "\<not> is_null writer_op"
proof
  assume "is_null writer_op"
  then have "mem_eq (op_step writer_op (\<lambda>_. 0)) (\<lambda>_. 0)"
    unfolding is_null_def by blast
  then have "op_step writer_op (\<lambda>_. 0) secret_cell = (\<lambda>_. 0) secret_cell"
    unfolding mem_eq_def by blast
  \<comment> \<open>The \<open>writer_op\<close> puts 7 into the secret cell, contradicting the 0 there.\<close>
  then show False
    by (simp add: writer_op_def mem_update_def secret_cell_def)
qed

text \<open>The headline theorem: the two pillars are logically independent. Neither
  \<open>is_null\<close> (the CNO notion) nor \<open>is_OND M\<close> entails the other.\<close>
theorem OND3_cno_ond_independent:
  "(\<exists>opr. is_null opr \<and> \<not> is_OND O_time opr) \<and>
   (\<exists>opr. is_OND O_all opr \<and> \<not> is_null opr)"
proof
  show "\<exists>opr. is_null opr \<and> \<not> is_OND O_time opr"
    using leaky_cno_is_null leaky_cno_not_OND_time by blast
next
  show "\<exists>opr. is_OND O_all opr \<and> \<not> is_null opr"
    using writer_is_OND_all writer_not_null by blast
qed

text \<open>The skip operation image is a null op, anchoring the CNO side of the split.\<close>
lemma skip_op_is_null: "is_null skip_op"
  by (simp add: is_null_def skip_op_def mem_eq_def)

subsection \<open>OND-4 — Conditional template for one real operation\<close>

text \<open>For the concrete constant-time operation \<open>ct_select\<close> we prove \<open>is_OND\<close>
  under the explicitly declared observation model \<open>O_all = (output, timing)\<close>.
  The CONSEQUENT is proved here; the ANTECEDENT — that real hardware exposes only
  \<open>O_all\<close> and nothing else — is the operation's METAL-DISCHARGED obligation,
  enumerated in its residue list (see proofs/residue), NOT proved in Isabelle.\<close>
theorem OND4_ct_select_is_OND_all: "is_OND O_all ct_select"
  \<comment> \<open>output = public input (cell 1); timing = 1; both secret-independent.\<close>
  by (simp add: is_OND_def O_all_def run_def ct_select_def inj_mem_def
                mem_update_def secret_cell_def public_cell_def output_cell_def)

subsection \<open>OND-5 — Non-composition counterexample\<close>

text \<open>Sequential composition: run \<open>o1\<close> then \<open>o2\<close>. The composite's effect is the
  functional composite of the effects; its time is the sum.\<close>
definition seq_op :: "Op \<Rightarrow> Op \<Rightarrow> Op" where
  "seq_op o1 o2 =
     \<lparr> op_step = (\<lambda>m. op_step o2 (op_step o1 m)),
       op_time = (\<lambda>m. op_time o1 m + op_time o2 (op_step o1 m)) \<rparr>"

text \<open>\<open>p_op\<close>: copy the secret cell into the (public) intermediate cell 1. Its own
  declared output (cell 2) and timing are constant, so it is OND.\<close>
definition p_op :: Op where
  "p_op = \<lparr> op_step = (\<lambda>m. mem_update m public_cell (m secret_cell)),
            op_time = (\<lambda>_. 1) \<rparr>"

text \<open>\<open>q_op\<close>: copy the intermediate cell 1 into the output cell 2. Over q's OWN
  secret input (cell 0) its output depends only on cell 1 (public to q), so it
  too is OND.\<close>
definition q_op :: Op where
  "q_op = \<lparr> op_step = (\<lambda>m. mem_update m output_cell (m public_cell)),
            op_time = (\<lambda>_. 1) \<rparr>"

lemma p_op_is_OND_all: "is_OND O_all p_op"
  \<comment> \<open>output cell 2 is untouched by writing cell 1; time = 1. Both constant.\<close>
  by (simp add: is_OND_def O_all_def run_def p_op_def inj_mem_def
                mem_update_def secret_cell_def public_cell_def output_cell_def)

lemma q_op_is_OND_all: "is_OND O_all q_op"
  \<comment> \<open>output cell 2 := cell 1 = public input; independent of the secret cell.\<close>
  by (simp add: is_OND_def O_all_def run_def q_op_def inj_mem_def
                mem_update_def secret_cell_def public_cell_def output_cell_def)

text \<open>Yet the composite \<open>p;q\<close> leaks the secret onto the output channel: p folds
  the secret into cell 1, which q — treating cell 1 as public — copies to the
  observed output. Neither operation is at fault alone; the leak is created by
  the state-chaining hand-off.\<close>
theorem OND5_composition_leaks: "\<not> is_OND O_all (seq_op p_op q_op)"
proof
  assume "is_OND O_all (seq_op p_op q_op)"
  then have "O_all (run (seq_op p_op q_op) 0 0)
           = O_all (run (seq_op p_op q_op) (Suc 0) 0)"
    unfolding is_OND_def by blast
  \<comment> \<open>\<open>out(comp, secret=0) = 0\<close> but \<open>out(comp, secret=1) = 1\<close>: absurd.\<close>
  then show False
    by (simp add: O_all_def run_def seq_op_def p_op_def q_op_def inj_mem_def
                  mem_update_def secret_cell_def public_cell_def output_cell_def)
qed

text \<open>Both parts are individually OND under \<open>O_all\<close>, but their composite is not:
  observational nullity does NOT compose cleanly (unlike CNO's clean composition,
  \<open>CNO.cno_composition\<close>). The negative result is first-class.\<close>
theorem OND5_non_composition:
  "is_OND O_all p_op \<and> is_OND O_all q_op \<and> \<not> is_OND O_all (seq_op p_op q_op)"
  using p_op_is_OND_all q_op_is_OND_all OND5_composition_leaks by blast

end
