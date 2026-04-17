/- CNOs in Lambda Calculus

   Proves that CNO theory applies to lambda calculus,
   showing the identity function (λx.x) is the canonical CNO.

   Demonstrates model-independence of CNO theory.

   Author: Jonathan D. A. Jewell
   Project: Absolute Zero
   License: AGPL-3.0 / Palimpsest 0.5
-/

namespace LambdaCNO

/-! ## Lambda Calculus Syntax -/

/-- Variables are de Bruijn indices -/
inductive LambdaTerm where
  | LVar : Nat → LambdaTerm
  | LApp : LambdaTerm → LambdaTerm → LambdaTerm
  | LAbs : LambdaTerm → LambdaTerm
  deriving Repr, BEq

open LambdaTerm

/-! ## Substitution -/

/-- Substitute term s for variable n in term t -/
def subst (n : Nat) (s : LambdaTerm) (t : LambdaTerm) : LambdaTerm :=
  match t with
  | LVar m => if n == m then s else LVar m
  | LApp t1 t2 => LApp (subst n s t1) (subst n s t2)
  | LAbs body => LAbs (subst (n + 1) s body)

/-! ## Beta Reduction -/

/-- One-step beta reduction -/
inductive BetaReduce : LambdaTerm → LambdaTerm → Prop where
  | beta_app :
      ∀ body arg,
        BetaReduce (LApp (LAbs body) arg) (subst 0 arg body)

  | beta_app_left :
      ∀ t1 t1' t2,
        BetaReduce t1 t1' →
        BetaReduce (LApp t1 t2) (LApp t1' t2)

  | beta_app_right :
      ∀ t1 t2 t2',
        BetaReduce t2 t2' →
        BetaReduce (LApp t1 t2) (LApp t1 t2')

  | beta_abs :
      ∀ body body',
        BetaReduce body body' →
        BetaReduce (LAbs body) (LAbs body')

/-- Multi-step beta reduction (reflexive transitive closure) -/
inductive BetaReduceStar : LambdaTerm → LambdaTerm → Prop where
  | beta_refl :
      ∀ t,
        BetaReduceStar t t

  | beta_step :
      ∀ t1 t2 t3,
        BetaReduce t1 t2 →
        BetaReduceStar t2 t3 →
        BetaReduceStar t1 t3

/-! ## Normal Forms -/

/-- A term is in normal form if no beta reduction is possible -/
def isNormalForm (t : LambdaTerm) : Prop :=
  ¬ ∃ t', BetaReduce t t'

/-- Evaluation: reduce to normal form -/
def evaluatesTo (t : LambdaTerm) (nf : LambdaTerm) : Prop :=
  BetaReduceStar t nf ∧ isNormalForm nf

/-! ## The Identity Function -/

/-- λx.x - The canonical CNO in lambda calculus -/
def lambda_id : LambdaTerm := LAbs (LVar 0)

/-! ## CNO Definition for Lambda Calculus -/

/-- A lambda term is a CNO if:
    1. It terminates (reaches a normal form)
    2. It acts as identity (for all arguments)
    3. No side effects (lambda calculus is pure by construction)
-/
def isLambdaCNO (t : LambdaTerm) : Prop :=
  ∀ arg : LambdaTerm,
    (∃ nf, evaluatesTo (LApp t arg) nf) ∧
    BetaReduceStar (LApp t arg) arg

/-! ## Main Theorem: Identity is a CNO -/

/-- Identity is a (lambda) CNO.

    Partially proved: the β-reduction `(λx.x) arg →* arg` IS closed
    cleanly. What remains as `sorry` is the `isNormalForm arg` conjunct
    embedded in `evaluatesTo`.

    DEFERRED — spec gap, not a proof gap. `isLambdaCNO` (line 92)
    requires there *exists* a normal form `nf` of `LApp t arg`. For an
    arbitrary `arg` this is false (e.g. `(λx.x)((λy.y)z)` is reachable
    but not in normal form). The spec needs ONE of:
      (a) Add an `arg`-is-value (or `isNormalForm arg`) hypothesis
          inside the universal quantifier in `isLambdaCNO`; OR
      (b) Drop `isNormalForm nf` from `evaluatesTo`; OR
      (c) Restrict `isLambdaCNO` to quantify only over normal-form args.
    Each choice changes downstream theorems. Defer to user. -/
theorem lambda_id_is_cno : isLambdaCNO lambda_id := by
  unfold isLambdaCNO lambda_id
  intro arg
  constructor
  · -- Terminates
    exists arg
    unfold evaluatesTo
    constructor
    · -- (λx.x) arg →* arg — provable directly.
      apply BetaReduceStar.beta_step
      · apply BetaReduce.beta_app
      · unfold subst
        simp
        apply BetaReduceStar.beta_refl
    · -- DEFERRED — `isNormalForm arg` requires arg-is-value spec change.
      sorry

  · -- Identity: same single β-step as above.
    apply BetaReduceStar.beta_step
    · apply BetaReduce.beta_app
    · unfold subst
      simp
      apply BetaReduceStar.beta_refl

/-! ## Composition Theorem -/

/-- Composing two lambda CNOs yields a CNO -/
def lambda_compose (f g : LambdaTerm) : LambdaTerm :=
  LAbs (LApp f (LApp g (LVar 0)))

/-- Composing two lambda CNOs yields a CNO.

    DEFERRED (×2) — spec gap. `isLambdaCNO f` only tells us that
    `(LApp f arg) →* arg` for any `arg` — that "applying `f` returns
    its argument back". It does NOT tell us `f = LAbs body`, so we
    cannot pattern-match on `f` to perform the outer β-reduction of
    `(λx. f (g x)) arg`. To close: ONE of
      (a) `isLambdaCNO` should require `t = LAbs _` (rule out
          non-abstraction "CNOs"); OR
      (b) Add a value/normal-form hypothesis on `f`/`g`; OR
      (c) Reformulate via the η-equivalence axiom on the outer LAbs.
    The first sorry also inherits the arg-is-value gap from
    `lambda_id_is_cno`. Defer to user. -/
theorem lambda_cno_composition (f g : LambdaTerm) :
    isLambdaCNO f →
    isLambdaCNO g →
    isLambdaCNO (lambda_compose f g) := by
  intro hf hg
  unfold isLambdaCNO at *
  intro arg
  constructor
  · -- DEFERRED — same arg-is-value gap as `lambda_id_is_cno`.
    sorry
  · -- DEFERRED — requires `f`/`g` to be syntactic abstractions.
    sorry

/-! ## Non-CNO Examples -/

/-- The Y combinator enables recursion -/
def y_combinator : LambdaTerm :=
  LAbs (LApp
    (LAbs (LApp (LVar 1) (LApp (LVar 0) (LVar 0))))
    (LAbs (LApp (LVar 1) (LApp (LVar 0) (LVar 0)))))

/-- Y is NOT a CNO because it doesn't terminate.

    DEFERRED — Lean's `BetaReduceStar` is *inductive* (only finite
    sequences), so "no normal form exists for Y" is a metatheoretic
    claim that cannot be discharged via the existing reduction
    relation. To close: ONE of
      (a) Add an axiom: `axiom y_combinator_no_normal_form :
          ¬ ∃ nf, evaluatesTo (LApp y_combinator lambda_id) nf` and
          contradict `h_eval` with it (cheapest; matches the file's
          existing axiom-heavy style — cf. `eta_equivalence`);
      (b) Switch `BetaReduceStar` to coinductive and prove divergence
          via that; OR
      (c) Build a strong-normalization framework and show Y is not SN.
    Defer to user. -/
theorem y_not_cno : ¬ isLambdaCNO y_combinator := by
  unfold isLambdaCNO y_combinator
  intro h
  have := h lambda_id
  obtain ⟨⟨_nf, _h_eval⟩, _⟩ := this
  sorry

/-! ## Church Encodings -/

/-- Church encoding of zero: λf.λx.x -/
def church_zero : LambdaTerm :=
  LAbs (LAbs (LVar 0))

/-- Church encoding β-reduces to the identity when applied to itself.

    Spec correction: the original example claimed
    `(λf.λx.x)(λf.λx.x) →* λf.λx.x` (back to `church_zero`). That is
    *false*: β-reducing `(LAbs (LAbs (LVar 0))) (LAbs (LAbs (LVar 0)))`
    substitutes the second copy for `f` in `LAbs (LVar 0)`, but `f`
    (= de Bruijn 1 inside the inner LAbs) does not occur, so the
    result is `LAbs (LVar 0)` = `lambda_id`, *not* `church_zero`.
    Restating to the correct target makes the example provable in one
    β-step. -/
example : BetaReduceStar (LApp church_zero church_zero) lambda_id := by
  apply BetaReduceStar.beta_step _ lambda_id
  · -- (LAbs (LAbs (LVar 0))) (LAbs (LAbs (LVar 0))) →β subst 0 _ (LAbs (LVar 0))
    --                                              = LAbs (LVar 0) = lambda_id
    exact BetaReduce.beta_app (LAbs (LVar 0)) church_zero
  · exact BetaReduceStar.beta_refl lambda_id

/-! ## Eta Equivalence -/

/-- Eta reduction: (λx. f x) ≡ f -/
axiom eta_equivalence (f : LambdaTerm) :
  BetaReduceStar (LAbs (LApp f (LVar 0))) f

/-- Eta-expanded identity is also a CNO.

    DEFERRED — pre-existing build break under v4.16.0. The original walk
    of two β-reductions hit `simp made no progress` on
    `if 0 == 0 then arg else LVar 0`; the right rewrite is
    `Nat.beq_self`/`decide` plus a careful `change`/`rfl` to thread the
    substitution. Folded into the broader LambdaCNO spec rework (the
    termination conjunct also needs an `arg`-is-value hypothesis on
    `isLambdaCNO`, which the current spec lacks). -/
theorem eta_expanded_id_is_cno :
    isLambdaCNO (LAbs (LApp lambda_id (LVar 0))) := by
  sorry

end LambdaCNO
