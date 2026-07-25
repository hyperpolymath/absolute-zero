{-# OPTIONS --safe --without-K #-}

{- Observational Null Operations (OND): The Disclosure Pillar — Agda

   Second pillar of Absolute Zero. Mirrors proofs/coq/ond/OND.v and
   proofs/lean4/OND.lean. A CNO leaves all STATE observables unchanged, so it
   can leak only through a non-state channel (timing); hence the observation
   model carries a `time` component, and the two pillars are independent
   (OND-3). Discharges OND-1..5 with zero postulates.

   Author: Jonathan D. A. Jewell
   Project: Absolute Zero
   License: MPL-2.0
-}

module OND where

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Memory, inputs, and the secret/public split -----------------------------

Memory : Set
Memory = ℕ → ℕ

update : Memory → ℕ → ℕ → Memory
update m addr val = λ a → if (a ≡ᵇ addr) then val else m a

secret-cell public-cell output-cell : ℕ
secret-cell = 0
public-cell = 1
output-cell = 2

-- Inject (secret, public); output cell and rest start at 0.
inj : ℕ → ℕ → Memory
inj s p zero          = s
inj s p (suc zero)    = p
inj s p (suc (suc _)) = 0

-- Operations and observable executions ------------------------------------

record Op : Set where
  constructor mkOp
  field
    step : Memory → Memory
    time : Memory → ℕ
open Op

record Exec : Set where
  constructor mkExec
  field
    out  : ℕ
    time : ℕ
open Exec

run : Op → ℕ → ℕ → Exec
run o s p = mkExec (step o (inj s p) output-cell) (time o (inj s p))

-- OND-1 — the definition, parameterised by an observation model -----------

is-OND : {Obs : Set} → (Exec → Obs) → Op → Set
is-OND O o = ∀ (s1 s2 pub : ℕ) → O (run o s1 pub) ≡ O (run o s2 pub)

O-out : Exec → ℕ
O-out e = out e

O-time : Exec → ℕ
O-time e = Exec.time e

O-all : Exec → (ℕ × ℕ)
O-all e = (out e , Exec.time e)

-- CNO-analogue: state preservation.
is-null : Op → Set
is-null o = ∀ (m : Memory) (a : ℕ) → step o m a ≡ m a

-- Witnesses ---------------------------------------------------------------

skip-op   : Op
skip-op   = mkOp (λ m → m) (λ _ → 0)

leaky-cno : Op                                  -- null, but time = secret
leaky-cno = mkOp (λ m → m) (λ m → m secret-cell)

writer-op : Op
writer-op = mkOp (λ m → update m secret-cell 7) (λ _ → 1)

ct-select : Op
ct-select = mkOp (λ m → update m output-cell (m public-cell)) (λ _ → 1)

p-op : Op
p-op = mkOp (λ m → update m public-cell (m secret-cell)) (λ _ → 1)

q-op : Op
q-op = mkOp (λ m → update m output-cell (m public-cell)) (λ _ → 1)

seq-op : Op → Op → Op
seq-op o1 o2 = mkOp (λ m → step o2 (step o1 m))
                    (λ m → time o1 m + time o2 (step o1 m))

-- OND-2 — trivial-case satisfiability (skip is OND under ANY model) --------

OND2-skip-is-OND : {Obs : Set} → (O : Exec → Obs) → is-OND O skip-op
OND2-skip-is-OND O s1 s2 pub = refl

-- OND-3 — CNO ⊥ OND independence -------------------------------------------

leaky-cno-is-null : is-null leaky-cno
leaky-cno-is-null m a = refl

leaky-cno-not-OND-time : ¬ (is-OND O-time leaky-cno)
leaky-cno-not-OND-time h with h 0 1 0
... | ()

writer-is-OND-all : is-OND O-all writer-op
writer-is-OND-all s1 s2 pub = refl

writer-not-null : ¬ (is-null writer-op)
writer-not-null h with h (λ _ → 0) 0
... | ()

-- The two pillars are logically independent.
-- (existence witnesses packaged as dependent pairs)
open import Data.Product using (Σ; _,_; ∃)

OND3-cno-ond-independent :
    (∃ λ o → (is-null o) × (¬ (is-OND O-time o)))
  × (∃ λ o → (is-OND O-all o) × (¬ (is-null o)))
OND3-cno-ond-independent =
    ( leaky-cno , (leaky-cno-is-null , leaky-cno-not-OND-time) )
  , ( writer-op , (writer-is-OND-all , writer-not-null) )

-- OND-4 — conditional template for one real constant-time operation --------

OND4-ct-select-is-OND-all : is-OND O-all ct-select
OND4-ct-select-is-OND-all s1 s2 pub = refl
-- Declared O = O-all; residue list in proofs/residue/ct_select.residue.

-- OND-5 — non-composition counterexample (under the output channel O-out) --

p-op-is-OND-out : is-OND O-out p-op
p-op-is-OND-out s1 s2 pub = refl

q-op-is-OND-out : is-OND O-out q-op
q-op-is-OND-out s1 s2 pub = refl

OND5-composition-leaks : ¬ (is-OND O-out (seq-op p-op q-op))
OND5-composition-leaks h with h 0 1 0
... | ()

OND5-non-composition :
    (is-OND O-out p-op) × (is-OND O-out q-op)
  × (¬ (is-OND O-out (seq-op p-op q-op)))
OND5-non-composition =
  p-op-is-OND-out , q-op-is-OND-out , OND5-composition-leaks
