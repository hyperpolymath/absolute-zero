{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

{- Certified Null Operations: Agda Formalization

   This file provides an Agda formalization of CNO theory.
   Agda's dependent type system allows for very precise specifications.

   Author: Jonathan D. A. Jewell
   Project: Absolute Zero
   License: AGPL-3.0 / Palimpsest 0.5
-}


module CNO where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; ≤-antisym)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to maybe-map)

----------------------------------------------------------------------------
-- Memory Model
----------------------------------------------------------------------------

-- Memory is a function from addresses to values
Memory : Set
Memory = ℕ → ℕ

-- Empty memory (all zeros)
empty-memory : Memory
empty-memory = λ _ → zero

-- Update memory at an address
mem-update : Memory → ℕ → ℕ → Memory
mem-update m addr val = λ a →
  if a Data.Nat.≡ᵇ addr then val else m a
  where
    open import Data.Nat using (_≡ᵇ_)

-- Memory equality
mem-eq : Memory → Memory → Set
mem-eq m₁ m₂ = ∀ (addr : ℕ) → m₁ addr ≡ m₂ addr

----------------------------------------------------------------------------
-- Registers and I/O
----------------------------------------------------------------------------

-- Registers are a list of natural numbers
Registers : Set
Registers = List ℕ

-- I/O operations
data IOOp : Set where
  NoIO   : IOOp
  ReadOp : ℕ → IOOp
  WriteOp : ℕ → IOOp

-- I/O state
IOState : Set
IOState = List IOOp

----------------------------------------------------------------------------
-- Program State
----------------------------------------------------------------------------

record ProgramState : Set where
  constructor mk-state
  field
    state-memory    : Memory
    state-registers : Registers
    state-io        : IOState
    state-pc        : ℕ

open ProgramState

-- Full state equality, program counter included.
state-eq : ProgramState → ProgramState → Set
state-eq s₁ s₂ =
  mem-eq (state-memory s₁) (state-memory s₂) ×
  state-registers s₁ ≡ state-registers s₂ ×
  state-io s₁ ≡ state-io s₂ ×
  state-pc s₁ ≡ state-pc s₂

-- Observable state equality: memory, registers and I/O.  The program
-- counter is control state, not an observable effect, so a CNO is judged
-- by this relation.  (Until 2026-11-09 `IsCNO` used `state-eq`, which
-- made every program that advances the counter, `Nop` included, fail to
-- be a CNO.)
obs-eq : ProgramState → ProgramState → Set
obs-eq s₁ s₂ =
  mem-eq (state-memory s₁) (state-memory s₂) ×
  state-registers s₁ ≡ state-registers s₂ ×
  state-io s₁ ≡ state-io s₂

obs-eq-refl : ∀ s → obs-eq s s
obs-eq-refl s = (λ _ → refl) , refl , refl

obs-eq-sym : ∀ {s₁ s₂} → obs-eq s₁ s₂ → obs-eq s₂ s₁
obs-eq-sym (m , r , i) = (λ a → sym (m a)) , sym r , sym i

obs-eq-trans : ∀ {s₁ s₂ s₃} → obs-eq s₁ s₂ → obs-eq s₂ s₃ → obs-eq s₁ s₃
obs-eq-trans (m₁ , r₁ , i₁) (m₂ , r₂ , i₂) =
  (λ a → trans (m₁ a) (m₂ a)) , trans r₁ r₂ , trans i₁ i₂

state-eq→obs-eq : ∀ {s₁ s₂} → state-eq s₁ s₂ → obs-eq s₁ s₂
state-eq→obs-eq (m , r , i , _) = m , r , i

----------------------------------------------------------------------------
-- Instructions
----------------------------------------------------------------------------

data Instruction : Set where
  Nop   : Instruction
  Halt  : Instruction
  Load  : ℕ → ℕ → Instruction      -- Load mem[addr] to reg
  Store : ℕ → ℕ → Instruction      -- Store reg to mem[addr]
  Add   : ℕ → ℕ → ℕ → Instruction  -- r3 := r1 + r2
  Jump  : ℕ → Instruction          -- absolute jump: pc := target

-- A program is a list of instructions, addressed from 0 by the pc.
Program : Set
Program = List Instruction

----------------------------------------------------------------------------
-- Helper Functions
----------------------------------------------------------------------------

-- Get register value
get-reg : Registers → ℕ → Maybe ℕ
get-reg []       _       = nothing
get-reg (r ∷ _)  zero    = just r
get-reg (_ ∷ rs) (suc n) = get-reg rs n

-- Set register value
set-reg : Registers → ℕ → ℕ → Registers
set-reg []       _       _   = []
set-reg (_ ∷ rs) zero    val = val ∷ rs
set-reg (r ∷ rs) (suc n) val = r ∷ set-reg rs n val

-- The instruction at a program counter, if any.
fetch : Program → ℕ → Maybe Instruction
fetch []       _       = nothing
fetch (i ∷ _)  zero    = just i
fetch (_ ∷ is) (suc n) = fetch is n

----------------------------------------------------------------------------
-- Operational Semantics: a pc-driven machine
----------------------------------------------------------------------------

-- What one instruction does to the machine.  `fault` is a Store or Add
-- that names a missing register: the machine stops abnormally, so a
-- faulting run does not terminate in the sense of `_⊢_⇓_`.
data Ctl : Set where
  halt  : Ctl
  fault : Ctl
  go    : ProgramState → Ctl

store-at : ProgramState → ℕ → Maybe ℕ → Ctl
store-at s addr (just v) = go (record s
  { state-memory = mem-update (state-memory s) addr v
  ; state-pc     = suc (state-pc s)
  })
store-at s addr nothing  = fault

add-at : ProgramState → ℕ → Maybe ℕ → Maybe ℕ → Ctl
add-at s r₃ (just v₁) (just v₂) = go (record s
  { state-registers = set-reg (state-registers s) r₃ (v₁ + v₂)
  ; state-pc        = suc (state-pc s)
  })
add-at s r₃ (just _)  nothing   = fault
add-at s r₃ nothing   _         = fault

-- Single step.
step : ProgramState → Instruction → Ctl
step s Nop              = go (record s { state-pc = suc (state-pc s) })
step s Halt             = halt
step s (Load addr reg)  = go (record s
  { state-registers = set-reg (state-registers s) reg (state-memory s addr)
  ; state-pc        = suc (state-pc s)
  })
step s (Store addr reg) = store-at s addr (get-reg (state-registers s) reg)
step s (Add r₁ r₂ r₃)   =
  add-at s r₃ (get-reg (state-registers s) r₁) (get-reg (state-registers s) r₂)
step s (Jump target)    = go (record s { state-pc = target })

-- Big-step semantics.  `p ⊢ s ⇓ s'`: started in `s`, program `p` stops
-- normally in `s'`, either by running off the end (no instruction at the
-- pc) or by executing `Halt`.
infix 4 _⊢_⇓_
data _⊢_⇓_ (p : Program) : ProgramState → ProgramState → Set where
  ⇓-end  : ∀ {s} → fetch p (state-pc s) ≡ nothing → p ⊢ s ⇓ s
  ⇓-halt : ∀ {s i} → fetch p (state-pc s) ≡ just i → step s i ≡ halt →
           p ⊢ s ⇓ s
  ⇓-step : ∀ {s i s₁ s'} → fetch p (state-pc s) ≡ just i →
           step s i ≡ go s₁ → p ⊢ s₁ ⇓ s' → p ⊢ s ⇓ s'

-- Fuel-bounded interpreter: the executable form of the same machine.
-- `run n p s` performs at most `n` non-halting steps; `nothing` means
-- out of fuel or a fault.
run      : ℕ → Program → ProgramState → Maybe ProgramState
run-from : ℕ → Program → ProgramState → Maybe Instruction → Maybe ProgramState
run-ctl  : Ctl → ℕ → Program → ProgramState → Maybe ProgramState

run n p s = run-from n p s (fetch p (state-pc s))

run-from n p s nothing  = just s
run-from n p s (just i) = run-ctl (step s i) n p s

run-ctl halt     n       p s = just s
run-ctl fault    n       p s = nothing
run-ctl (go s₁)  zero    p s = nothing
run-ctl (go s₁)  (suc n) p s = run n p s₁

-- Every program starts at pc 0.
start : ProgramState → ProgramState
start s = record s { state-pc = 0 }

----------------------------------------------------------------------------
-- Small lemmas
----------------------------------------------------------------------------

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

go-inj : ∀ {s₁ s₂} → go s₁ ≡ go s₂ → s₁ ≡ s₂
go-inj refl = refl

nothing≢just : ∀ {A : Set} {x : A} → ¬ (nothing ≡ just x)
nothing≢just ()

halt≢go : ∀ {s} → ¬ (halt ≡ go s)
halt≢go ()

fetch-nothing : ∀ p n → fetch p n ≡ nothing → length p ≤ n
fetch-nothing []      n       e = z≤n
fetch-nothing (i ∷ p) zero    ()
fetch-nothing (i ∷ p) (suc n) e = s≤s (fetch-nothing p n e)

fetch-just : ∀ p n {i} → fetch p n ≡ just i → n < length p
fetch-just []      n       ()
fetch-just (i ∷ p) zero    e = s≤s z≤n
fetch-just (i ∷ p) (suc n) e = s≤s (fetch-just p n e)

fetch-++-left : ∀ p q n {i} → fetch p n ≡ just i → fetch (p ++ q) n ≡ just i
fetch-++-left []      q n       ()
fetch-++-left (x ∷ p) q zero    e = e
fetch-++-left (x ∷ p) q (suc n) e = fetch-++-left p q n e

fetch-++-right : ∀ p q j → fetch (p ++ q) (length p + j) ≡ fetch q j
fetch-++-right []      q j = refl
fetch-++-right (x ∷ p) q j = fetch-++-right p q j

fetch-map : ∀ (f : Instruction → Instruction) q j →
            fetch (map f q) j ≡ maybe-map f (fetch q j)
fetch-map f []      j       = refl
fetch-map f (x ∷ q) zero    = refl
fetch-map f (x ∷ q) (suc j) = fetch-map f q j

----------------------------------------------------------------------------
-- Adequacy: the interpreter and the big-step relation agree
----------------------------------------------------------------------------

run-sound  : ∀ n p s {s'} → run n p s ≡ just s' → p ⊢ s ⇓ s'
from-sound : ∀ n p s m {s'} → fetch p (state-pc s) ≡ m →
             run-from n p s m ≡ just s' → p ⊢ s ⇓ s'
ctl-sound  : ∀ c n p s i {s'} → fetch p (state-pc s) ≡ just i →
             step s i ≡ c → run-ctl c n p s ≡ just s' → p ⊢ s ⇓ s'

run-sound n p s h = from-sound n p s (fetch p (state-pc s)) refl h

from-sound n p s nothing  e refl = ⇓-end e
from-sound n p s (just i) e h    = ctl-sound (step s i) n p s i e refl h

ctl-sound halt    n       p s i e g refl = ⇓-halt e g
ctl-sound fault   n       p s i e g ()
ctl-sound (go s₁) zero    p s i e g ()
ctl-sound (go s₁) (suc n) p s i e g h    = ⇓-step e g (run-sound n p s₁ h)

run-complete : ∀ {p s s'} → p ⊢ s ⇓ s' → Σ ℕ (λ n → run n p s ≡ just s')
run-complete {p} {s} (⇓-end e)    = 0 , cong (run-from 0 p s) e
run-complete {p} {s} (⇓-halt e g) =
  0 , trans (cong (run-from 0 p s) e) (cong (λ c → run-ctl c 0 p s) g)
run-complete {p} {s} (⇓-step e g d) with run-complete d
... | n , h = suc n , trans (cong (run-from (suc n) p s) e)
                            (trans (cong (λ c → run-ctl c (suc n) p s) g) h)

-- The machine is deterministic.
⇓-det : ∀ {p s a b} → p ⊢ s ⇓ a → p ⊢ s ⇓ b → a ≡ b
⇓-det (⇓-end e)    (⇓-end e')      = refl
⇓-det (⇓-end e)    (⇓-halt e' _)   = ⊥-elim (nothing≢just (trans (sym e) e'))
⇓-det (⇓-end e)    (⇓-step e' _ _) = ⊥-elim (nothing≢just (trans (sym e) e'))
⇓-det (⇓-halt e _) (⇓-end e')      = ⊥-elim (nothing≢just (trans (sym e') e))
⇓-det (⇓-halt e _) (⇓-halt _ _)    = refl
⇓-det {s = s} (⇓-halt e h) (⇓-step e' g _) =
  ⊥-elim (halt≢go (trans (sym h)
    (trans (cong (step s) (just-inj (trans (sym e) e'))) g)))
⇓-det (⇓-step e _ _) (⇓-end e')    = ⊥-elim (nothing≢just (trans (sym e') e))
⇓-det {s = s} (⇓-step e g _) (⇓-halt e' h) =
  ⊥-elim (halt≢go (trans (sym h)
    (trans (cong (step s) (just-inj (trans (sym e') e))) g)))
⇓-det {p} {s} {b = b} (⇓-step e g d) (⇓-step e' g' d') =
  ⇓-det d (subst (λ x → p ⊢ x ⇓ b) (sym s₁≡s₂) d')
  where
    s₁≡s₂ = go-inj (trans (sym g)
              (trans (cong (step s) (just-inj (trans (sym e) e'))) g'))

-- A run stops either off the end or at an instruction that halts.
⇓-final : ∀ {p s s'} → p ⊢ s ⇓ s' →
          (fetch p (state-pc s') ≡ nothing) ⊎
          Σ Instruction (λ i → fetch p (state-pc s') ≡ just i × step s' i ≡ halt)
⇓-final (⇓-end e)      = inj₁ e
⇓-final (⇓-halt e h)   = inj₂ (_ , e , h)
⇓-final (⇓-step _ _ d) = ⇓-final d

----------------------------------------------------------------------------
-- Termination
----------------------------------------------------------------------------

-- `p` terminates from `s` when the machine, started at pc 0, stops
-- normally.  Programs can loop (`jump-self-diverges` below) or fault, so
-- this is a real property, not a consequence of evaluation being total.
Terminates : Program → ProgramState → Set
Terminates p s = Σ ProgramState (λ s' → p ⊢ start s ⇓ s')

-- The same notion through the fuel interpreter.
terminates→fuel : ∀ {p s} → Terminates p s →
                  Σ ℕ (λ n → Σ ProgramState (λ s' → run n p (start s) ≡ just s'))
terminates→fuel (s' , d) with run-complete d
... | n , h = n , s' , h

fuel→terminates : ∀ {p s} n {s'} → run n p (start s) ≡ just s' → Terminates p s
fuel→terminates {p} {s} n {s'} h = s' , run-sound n p (start s) h

----------------------------------------------------------------------------
-- Side Effects
----------------------------------------------------------------------------

-- No I/O operations occurred
no-io : ProgramState → ProgramState → Set
no-io s₁ s₂ = state-io s₁ ≡ state-io s₂

-- No memory allocation (memory equality)
no-memory-alloc : ProgramState → ProgramState → Set
no-memory-alloc s₁ s₂ = mem-eq (state-memory s₁) (state-memory s₂)

-- Pure computation (no side effects)
pure : ProgramState → ProgramState → Set
pure s₁ s₂ = no-io s₁ s₂ × no-memory-alloc s₁ s₂

----------------------------------------------------------------------------
-- CNO Definition
----------------------------------------------------------------------------

-- A Certified Null Operation: from every state the machine stops
-- normally, and every normal stop leaves memory, registers and I/O as
-- they were.  Purity and reversibility are consequences, proved below.
record IsCNO (p : Program) : Set where
  field
    cno-terminates : ∀ s → Terminates p s
    cno-identity   : ∀ {s s'} → p ⊢ start s ⇓ s' → obs-eq s' s

-- Build a CNO certificate from one witnessing run per state; determinism
-- extends the identity to every run.
cno-from-runs : ∀ {p} →
  (∀ s → Σ ProgramState (λ s' → p ⊢ start s ⇓ s' × obs-eq s' s)) → IsCNO p
cno-from-runs f = record
  { cno-terminates = λ s → proj₁ (f s) , proj₁ (proj₂ (f s))
  ; cno-identity   = λ {s} d →
      subst (λ x → obs-eq x s) (⇓-det (proj₁ (proj₂ (f s))) d)
            (proj₂ (proj₂ (f s)))
  }

----------------------------------------------------------------------------
-- CNO Properties
----------------------------------------------------------------------------

cno-terminates-thm : ∀ {p} → IsCNO p → ∀ s → Terminates p s
cno-terminates-thm cno = IsCNO.cno-terminates cno

-- The final state of a CNO's run.
cno-result : ∀ {p} → IsCNO p → ProgramState → ProgramState
cno-result cno s = proj₁ (IsCNO.cno-terminates cno s)

cno-result-run : ∀ {p} (cno : IsCNO p) s → p ⊢ start s ⇓ cno-result cno s
cno-result-run cno s = proj₂ (IsCNO.cno-terminates cno s)

cno-preserves-state : ∀ {p} (cno : IsCNO p) s → obs-eq (cno-result cno s) s
cno-preserves-state cno s = IsCNO.cno-identity cno {s} (cno-result-run cno s)

-- CNOs are pure: no I/O, no memory change.
cno-pure-thm : ∀ {p s s'} → IsCNO p → p ⊢ start s ⇓ s' → pure s s'
cno-pure-thm {s = s} cno d with IsCNO.cno-identity cno {s} d
... | m , _ , i = sym i , (λ a → sym (m a))

-- Observational reversibility: running `q` after `p` restores every
-- observable component.  This is a consequence of the identity law, not
-- a thermodynamic statement; the Landauer accounting lives in echo-types
-- (`EchoThermodynamics`).
ObsLeftInverse : Program → Program → Set
ObsLeftInverse p q =
  ∀ {s s₁ s₂} → p ⊢ start s ⇓ s₁ → q ⊢ start s₁ ⇓ s₂ → obs-eq s₂ s

cno-left-inverse : ∀ {p q} → IsCNO p → IsCNO q → ObsLeftInverse p q
cno-left-inverse cp cq {s} {s₁} {s₂} d₁ d₂ =
  obs-eq-trans {s₂} {s₁} {s}
    (IsCNO.cno-identity cq {s₁} d₂) (IsCNO.cno-identity cp {s} d₁)

----------------------------------------------------------------------------
-- Composition
----------------------------------------------------------------------------

-- Jumps are absolute, so the second program is relocated by the length
-- of the first.
shift-instr : ℕ → Instruction → Instruction
shift-instr k (Jump t)      = Jump (t + k)
shift-instr k Nop           = Nop
shift-instr k Halt          = Halt
shift-instr k (Load a r)    = Load a r
shift-instr k (Store a r)   = Store a r
shift-instr k (Add a b c)   = Add a b c

seq-comp : Program → Program → Program
seq-comp p₁ p₂ = p₁ ++ map (shift-instr (length p₁)) p₂

-- A program is closed when no jump leaves it except to its end.  Without
-- this, a jump past the end of `p₁` lands inside `p₂` in the composite
-- (`closedness-needed` below).
Closed : Program → Set
Closed p = ∀ {n t} → fetch p n ≡ just (Jump t) → t ≤ length p

shift-pc : ℕ → ProgramState → ProgramState
shift-pc k s = record s { state-pc = state-pc s + k }

shift-ctl : ℕ → Ctl → Ctl
shift-ctl k halt   = halt
shift-ctl k fault  = fault
shift-ctl k (go s) = go (shift-pc k s)

obs-shift : ∀ k s → obs-eq (shift-pc k s) s
obs-shift k s = obs-eq-refl s

store-shift : ∀ k s a m → store-at (shift-pc k s) a m ≡ shift-ctl k (store-at s a m)
store-shift k s a (just v) = refl
store-shift k s a nothing  = refl

add-shift : ∀ k s r m₁ m₂ →
            add-at (shift-pc k s) r m₁ m₂ ≡ shift-ctl k (add-at s r m₁ m₂)
add-shift k s r (just v₁) (just v₂) = refl
add-shift k s r (just v₁) nothing   = refl
add-shift k s r nothing   m₂        = refl

step-shift : ∀ k s i → step (shift-pc k s) (shift-instr k i) ≡ shift-ctl k (step s i)
step-shift k s Nop           = refl
step-shift k s Halt          = refl
step-shift k s (Load a r)    = refl
step-shift k s (Store a r)   = store-shift k s a (get-reg (state-registers s) r)
step-shift k s (Add a b c)   =
  add-shift k s c (get-reg (state-registers s) a) (get-reg (state-registers s) b)
step-shift k s (Jump t)      = refl

store-pc : ∀ s a m {s₁} → store-at s a m ≡ go s₁ → state-pc s₁ ≡ suc (state-pc s)
store-pc s a (just v) refl = refl
store-pc s a nothing  ()

add-pc : ∀ s r m₁ m₂ {s₁} → add-at s r m₁ m₂ ≡ go s₁ →
         state-pc s₁ ≡ suc (state-pc s)
add-pc s r (just v₁) (just v₂) refl = refl
add-pc s r (just v₁) nothing   ()
add-pc s r nothing   m₂        ()

-- In a closed program every step keeps the pc within `0 .. length p`.
step-pc-bound : ∀ {p s i s₁} → Closed p → fetch p (state-pc s) ≡ just i →
                step s i ≡ go s₁ → state-pc s₁ ≤ length p
step-pc-bound {p} {s} {Nop} cl e g =
  subst (λ x → x ≤ length p) (cong state-pc (go-inj g)) (fetch-just p _ e)
step-pc-bound {p} {s} {Halt} cl e ()
step-pc-bound {p} {s} {Load a r} cl e g =
  subst (λ x → x ≤ length p) (cong state-pc (go-inj g)) (fetch-just p _ e)
step-pc-bound {p} {s} {Store a r} cl e g =
  subst (λ x → x ≤ length p)
        (sym (store-pc s a (get-reg (state-registers s) r) g))
        (fetch-just p _ e)
step-pc-bound {p} {s} {Add a b c} cl e g =
  subst (λ x → x ≤ length p)
        (sym (add-pc s c (get-reg (state-registers s) a)
                         (get-reg (state-registers s) b) g))
        (fetch-just p _ e)
step-pc-bound {p} {s} {Jump t} cl e g =
  subst (λ x → x ≤ length p) (cong state-pc (go-inj g)) (cl e)

⇓-pc-bound : ∀ {p s s'} → Closed p → state-pc s ≤ length p →
             p ⊢ s ⇓ s' → state-pc s' ≤ length p
⇓-pc-bound cl b (⇓-end _)      = b
⇓-pc-bound cl b (⇓-halt _ _)   = b
⇓-pc-bound {p} cl b (⇓-step e g d) =
  ⇓-pc-bound {p} cl (step-pc-bound {p} cl e g) d

-- Phase 1: a run of `p` is a prefix of a run of `p ++ q`.
prefix : ∀ {p q s s' s''} → p ⊢ s ⇓ s' → (p ++ q) ⊢ s' ⇓ s'' → (p ++ q) ⊢ s ⇓ s''
prefix (⇓-end _)                 k = k
prefix (⇓-halt _ _)              k = k
prefix {p} {q} {s} (⇓-step e g d) k =
  ⇓-step (fetch-++-left p q (state-pc s) e) g (prefix d k)

-- Phase 2: a run of `p₂` is a run of the relocated copy in the composite.
module Seq (p₁ p₂ : Program) where
  k : ℕ
  k = length p₁

  fetch-comp : ∀ j → fetch (seq-comp p₁ p₂) (j + k)
                     ≡ maybe-map (shift-instr k) (fetch p₂ j)
  fetch-comp j =
    trans (cong (fetch (seq-comp p₁ p₂)) (+-comm j k))
          (trans (fetch-++-right p₁ (map (shift-instr k) p₂) j)
                 (fetch-map (shift-instr k) p₂ j))

  phase2 : ∀ {t t'} → p₂ ⊢ t ⇓ t' → seq-comp p₁ p₂ ⊢ shift-pc k t ⇓ shift-pc k t'
  phase2 {t} (⇓-end e) =
    ⇓-end (trans (fetch-comp (state-pc t)) (cong (maybe-map (shift-instr k)) e))
  phase2 {t} (⇓-halt {i = i} e h) =
    ⇓-halt (trans (fetch-comp (state-pc t)) (cong (maybe-map (shift-instr k)) e))
           (trans (step-shift k t i) (cong (shift-ctl k) h))
  phase2 {t} (⇓-step {i = i} e g d) =
    ⇓-step (trans (fetch-comp (state-pc t)) (cong (maybe-map (shift-instr k)) e))
           (trans (step-shift k t i) (cong (shift-ctl k) g))
           (phase2 d)

shift-start : ∀ {k} s → state-pc s ≡ k → shift-pc k (start s) ≡ s
shift-start (mk-state m r io pc) e = cong (mk-state m r io) (sym e)

-- Sequential composition of CNOs is a CNO when the first is closed.
cno-composition : ∀ {p₁ p₂} → Closed p₁ → IsCNO p₁ → IsCNO p₂ →
                  IsCNO (seq-comp p₁ p₂)
cno-composition {p₁} {p₂} cl c₁ c₂ = cno-from-runs runs
  where
    open Seq p₁ p₂

    comp : Program
    comp = seq-comp p₁ p₂

    runs : ∀ s → Σ ProgramState (λ s' → comp ⊢ start s ⇓ s' × obs-eq s' s)
    runs s with IsCNO.cno-terminates c₁ s
    ... | s₁ , d₁ with ⇓-final d₁
    ...   | inj₂ (i , e , h) =
            s₁ ,
            prefix d₁ (⇓-halt (fetch-++-left p₁ _ (state-pc s₁) e) h) ,
            IsCNO.cno-identity c₁ {s} d₁
    ...   | inj₁ e with IsCNO.cno-terminates c₂ s₁
    ...     | t' , d₂ =
              shift-pc k t' ,
              prefix d₁ (subst (λ x → comp ⊢ x ⇓ shift-pc k t')
                               (shift-start s₁ pc≡k) (phase2 d₂)) ,
              obs-eq-trans {shift-pc k t'} {t'} {s} (obs-shift k t')
                (obs-eq-trans {t'} {s₁} {s}
                  (IsCNO.cno-identity c₂ {s₁} d₂) (IsCNO.cno-identity c₁ {s} d₁))
      where
        pc≡k : state-pc s₁ ≡ k
        pc≡k = ≤-antisym (⇓-pc-bound {p₁} cl z≤n d₁) (fetch-nothing p₁ _ e)

----------------------------------------------------------------------------
-- Witnesses
----------------------------------------------------------------------------

-- The empty program is a CNO
empty-is-cno : IsCNO []
empty-is-cno = cno-from-runs (λ s → start s , ⇓-end refl , obs-eq-refl s)

-- Halt is a CNO
halt-is-cno : IsCNO (Halt ∷ [])
halt-is-cno = cno-from-runs (λ s → start s , ⇓-halt refl refl , obs-eq-refl s)

-- Nop advances the pc and is a CNO: the class is not Halt-only.
nop-is-cno : IsCNO (Nop ∷ [])
nop-is-cno =
  cno-from-runs (λ s → _ , ⇓-step refl refl (⇓-end refl) , obs-eq-refl s)

-- A jump to the end is a CNO.
jump-exit-is-cno : IsCNO (Jump 1 ∷ [])
jump-exit-is-cno =
  cno-from-runs (λ s → _ , ⇓-step refl refl (⇓-end refl) , obs-eq-refl s)

nop-closed : Closed (Nop ∷ [])
nop-closed {zero}  ()
nop-closed {suc n} ()

-- Composition at work: Nop ; Nop.
nop-nop-is-cno : IsCNO (seq-comp (Nop ∷ []) (Nop ∷ []))
nop-nop-is-cno = cno-composition {Nop ∷ []} {Nop ∷ []} (λ {n} {t} → nop-closed {n} {t}) nop-is-cno nop-is-cno

-- A self-loop never stops: termination is not automatic.
loop : Program
loop = Jump 0 ∷ []

loop-stuck : ∀ {t t'} → state-pc t ≡ 0 → ¬ (loop ⊢ t ⇓ t')
loop-stuck {t} pc0 (⇓-end e) =
  nothing≢just (trans (sym e) (cong (fetch loop) pc0))
loop-stuck {t} pc0 (⇓-halt e h) =
  halt≢go (trans (sym h)
    (cong (step t) (just-inj (trans (sym e) (cong (fetch loop) pc0)))))
loop-stuck {t} pc0 (⇓-step e g d) =
  loop-stuck (sym (cong state-pc (go-inj (trans (sym
    (cong (step t) (just-inj (trans (sym e) (cong (fetch loop) pc0))))) g)))) d

jump-self-diverges : ∀ s → ¬ Terminates loop s
jump-self-diverges s (_ , d) = loop-stuck refl d

-- A Load that changes a register is not a CNO: the class is not
-- everything.
load-prog : Program
load-prog = Load 0 0 ∷ []

load-not-cno : ¬ IsCNO load-prog
load-not-cno cno with IsCNO.cno-identity cno
  {s = mk-state empty-memory (5 ∷ []) [] 0}
  (⇓-step refl refl (⇓-end refl))
... | _ , () , _

-- The closedness side condition is needed.  `Jump 2` and
-- `Jump 2 ; Load 0 0` are both CNOs, but in the composite the first
-- jump lands on the relocated Load.
jump2 : Program
jump2 = Jump 2 ∷ []

jump2-load : Program
jump2-load = Jump 2 ∷ Load 0 0 ∷ []

closedness-needed :
  IsCNO jump2 × IsCNO jump2-load × ¬ Closed jump2 × ¬ IsCNO (seq-comp jump2 jump2-load)
closedness-needed =
  cno-from-runs (λ s → _ , ⇓-step refl refl (⇓-end refl) , obs-eq-refl s) ,
  cno-from-runs (λ s → _ , ⇓-step refl refl (⇓-end refl) , obs-eq-refl s) ,
  (λ cl → two≰one (cl {0} refl)) ,
  bad
  where
    two≰one : ¬ (2 ≤ 1)
    two≰one (s≤s ())

    bad : ¬ IsCNO (seq-comp jump2 jump2-load)
    bad cno with IsCNO.cno-identity cno
      {s = mk-state empty-memory (5 ∷ []) [] 0}
      (⇓-step refl refl (⇓-step refl refl (⇓-end refl)))
    ... | _ , () , _

----------------------------------------------------------------------------
-- Malbolge-Specific
----------------------------------------------------------------------------
-- Ternary operations: addition mod 3 (Malbolge-flavoured).
-- Local `mod3` is structural-recursive on its argument, so it
-- terminates and stays inside `--safe --without-K` without pulling
-- in `Data.Nat.DivMod._%_` (whose `NonZero` instance lookup adds
-- noise that this helper does not need).
mod3 : ℕ → ℕ
mod3 zero                    = zero
mod3 (suc zero)              = suc zero
mod3 (suc (suc zero))        = suc (suc zero)
mod3 (suc (suc (suc n)))     = mod3 n

ternary-add : ℕ → ℕ → ℕ
ternary-add a b = mod3 (a + b)

-- Crazy operation (Malbolge crazy op surface; placeholder semantics)
crazy-op : ℕ → ℕ → ℕ
crazy-op a b = mod3 (a + b)

----------------------------------------------------------------------------
-- Absolute Zero
----------------------------------------------------------------------------

-- The titular "Absolute Zero" program
absolute-zero : Program
absolute-zero = []

-- Absolute Zero is a CNO
absolute-zero-is-cno : IsCNO absolute-zero
absolute-zero-is-cno = empty-is-cno

----------------------------------------------------------------------------
-- Decidability and Complexity
----------------------------------------------------------------------------

-- Complexity measure
complexity : Instruction → ℕ
complexity Nop         = 0
complexity Halt        = 0
complexity (Load _ _)  = 1
complexity (Store _ _) = 1
complexity (Add _ _ _) = 2
complexity (Jump _)    = 1

-- Program complexity
program-complexity : Program → ℕ
program-complexity []       = 0
program-complexity (i ∷ is) = complexity i + program-complexity is

-- Simple instructions have minimal complexity
nop-minimal : complexity Nop ≡ 0
nop-minimal = refl

halt-minimal : complexity Halt ≡ 0
halt-minimal = refl

----------------------------------------------------------------------------
-- Export
----------------------------------------------------------------------------

-- Key definitions and theorems available for import
