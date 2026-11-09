{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

-- Unit regressions for the pc-driven machine. Each equality is checked by
-- normalization; expected states are explicit, rather than computed by step.
-- Run from proofs/agda using the CI Agda invocation, targeting CNOTests.agda.
module CNOTests where

open import CNO
open ProgramState
open import Data.Nat using (ℕ; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Nonempty memory, registers and I/O expose accidental resets or clobbers.
mem : Memory
mem = mem-update empty-memory 4 11

io : IOState
io = ReadOp 3 ∷ WriteOp 8 ∷ []

at : ℕ → ProgramState
at pc = mk-state mem (2 ∷ 5 ∷ 9 ∷ []) io pc

empty-needs-no-fuel : run 0 [] (at 7) ≡ just (at 7)
empty-needs-no-fuel = refl

halt-needs-no-fuel : run 0 (Halt ∷ []) (at 0) ≡ just (at 0)
halt-needs-no-fuel = refl

halt-skips-effects : run 10 (Halt ∷ Store 4 0 ∷ []) (at 0) ≡ just (at 0)
halt-skips-effects = refl

pc-selects-instruction :
  run 0 (Store 4 0 ∷ Halt ∷ []) (at 1) ≡ just (at 1)
pc-selects-instruction = refl

pc-at-end : run 0 (Nop ∷ []) (at 1) ≡ just (at 1)
pc-at-end = refl

pc-beyond-end : run 0 (Nop ∷ []) (at 8) ≡ just (at 8)
pc-beyond-end = refl

nop-needs-fuel : run 0 (Nop ∷ []) (at 0) ≡ nothing
nop-needs-fuel = refl

nop-exact-fuel : run 1 (Nop ∷ []) (at 0) ≡ just (at 1)
nop-exact-fuel = refl

halt-after-last-fuel : run 1 (Nop ∷ Halt ∷ []) (at 0) ≡ just (at 1)
halt-after-last-fuel = refl

load-existing : step (at 3) (Load 4 1) ≡
  go (mk-state mem (2 ∷ 11 ∷ 9 ∷ []) io 4)
load-existing = refl

load-default-memory : step (at 3) (Load 7 2) ≡
  go (mk-state mem (2 ∷ 5 ∷ 0 ∷ []) io 4)
load-default-memory = refl

-- Missing destinations retain the register list under the existing set-reg
-- contract; only missing source registers fault.
load-missing-destination : step (at 3) (Load 4 3) ≡ go (at 4)
load-missing-destination = refl

store-existing : step (at 3) (Store 4 2) ≡
  go (mk-state (mem-update mem 4 9) (2 ∷ 5 ∷ 9 ∷ []) io 4)
store-existing = refl

store-missing : step (at 3) (Store 4 3) ≡ fault
store-missing = refl

store-empty-registers : step (mk-state mem [] io 0) (Store 4 0) ≡ fault
store-empty-registers = refl

add-existing : step (at 3) (Add 0 1 2) ≡
  go (mk-state mem (2 ∷ 5 ∷ 7 ∷ []) io 4)
add-existing = refl

add-aliases-source : step (at 3) (Add 0 0 0) ≡
  go (mk-state mem (4 ∷ 5 ∷ 9 ∷ []) io 4)
add-aliases-source = refl

add-missing-left : step (at 3) (Add 3 0 1) ≡ fault
add-missing-left = refl

add-missing-right : step (at 3) (Add 0 3 1) ≡ fault
add-missing-right = refl

add-missing-both : step (at 3) (Add 3 4 1) ≡ fault
add-missing-both = refl

add-missing-destination : step (at 3) (Add 0 1 3) ≡ go (at 4)
add-missing-destination = refl

fault-is-not-normal-stop : run 5 (Store 4 3 ∷ Halt ∷ []) (at 0) ≡ nothing
fault-is-not-normal-stop = refl

add-fault-is-not-normal-stop : run 5 (Add 0 3 1 ∷ Halt ∷ []) (at 0) ≡ nothing
add-fault-is-not-normal-stop = refl

-- A multi-instruction data dependency tests fetch and state threading.
arithmetic : Program
arithmetic = Load 4 0 ∷ Add 0 1 2 ∷ Store 7 2 ∷ Halt ∷ []

arithmetic-short-fuel : run 2 arithmetic (at 0) ≡ nothing
arithmetic-short-fuel = refl

arithmetic-exact-fuel : run 3 arithmetic (at 0) ≡
  just (mk-state (mem-update mem 7 16) (11 ∷ 5 ∷ 16 ∷ []) io 3)
arithmetic-exact-fuel = refl

stored-address : mem-update mem 7 16 7 ≡ 16
stored-address = refl

other-address-preserved : mem-update mem 7 16 4 ≡ 11
other-address-preserved = refl

jump-skips-fault : run 1 (Jump 2 ∷ Store 4 3 ∷ Halt ∷ []) (at 0) ≡ just (at 2)
jump-skips-fault = refl

jump-beyond-end : run 1 (Jump 20 ∷ []) (at 0) ≡ just (at 20)
jump-beyond-end = refl

jump-is-absolute : step (at 7) (Jump 2) ≡ go (at 2)
jump-is-absolute = refl

-- Universal fuel regression: a backward jump never becomes a normal stop.
self-loop-no-fuel : ∀ n → run n loop (at 0) ≡ nothing
self-loop-no-fuel 0 = refl
self-loop-no-fuel (suc n) = self-loop-no-fuel n

backward-loop : run 8 (Nop ∷ Jump 0 ∷ []) (at 0) ≡ nothing
backward-loop = refl

start-resets-only-pc : start (at 19) ≡ at 0
start-resets-only-pc = refl

nop-result-starts-at-zero : cno-result nop-is-cno (at 19) ≡ at 1
nop-result-starts-at-zero = refl

pc-not-observable : obs-eq (at 1) (at 19)
pc-not-observable = (λ _ → refl) , refl , refl

pc-still-in-full-equality : ¬ state-eq (at 1) (at 19)
pc-still-in-full-equality (_ , _ , _ , ())

memory-change-observable : ¬ obs-eq (mk-state empty-memory (2 ∷ 5 ∷ 9 ∷ []) io 0) (at 0)
memory-change-observable (m , _ , _) with m 4
... | ()

register-change-observable : ¬ obs-eq (mk-state mem [] io 0) (at 0)
register-change-observable (_ , () , _)

io-change-observable : ¬ obs-eq (mk-state mem (2 ∷ 5 ∷ 9 ∷ []) [] 0) (at 0)
io-change-observable (_ , _ , ())

-- Exercise adequacy on a run with real control flow, and determinism across
-- two fuel budgets, rather than only on the empty program witnesses.
skip : Program
skip = Jump 2 ∷ Store 4 3 ∷ Halt ∷ []

skip-derivation : skip ⊢ at 0 ⇓ at 2
skip-derivation = run-sound 1 skip (at 0) refl

complete-roundtrip :
  run (proj₁ (run-complete skip-derivation)) skip (at 0) ≡ just (at 2)
complete-roundtrip = proj₂ (run-complete skip-derivation)

fuel-independent : at 2 ≡ at 2
fuel-independent = ⇓-det skip-derivation (run-sound 8 skip (at 0) refl)

termination-resets-pc : Terminates skip (at 19)
termination-resets-pc = fuel→terminates {p = skip} {s = at 19} 1 refl

-- Relocate jumps only in the second component; its local exit must become
-- the composite exit, rather than a self-loop at the second instruction.
relocated-layout : seq-comp (Nop ∷ [])
  (Jump 2 ∷ Load 4 0 ∷ []) ≡ Nop ∷ Jump 3 ∷ Load 4 0 ∷ []
relocated-layout = refl

relocated-run : run 2 (seq-comp (Nop ∷ []) (Jump 2 ∷ Load 4 0 ∷ [])) (at 0) ≡ just (at 3)
relocated-run = refl

relocation-preserves-other-instructions :
  seq-comp (Nop ∷ []) (Nop ∷ Halt ∷ Load 4 0 ∷ Store 7 1 ∷ Add 0 1 2 ∷ []) ≡
  Nop ∷ Nop ∷ Halt ∷ Load 4 0 ∷ Store 7 1 ∷ Add 0 1 2 ∷ []
relocation-preserves-other-instructions = refl

halt-prefix-skips-second :
  run 0 (seq-comp (Halt ∷ []) (Store 4 3 ∷ [])) (at 0) ≡ just (at 0)
halt-prefix-skips-second = refl

-- Observable regression witnessing why composition requires Closed.
unclosed-prefix-changes-register :
  run 2 (seq-comp jump2 jump2-load) (at 0) ≡
  just (mk-state mem (0 ∷ 5 ∷ 9 ∷ []) io 3)
unclosed-prefix-changes-register = refl
