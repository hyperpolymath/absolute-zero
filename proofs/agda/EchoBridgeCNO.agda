{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

-- Concrete Echo/CNO instantiation against CNO's pc-driven machine.
--
-- A CNO certificate fixes a total result function `cno-result`, and its
-- identity law is stated up to `CNO.obs-eq` (memory, registers, I/O; the
-- program counter is control state).  So:
--
-- * primary bridge: relation-based echoes via `EchoRel ... CNO.obs-eq`
--   (no extensionality needed);
-- * secondary bridge: propositional `Echo` on the observable projection,
--   given function extensionality for memory, plus a `CNOModel` instance
--   over observable states.
--
-- Until 2026-11-09 this module used the old list-walking `eval` and
-- `state-eq`, under which only Halt-only programs were CNOs.

module EchoBridgeCNO where

open import Level using (zero)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Axiom.Extensionality.Propositional using (Extensionality)

import CNO
module PS = CNO.ProgramState
open import EchoBridgeScaffold using
  ( CNOModel
  ; Echo
  ; EchoRel
  ; echo-from-cno
  ; echo-from-rel
  )

----------------------------------------------------------------------------
-- Primary: up to observable equality
----------------------------------------------------------------------------

echo-from-cno-program-rel :
  (p : CNO.Program) →
  (cno : CNO.IsCNO p) →
  (s : CNO.ProgramState) →
  EchoRel (CNO.cno-result cno) CNO.obs-eq s
echo-from-cno-program-rel p cno s =
  echo-from-rel (CNO.cno-result cno) CNO.obs-eq s s
    (CNO.cno-preserves-state cno s)

absolute-zero-echo-rel :
  (s : CNO.ProgramState) →
  EchoRel (CNO.cno-result CNO.absolute-zero-is-cno) CNO.obs-eq s
absolute-zero-echo-rel s =
  echo-from-cno-program-rel CNO.absolute-zero CNO.absolute-zero-is-cno s

----------------------------------------------------------------------------
-- Secondary: propositional equality on observable states
----------------------------------------------------------------------------

Obs : Set
Obs = CNO.Memory × CNO.Registers × CNO.IOState

observe : CNO.ProgramState → Obs
observe s = PS.state-memory s , PS.state-registers s , PS.state-io s

-- An observable state, placed at pc 0.
inject : Obs → CNO.ProgramState
inject (m , r , io) = CNO.mk-state m r io 0

observe-inject : ∀ o → observe (inject o) ≡ o
observe-inject (m , r , io) = refl

obs-eq→≡ :
  Extensionality zero zero →
  ∀ {s₁ s₂ : CNO.ProgramState} →
  CNO.obs-eq s₁ s₂ → observe s₁ ≡ observe s₂
obs-eq→≡ ext {CNO.mk-state m₁ r₁ i₁ pc₁} {CNO.mk-state m₂ r₂ i₂ pc₂}
             (m-eq , r-eq , io-eq)
  rewrite ext m-eq | r-eq | io-eq = refl

-- Full state equality still yields propositional equality.
state-eq→≡ :
  Extensionality zero zero →
  ∀ {s₁ s₂ : CNO.ProgramState} →
  CNO.state-eq s₁ s₂ → s₁ ≡ s₂
state-eq→≡ ext {CNO.mk-state m₁ r₁ i₁ pc₁} {CNO.mk-state m₂ r₂ i₂ pc₂}
             (m-eq , r-eq , io-eq , pc-eq)
  rewrite ext m-eq | r-eq | io-eq | pc-eq = refl

echo-from-cno-program-≡ :
  (ext : Extensionality zero zero) →
  (p : CNO.Program) →
  (cno : CNO.IsCNO p) →
  (s : CNO.ProgramState) →
  Echo (λ x → observe (CNO.cno-result cno x)) (observe s)
echo-from-cno-program-≡ ext p cno s =
  s , obs-eq→≡ ext {CNO.cno-result cno s} {s} (CNO.cno-preserves-state cno s)

absolute-zero-echo-≡ :
  (ext : Extensionality zero zero) →
  (s : CNO.ProgramState) →
  Echo (λ x → observe (CNO.cno-result CNO.absolute-zero-is-cno x)) (observe s)
absolute-zero-echo-≡ ext s =
  echo-from-cno-program-≡ ext CNO.absolute-zero CNO.absolute-zero-is-cno s

-- Certified programs act on observable states as the identity.  The
-- certificate travels with the operation, so the model's own `IsCNO`
-- predicate is trivial.
CertifiedProgram : Set
CertifiedProgram = Σ CNO.Program CNO.IsCNO

run-obs : CertifiedProgram → Obs → Obs
run-obs (p , cno) o = observe (CNO.cno-result cno (inject o))

program-state-model : Extensionality zero zero → CNOModel Obs
program-state-model ext = record
  { Op = CertifiedProgram
  ; run = run-obs
  ; IsCNO = λ _ → ⊤
  ; cno-identity = λ { {p , cno} _ o →
      trans′ (obs-eq→≡ ext {CNO.cno-result cno (inject o)} {inject o}
                     (CNO.cno-preserves-state cno (inject o)))
             (observe-inject o) }
  }
  where
    trans′ : ∀ {a b c : Obs} → a ≡ b → b ≡ c → a ≡ c
    trans′ refl q = q

echo-from-certified-program :
  (ext : Extensionality zero zero) →
  (cp : CertifiedProgram) →
  (o : Obs) →
  Echo (run-obs cp) o
echo-from-certified-program ext cp o =
  echo-from-cno (program-state-model ext) cp tt o
