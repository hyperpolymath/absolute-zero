{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

-- Bridge regressions use a nonzero initial pc and nonempty observables.
module EchoBridgeCNOTests where

open import CNO
open ProgramState
open import EchoBridgeCNO
open import EchoBridgeScaffold using (CNOModel)
open import CNOTests using (at; mem; io)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Level using (zero)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

visible : Obs
visible = mem , (2 ∷ 5 ∷ 9 ∷ []) , io

projection-discards-pc : observe (at 19) ≡ visible
projection-discards-pc = refl

injection-starts-at-zero : inject visible ≡ at 0
injection-starts-at-zero = refl

projection-roundtrip : observe (inject visible) ≡ visible
projection-roundtrip = observe-inject visible

injection-roundtrip-resets-pc : inject (observe (at 19)) ≡ start (at 19)
injection-roundtrip-resets-pc = refl

nop-certified : CertifiedProgram
nop-certified = (Nop ∷ []) , nop-is-cno

certified-nop-observables : run-obs nop-certified visible ≡ visible
certified-nop-observables = refl

certified-composition-observables :
  run-obs (seq-comp (Nop ∷ []) (Nop ∷ []) , nop-nop-is-cno) visible ≡ visible
certified-composition-observables = refl

relational-echo-retains-input :
  proj₁ (echo-from-cno-program-rel (Nop ∷ []) nop-is-cno (at 19)) ≡ at 19
relational-echo-retains-input = refl

relational-echo-certifies-observables :
  obs-eq (cno-result nop-is-cno (at 19)) (at 19)
relational-echo-certifies-observables =
  proj₂ (echo-from-cno-program-rel (Nop ∷ []) nop-is-cno (at 19))

-- Extensionality stays an explicit parameter, never a test postulate.
model-uses-certified-run : (ext : Extensionality zero zero) →
  CNOModel.run (program-state-model ext) nop-certified visible ≡ visible
model-uses-certified-run ext = refl

model-identity : (ext : Extensionality zero zero) →
  run-obs nop-certified visible ≡ visible
model-identity ext = CNOModel.cno-identity (program-state-model ext) {op = nop-certified} tt visible

certified-echo-retains-observables : (ext : Extensionality zero zero) →
  proj₁ (echo-from-certified-program ext nop-certified visible) ≡ visible
certified-echo-retains-observables ext = refl

propositional-echo-retains-input : (ext : Extensionality zero zero) →
  proj₁ (echo-from-cno-program-≡ ext (Nop ∷ []) nop-is-cno (at 19)) ≡ at 19
propositional-echo-retains-input ext = refl
