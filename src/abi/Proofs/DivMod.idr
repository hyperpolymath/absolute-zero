||| Div/mod lemma library for ABI alignment proofs.
|||
||| Consolidates the trusted base of number-theoretic lemmas used by ABI
||| layout modules across the hyperpolymath estate (absolute-zero,
||| civic-connect, and any future Idris2 ABI consumers).
|||
||| Design goals:
|||   * Single shared module — each estate repo imports the same lemmas
|||     rather than re-postulating per file.
|||   * Each lemma is an individually-named declaration so it can be
|||     discharged incrementally (one Qed/proof per audit pass) without
|||     touching consumers.
|||   * Definitions of the functions the lemmas talk about live here too,
|||     so the lemma statements don't drift from their referent.
|||
||| Discharge tracker: absolute-zero#27.
|||
||| @see https://github.com/hyperpolymath/absolute-zero/issues/27

-- SPDX-License-Identifier: PMPL-1.0-or-later

module AbsoluteZero.ABI.Proofs.DivMod

import Data.So
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Aligned size
--------------------------------------------------------------------------------

||| Round `size` up to the next multiple of `align`.
||| If `size` is already aligned, returns `size` unchanged.
public export
alignedSize : (size : Nat) -> (align : Nat) -> Nat
alignedSize size align =
  let remainder = size `mod` align
  in if remainder == 0
     then size
     else size + (align - remainder)

--------------------------------------------------------------------------------
-- Trusted lemma surface
--
-- Each `postulate` below is an individually-audit-trackable item. Discharge
-- one at a time; the lemma name stays stable so consumers don't break.
--
-- Estate cross-reference (as of 2026-05-20):
--   * civic-connect/src/Abi/Layout.idr defers the same family under
--     `alignUpDivides`, `mkFieldsAligned`, `offsetInBoundsPrf`. Those
--     should migrate to import these names.
--------------------------------------------------------------------------------

||| `alignedSize size align` is always a multiple of `align`.
|||
||| Proof outline (deferred — see audit tracker):
|||   Let r = size `mod` align.
|||   Case r == 0: alignedSize = size, divisible by hypothesis.
|||   Case r /= 0: alignedSize = size + (align - r)
|||                            = ((size `div` align) * align + r) + (align - r)
|||                              [by divModIdentity]
|||                            = ((size `div` align) + 1) * align
|||                              [by Nat ring rewriting]
|||                            and (k * align) `mod` align = 0
|||                              [by multModZero].
|||
||| Reduces to: `divModIdentity` + `multModZero` + `addModDistrib`.
export
postulate alignedSizeCorrect :
  (size : Nat) -> (align : Nat) ->
  {auto 0 nonZero : So (align /= 0)} ->
  So (alignedSize size align `mod` align == 0)

||| Euclidean division identity: every Nat decomposes as q*d + r where r < d.
||| The single most-used lemma in the alignment proofs — proving this
||| (likely by induction on `size`, or via Idris2 stdlib `Data.Nat.Division`)
||| would shrink the trusted base substantially.
export
postulate divModIdentity :
  (n : Nat) -> (d : Nat) ->
  {auto 0 nonZero : So (d /= 0)} ->
  n = (n `div` d) * d + (n `mod` d)

||| Any multiple of `d` is congruent to zero mod `d`.
export
postulate multModZero :
  (k : Nat) -> (d : Nat) ->
  {auto 0 nonZero : So (d /= 0)} ->
  So ((k * d) `mod` d == 0)

||| Mod distributes over addition (in the sense that `(a + b) mod d` is
||| determined by `a mod d` and `b mod d`).
export
postulate addModDistrib :
  (a : Nat) -> (b : Nat) -> (d : Nat) ->
  {auto 0 nonZero : So (d /= 0)} ->
  (a + b) `mod` d = ((a `mod` d) + (b `mod` d)) `mod` d
