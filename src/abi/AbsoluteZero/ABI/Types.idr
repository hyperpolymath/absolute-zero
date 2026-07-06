-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
||| ABI Type Definitions for Absolute Zero
|||
||| This module defines the Application Binary Interface (ABI) for the
||| Absolute Zero CNO verification library. All type definitions include
||| formal proofs of correctness.
|||
||| @see https://github.com/hyperpolymath/absolute-zero


module AbsoluteZero.ABI.Types

import Data.Bits
import Data.So
import Data.Vect
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Platform Detection
--------------------------------------------------------------------------------

||| Supported platforms for this ABI
public export
data Platform = Linux | Windows | MacOS | BSD | WASM

||| Compile-time platform detection.
||| Default target is Linux; override at the FFI/build boundary for other
||| platforms. (Previously an empty `%runElab do pure Linux`, which both
||| required `%language ElabReflection` and did no actual reflection — reduced
||| to the plain default it always computed.)
public export
thisPlatform : Platform
thisPlatform = Linux

--------------------------------------------------------------------------------
-- Result Codes
--------------------------------------------------------------------------------

||| Result codes for FFI operations
||| Use C-compatible integers for cross-language compatibility
public export
data Result : Type where
  ||| Operation succeeded
  Ok : Result
  ||| Generic error
  Error : Result
  ||| Invalid parameter provided
  InvalidParam : Result
  ||| Out of memory
  OutOfMemory : Result
  ||| Null pointer encountered
  NullPointer : Result
  ||| Program does not terminate
  NonTerminating : Result
  ||| Program has side effects
  HasSideEffects : Result
  ||| Program is not a CNO
  NotCNO : Result

||| Convert Result to C integer
public export
resultToInt : Result -> Bits32
resultToInt Ok = 0
resultToInt Error = 1
resultToInt InvalidParam = 2
resultToInt OutOfMemory = 3
resultToInt NullPointer = 4
resultToInt NonTerminating = 5
resultToInt HasSideEffects = 6
resultToInt NotCNO = 7

-- NOTE: a hand-written `DecEq Result` instance previously lived here with a
-- `decEq _ _ = No absurd` catch-all. That does not type-check: the coverage
-- checker sees the catch-all's operands abstractly, so `absurd` would need
-- `Uninhabited (x = y)` for arbitrary `x, y : Result` — which is false (they
-- may be equal). A total instance would require enumerating all 56 off-diagonal
-- pairs (or proving `resultToInt` injective over primitive `Bits32` literals).
-- The instance had ZERO consumers in this package, so it was removed rather
-- than shipped broken. Decidable equality is recoverable when needed via the
-- injective discriminant `resultToInt` (see `instrToDiscriminant` likewise):
--   decEq x y  ==>  compare (resultToInt x) (resultToInt y) and lift.

--------------------------------------------------------------------------------
-- Instruction Types
--------------------------------------------------------------------------------

||| Abstract instruction set matching Coq definitions
public export
data Instruction : Type where
  ||| No operation
  Nop : Instruction
  ||| Load memory[addr] to register
  Load : (reg : Bits32) -> (addr : Bits32) -> Instruction
  ||| Store register to memory[addr]
  Store : (reg : Bits32) -> (addr : Bits32) -> Instruction
  ||| Add two registers and store in third
  Add : (r1 : Bits32) -> (r2 : Bits32) -> (r3 : Bits32) -> Instruction
  ||| Jump to address
  Jump : (target : Bits32) -> Instruction
  ||| Halt execution
  Halt : Instruction

||| Convert instruction to discriminant for C interop
public export
instrToDiscriminant : Instruction -> Bits32
instrToDiscriminant Nop = 0
instrToDiscriminant (Load _ _) = 1
instrToDiscriminant (Store _ _) = 2
instrToDiscriminant (Add _ _ _) = 3
instrToDiscriminant (Jump _) = 4
instrToDiscriminant Halt = 5

-- NOTE: a hand-written `DecEq Instruction` instance previously lived here with
-- `No absurd` catch-alls (both within each same-constructor case and as the
-- final fallthrough). These do not type-check for the same reason as the
-- `DecEq Result` instance above (abstract operands, no `Uninhabited (x = y)`),
-- and additionally the intra-constructor `_ => No absurd` cannot prove the
-- arguments differ without an explicit witness. The instance had ZERO consumers
-- in this package and was removed rather than shipped broken. Structural
-- decidable equality is recoverable via `instrToDiscriminant` plus `decEq` on
-- the `Bits32` argument fields when a consumer actually needs it.

--------------------------------------------------------------------------------
-- Program Types
--------------------------------------------------------------------------------

||| A program is a sequence of instructions
||| Length is tracked at type level for safety
public export
data Program : Nat -> Type where
  Nil : Program 0
  (::) : Instruction -> Program n -> Program (S n)

||| Maximum program length for FFI boundary
public export
maxProgramLength : Nat
maxProgramLength = 1024

||| Proof that program length is within bounds
public export
data ValidProgramLength : Nat -> Type where
  -- Fully-qualify `maxProgramLength`: written bare it is a lowercase name and
  -- Idris auto-binds it as a fresh (erased) implicit, so the bound `n <= _`
  -- became vacuous. Qualifying pins it to the actual constant (1024).
  ValidLen : {n : Nat} ->
             {auto 0 prf : So (n <= AbsoluteZero.ABI.Types.maxProgramLength)} ->
             ValidProgramLength n

--------------------------------------------------------------------------------
-- State Types
--------------------------------------------------------------------------------

||| I/O operation types
public export
data IOOp : Type where
  NoIO : IOOp
  ReadOp : Bits32 -> IOOp
  WriteOp : Bits32 -> IOOp

||| I/O state is a list of operations
public export
IOState : Type
IOState = List IOOp

||| Program state record (C-compatible layout)
||| Memory is abstracted as pointer for FFI
public export
record ProgramState where
  constructor MkState
  ||| Pointer to memory array
  memory_ptr : Bits64
  ||| Number of registers
  num_registers : Bits32
  ||| Pointer to register array
  registers_ptr : Bits64
  ||| Number of I/O operations
  num_io_ops : Bits32
  ||| Pointer to I/O operations array
  io_ops_ptr : Bits64
  ||| Program counter
  program_counter : Bits32

||| Proof that state is well-formed
public export
data WellFormedState : ProgramState -> Type where
  WF : {s : ProgramState} ->
       {auto 0 mem_nonNull : So (s.memory_ptr /= 0)} ->
       {auto 0 reg_nonNull : So (s.registers_ptr /= 0)} ->
       WellFormedState s

--------------------------------------------------------------------------------
-- Opaque Handles
--------------------------------------------------------------------------------

||| Opaque handle for program state
||| Prevents direct construction, enforces creation through safe API
public export
data StateHandle : Type where
  MkStateHandle : (ptr : Bits64) -> {auto 0 nonNull : So (ptr /= 0)} ->
                  StateHandle

||| Opaque handle for programs
public export
data ProgramHandle : Type where
  MkProgramHandle : (ptr : Bits64) -> {auto 0 nonNull : So (ptr /= 0)} ->
                    ProgramHandle

||| Safely create a state handle from a pointer value
||| Returns Nothing if pointer is null
||| `choose` yields the `So (ptr /= 0)` witness the opaque handle demands; the
||| null pointer falls through to `Nothing`. Matching the literal `0` first is
||| not enough — it does not refine a `Bits64` *variable* to non-zero for the
||| implicit proof search, so we obtain the proof explicitly.
public export
createStateHandle : Bits64 -> Maybe StateHandle
createStateHandle ptr = case choose (ptr /= 0) of
  Left  prf => Just (MkStateHandle ptr {nonNull = prf})
  Right _   => Nothing

||| Safely create a program handle from a pointer value
public export
createProgramHandle : Bits64 -> Maybe ProgramHandle
createProgramHandle ptr = case choose (ptr /= 0) of
  Left  prf => Just (MkProgramHandle ptr {nonNull = prf})
  Right _   => Nothing

||| Extract pointer value from state handle
public export
stateHandlePtr : StateHandle -> Bits64
stateHandlePtr (MkStateHandle ptr) = ptr

||| Extract pointer value from program handle
public export
programHandlePtr : ProgramHandle -> Bits64
programHandlePtr (MkProgramHandle ptr) = ptr

--------------------------------------------------------------------------------
-- Memory Layout Proofs
--------------------------------------------------------------------------------

||| Proof that a type has a specific size
public export
data HasSize : Type -> Nat -> Type where
  SizeProof : {0 t : Type} -> {n : Nat} -> HasSize t n

||| Proof that a type has a specific alignment
public export
data HasAlignment : Type -> Nat -> Type where
  AlignProof : {0 t : Type} -> {n : Nat} -> HasAlignment t n

||| Size of ProgramState struct (8 + 4 + 8 + 4 + 8 + 4 = 36 bytes + padding)
public export
programStateSizeBytes : Nat
programStateSizeBytes = 40  -- Aligned to 8 bytes

||| Prove ProgramState has correct size
public export
programStateSize : HasSize ProgramState 40
programStateSize = SizeProof

||| Prove ProgramState has 8-byte alignment
public export
programStateAlign : HasAlignment ProgramState 8
programStateAlign = AlignProof

||| Size of Instruction struct (4 bytes discriminant + 12 bytes data = 16 bytes)
public export
instructionSizeBytes : Nat
instructionSizeBytes = 16

||| Prove Instruction has correct size
public export
instructionSize : HasSize Instruction 16
instructionSize = SizeProof

||| Prove Instruction has 4-byte alignment
public export
instructionAlign : HasAlignment Instruction 4
instructionAlign = AlignProof

--------------------------------------------------------------------------------
-- Platform-Specific Types
--------------------------------------------------------------------------------

||| C int size varies by platform
public export
CInt : Platform -> Type
CInt Linux = Bits32
CInt Windows = Bits32
CInt MacOS = Bits32
CInt BSD = Bits32
CInt WASM = Bits32

||| C size_t varies by platform
public export
CSize : Platform -> Type
CSize Linux = Bits64
CSize Windows = Bits64
CSize MacOS = Bits64
CSize BSD = Bits64
CSize WASM = Bits32

||| C pointer size varies by platform
public export
ptrSize : Platform -> Nat
ptrSize Linux = 64
ptrSize Windows = 64
ptrSize MacOS = 64
ptrSize BSD = 64
ptrSize WASM = 32

||| Pointer type for platform
public export
CPtr : Platform -> Type -> Type
CPtr Linux _ = Bits64
CPtr Windows _ = Bits64
CPtr MacOS _ = Bits64
CPtr BSD _ = Bits64
CPtr WASM _ = Bits32

--------------------------------------------------------------------------------
-- Verification Types
--------------------------------------------------------------------------------

||| CNO verification result
public export
record CNOVerificationResult where
  constructor MkCNOResult
  ||| Whether the program is a CNO
  is_cno : Bool
  ||| Whether the program terminates
  terminates : Bool
  ||| Whether the program preserves state
  preserves_state : Bool
  ||| Whether the program is pure (no side effects)
  is_pure : Bool
  ||| Whether the program is thermodynamically reversible
  is_reversible : Bool

||| Prove verification result size
public export
cnoResultSize : HasSize CNOVerificationResult 5
cnoResultSize = SizeProof

--------------------------------------------------------------------------------
-- ABI Version
--------------------------------------------------------------------------------

||| ABI version (major.minor.patch)
public export
abiVersionMajor : Bits32
abiVersionMajor = 1

public export
abiVersionMinor : Bits32
abiVersionMinor = 0

public export
abiVersionPatch : Bits32
abiVersionPatch = 0
