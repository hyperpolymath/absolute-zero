/- Filesystem CNOs: Reversible File Operations

   Formalizes Certified Null Operations in filesystem contexts,
   integrating Valence Shell reversibility proofs.

   Author: Jonathan D. A. Jewell
   Project: Absolute Zero (integrating Valence Shell)
   License: MPL-2.0
-/

-- Std.Data.List.Basic was vestigial in pre-Batteries layouts. The List
-- type used here comes from core Lean 4's Init; no external imports required.

namespace FilesystemCNO

/-! ## Filesystem Model -/

/-- File paths. `abbrev` so String's Repr/BEq propagate. -/
abbrev Path : Type := String

/-- File permissions (simplified) -/
inductive Permission where
  | Read : Permission
  | Write : Permission
  | Execute : Permission
  deriving Repr, BEq

/-- Set of permissions on a file. `abbrev` so List instances propagate. -/
abbrev PermSet : Type := List Permission

/-- File content (byte array). `abbrev` so List instances propagate. -/
abbrev FileContent : Type := List Nat

/-- Filesystem metadata -/
structure FileMetadata where
  permissions : PermSet
  owner : Nat  -- User ID
  size : Nat
  mtime : Nat  -- Modification timestamp
  deriving Repr, BEq

/-- File entries -/
inductive FileEntry where
  | File : Path → FileContent → FileMetadata → FileEntry
  | Directory : Path → List FileEntry → FileMetadata → FileEntry
  | Symlink : Path → Path → FileMetadata → FileEntry
  deriving Repr

/-- Filesystem state. `abbrev` so List instances propagate. -/
abbrev Filesystem : Type := List FileEntry

/-! ## Occupancy predicates

These are the preconditions of the Coq lemmas in
`proofs/coq/filesystem/FilesystemCNO.v`, mirrored verbatim. The laws below
hold on the concrete Coq model ONLY under them; stating the laws without
them let `False` be derived (issue #125). -/

/-- No directory entry at `p`. Precondition of Coq's `mkdir_rmdir_inverse`. -/
def noDirAt (p : Path) (fs : Filesystem) : Prop :=
  ∀ e, e ∈ fs → match e with
    | FileEntry.Directory p' _ _ => p ≠ p'
    | _ => True

/-- No file entry at `p`. Precondition of Coq's `create_unlink_inverse`. -/
def noFileAt (p : Path) (fs : Filesystem) : Prop :=
  ∀ e, e ∈ fs → match e with
    | FileEntry.File p' _ _ => p ≠ p'
    | _ => True

/-- No entry of any kind at `p`. Precondition of Coq's `rename_inverse`. -/
def noEntryAt (p : Path) (fs : Filesystem) : Prop :=
  ∀ e, e ∈ fs → match e with
    | FileEntry.File p' _ _ => p ≠ p'
    | FileEntry.Directory p' _ _ => p ≠ p'
    | FileEntry.Symlink p' _ _ => p ≠ p'

/-! ## Filesystem Operations -/

/-- Create directory -/
-- AXIOM: mkdir; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom mkdir : Path → Filesystem → Filesystem

/-- Remove directory -/
-- AXIOM: rmdir; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom rmdir : Path → Filesystem → Filesystem

/-- Create file -/
-- AXIOM: create; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom create : Path → Filesystem → Filesystem

/-- Delete file -/
-- AXIOM: unlink; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom unlink : Path → Filesystem → Filesystem

/-- Read file content -/
-- AXIOM: readFile; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom readFile : Path → Filesystem → Option FileContent

/-- Write file content -/
-- AXIOM: writeFile; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom writeFile : Path → FileContent → Filesystem → Filesystem

/-- Get file metadata -/
-- AXIOM: stat; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom stat : Path → Filesystem → Option FileMetadata

/-- Change permissions -/
-- AXIOM: chmod; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom chmod : Path → PermSet → Filesystem → Filesystem

/-- Change owner -/
-- AXIOM: chown; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom chown : Path → Nat → Filesystem → Filesystem

/-- Rename/move file -/
-- AXIOM: rename; opaque POSIX primitive op; §(c) per docs/proof-debt.md.
axiom rename : Path → Path → Filesystem → Filesystem

/-! ## Operation Axioms -/

/-- mkdir followed by rmdir is identity — on a filesystem with no directory
    at `p`. Without the precondition the law is false (mkdir on an existing
    directory is a no-op, so rmdir then removes it) and, together with
    `mkdir_idempotent` and `mkdir_not_identity`, derived `False` (#125). -/
-- AXIOM: mkdir_rmdir_inverse; POSIX-semantics specification (mirrors Coq Lemma, same precondition); §(c) per docs/proof-debt.md.
axiom mkdir_rmdir_inverse (p : Path) (fs : Filesystem) :
  noDirAt p fs →
  rmdir p (mkdir p fs) = fs

/-- create followed by unlink is identity — on a filesystem with no file at
    `p` (the precondition Coq's `create_unlink_inverse` states). -/
-- AXIOM: create_unlink_inverse; POSIX-semantics specification (mirrors Coq Lemma, same precondition); §(c) per docs/proof-debt.md.
axiom create_unlink_inverse (p : Path) (fs : Filesystem) :
  noFileAt p fs →
  unlink p (create p fs) = fs

/-- read followed by write is identity -/
-- AXIOM: read_write_identity; POSIX-semantics specification (mirrors Coq); §(c) per docs/proof-debt.md.
axiom read_write_identity (p : Path) (fs : Filesystem) (content : FileContent) :
  readFile p fs = some content →
  writeFile p content fs = fs

/-- chmod to current permissions is identity -/
-- AXIOM: chmod_identity; POSIX-semantics specification (mirrors Coq); §(c) per docs/proof-debt.md.
axiom chmod_identity (p : Path) (fs : Filesystem) (meta : FileMetadata) :
  stat p fs = some meta →
  chmod p meta.permissions fs = fs

/-- rename to same path is identity -/
-- AXIOM: rename_identity; POSIX-semantics specification (mirrors Coq); §(c) per docs/proof-debt.md.
axiom rename_identity (p : Path) (fs : Filesystem) :
  rename p p fs = fs

/-- rename A to B followed by rename B to A is identity — when `p1 ≠ p2` and
    nothing lives at `p2` (both preconditions Coq's `rename_inverse` states). -/
-- AXIOM: rename_inverse; POSIX-semantics specification (mirrors Coq Lemma, same preconditions); §(c) per docs/proof-debt.md.
axiom rename_inverse (p1 p2 : Path) (fs : Filesystem) :
  p1 ≠ p2 →
  noEntryAt p2 fs →
  rename p2 p1 (rename p1 p2 fs) = fs

/-! ## Filesystem CNO Definition -/

/-- A filesystem operation. `abbrev` so HAppend / fn instances propagate. -/
abbrev FsOp : Type := Filesystem → Filesystem

/-- A filesystem operation is a CNO if it leaves filesystem unchanged -/
def isFsCNO (op : FsOp) : Prop :=
  ∀ fs : Filesystem, op fs = fs

/-! ## Basic Filesystem CNOs -/

/-- Identity operation -/
def fs_nop : FsOp := fun fs => fs

theorem fs_nop_is_cno : isFsCNO fs_nop := by
  unfold isFsCNO fs_nop
  intro fs
  rfl

/-- mkdir followed by rmdir. `noncomputable` — calls axioms `mkdir`/`rmdir`. -/
noncomputable def mkdirRmdirOp (p : Path) : FsOp :=
  fun fs => rmdir p (mkdir p fs)

/-- mkdir;rmdir is the identity on every filesystem with no directory at `p`
    (Coq `mkdir_rmdir_is_cno`, same statement). The unconditional
    `isFsCNO (mkdirRmdirOp p)` is not provable and is false on the Coq model. -/
theorem mkdir_rmdir_is_cno (p : Path) (fs : Filesystem) (h : noDirAt p fs) :
    mkdirRmdirOp p fs = fs := by
  unfold mkdirRmdirOp
  exact mkdir_rmdir_inverse p fs h

/-- create followed by unlink. `noncomputable` — wraps axioms. -/
noncomputable def createUnlinkOp (p : Path) : FsOp :=
  fun fs => unlink p (create p fs)

/-- create;unlink is the identity on every filesystem with no file at `p`
    (Coq `create_unlink_is_cno`, same statement). -/
theorem create_unlink_is_cno (p : Path) (fs : Filesystem) (h : noFileAt p fs) :
    createUnlinkOp p fs = fs := by
  unfold createUnlinkOp
  exact create_unlink_inverse p fs h

/-- read followed by write. `noncomputable` — wraps axioms. -/
noncomputable def readWriteOp (p : Path) : FsOp :=
  fun fs =>
    match readFile p fs with
    | some content => writeFile p content fs
    | none => fs

theorem read_write_is_cno (p : Path) :
    isFsCNO (readWriteOp p) := by
  unfold isFsCNO readWriteOp
  intro fs
  cases h : readFile p fs with
  | none => rfl
  | some content =>
      exact read_write_identity p fs content h

/-- chmod to current permissions. `noncomputable` — wraps axioms. -/
noncomputable def chmodNopOp (p : Path) : FsOp :=
  fun fs =>
    match stat p fs with
    | some meta => chmod p meta.permissions fs
    | none => fs

theorem chmod_nop_is_cno (p : Path) :
    isFsCNO (chmodNopOp p) := by
  unfold isFsCNO chmodNopOp
  intro fs
  cases h : stat p fs with
  | none => rfl
  | some meta =>
      exact chmod_identity p fs meta h

/-- rename to same path. `noncomputable` — wraps axiom. -/
noncomputable def renameNopOp (p : Path) : FsOp :=
  fun fs => rename p p fs

theorem rename_nop_is_cno (p : Path) :
    isFsCNO (renameNopOp p) := by
  unfold isFsCNO renameNopOp
  intro fs
  exact rename_identity p fs

/-! ## Composition of Filesystem Operations -/

/-- Sequential composition -/
def fsSeqComp (op1 op2 : FsOp) : FsOp :=
  fun fs => op2 (op1 fs)

notation:60 op1 " ;; " op2 => fsSeqComp op1 op2

/-- Composition of CNOs is a CNO -/
theorem fs_cno_composition (op1 op2 : FsOp) :
    isFsCNO op1 →
    isFsCNO op2 →
    isFsCNO (op1 ;; op2) := by
  intro h1 h2
  unfold isFsCNO at *
  intro fs
  unfold fsSeqComp
  rw [h1, h2]

/-! ## Non-CNO Operations -/

/-- mkdir alone is NOT a CNO. Coq proves this Lemma on its concrete model
    (`exists "" nil`); over opaque operations it has to be assumed. -/
-- AXIOM: mkdir_not_identity; mirrors the Coq Lemma (proved on the concrete model); §(c) per docs/proof-debt.md.
axiom mkdir_not_identity : ∃ (p : Path) (fs : Filesystem), mkdir p fs ≠ fs

theorem mkdir_alone_not_cno :
    ¬ (∀ p, isFsCNO (fun fs => mkdir p fs)) := by
  intro h
  obtain ⟨p, fs, h_neq⟩ := mkdir_not_identity
  have := h p
  unfold isFsCNO at this
  have := this fs
  contradiction

/-! ## Valence Shell Integration -/

/-- A Valence Shell reversible operation -/
def valenceReversible (op : FsOp) (op_inv : FsOp) : Prop :=
  ∀ fs, op_inv (op fs) = fs

/-- Valence Shell reversible pairs are CNOs -/
theorem valence_reversible_pair_is_cno (op op_inv : FsOp) :
    valenceReversible op op_inv →
    isFsCNO (op ;; op_inv) := by
  intro h
  unfold isFsCNO fsSeqComp
  intro fs
  exact h fs

/-- Example: mkdir/rmdir pair from Valence Shell (Coq `valence_mkdir_rmdir`):
    reversible on every filesystem with no directory at `p`. -/
example (p : Path) (fs : Filesystem) (h : noDirAt p fs) :
    rmdir p (mkdir p fs) = fs :=
  mkdir_rmdir_inverse p fs h

/-- Example: create/unlink pair from Valence Shell (Coq `valence_create_unlink`):
    reversible on every filesystem with no file at `p`. -/
example (p : Path) (fs : Filesystem) (h : noFileAt p fs) :
    unlink p (create p fs) = fs :=
  create_unlink_inverse p fs h

/-! ## Snapshot and Restore -/

/-- Snapshot operation -/
-- AXIOM: snapshot; opaque snapshot primitive; §(c) per docs/proof-debt.md.
axiom snapshot : Filesystem → Filesystem

/-- Restore from snapshot -/
-- AXIOM: restore; opaque restore primitive; §(c) per docs/proof-debt.md.
axiom restore : Filesystem → Filesystem → Filesystem

/-- snapshot followed by restore is identity -/
axiom snapshot_restore_identity (fs : Filesystem) :
  restore (snapshot fs) fs = fs

-- `noncomputable` because `restore` and `snapshot` are axioms with no
-- executable body; without this Lean 4.16 refuses to emit code for `def`.
noncomputable def snapshotRestoreOp : FsOp :=
  fun fs => restore (snapshot fs) fs

theorem snapshot_restore_is_cno :
    isFsCNO snapshotRestoreOp := by
  unfold isFsCNO snapshotRestoreOp
  intro fs
  exact snapshot_restore_identity fs

/-! ## Idempotent Operations -/

/-- An operation is idempotent if applying it twice = applying it once -/
def isIdempotent (op : FsOp) : Prop :=
  ∀ fs, op (op fs) = op fs

/-- mkdir is idempotent (but not CNO). Coq proves this Lemma on its concrete
    model; over opaque operations it has to be assumed. Consistent with the
    conditional `mkdir_rmdir_inverse`: `mkdir p fs` has a directory at `p`,
    so the inverse law does not apply to it. -/
-- AXIOM: mkdir_idempotent; mirrors the Coq Lemma (proved on the concrete model); §(c) per docs/proof-debt.md.
axiom mkdir_idempotent (p : Path) :
  isIdempotent (fun fs => mkdir p fs)

/-- The unconditional law `∀ p fs, rmdir p (mkdir p fs) = fs` — the former
    statement of `mkdir_rmdir_inverse` — is refuted by `mkdir_idempotent` and
    `mkdir_not_identity` alone: on `mkdir p fs` the second `mkdir` is a no-op,
    so the law would force `mkdir p fs = fs`. This is the derivation that
    made issue #125's `False` proof go through; it is now a theorem about the
    old statement instead of a contradiction in the axioms. -/
theorem unconditional_mkdir_rmdir_inverse_is_false :
    ¬ ∀ (p : Path) (fs : Filesystem), rmdir p (mkdir p fs) = fs := by
  intro law
  obtain ⟨p, fs, hne⟩ := mkdir_not_identity
  have h1 : rmdir p (mkdir p (mkdir p fs)) = mkdir p fs := law p (mkdir p fs)
  have h2 : mkdir p (mkdir p fs) = mkdir p fs := mkdir_idempotent p fs
  rw [h2, law p fs] at h1
  exact hne h1.symm

/-- Idempotent does NOT imply CNO.
    Proof: destructure mkdir_not_identity to get a specific (p, fs) where
    mkdir p fs ≠ fs, then exhibit `fun fs => mkdir p fs` as the witness.
    It is idempotent (mkdir_idempotent), but it cannot be a CNO: if it were,
    applying it to fs would leave fs unchanged, contradicting h_neq. -/
example : ∃ op : FsOp, isIdempotent op ∧ ¬ isFsCNO op := by
  obtain ⟨p, fs, h_neq⟩ := mkdir_not_identity
  exists (fun fs' => mkdir p fs')
  constructor
  · exact mkdir_idempotent p
  · intro h
    unfold isFsCNO at h
    exact h_neq (h fs)

end FilesystemCNO
