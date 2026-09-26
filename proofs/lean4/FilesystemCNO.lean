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

/-! ## Helper Definitions for Concrete Filesystem Operations -/

/-- Default metadata used when fresh entries are created. -/
def default_meta : FileMetadata :=
  { permissions := [], owner := 0, size := 0, mtime := 0 }

/-- The path of an entry regardless of its kind. -/
def path_of : FileEntry → Path
  | FileEntry.File p _ _ => p
  | FileEntry.Directory p _ _ => p
  | FileEntry.Symlink p _ _ => p

/-- Rename an entry's own path, preserving all other components. -/
def set_path (np : Path) : FileEntry → FileEntry
  | FileEntry.File _ c m => FileEntry.File np c m
  | FileEntry.Directory _ es m => FileEntry.Directory np es m
  | FileEntry.Symlink _ t m => FileEntry.Symlink np t m

/-- Set permissions on a metadata record. -/
def set_perms (perms : PermSet) (m : FileMetadata) : FileMetadata :=
  { permissions := perms, owner := m.owner, size := m.size, mtime := m.mtime }

/-- Set owner on a metadata record. -/
def set_owner (o : Nat) (m : FileMetadata) : FileMetadata :=
  { permissions := m.permissions, owner := o, size := m.size, mtime := m.mtime }

/-- Check if a directory with the given path exists in the filesystem. -/
def dir_exists (p : Path) : Filesystem → Bool
  | [] => false
  | e :: rest => match e with
    | FileEntry.Directory p' _ _ => (p == p') || dir_exists p rest
    | _ => dir_exists p rest

@[simp] lemma path_of_set_path (p : Path) (e : FileEntry) :
    path_of (set_path p e) = p := by
  cases e <;> rfl

@[simp] lemma set_path_id (e : FileEntry) :
    set_path (path_of e) e = e := by
  cases e <;> rfl

@[simp] lemma set_path_set_path (p1 p2 : Path) (e : FileEntry) :
    set_path p2 (set_path p1 e) = set_path p2 e := by
  cases e <;> rfl

@[simp] lemma set_perms_id (m : FileMetadata) :
    set_perms m.permissions m = m := by
  cases m; rfl

/-! ## Filesystem Operations (Concrete, executable definitions) -/

/-- Create directory: prepends fresh directory if absent, no-op if exists. -/
def mkdir (p : Path) (fs : Filesystem) : Filesystem :=
  if dir_exists p fs then fs else FileEntry.Directory p [] default_meta :: fs

/-- Remove empty directory: drops first matching empty directory. -/
def rmdir (p : Path) : Filesystem → Filesystem
  | [] => []
  | e :: rest => match e with
    | FileEntry.Directory p' [] _ => if p == p' then rest else e :: rmdir p rest
    | _ => e :: rmdir p rest

/-- Create file: prepends fresh empty file. -/
def create (p : Path) (fs : Filesystem) : Filesystem :=
  FileEntry.File p [] default_meta :: fs

/-- Delete file: drops first matching file. -/
def unlink (p : Path) : Filesystem → Filesystem
  | [] => []
  | e :: rest => match e with
    | FileEntry.File p' _ _ => if p == p' then rest else e :: unlink p rest
    | _ => e :: unlink p rest

/-- Read file content: content of first matching file, if any. -/
def readFile (p : Path) : Filesystem → Option FileContent
  | [] => none
  | e :: rest => match e with
    | FileEntry.File p' c _ => if p == p' then some c else readFile p rest
    | _ => readFile p rest

/-- Write file content: update content of first matching file. -/
def writeFile (p : Path) (content : FileContent) : Filesystem → Filesystem
  | [] => []
  | e :: rest => match e with
    | FileEntry.File p' c m =>
      if p == p' then FileEntry.File p' content m :: rest
      else FileEntry.File p' c m :: writeFile p content rest
    | _ => e :: writeFile p content rest

/-- Get file metadata: metadata of first matching entry. -/
def stat (p : Path) : Filesystem → Option FileMetadata
  | [] => none
  | e :: rest => match e with
    | FileEntry.File p' _ m => if p == p' then some m else stat p rest
    | FileEntry.Directory p' _ m => if p == p' then some m else stat p rest
    | FileEntry.Symlink p' _ m => if p == p' then some m else stat p rest

/-- Change permissions of first matching entry. -/
def chmod (p : Path) (perms : PermSet) : Filesystem → Filesystem
  | [] => []
  | e :: rest => match e with
    | FileEntry.File p' c m =>
      if p == p' then FileEntry.File p' c (set_perms perms m) :: rest
      else FileEntry.File p' c m :: chmod p perms rest
    | FileEntry.Directory p' es m =>
      if p == p' then FileEntry.Directory p' es (set_perms perms m) :: rest
      else FileEntry.Directory p' es m :: chmod p perms rest
    | FileEntry.Symlink p' t m =>
      if p == p' then FileEntry.Symlink p' t (set_perms perms m) :: rest
      else FileEntry.Symlink p' t m :: chmod p perms rest

/-- Change owner of first matching entry. -/
def chown (p : Path) (o : Nat) : Filesystem → Filesystem
  | [] => []
  | e :: rest => match e with
    | FileEntry.File p' c m =>
      if p == p' then FileEntry.File p' c (set_owner o m) :: rest
      else FileEntry.File p' c m :: chown p o rest
    | FileEntry.Directory p' es m =>
      if p == p' then FileEntry.Directory p' es (set_owner o m) :: rest
      else FileEntry.Directory p' es m :: chown p o rest
    | FileEntry.Symlink p' t m =>
      if p == p' then FileEntry.Symlink p' t (set_owner o m) :: rest
      else FileEntry.Symlink p' t m :: chown p o rest

/-- Rename/move file: retargets path of first matching entry. -/
def rename (p1 p2 : Path) : Filesystem → Filesystem
  | [] => []
  | e :: rest =>
    if p1 == path_of e then set_path p2 e :: rest
    else e :: rename p1 p2 rest

/-- Snapshot operation: capture current filesystem state. -/
def snapshot (fs : Filesystem) : Filesystem := fs

/-- Restore operation: restore from snapshot. -/
def restore (snap : Filesystem) (_current : Filesystem) : Filesystem := snap

/-! ## Helper lemmas -/

lemma no_dir_dir_exists_false (p : Path) (fs : Filesystem) (h : noDirAt p fs) :
    dir_exists p fs = false := by
  induction fs with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | Directory p' es m =>
      have h_not : p ≠ p' := h (FileEntry.Directory p' es m) (List.Mem.head _)
      have h_beq : (p == p') = false := beq_false_of_ne h_not
      have h_rest : noDirAt p rest := fun e' he' => h e' (List.Mem.tail _ he')
      show ((p == p') || dir_exists p rest) = false
      rw [h_beq, ih h_rest]
      rfl
    | File p' c m =>
      have h_rest : noDirAt p rest := fun e' he' => h e' (List.Mem.tail _ he')
      show dir_exists p rest = false
      exact ih h_rest
    | Symlink p' t m =>
      have h_rest : noDirAt p rest := fun e' he' => h e' (List.Mem.tail _ he')
      show dir_exists p rest = false
      exact ih h_rest

/-! ## Operation Theorems (Ported from Coq FilesystemCNO.v) -/

/-- mkdir followed by rmdir is identity — on a filesystem with no directory at `p`. -/
theorem mkdir_rmdir_inverse (p : Path) (fs : Filesystem) (h : noDirAt p fs) :
    rmdir p (mkdir p fs) = fs := by
  unfold mkdir
  have h_false : dir_exists p fs = false := no_dir_dir_exists_false p fs h
  rw [if_neg (by rw [h_false]; decide)]
  show (if p == p then fs else _) = fs
  rw [beq_self_eq_true p]
  rfl

/-- create followed by unlink is identity — on a filesystem with no file at `p`. -/
theorem create_unlink_inverse (p : Path) (fs : Filesystem) (_h : noFileAt p fs) :
    unlink p (create p fs) = fs := by
  unfold create unlink
  show (if p == p then fs else _) = fs
  rw [beq_self_eq_true p]
  rfl

/-- read followed by write is identity -/
theorem read_write_identity (p : Path) (fs : Filesystem) (content : FileContent)
    (h : readFile p fs = some content) :
    writeFile p content fs = fs := by
  induction fs with
  | nil => contradiction
  | cons e rest ih =>
    cases e with
    | File p' c m =>
      by_cases hp : p == p'
      · have hp_eq : p = p' := eq_of_beq hp
        subst hp_eq
        show (if p' == p' then FileEntry.File p' content m :: rest else _) = FileEntry.File p' c m :: rest
        rw [beq_self_eq_true p']
        have h_content : c = content := by
          revert h
          show (if p' == p' then some c else readFile p' rest) = some content → c = content
          rw [beq_self_eq_true p']
          intro h_eq; injection h_eq
        subst h_content
        rfl
      · have h_read : readFile p rest = some content := by
        revert h
        show (if p == p' then some c else readFile p rest) = some content → readFile p rest = some content
        rw [if_neg hp]
        exact id
        show (if p == p' then _ else FileEntry.File p' c m :: writeFile p content rest) = FileEntry.File p' c m :: rest
        rw [if_neg hp]
        rw [ih h_read]
    | Directory p' es m =>
      have h_read : readFile p rest = some content := h
      show FileEntry.Directory p' es m :: writeFile p content rest = FileEntry.Directory p' es m :: rest
      rw [ih h_read]
    | Symlink p' t m =>
      have h_read : readFile p rest = some content := h
      show FileEntry.Symlink p' t m :: writeFile p content rest = FileEntry.Symlink p' t m :: rest
      rw [ih h_read]

/-- chmod to current permissions is identity -/
theorem chmod_identity (p : Path) (fs : Filesystem) (meta : FileMetadata)
    (h : stat p fs = some meta) :
    chmod p meta.permissions fs = fs := by
  induction fs with
  | nil => contradiction
  | cons e rest ih =>
    cases e with
    | File p' c m =>
      by_cases hp : p == p'
      · have hp_eq : p = p' := eq_of_beq hp
        subst hp_eq
        show (if p' == p' then FileEntry.File p' c (set_perms meta.permissions m) :: rest else _) = FileEntry.File p' c m :: rest
        rw [beq_self_eq_true p']
        have h_meta : m = meta := by
          revert h
          show (if p' == p' then some m else stat p' rest) = some meta → m = meta
          rw [beq_self_eq_true p']
          intro h_eq; injection h_eq
        subst h_meta
        rw [set_perms_id]
      · have h_stat : stat p rest = some meta := by
          revert h
          show (if p == p' then some m else stat p rest) = some meta → stat p rest = some meta
          rw [if_neg hp]
          exact id
        show (if p == p' then _ else FileEntry.File p' c m :: chmod p meta.permissions rest) = FileEntry.File p' c m :: rest
        rw [if_neg hp]
        rw [ih h_stat]
    | Directory p' es m =>
      by_cases hp : p == p'
      · have hp_eq : p = p' := eq_of_beq hp
        subst hp_eq
        show (if p' == p' then FileEntry.Directory p' es (set_perms meta.permissions m) :: rest else _) = FileEntry.Directory p' es m :: rest
        rw [beq_self_eq_true p']
        have h_meta : m = meta := by
          revert h
          show (if p' == p' then some m else stat p' rest) = some meta → m = meta
          rw [beq_self_eq_true p']
          intro h_eq; injection h_eq
        subst h_meta
        rw [set_perms_id]
      · have h_stat : stat p rest = some meta := by
          revert h
          show (if p == p' then some m else stat p rest) = some meta → stat p rest = some meta
          rw [if_neg hp]
          exact id
        show (if p == p' then _ else FileEntry.Directory p' es m :: chmod p meta.permissions rest) = FileEntry.Directory p' es m :: rest
        rw [if_neg hp]
        rw [ih h_stat]
    | Symlink p' t m =>
      by_cases hp : p == p'
      · have hp_eq : p = p' := eq_of_beq hp
        subst hp_eq
        show (if p' == p' then FileEntry.Symlink p' t (set_perms meta.permissions m) :: rest else _) = FileEntry.Symlink p' t m :: rest
        rw [beq_self_eq_true p']
        have h_meta : m = meta := by
          revert h
          show (if p' == p' then some m else stat p' rest) = some meta → m = meta
          rw [beq_self_eq_true p']
          intro h_eq; injection h_eq
        subst h_meta
        rw [set_perms_id]
      · have h_stat : stat p rest = some meta := by
          revert h
          show (if p == p' then some m else stat p rest) = some meta → stat p rest = some meta
          rw [if_neg hp]
          exact id
        show (if p == p' then _ else FileEntry.Symlink p' t m :: chmod p meta.permissions rest) = FileEntry.Symlink p' t m :: rest
        rw [if_neg hp]
        rw [ih h_stat]

/-- rename to same path is identity -/
theorem rename_identity (p : Path) (fs : Filesystem) :
    rename p p fs = fs := by
  induction fs with
  | nil => rfl
  | cons e rest ih =>
    show (if p == path_of e then set_path p e :: rest else e :: rename p p rest) = e :: rest
    by_cases hp : p == path_of e
    · rw [if_pos hp]
      have hp_eq : p = path_of e := eq_of_beq hp
      subst hp_eq
      rw [set_path_id]
    · rw [if_neg hp]
      rw [ih]

/-- rename A to B followed by rename B to A is identity -/
theorem rename_inverse (p1 p2 : Path) (fs : Filesystem) (hneq : p1 ≠ p2) (hno : noEntryAt p2 fs) :
    rename p2 p1 (rename p1 p2 fs) = fs := by
  induction fs with
  | nil => rfl
  | cons e rest ih =>
    show rename p2 p1 (if p1 == path_of e then set_path p2 e :: rest else e :: rename p1 p2 rest) = e :: rest
    by_cases hp1 : p1 == path_of e
    · rw [if_pos hp1]
      show (if p2 == path_of (set_path p2 e) then set_path p1 (set_path p2 e) :: rest else _) = e :: rest
      rw [path_of_set_path]
      rw [beq_self_eq_true p2]
      rw [if_pos rfl]
      rw [set_path_set_path]
      have hp1_eq : p1 = path_of e := eq_of_beq hp1
      subst hp1_eq
      rw [set_path_id]
    · rw [if_neg hp1]
      show (if p2 == path_of e then _ else e :: rename p2 p1 (rename p1 p2 rest)) = e :: rest
      have hp2_ne : p2 ≠ path_of e := by
        intro h_contra
        specialize hno e (List.Mem.head _)
        cases e with
        | File p' _ _ => exact hno h_contra
        | Directory p' _ _ => exact hno h_contra
        | Symlink p' _ _ => exact hno h_contra
      have hp2_beq : (p2 == path_of e) = false := beq_false_of_ne hp2_ne
      rw [if_neg (by rw [hp2_beq]; decide)]
      have hno_rest : noEntryAt p2 rest := fun e' he' => hno e' (List.Mem.tail _ he')
      rw [ih hno_rest]

/-- snapshot followed by restore is identity -/
theorem snapshot_restore_identity (fs : Filesystem) :
    restore (snapshot fs) fs = fs := rfl

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

/-- mkdir followed by rmdir. -/
def mkdirRmdirOp (p : Path) : FsOp :=
  fun fs => rmdir p (mkdir p fs)

/-- mkdir;rmdir is the identity on every filesystem with no directory at `p`. -/
theorem mkdir_rmdir_is_cno (p : Path) (fs : Filesystem) (h : noDirAt p fs) :
    mkdirRmdirOp p fs = fs := by
  unfold mkdirRmdirOp
  exact mkdir_rmdir_inverse p fs h

/-- create followed by unlink. -/
def createUnlinkOp (p : Path) : FsOp :=
  fun fs => unlink p (create p fs)

/-- create;unlink is the identity on every filesystem with no file at `p`. -/
theorem create_unlink_is_cno (p : Path) (fs : Filesystem) (h : noFileAt p fs) :
    createUnlinkOp p fs = fs := by
  unfold createUnlinkOp
  exact create_unlink_inverse p fs h

/-- read followed by write. -/
def readWriteOp (p : Path) : FsOp :=
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

/-- chmod to current permissions. -/
def chmodNopOp (p : Path) : FsOp :=
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

/-- rename to same path. -/
def renameNopOp (p : Path) : FsOp :=
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

/-- mkdir alone is NOT a CNO. -/
theorem mkdir_not_identity : ∃ (p : Path) (fs : Filesystem), mkdir p fs ≠ fs := by
  exists ""
  exists []
  unfold mkdir dir_exists
  intro h
  contradiction

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

def snapshotRestoreOp : FsOp :=
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

/-- mkdir is idempotent (but not CNO). -/
theorem mkdir_idempotent (p : Path) :
    isIdempotent (fun fs => mkdir p fs) := by
  intro fs
  unfold mkdir
  by_cases h : dir_exists p fs = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h]
    have h_dir : dir_exists p (FileEntry.Directory p [] default_meta :: fs) = true := by
      show ((p == p) || dir_exists p fs) = true
      rw [beq_self_eq_true p]
      rfl
    rw [if_pos h_dir]

/-- The unconditional law `∀ p fs, rmdir p (mkdir p fs) = fs` is refuted by
    `mkdir_idempotent` and `mkdir_not_identity`. -/
theorem unconditional_mkdir_rmdir_inverse_is_false :
    ¬ ∀ (p : Path) (fs : Filesystem), rmdir p (mkdir p fs) = fs := by
  intro law
  obtain ⟨p, fs, hne⟩ := mkdir_not_identity
  have h1 : rmdir p (mkdir p (mkdir p fs)) = mkdir p fs := law p (mkdir p fs)
  have h2 : mkdir p (mkdir p fs) = mkdir p fs := mkdir_idempotent p fs
  rw [h2, law p fs] at h1
  exact hne h1.symm

/-- Idempotent does NOT imply CNO. -/
example : ∃ op : FsOp, isIdempotent op ∧ ¬ isFsCNO op := by
  obtain ⟨p, fs, h_neq⟩ := mkdir_not_identity
  exists (fun fs' => mkdir p fs')
  constructor
  · exact mkdir_idempotent p
  · intro h
    unfold isFsCNO at h
    exact h_neq (h fs)

end FilesystemCNO
