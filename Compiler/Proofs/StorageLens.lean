import Compiler.Proofs.MappingSlot

namespace Compiler.Proofs

open Compiler.Proofs.IRGeneration (IRStorageSlot IRStorageWord)

/-!
Proof-facing storage lenses.

This module is the first C2 part 2 entry point.  It keeps the lens surface
small: a `ViewLens` observes through a source without mutation, while a
`StorageLens` additionally carries the write half needed by later frame and
composition proofs.
-/

/-- Proof-side flat storage carrier. -/
abbrev Storage : Type := IRStorageSlot → IRStorageWord

/--
Read-only lens from `σ` to `α`.

The `slotOffset` and `decode` fields record the storage-observation shape used
by concrete storage views.  Generic views can still provide any `read` function;
composition proofs only rely on `read`.
-/
structure ViewLens (σ : Type) (α : Type) where
  slotOffset : Nat
  decode : IRStorageWord → α
  read : σ → α

/-- Read-write lens from `σ` to `α`. -/
structure StorageLens (σ : Type) (α : Type) where
  slotOffset : Nat
  decode : IRStorageWord → α
  encode : α → IRStorageWord
  read : σ → α
  write : α → σ → σ

namespace ViewLens

/-- Read one resolved storage word. -/
def word (slot : Nat) : ViewLens Storage IRStorageWord :=
  { slotOffset := slot
    decode := id
    read := fun storage => abstractLoadStorageOrMapping storage slot }

/-- Read and decode one resolved storage word. -/
def wordDecoded (slot : Nat) (decode : IRStorageWord → α) : ViewLens Storage α :=
  { slotOffset := slot
    decode := decode
    read := fun storage => decode (abstractLoadStorageOrMapping storage slot) }

/-- Read one Solidity mapping word using the shared mapping-slot model. -/
def mappingWord (baseSlot key : Nat) : ViewLens Storage IRStorageWord :=
  word (solidityMappingSlot baseSlot key)

/-- Read and decode one Solidity mapping word using the shared mapping-slot model. -/
def mappingWordDecoded
    (baseSlot key : Nat) (decode : IRStorageWord → α) : ViewLens Storage α :=
  wordDecoded (solidityMappingSlot baseSlot key) decode

@[simp] theorem word_read (slot : Nat) (storage : Storage) :
    (word slot).read storage = abstractLoadStorageOrMapping storage slot := rfl

@[simp] theorem wordDecoded_read
    (slot : Nat) (decode : IRStorageWord → α) (storage : Storage) :
    (wordDecoded slot decode).read storage =
      decode (abstractLoadStorageOrMapping storage slot) := rfl

@[simp] theorem mappingWord_read (baseSlot key : Nat) (storage : Storage) :
    (mappingWord baseSlot key).read storage =
      abstractLoadStorageOrMapping storage (solidityMappingSlot baseSlot key) := rfl

/-- A flat-slot write to a projected-distinct slot preserves a word view. -/
theorem word_read_store_other
    (storage : Storage)
    (readSlot writeSlot value : Nat)
    (h : IRStorageSlot.ofNat readSlot ≠ IRStorageSlot.ofNat writeSlot) :
    (word readSlot).read
      (abstractStoreStorageOrMapping storage writeSlot value) =
    (word readSlot).read storage := by
  simp [word, abstractLoadStorageOrMapping, abstractStoreStorageOrMapping, h]

end ViewLens

namespace StorageLens

/-- The identity storage lens, useful as the root of storage-view composition. -/
def idStorage : StorageLens Storage Storage :=
  { slotOffset := 0
    decode := fun word _ => word
    encode := fun storage => storage (IRStorageSlot.ofNat 0)
    read := id
    write := fun replacement _ => replacement }

/-- Read-write lens for one resolved storage word. -/
def word (slot : Nat) : StorageLens Storage IRStorageWord :=
  { slotOffset := slot
    decode := id
    encode := id
    read := fun storage => abstractLoadStorageOrMapping storage slot
    write := fun value storage =>
      fun s => if s = IRStorageSlot.ofNat slot then value else storage s }

/-- Project the read half of a storage lens as a view lens. -/
def toViewLens (sl : StorageLens σ α) : ViewLens σ α :=
  { slotOffset := sl.slotOffset
    decode := sl.decode
    read := sl.read }

@[simp] theorem toViewLens_read (sl : StorageLens σ α) (s : σ) :
    sl.toViewLens.read s = sl.read s := rfl

@[simp] theorem word_read (slot : Nat) (storage : Storage) :
    (word slot).read storage = abstractLoadStorageOrMapping storage slot := rfl

@[simp] theorem word_write (slot : Nat) (value : IRStorageWord) (storage : Storage) :
    (word slot).write value storage =
      (fun s => if s = IRStorageSlot.ofNat slot then value else storage s) := rfl

end StorageLens

/-- Compose a read-only view through the read half of a storage lens. -/
def view_lens_comp (vl : ViewLens τ α) (sl : StorageLens σ τ) (s : σ) : α :=
  vl.read (sl.read s)

/--
Composing a view lens with a storage lens is observationally the same as
reading the storage lens focus and then reading the view.
-/
@[simp] theorem view_lens_comp_correct
    (vl : ViewLens τ α) (sl : StorageLens σ τ) (s : σ) :
    view_lens_comp vl sl s = vl.read (sl.read s) := rfl

/-- Project the read-only view carried by a read-write storage lens. -/
def view_lens_of_storage_lens (sl : StorageLens σ α) : ViewLens σ α :=
  sl.toViewLens

/-- The projected view lens observes exactly the storage lens read. -/
@[simp] theorem view_lens_of_storage_lens_correct
    (sl : StorageLens σ α) (s : σ) :
    (view_lens_of_storage_lens sl).read s = sl.read s := rfl

/-- Composing with a projected storage lens view is the same as nested reads. -/
@[simp] theorem view_lens_comp_of_storage_lens_correct
    (outer : StorageLens τ α) (inner : StorageLens σ τ) (s : σ) :
    view_lens_comp (view_lens_of_storage_lens outer) inner s =
      outer.read (inner.read s) := rfl

end Compiler.Proofs
