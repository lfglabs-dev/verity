/-
  C5 step 4 (field-list slice): collapse a CompilationModel field list to
  a source StorageKey, then to the compiler slot via `storageKeySlot`.

  Mapping-entry constructors cover the typed cases that already have a
  StorageKey (`map` / `mapUint` / `map2`). Address-keyed mappingStruct
  / mappingStruct2 members collapse to `mappingSlotLocation` /
  `nestedMappingSlotLocation`. Compatibility `aliasSlots` are extra
  compiler write targets; only the resolved head has a StorageKey.
  bytes32-keyed maps collapse to `solidityMappingSlot` of the 32-byte
  word (no `StorageKey.mapBytes32`). All nine `MappingType.nested`
  key-type pairs collapse to `abstractNestedMappingSlot`.
  Packed bit-ranges extract from the same `storageKeySlot` word
  (`packedExtract`). Compiler packed-read composition with
  SolidityStorage and global MappingCoherent preservation stay open.
-/

import Compiler.Proofs.Storage.MappingCoherence
import Verity.Core.Model.Types
import Compiler.CompilationModel.ValidationHelpers

namespace Compiler.Proofs.Storage.FieldStorageKey

open Verity
open Verity.ContractState
open Compiler.CompilationModel
open Compiler.Proofs.Storage.MappingCoherence
open Compiler.Proofs

/-- Root source key for one resolved field. Transient fields stay off the
    persistent Solidity slot map. Address scalars use `.addr`; every other
    persistent type uses the field's resolved word as `.slot` (mapping
    roots included). -/
def fieldRootKey (f : Field) (resolvedSlot : Nat) : StorageKey :=
  if f.isTransient then
    .transient resolvedSlot
  else
    match f.ty with
    | .address => .addr resolvedSlot
    | _ => .slot resolvedSlot

/-- Named field in a contract field list, if it resolves. -/
def fieldListRootKey (fields : List Field) (name : String) : Option StorageKey :=
  match findFieldWithResolvedSlot fields name with
  | some (f, slot) => some (fieldRootKey f slot)
  | none => none

theorem storageKeySlot_fieldRootKey (f : Field) (slot : Nat) :
    storageKeySlot (fieldRootKey f slot) =
      if f.isTransient then none else some slot := by
  unfold fieldRootKey
  split
  · rfl
  · cases f.ty <;> rfl

theorem fieldListRootKey_eq
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    fieldListRootKey fields name = some (fieldRootKey f slot) := by
  simp [fieldListRootKey, h]

theorem storageKeySlot_fieldListRootKey
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    Option.bind (fieldListRootKey fields name) storageKeySlot =
      if f.isTransient then none else some slot := by
  rw [fieldListRootKey_eq h, Option.bind_some, storageKeySlot_fieldRootKey]

theorem fieldRootKey_uint256
    {f : Field} {slot : Nat}
    (htr : f.isTransient = false) (hty : f.ty = .uint256) :
    fieldRootKey f slot = .slot slot := by
  simp [fieldRootKey, htr, hty]

theorem fieldRootKey_address
    {f : Field} {slot : Nat}
    (htr : f.isTransient = false) (hty : f.ty = .address) :
    fieldRootKey f slot = .addr slot := by
  simp [fieldRootKey, htr, hty]

theorem fieldRootKey_mappingTyped
    {f : Field} {slot : Nat} {mt : MappingType}
    (htr : f.isTransient = false) (hty : f.ty = .mappingTyped mt) :
    fieldRootKey f slot = .slot slot := by
  simp [fieldRootKey, htr, hty]

theorem fieldRootKey_transient {f : Field} {slot : Nat} (htr : f.isTransient = true) :
    fieldRootKey f slot = .transient slot := by
  simp [fieldRootKey, htr]

/-- Persistent `mapping(address => uint256)` entry. -/
def fieldMapKey (f : Field) (resolvedSlot : Nat) (key : Address) : Option StorageKey :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.simple .address) => some (.map resolvedSlot key)
    | _ => none

/-- Persistent `mapping(uint256 => uint256)` entry. -/
def fieldMapUintKey (f : Field) (resolvedSlot : Nat) (key : Uint256) : Option StorageKey :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.simple .uint256) => some (.mapUint resolvedSlot key)
    | _ => none

/-- Persistent `mapping(address => mapping(address => uint256))` entry. -/
def fieldMap2Key (f : Field) (resolvedSlot : Nat) (k1 k2 : Address) : Option StorageKey :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .address .address) => some (.map2 resolvedSlot k1 k2)
    | _ => none

theorem storageKeySlot_fieldMapKey
    {f : Field} {slot : Nat} {key : Address}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.simple .address)) :
    Option.bind (fieldMapKey f slot key) storageKeySlot =
      some (solidityMappingSlot slot (addressToWord key).val) := by
  simp [fieldMapKey, htr, hty, storageKeySlot]

theorem storageKeySlot_fieldMapUintKey
    {f : Field} {slot : Nat} {key : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.simple .uint256)) :
    Option.bind (fieldMapUintKey f slot key) storageKeySlot =
      some (solidityMappingSlot slot key.val) := by
  simp [fieldMapUintKey, htr, hty, storageKeySlot]

theorem storageKeySlot_fieldMap2Key
    {f : Field} {slot : Nat} {k1 k2 : Address}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .address .address)) :
    Option.bind (fieldMap2Key f slot k1 k2) storageKeySlot =
      some (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) := by
  simp [fieldMap2Key, htr, hty, storageKeySlot]

/-- Persistent `mapping(address => mapping(uint256 => uint256))` entry.
    There is no mixed `StorageKey`; the collapse is the nested compiler slot. -/
def fieldMapAddrUintSlot (f : Field) (resolvedSlot : Nat) (k1 : Address) (k2 : Uint256) :
    Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .address .uint256) =>
      some (abstractNestedMappingSlot resolvedSlot (addressToWord k1).val k2.val)
    | _ => none

/-- Persistent `mapping(uint256 => mapping(address => uint256))` entry. -/
def fieldMapUintAddrSlot (f : Field) (resolvedSlot : Nat) (k1 : Uint256) (k2 : Address) :
    Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .uint256 .address) =>
      some (abstractNestedMappingSlot resolvedSlot k1.val (addressToWord k2).val)
    | _ => none

theorem fieldMapAddrUintSlot_eq
    {f : Field} {slot : Nat} {k1 : Address} {k2 : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .address .uint256)) :
    fieldMapAddrUintSlot f slot k1 k2 =
      some (abstractNestedMappingSlot slot (addressToWord k1).val k2.val) := by
  simp [fieldMapAddrUintSlot, htr, hty]

theorem fieldMapUintAddrSlot_eq
    {f : Field} {slot : Nat} {k1 : Uint256} {k2 : Address}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .uint256 .address)) :
    fieldMapUintAddrSlot f slot k1 k2 =
      some (abstractNestedMappingSlot slot k1.val (addressToWord k2).val) := by
  simp [fieldMapUintAddrSlot, htr, hty]

/-- Remaining `MappingType.nested` pairs collapse to `abstractNestedMappingSlot`.
    Word keys (uint256 / bytes32) use `.val`; address keys use `addressToWord`. -/
def fieldMapUintUintSlot (f : Field) (resolvedSlot : Nat) (k1 k2 : Uint256) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .uint256 .uint256) =>
      some (abstractNestedMappingSlot resolvedSlot k1.val k2.val)
    | _ => none

def fieldMapBytes32Bytes32Slot (f : Field) (resolvedSlot : Nat) (k1 k2 : Uint256) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .bytes32 .bytes32) =>
      some (abstractNestedMappingSlot resolvedSlot k1.val k2.val)
    | _ => none

def fieldMapAddrBytes32Slot (f : Field) (resolvedSlot : Nat) (k1 : Address) (k2 : Uint256) :
    Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .address .bytes32) =>
      some (abstractNestedMappingSlot resolvedSlot (addressToWord k1).val k2.val)
    | _ => none

def fieldMapBytes32AddrSlot (f : Field) (resolvedSlot : Nat) (k1 : Uint256) (k2 : Address) :
    Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .bytes32 .address) =>
      some (abstractNestedMappingSlot resolvedSlot k1.val (addressToWord k2).val)
    | _ => none

def fieldMapUintBytes32Slot (f : Field) (resolvedSlot : Nat) (k1 k2 : Uint256) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .uint256 .bytes32) =>
      some (abstractNestedMappingSlot resolvedSlot k1.val k2.val)
    | _ => none

def fieldMapBytes32UintSlot (f : Field) (resolvedSlot : Nat) (k1 k2 : Uint256) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.nested .bytes32 .uint256) =>
      some (abstractNestedMappingSlot resolvedSlot k1.val k2.val)
    | _ => none

theorem fieldMapUintUintSlot_eq
    {f : Field} {slot : Nat} {k1 k2 : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .uint256 .uint256)) :
    fieldMapUintUintSlot f slot k1 k2 =
      some (abstractNestedMappingSlot slot k1.val k2.val) := by
  simp [fieldMapUintUintSlot, htr, hty]

theorem fieldMapBytes32Bytes32Slot_eq
    {f : Field} {slot : Nat} {k1 k2 : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .bytes32 .bytes32)) :
    fieldMapBytes32Bytes32Slot f slot k1 k2 =
      some (abstractNestedMappingSlot slot k1.val k2.val) := by
  simp [fieldMapBytes32Bytes32Slot, htr, hty]

theorem fieldMapAddrBytes32Slot_eq
    {f : Field} {slot : Nat} {k1 : Address} {k2 : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .address .bytes32)) :
    fieldMapAddrBytes32Slot f slot k1 k2 =
      some (abstractNestedMappingSlot slot (addressToWord k1).val k2.val) := by
  simp [fieldMapAddrBytes32Slot, htr, hty]

theorem fieldMapBytes32AddrSlot_eq
    {f : Field} {slot : Nat} {k1 : Uint256} {k2 : Address}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .bytes32 .address)) :
    fieldMapBytes32AddrSlot f slot k1 k2 =
      some (abstractNestedMappingSlot slot k1.val (addressToWord k2).val) := by
  simp [fieldMapBytes32AddrSlot, htr, hty]

theorem fieldMapUintBytes32Slot_eq
    {f : Field} {slot : Nat} {k1 k2 : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .uint256 .bytes32)) :
    fieldMapUintBytes32Slot f slot k1 k2 =
      some (abstractNestedMappingSlot slot k1.val k2.val) := by
  simp [fieldMapUintBytes32Slot, htr, hty]

theorem fieldMapBytes32UintSlot_eq
    {f : Field} {slot : Nat} {k1 k2 : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .bytes32 .uint256)) :
    fieldMapBytes32UintSlot f slot k1 k2 =
      some (abstractNestedMappingSlot slot k1.val k2.val) := by
  simp [fieldMapBytes32UintSlot, htr, hty]

/-- Persistent `mapping(bytes32 => uint256)` entry. There is no
    `StorageKey.mapBytes32`; Solidity ABI-encodes the 32-byte word
    the same way as a uint256 key. The collapse is the compiler slot. -/
def fieldMapBytes32Slot (f : Field) (resolvedSlot : Nat) (key : Uint256) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingTyped (.simple .bytes32) => some (solidityMappingSlot resolvedSlot key.val)
    | _ => none

theorem fieldMapBytes32Slot_eq
    {f : Field} {slot : Nat} {key : Uint256}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.simple .bytes32)) :
    fieldMapBytes32Slot f slot key = some (solidityMappingSlot slot key.val) := by
  simp [fieldMapBytes32Slot, htr, hty]

/-- Persistent `mapping(bytes32 => Struct)` member word. -/
def fieldStructMemberBytes32Slot (f : Field) (resolvedSlot : Nat) (key : Uint256)
    (memberName : String) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingStruct .bytes32 members =>
      match findStructMember members memberName with
      | some m =>
        some (mappingSlotLocation resolvedSlot key.val m.wordOffset)
      | none => none
    | _ => none

theorem fieldStructMemberBytes32Slot_eq
    {f : Field} {slot : Nat} {key : Uint256} {memberName : String}
    {members : List StructMember} {m : StructMember}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingStruct .bytes32 members)
    (hmem : findStructMember members memberName = some m) :
    fieldStructMemberBytes32Slot f slot key memberName =
      some (mappingSlotLocation slot key.val m.wordOffset) := by
  simp [fieldStructMemberBytes32Slot, htr, hty, hmem]

theorem fieldStructMemberBytes32Slot_eq_base_add
    {f : Field} {slot : Nat} {key : Uint256} {memberName : String}
    {members : List StructMember} {m : StructMember}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingStruct .bytes32 members)
    (hmem : findStructMember members memberName = some m) :
    fieldStructMemberBytes32Slot f slot key memberName =
      some ((solidityMappingSlot slot key.val + m.wordOffset) %
        Compiler.Constants.evmModulus) := by
  simp [fieldStructMemberBytes32Slot_eq htr hty hmem, mappingSlotLocation]

/-- Persistent `mapping(address => Struct)` member word. There is no
    StorageKey constructor for a struct member; the collapse is the
    compiler slot `mappingSlotLocation`. -/
def fieldStructMemberSlot (f : Field) (resolvedSlot : Nat) (key : Address)
    (memberName : String) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingStruct .address members =>
      match findStructMember members memberName with
      | some m =>
        some (mappingSlotLocation resolvedSlot (addressToWord key).val m.wordOffset)
      | none => none
    | _ => none

/-- Persistent `mapping(address => mapping(address => Struct))` member word. -/
def fieldStructMember2Slot (f : Field) (resolvedSlot : Nat) (k1 k2 : Address)
    (memberName : String) : Option Nat :=
  if f.isTransient then none
  else
    match f.ty with
    | .mappingStruct2 .address .address members =>
      match findStructMember members memberName with
      | some m =>
        some (nestedMappingSlotLocation resolvedSlot
          (addressToWord k1).val (addressToWord k2).val m.wordOffset)
      | none => none
    | _ => none

theorem fieldStructMemberSlot_eq
    {f : Field} {slot : Nat} {key : Address} {memberName : String}
    {members : List StructMember} {m : StructMember}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingStruct .address members)
    (hmem : findStructMember members memberName = some m) :
    fieldStructMemberSlot f slot key memberName =
      some (mappingSlotLocation slot (addressToWord key).val m.wordOffset) := by
  simp [fieldStructMemberSlot, htr, hty, hmem]

theorem fieldStructMember2Slot_eq
    {f : Field} {slot : Nat} {k1 k2 : Address} {memberName : String}
    {members : List StructMember} {m : StructMember}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingStruct2 .address .address members)
    (hmem : findStructMember members memberName = some m) :
    fieldStructMember2Slot f slot k1 k2 memberName =
      some (nestedMappingSlotLocation slot
        (addressToWord k1).val (addressToWord k2).val m.wordOffset) := by
  simp [fieldStructMember2Slot, htr, hty, hmem]

/-- A struct member word is the mapping-entry `storageKeySlot` plus
    `wordOffset`, reduced mod 2^256. -/
theorem fieldStructMemberSlot_eq_storageKeySlot_add
    {f : Field} {slot : Nat} {key : Address} {memberName : String}
    {members : List StructMember} {m : StructMember}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingStruct .address members)
    (hmem : findStructMember members memberName = some m) :
    fieldStructMemberSlot f slot key memberName =
      (storageKeySlot (.map slot key)).map fun base =>
        (base + m.wordOffset) % Compiler.Constants.evmModulus := by
  simp [fieldStructMemberSlot_eq htr hty hmem, storageKeySlot, mappingSlotLocation]

theorem fieldStructMember2Slot_eq_storageKeySlot_add
    {f : Field} {slot : Nat} {k1 k2 : Address} {memberName : String}
    {members : List StructMember} {m : StructMember}
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingStruct2 .address .address members)
    (hmem : findStructMember members memberName = some m) :
    fieldStructMember2Slot f slot k1 k2 memberName =
      (storageKeySlot (.map2 slot k1 k2)).map fun base =>
        (base + m.wordOffset) % Compiler.Constants.evmModulus := by
  simp [fieldStructMember2Slot_eq htr hty hmem, storageKeySlot,
    nestedMappingSlotLocation, abstractNestedMappingSlot, abstractMappingSlot]

/-- `findFieldWriteSlots` is the resolved slot cons the compatibility
    aliases. Aliases have no `StorageKey`. -/
theorem findFieldWriteSlotsCopyFrom_of_resolved
    (fields : List Field) (idx : Nat) (name : String) {f : Field} {slot : Nat}
    (h : findFieldWithResolvedSlotCopyFrom fields idx name = some (f, slot)) :
    findFieldWriteSlotsCopyFrom fields idx name = some (slot :: f.aliasSlots) := by
  induction fields generalizing idx with
  | nil =>
    simp [findFieldWithResolvedSlotCopyFrom] at h
  | cons hd tl ih =>
    simp only [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom] at h ⊢
    split
    · next hname =>
      simp [hname] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    · next hname =>
      simp [hname] at h
      exact ih (idx + 1) h

theorem findFieldWriteSlots_of_resolved
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    findFieldWriteSlots fields name = some (slot :: f.aliasSlots) := by
  rw [findFieldWriteSlots_eq_CopyFrom, findFieldWithResolvedSlot_eq_CopyFrom] at *
  exact findFieldWriteSlotsCopyFrom_of_resolved fields 0 name h

/-- The persistent field's `storageKeySlot` is the head of the write-slot
    list. Aliases are extra compiler slots, not extra source keys. -/
theorem storageKeySlot_head_of_fieldWriteSlots
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot))
    (htr : f.isTransient = false) :
    (findFieldWriteSlots fields name).bind List.head? =
      storageKeySlot (fieldRootKey f slot) := by
  rw [findFieldWriteSlots_of_resolved h, storageKeySlot_fieldRootKey, htr]
  rfl

/-- Packed subfield extract: shift then mask. Lives in the same word as
    `storageKeySlot`, not a different slot. -/
def packedExtract (word : Nat) (pb : PackedBits) : Nat :=
  Nat.land (word / (2 ^ pb.offset)) (packedMaskNat pb)

def fieldPackedExtract (s : ContractState) (f : Field) (resolvedSlot : Nat) : Option Nat :=
  match f.packedBits with
  | none => none
  | some pb =>
    match storageKeySlot (fieldRootKey f resolvedSlot) with
    | none => none
    | some slot => some (packedExtract (s.storage slot).val pb)

theorem packedBits_same_storageKeySlot
    {f : Field} {slot : Nat} {pb : PackedBits}
    (htr : f.isTransient = false) (_hpk : f.packedBits = some pb) :
    storageKeySlot (fieldRootKey f slot) = some slot := by
  rw [storageKeySlot_fieldRootKey, htr]
  rfl

theorem fieldPackedExtract_eq
    {s : ContractState} {f : Field} {slot : Nat} {pb : PackedBits}
    (htr : f.isTransient = false) (hpk : f.packedBits = some pb) :
    fieldPackedExtract s f slot = some (packedExtract (s.storage slot).val pb) := by
  simp [fieldPackedExtract, hpk, packedBits_same_storageKeySlot htr hpk]

theorem fieldPackedExtract_writeSlot_other
    {s : ContractState} {f : Field} {slot slot' : Nat} {v : Uint256} {pb : PackedBits}
    (htr : f.isTransient = false) (hpk : f.packedBits = some pb)
    (hne : slot ≠ slot') :
    fieldPackedExtract (s.writeSlot slot' v) f slot = fieldPackedExtract s f slot := by
  rw [fieldPackedExtract_eq htr hpk, fieldPackedExtract_eq htr hpk]
  simp [storage_writeSlot_other (s := s) (slot := slot') (slot' := slot) hne]

theorem fieldPackedExtract_writeSlot_same
    {s : ContractState} {f : Field} {slot : Nat} {v : Uint256} {pb : PackedBits}
    (htr : f.isTransient = false) (hpk : f.packedBits = some pb) :
    fieldPackedExtract (s.writeSlot slot v) f slot =
      some (packedExtract v.val pb) := by
  rw [fieldPackedExtract_eq htr hpk]
  simp [storage, writeSlot]

end Compiler.Proofs.Storage.FieldStorageKey
