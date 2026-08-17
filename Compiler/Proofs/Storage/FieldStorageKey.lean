/-
  C5 step 4 (field-list slice): collapse a CompilationModel field list to
  a source StorageKey, then to the compiler slot via `storageKeySlot`.

  Mapping-entry constructors cover the typed cases that already have a
  StorageKey (`map` / `mapUint` / `map2`). Address-keyed mappingStruct
  / mappingStruct2 members collapse to `mappingSlotLocation` /
  `nestedMappingSlotLocation`. bytes32 keys, packed bit-ranges, alias
  slots, and global MappingCoherent preservation stay open.
-/

import Compiler.Proofs.Storage.MappingCoherence
import Verity.Core.Model.Types

namespace Compiler.Proofs.Storage.FieldStorageKey

open Verity
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

end Compiler.Proofs.Storage.FieldStorageKey
