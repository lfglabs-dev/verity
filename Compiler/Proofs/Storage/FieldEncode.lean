/-
  C5 step 4 composition seam: `storageKeySlot` of a persistent unpacked
  uint256/address field is the slot `encodeStorageAt` reads, once the
  field list has no write-slot conflict. `findResolvedFieldAtSlot` is
  derived, not hypothesized.
-/

import Compiler.Proofs.Storage.FieldStorageKey
import Compiler.Proofs.Storage.MappingCoherence
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.GenericInduction.Storage
import Compiler.CompilationModel.LayoutValidation

namespace Compiler.Proofs.Storage.FieldEncode

open Verity
open Verity.ContractState
open Compiler.CompilationModel
open Compiler.Proofs.Storage.FieldStorageKey
open Compiler.Proofs.Storage.MappingCoherence
open Compiler.Proofs
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.IRGeneration.SourceSemantics

theorem encodeStorageAt_of_resolved_uint256
    {fields : List Field} {world : ContractState} {slot : Nat} {f : Field}
    (hresolved : findResolvedFieldAtSlot fields slot = some f)
    (hty : f.ty = .uint256) :
    encodeStorageAt fields world slot = (world.storage slot).val := by
  simp [encodeStorageAt, hresolved, fieldUsesAddressStorage, fieldUsesDynamicArrayStorage, hty]

theorem encodeStorageAt_of_resolved_address
    {fields : List Field} {world : ContractState} {slot : Nat} {f : Field}
    (hresolved : findResolvedFieldAtSlot fields slot = some f)
    (hty : f.ty = .address) :
    encodeStorageAt fields world slot = (world.storageAddr slot).val := by
  simp [encodeStorageAt, hresolved, fieldUsesAddressStorage, hty]

/-- Persistent unpacked field with no write-slot conflict: the named
    field's resolved slot is the `findResolvedFieldAtSlot` hit. Aliases
    may exist; this names the canonical head, not an alias. -/
theorem findResolvedFieldAtSlot_of_fieldRoot
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields name = some (f, slot))
    (htr : f.isTransient = false)
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlot fields slot = some f := by
  have hwrite := findFieldWriteSlots_of_resolved hfind
  rw [findResolvedFieldAtSlotCopy_eq]
  exact findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
    hnoConflict hfind hwrite (by simp) htr hunpacked

theorem encodeStorageAt_fieldRootKey_uint256
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    {world : ContractState}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields name = some (f, slot))
    (htr : f.isTransient = false)
    (hunpacked : f.packedBits = none)
    (hty : f.ty = .uint256) :
    fieldListRootKey fields name = some (fieldRootKey f slot) ∧
      storageKeySlot (fieldRootKey f slot) = some slot ∧
      encodeStorageAt fields world slot = (world.storage slot).val :=
  ⟨fieldListRootKey_eq hfind,
    by rw [storageKeySlot_fieldRootKey, htr]; rfl,
    encodeStorageAt_of_resolved_uint256
      (findResolvedFieldAtSlot_of_fieldRoot hnoConflict hfind htr hunpacked) hty⟩

theorem encodeStorageAt_fieldRootKey_address
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    {world : ContractState}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields name = some (f, slot))
    (htr : f.isTransient = false)
    (hunpacked : f.packedBits = none)
    (hty : f.ty = .address) :
    fieldListRootKey fields name = some (fieldRootKey f slot) ∧
      storageKeySlot (fieldRootKey f slot) = some slot ∧
      encodeStorageAt fields world slot = (world.storageAddr slot).val :=
  ⟨fieldListRootKey_eq hfind,
    by rw [storageKeySlot_fieldRootKey, htr]; rfl,
    encodeStorageAt_of_resolved_address
      (findResolvedFieldAtSlot_of_fieldRoot hnoConflict hfind htr hunpacked) hty⟩

/-- A slot that is not a named field and not a dynamic-array element
    is the flat `storage` word. Mapping-derived keccak slots usually
    look like this. -/
theorem encodeStorageAt_of_unresolved
    {fields : List Field} {world : ContractState} {slot : Nat}
    (hresolved : findResolvedFieldAtSlot fields slot = none)
    (hdyn : findDynamicArrayElementAtSlot fields world slot = none) :
    encodeStorageAt fields world slot = (world.storage slot).val := by
  simp [encodeStorageAt, hresolved, hdyn]

theorem encodeStorageAt_fieldMapKey
    {fields : List Field} {s : ContractState} {slot : Nat} {key : Address}
    (hcoh : MappingCoherent s)
    (hresolved :
      findResolvedFieldAtSlot fields
        (solidityMappingSlot slot (addressToWord key).val) = none)
    (hdyn :
      findDynamicArrayElementAtSlot fields s
        (solidityMappingSlot slot (addressToWord key).val) = none) :
    encodeStorageAt fields s (solidityMappingSlot slot (addressToWord key).val) =
      (s.storageMap slot key).val := by
  rw [encodeStorageAt_of_unresolved hresolved hdyn, hcoh slot key]

theorem encodeStorageAt_fieldMapUintKey
    {fields : List Field} {s : ContractState} {slot : Nat} {key : Uint256}
    (hcoh : MappingCoherentUint s)
    (hresolved :
      findResolvedFieldAtSlot fields (solidityMappingSlot slot key.val) = none)
    (hdyn :
      findDynamicArrayElementAtSlot fields s (solidityMappingSlot slot key.val) = none) :
    encodeStorageAt fields s (solidityMappingSlot slot key.val) =
      (s.storageMapUint slot key).val := by
  rw [encodeStorageAt_of_unresolved hresolved hdyn, hcoh slot key]

end Compiler.Proofs.Storage.FieldEncode
