/-
  C5 step 4 composition seam: `storageKeySlot` of a persistent uint256
  field is the slot `encodeStorageAt` reads when `findResolvedFieldAtSlot`
  agrees. The slot-lookup hypothesis is explicit; this does not prove
  field-list uniqueness.
-/

import Compiler.Proofs.Storage.FieldStorageKey
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace Compiler.Proofs.Storage.FieldEncode

open Verity
open Verity.ContractState
open Compiler.CompilationModel
open Compiler.Proofs.Storage.FieldStorageKey
open Compiler.Proofs.Storage.MappingCoherence
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

theorem encodeStorageAt_fieldRootKey_uint256
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    {world : ContractState}
    (hfind : findFieldWithResolvedSlot fields name = some (f, slot))
    (htr : f.isTransient = false)
    (hty : f.ty = .uint256)
    (hresolved : findResolvedFieldAtSlot fields slot = some f) :
    fieldListRootKey fields name = some (fieldRootKey f slot) ∧
      storageKeySlot (fieldRootKey f slot) = some slot ∧
      encodeStorageAt fields world slot = (world.storage slot).val :=
  ⟨fieldListRootKey_eq hfind,
    by rw [storageKeySlot_fieldRootKey, htr]; rfl,
    encodeStorageAt_of_resolved_uint256 hresolved hty⟩

theorem encodeStorageAt_fieldRootKey_address
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    {world : ContractState}
    (hfind : findFieldWithResolvedSlot fields name = some (f, slot))
    (htr : f.isTransient = false)
    (hty : f.ty = .address)
    (hresolved : findResolvedFieldAtSlot fields slot = some f) :
    fieldListRootKey fields name = some (fieldRootKey f slot) ∧
      storageKeySlot (fieldRootKey f slot) = some slot ∧
      encodeStorageAt fields world slot = (world.storageAddr slot).val :=
  ⟨fieldListRootKey_eq hfind,
    by rw [storageKeySlot_fieldRootKey, htr]; rfl,
    encodeStorageAt_of_resolved_address hresolved hty⟩

end Compiler.Proofs.Storage.FieldEncode
