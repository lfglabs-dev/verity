/-
  C5 step 4 composition: a named mapping field's `storageKeySlot` is
  the flat slot `MappingCoherent*` reads. Global preservation is not
  claimed; the `*Coherent` hypothesis is still pointwise or finite-set.
-/

import Compiler.Proofs.Storage.FieldStorageKey
import Compiler.Proofs.Storage.MappingCoherence
import Compiler.Proofs.Storage.MappingCoherenceOn

namespace Compiler.Proofs.Storage.FieldCoherence

open Verity
open Verity.ContractState
open Compiler.CompilationModel
open Compiler.Proofs.Storage.FieldStorageKey
open Compiler.Proofs.Storage.MappingCoherence
open Compiler.Proofs.Storage.MappingCoherenceOn
open Compiler.Proofs

theorem fieldMapKey_coherent_storageKeySlot
    {s : ContractState} {f : Field} {slot : Nat} {key : Address}
    (hcoh : MappingCoherent s)
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.simple .address)) :
    (fieldMapKey f slot key).bind (fun sk =>
      (storageKeySlot sk).map (fun n => s.storage n)) =
      some (s.storageMap slot key) := by
  simp [fieldMapKey, htr, hty, storageKeySlot]
  exact (hcoh slot key).symm

theorem fieldMapUintKey_coherent_storageKeySlot
    {s : ContractState} {f : Field} {slot : Nat} {key : Uint256}
    (hcoh : MappingCoherentUint s)
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.simple .uint256)) :
    (fieldMapUintKey f slot key).bind (fun sk =>
      (storageKeySlot sk).map (fun n => s.storage n)) =
      some (s.storageMapUint slot key) := by
  simp [fieldMapUintKey, htr, hty, storageKeySlot]
  exact (hcoh slot key).symm

theorem fieldMap2Key_coherent_storageKeySlot
    {s : ContractState} {f : Field} {slot : Nat} {k1 k2 : Address}
    (hcoh : MappingCoherentMap2 s)
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .address .address)) :
    (fieldMap2Key f slot k1 k2).bind (fun sk =>
      (storageKeySlot sk).map (fun n => s.storage n)) =
      some (s.storageMap2 slot k1 k2) := by
  simp [fieldMap2Key, htr, hty, storageKeySlot]
  exact (hcoh slot k1 k2).symm

theorem fieldMapKey_coherentOn_storageKeySlot
    {s : ContractState} {f : Field} {slot : Nat} {key : Address}
    {pairs : List (Nat × Address)}
    (hcoh : MappingCoherentOn s pairs)
    (hp : (slot, key) ∈ pairs)
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.simple .address)) :
    (fieldMapKey f slot key).bind (fun sk =>
      (storageKeySlot sk).map (fun n => s.storage n)) =
      some (s.storageMap slot key) := by
  simp [fieldMapKey, htr, hty, storageKeySlot]
  exact (hcoh (slot, key) hp).symm

theorem fieldMapUintKey_coherentOn_storageKeySlot
    {s : ContractState} {f : Field} {slot : Nat} {key : Uint256}
    {pairs : List (Nat × Uint256)}
    (hcoh : MappingCoherentUintOn s pairs)
    (hp : (slot, key) ∈ pairs)
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.simple .uint256)) :
    (fieldMapUintKey f slot key).bind (fun sk =>
      (storageKeySlot sk).map (fun n => s.storage n)) =
      some (s.storageMapUint slot key) := by
  simp [fieldMapUintKey, htr, hty, storageKeySlot]
  exact (hcoh (slot, key) hp).symm

theorem fieldMap2Key_coherentOn_storageKeySlot
    {s : ContractState} {f : Field} {slot : Nat} {k1 k2 : Address}
    {pairs : List (Nat × Address × Address)}
    (hcoh : MappingCoherentMap2On s pairs)
    (hp : (slot, k1, k2) ∈ pairs)
    (htr : f.isTransient = false)
    (hty : f.ty = .mappingTyped (.nested .address .address)) :
    (fieldMap2Key f slot k1 k2).bind (fun sk =>
      (storageKeySlot sk).map (fun n => s.storage n)) =
      some (s.storageMap2 slot k1 k2) := by
  simp [fieldMap2Key, htr, hty, storageKeySlot]
  exact (hcoh (slot, k1, k2) hp).symm

end Compiler.Proofs.Storage.FieldCoherence
