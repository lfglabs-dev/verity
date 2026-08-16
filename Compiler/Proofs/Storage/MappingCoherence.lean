/-
  C5 step 4 (first slice): structural StorageKey → Solidity-slot collapse
  and shadow-vs-flat mapping coherence.

  Source `StorageKey` constructors stay injective. Keccak layout lives only
  here, on the compiler side. Global preservation of `MappingCoherent` is
  not claimed: that needs finite non-alias certificates, because keccak
  injectivity is not assumed.
-/

import Verity.Core
import Compiler.Proofs.MappingSlot

namespace Compiler.Proofs.Storage.MappingCoherence

open Verity
open Verity.ContractState
open Compiler.Proofs

/-- Collapse a source key to a compiler word slot when the key is persistent. -/
def storageKeySlot : StorageKey → Option Nat
  | .slot n => some n
  | .addr n => some n
  | .map n key => some (solidityMappingSlot n (addressToWord key).val)
  | .mapUint n key => some (solidityMappingSlot n key.val)
  | .map2 n k1 k2 =>
      some (abstractNestedMappingSlot n (addressToWord k1).val (addressToWord k2).val)
  | .transient _ => none
  | .contractSlot c n => if c = 0 then some n else none

/-- Address-keyed mapping shadow agrees with the flat channel at the
    derived Solidity slot. -/
def MappingCoherent (s : ContractState) : Prop :=
  ∀ (slot : Nat) (key : Address),
    s.storageMap slot key =
      s.storage (solidityMappingSlot slot (addressToWord key).val)

theorem defaultState_mappingCoherent : MappingCoherent defaultState := by
  intro slot key
  simp [MappingCoherent, storageMap, storage, defaultState]

/-- The aligned write — shadow map plus the derived flat slot — makes the
    written pair coherent regardless of the prior world. -/
theorem writeMap_aligned_same (s : ContractState) (slot : Nat) (key : Address)
    (v : Uint256) :
    ((s.writeMap slot key v).writeSlot
      (solidityMappingSlot slot (addressToWord key).val) v).storageMap slot key =
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v).storage
        (solidityMappingSlot slot (addressToWord key).val) := by
  simp [storageMap_writeSlot, storageMap, writeMap, storage, writeSlot, storage_writeMap]

/-- Another mapping pair stays coherent when its derived slot is distinct
    from the written one. The distinctness hypothesis is the non-alias
    certificate; it is not keccak injectivity. -/
theorem writeMap_aligned_other (s : ContractState) (slot : Nat) (key : Address)
    (v : Uint256) (slot' : Nat) (key' : Address)
    (hcoh : s.storageMap slot' key' =
      s.storage (solidityMappingSlot slot' (addressToWord key').val))
    (hkey : StorageKey.map slot' key' ≠ StorageKey.map slot key)
    (hslot :
      solidityMappingSlot slot' (addressToWord key').val ≠
        solidityMappingSlot slot (addressToWord key).val) :
    ((s.writeMap slot key v).writeSlot
      (solidityMappingSlot slot (addressToWord key).val) v).storageMap slot' key' =
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v).storage
        (solidityMappingSlot slot' (addressToWord key').val) := by
  have hmap :
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v).storageMap slot' key' =
        s.storageMap slot' key' := by
    simp [storageMap_writeSlot, storageMap, writeMap, writeSlot, hkey]
  have hflat :
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v).storage
        (solidityMappingSlot slot' (addressToWord key').val) =
        s.storage (solidityMappingSlot slot' (addressToWord key').val) := by
    rw [storage_writeSlot_other (s := s.writeMap slot key v) hslot v,
      storage_writeMap]
  exact (hmap.trans hcoh).trans hflat.symm

/-- `storageKeySlot` on an address-keyed map is exactly the Solidity derivation. -/
theorem storageKeySlot_map (slot : Nat) (key : Address) :
    storageKeySlot (.map slot key) =
      some (solidityMappingSlot slot (addressToWord key).val) := rfl

theorem storageKeySlot_slot (n : Nat) : storageKeySlot (.slot n) = some n := rfl

theorem storageKeySlot_transient (n : Nat) : storageKeySlot (.transient n) = none :=
  rfl

end Compiler.Proofs.Storage.MappingCoherence
