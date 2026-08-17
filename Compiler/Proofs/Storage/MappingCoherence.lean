/-
  C5 step 4 (first slice): structural StorageKey → Solidity-slot collapse
  and shadow-vs-flat mapping coherence.

  Source `StorageKey` constructors stay injective. Keccak layout lives only
  here, on the compiler side. Global preservation of `MappingCoherent` is
  not claimed without `solidityMappingSlot_injective`. That axiom is
  ABI mapping-preimage collision-resistance, not keccak-on-all-bytes.
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
  simp [storageMap, storage, defaultState]

/-- The aligned write — shadow map plus the derived flat slot — makes the
    written pair coherent regardless of the prior world. -/
theorem writeMap_aligned_same (s : ContractState) (slot : Nat) (key : Address)
    (v : Uint256) :
    ((s.writeMap slot key v).writeSlot
      (solidityMappingSlot slot (addressToWord key).val) v).storageMap slot key =
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v).storage
        (solidityMappingSlot slot (addressToWord key).val) := by
  simp [storageMap, writeMap, storage, writeSlot]

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
    simp [storageMap, writeMap, writeSlot, hkey]
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

theorem storageKeySlot_addr (n : Nat) : storageKeySlot (.addr n) = some n := rfl

theorem storageKeySlot_contractSlot_zero (n : Nat) :
    storageKeySlot (.contractSlot 0 n) = some n := rfl

theorem storageKeySlot_contractSlot_nonzero {c n : Nat} (h : c ≠ 0) :
    storageKeySlot (.contractSlot c n) = none := by
  simp [storageKeySlot, h]

theorem storageKeySlot_transient (n : Nat) : storageKeySlot (.transient n) = none :=
  rfl

/-- Uint-keyed mapping shadow agrees with the flat channel at the derived slot. -/
def MappingCoherentUint (s : ContractState) : Prop :=
  ∀ (slot : Nat) (key : Uint256),
    s.storageMapUint slot key = s.storage (solidityMappingSlot slot key.val)

theorem defaultState_mappingCoherentUint : MappingCoherentUint defaultState := by
  intro slot key
  simp [storageMapUint, storage, defaultState]

theorem writeMapUint_aligned_same (s : ContractState) (slot : Nat) (key v : Uint256) :
    ((s.writeMapUint slot key v).writeSlot (solidityMappingSlot slot key.val) v).storageMapUint
        slot key =
      ((s.writeMapUint slot key v).writeSlot (solidityMappingSlot slot key.val) v).storage
        (solidityMappingSlot slot key.val) := by
  simp [storageMapUint, writeMapUint, storage, writeSlot]

theorem writeMapUint_aligned_other (s : ContractState) (slot : Nat) (key v : Uint256)
    (slot' : Nat) (key' : Uint256)
    (hcoh : s.storageMapUint slot' key' = s.storage (solidityMappingSlot slot' key'.val))
    (hkey : StorageKey.mapUint slot' key' ≠ StorageKey.mapUint slot key)
    (hslot : solidityMappingSlot slot' key'.val ≠ solidityMappingSlot slot key.val) :
    ((s.writeMapUint slot key v).writeSlot (solidityMappingSlot slot key.val) v).storageMapUint
        slot' key' =
      ((s.writeMapUint slot key v).writeSlot (solidityMappingSlot slot key.val) v).storage
        (solidityMappingSlot slot' key'.val) := by
  have hmap :
      ((s.writeMapUint slot key v).writeSlot (solidityMappingSlot slot key.val) v).storageMapUint
          slot' key' =
        s.storageMapUint slot' key' := by
    simp [storageMapUint, writeMapUint, writeSlot, hkey]
  have hflat :
      ((s.writeMapUint slot key v).writeSlot (solidityMappingSlot slot key.val) v).storage
          (solidityMappingSlot slot' key'.val) =
        s.storage (solidityMappingSlot slot' key'.val) := by
    rw [storage_writeSlot_other (s := s.writeMapUint slot key v) hslot v, storage_writeMapUint]
  exact (hmap.trans hcoh).trans hflat.symm

/-- Double-address mapping shadow agrees with the nested derived slot. -/
def MappingCoherentMap2 (s : ContractState) : Prop :=
  ∀ (slot : Nat) (k1 k2 : Address),
    s.storageMap2 slot k1 k2 =
      s.storage (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val)

theorem defaultState_mappingCoherentMap2 : MappingCoherentMap2 defaultState := by
  intro slot k1 k2
  simp [storageMap2, storage, defaultState]

theorem writeMap2_aligned_same (s : ContractState) (slot : Nat) (k1 k2 : Address)
    (v : Uint256) :
    ((s.writeMap2 slot k1 k2 v).writeSlot
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) v).storageMap2
        slot k1 k2 =
      ((s.writeMap2 slot k1 k2 v).writeSlot
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) v).storage
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) := by
  simp [storageMap2, writeMap2, storage, writeSlot]

theorem writeMap2_aligned_other (s : ContractState) (slot : Nat) (k1 k2 : Address)
    (v : Uint256) (slot' : Nat) (k1' k2' : Address)
    (hcoh : s.storageMap2 slot' k1' k2' =
      s.storage (abstractNestedMappingSlot slot' (addressToWord k1').val (addressToWord k2').val))
    (hkey : StorageKey.map2 slot' k1' k2' ≠ StorageKey.map2 slot k1 k2)
    (hslot :
      abstractNestedMappingSlot slot' (addressToWord k1').val (addressToWord k2').val ≠
        abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) :
    ((s.writeMap2 slot k1 k2 v).writeSlot
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val)
        v).storageMap2 slot' k1' k2' =
      ((s.writeMap2 slot k1 k2 v).writeSlot
        (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) v).storage
        (abstractNestedMappingSlot slot' (addressToWord k1').val (addressToWord k2').val) := by
  have hmap :
      ((s.writeMap2 slot k1 k2 v).writeSlot
          (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val)
          v).storageMap2 slot' k1' k2' =
        s.storageMap2 slot' k1' k2' := by
    simp [storageMap2, writeMap2, writeSlot, hkey]
  have hflat :
      ((s.writeMap2 slot k1 k2 v).writeSlot
          (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val)
          v).storage
          (abstractNestedMappingSlot slot' (addressToWord k1').val (addressToWord k2').val) =
        s.storage
          (abstractNestedMappingSlot slot' (addressToWord k1').val (addressToWord k2').val) := by
    rw [storage_writeSlot_other (s := s.writeMap2 slot k1 k2 v) hslot v, storage_writeMap2]
  exact (hmap.trans hcoh).trans hflat.symm

theorem storageKeySlot_mapUint (slot : Nat) (key : Uint256) :
    storageKeySlot (.mapUint slot key) = some (solidityMappingSlot slot key.val) := rfl

theorem storageKeySlot_map2 (slot : Nat) (k1 k2 : Address) :
    storageKeySlot (.map2 slot k1 k2) =
      some (abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val) :=
  rfl

theorem addressToWord_injective {a b : Address}
    (h : addressToWord a = addressToWord b) : a = b := by
  apply Core.Address.ext
  have hval :
      a.toNat % Core.Uint256.modulus = b.toNat % Core.Uint256.modulus := by
    simpa [addressToWord, Core.Uint256.val_ofNat] using
      congrArg Core.Uint256.val h
  have ha : a.toNat < Core.Uint256.modulus :=
    Nat.lt_trans a.isLt (by decide : Core.ADDRESS_MODULUS < Core.Uint256.modulus)
  have hb : b.toNat < Core.Uint256.modulus :=
    Nat.lt_trans b.isLt (by decide : Core.ADDRESS_MODULUS < Core.Uint256.modulus)
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval
  simpa [Core.Address.toNat] using hval

theorem mappingAddrSlot_ne_of_map_ne {slot slot' : Nat} {key key' : Address}
    (h : StorageKey.map slot' key' ≠ StorageKey.map slot key) :
    solidityMappingSlot slot' (addressToWord key').val ≠
      solidityMappingSlot slot (addressToWord key).val := by
  intro heq
  rcases solidityMappingSlot_injective slot' (addressToWord key').val
      slot (addressToWord key).val heq with ⟨hs, hk⟩
  apply h
  rw [hs, addressToWord_injective (Core.Uint256.ext hk)]

theorem mappingUintSlot_ne_of_mapUint_ne {slot slot' : Nat} {key key' : Uint256}
    (h : StorageKey.mapUint slot' key' ≠ StorageKey.mapUint slot key) :
    solidityMappingSlot slot' key'.val ≠ solidityMappingSlot slot key.val := by
  intro heq
  rcases solidityMappingSlot_injective slot' key'.val slot key.val heq with ⟨hs, hk⟩
  apply h
  rw [hs, Core.Uint256.ext hk]

theorem mappingMap2Slot_ne_of_map2_ne
    {slot slot' : Nat} {k1 k1' k2 k2' : Address}
    (h : StorageKey.map2 slot' k1' k2' ≠ StorageKey.map2 slot k1 k2) :
    abstractNestedMappingSlot slot' (addressToWord k1').val (addressToWord k2').val ≠
      abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val := by
  intro heq
  rcases abstractNestedMappingSlot_injective slot' (addressToWord k1').val
      (addressToWord k2').val slot (addressToWord k1).val (addressToWord k2).val heq
    with ⟨hs, hk1, hk2⟩
  apply h
  rw [hs, addressToWord_injective (Core.Uint256.ext hk1),
    addressToWord_injective (Core.Uint256.ext hk2)]

/-- Global aligned-write preservation. Other-pair slot inequality comes
    from `solidityMappingSlot_injective`, not from a listed certificate.
    Not injectivity of keccak on all ByteArrays. -/
theorem writeMap_aligned_preserves_mappingCoherent
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256)
    (hcoh : MappingCoherent s) :
    MappingCoherent
      ((s.writeMap slot key v).writeSlot
        (solidityMappingSlot slot (addressToWord key).val) v) := by
  intro slot' key'
  by_cases hs : slot' = slot
  · by_cases hk : key' = key
    · simpa [hs, hk] using writeMap_aligned_same s slot key v
    · have hkey : StorageKey.map slot' key' ≠ StorageKey.map slot key := by
        intro heq; injection heq with _ hk'; exact hk hk'
      exact writeMap_aligned_other s slot key v slot' key' (hcoh slot' key')
        hkey (mappingAddrSlot_ne_of_map_ne hkey)
  · have hkey : StorageKey.map slot' key' ≠ StorageKey.map slot key := by
      intro heq; injection heq with hs' _; exact hs hs'
    exact writeMap_aligned_other s slot key v slot' key' (hcoh slot' key')
      hkey (mappingAddrSlot_ne_of_map_ne hkey)

end Compiler.Proofs.Storage.MappingCoherence
