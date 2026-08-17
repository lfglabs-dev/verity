/-
  C5 step 4 (finite-set preservation slice): `MappingCoherent` restricted
  to a finite list of (slot, key) pairs is preserved by an aligned
  `writeMap`+`writeSlot` when every other listed pair carries an explicit
  derived-slot inequality.

  Cross-channel aligned writes preserve another channel's finite list
  under an explicit derived-slot inequality between the written slot
  and every listed pair.

  This is not global preservation. A certificate for every pair would
  be keccak injectivity on an unbounded preimage set.
-/

import Compiler.Proofs.Storage.MappingCoherence

namespace Compiler.Proofs.Storage.MappingCoherenceOn

open Verity
open Verity.ContractState
open Compiler.Proofs
open Compiler.Proofs.Storage.MappingCoherence

def mappingAddrSlot (slot : Nat) (key : Address) : Nat :=
  solidityMappingSlot slot (addressToWord key).val

def MappingCoherentAt (s : ContractState) (slot : Nat) (key : Address) : Prop :=
  s.storageMap slot key = s.storage (mappingAddrSlot slot key)

def MappingCoherentOn (s : ContractState) (pairs : List (Nat × Address)) : Prop :=
  ∀ p ∈ pairs, MappingCoherentAt s p.1 p.2

/-- Finite non-alias certificate: distinct listed pairs have distinct
    derived slots. Not keccak injectivity. -/
def DerivedAddrSlotsDistinct (pairs : List (Nat × Address)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
    mappingAddrSlot p.1 p.2 ≠ mappingAddrSlot q.1 q.2

theorem mappingCoherentOn_of_mappingCoherent
    (s : ContractState) (pairs : List (Nat × Address))
    (h : MappingCoherent s) : MappingCoherentOn s pairs := by
  intro p hp
  exact h p.1 p.2

theorem defaultState_mappingCoherentOn (pairs : List (Nat × Address)) :
    MappingCoherentOn defaultState pairs :=
  mappingCoherentOn_of_mappingCoherent _ _ defaultState_mappingCoherent

theorem writeMap_aligned_preserves_at_same
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    MappingCoherentAt
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v)
      slot key :=
  writeMap_aligned_same s slot key v

theorem storageKey_map_ne_of_pair_ne
    {p q : Nat × Address} (h : p ≠ q) :
    StorageKey.map p.1 p.2 ≠ StorageKey.map q.1 q.2 := by
  intro heq
  apply h
  injection heq with hs hk
  exact Prod.ext hs hk

theorem writeMap_aligned_preserves_at_other
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256)
    (slot' : Nat) (key' : Address)
    (hcoh : MappingCoherentAt s slot' key')
    (hkey : StorageKey.map slot' key' ≠ StorageKey.map slot key)
    (hslot : mappingAddrSlot slot' key' ≠ mappingAddrSlot slot key) :
    MappingCoherentAt
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v)
      slot' key' :=
  writeMap_aligned_other s slot key v slot' key' hcoh hkey hslot

theorem writeMap_aligned_preserves_on
    (s : ContractState) (pairs : List (Nat × Address))
    (slot : Nat) (key : Address) (v : Uint256)
    (hcoh : MappingCoherentOn s pairs)
    (hna : DerivedAddrSlotsDistinct pairs)
    (hp : (slot, key) ∈ pairs) :
    MappingCoherentOn
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v)
      pairs := by
  intro p hp'
  by_cases hpeq : p = (slot, key)
  · subst hpeq
    exact writeMap_aligned_preserves_at_same s slot key v
  · exact writeMap_aligned_preserves_at_other s slot key v p.1 p.2
      (hcoh p hp') (storageKey_map_ne_of_pair_ne hpeq)
      (hna p hp' (slot, key) hp hpeq)

/-- Uint-keyed finite-set coherence. Same shape as the address-keyed
    certificate; still not keccak injectivity. -/
def mappingUintSlot (slot : Nat) (key : Uint256) : Nat :=
  solidityMappingSlot slot key.val

def MappingCoherentUintAt (s : ContractState) (slot : Nat) (key : Uint256) : Prop :=
  s.storageMapUint slot key = s.storage (mappingUintSlot slot key)

def MappingCoherentUintOn (s : ContractState) (pairs : List (Nat × Uint256)) : Prop :=
  ∀ p ∈ pairs, MappingCoherentUintAt s p.1 p.2

def DerivedUintSlotsDistinct (pairs : List (Nat × Uint256)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
    mappingUintSlot p.1 p.2 ≠ mappingUintSlot q.1 q.2

theorem mappingCoherentUintOn_of_mappingCoherentUint
    (s : ContractState) (pairs : List (Nat × Uint256))
    (h : MappingCoherentUint s) : MappingCoherentUintOn s pairs := by
  intro p hp
  exact h p.1 p.2

theorem defaultState_mappingCoherentUintOn (pairs : List (Nat × Uint256)) :
    MappingCoherentUintOn defaultState pairs :=
  mappingCoherentUintOn_of_mappingCoherentUint _ _ defaultState_mappingCoherentUint

theorem writeMapUint_aligned_preserves_at_same
    (s : ContractState) (slot : Nat) (key v : Uint256) :
    MappingCoherentUintAt
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v)
      slot key :=
  writeMapUint_aligned_same s slot key v

theorem storageKey_mapUint_ne_of_pair_ne
    {p q : Nat × Uint256} (h : p ≠ q) :
    StorageKey.mapUint p.1 p.2 ≠ StorageKey.mapUint q.1 q.2 := by
  intro heq
  apply h
  injection heq with hs hk
  exact Prod.ext hs hk

theorem writeMapUint_aligned_preserves_at_other
    (s : ContractState) (slot : Nat) (key v : Uint256)
    (slot' : Nat) (key' : Uint256)
    (hcoh : MappingCoherentUintAt s slot' key')
    (hkey : StorageKey.mapUint slot' key' ≠ StorageKey.mapUint slot key)
    (hslot : mappingUintSlot slot' key' ≠ mappingUintSlot slot key) :
    MappingCoherentUintAt
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v)
      slot' key' :=
  writeMapUint_aligned_other s slot key v slot' key' hcoh hkey hslot

theorem writeMapUint_aligned_preserves_on
    (s : ContractState) (pairs : List (Nat × Uint256))
    (slot : Nat) (key v : Uint256)
    (hcoh : MappingCoherentUintOn s pairs)
    (hna : DerivedUintSlotsDistinct pairs)
    (hp : (slot, key) ∈ pairs) :
    MappingCoherentUintOn
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v)
      pairs := by
  intro p hp'
  by_cases hpeq : p = (slot, key)
  · subst hpeq
    exact writeMapUint_aligned_preserves_at_same s slot key v
  · exact writeMapUint_aligned_preserves_at_other s slot key v p.1 p.2
      (hcoh p hp') (storageKey_mapUint_ne_of_pair_ne hpeq)
      (hna p hp' (slot, key) hp hpeq)

/-- Nested-address finite-set coherence. Pairs are `(slot, k1, k2)`. -/
def mappingMap2Slot (slot : Nat) (k1 k2 : Address) : Nat :=
  abstractNestedMappingSlot slot (addressToWord k1).val (addressToWord k2).val

def MappingCoherentMap2At (s : ContractState) (slot : Nat) (k1 k2 : Address) : Prop :=
  s.storageMap2 slot k1 k2 = s.storage (mappingMap2Slot slot k1 k2)

def MappingCoherentMap2On (s : ContractState)
    (pairs : List (Nat × Address × Address)) : Prop :=
  ∀ p ∈ pairs, MappingCoherentMap2At s p.1 p.2.1 p.2.2

def DerivedMap2SlotsDistinct (pairs : List (Nat × Address × Address)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
    mappingMap2Slot p.1 p.2.1 p.2.2 ≠ mappingMap2Slot q.1 q.2.1 q.2.2

theorem mappingCoherentMap2On_of_mappingCoherentMap2
    (s : ContractState) (pairs : List (Nat × Address × Address))
    (h : MappingCoherentMap2 s) : MappingCoherentMap2On s pairs := by
  intro p hp
  exact h p.1 p.2.1 p.2.2

theorem defaultState_mappingCoherentMap2On (pairs : List (Nat × Address × Address)) :
    MappingCoherentMap2On defaultState pairs :=
  mappingCoherentMap2On_of_mappingCoherentMap2 _ _ defaultState_mappingCoherentMap2

theorem writeMap2_aligned_preserves_at_same
    (s : ContractState) (slot : Nat) (k1 k2 : Address) (v : Uint256) :
    MappingCoherentMap2At
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v)
      slot k1 k2 :=
  writeMap2_aligned_same s slot k1 k2 v

theorem storageKey_map2_ne_of_pair_ne
    {p q : Nat × Address × Address} (h : p ≠ q) :
    StorageKey.map2 p.1 p.2.1 p.2.2 ≠ StorageKey.map2 q.1 q.2.1 q.2.2 := by
  intro heq
  apply h
  injection heq with hs hk1 hk2
  exact Prod.ext hs (Prod.ext hk1 hk2)

theorem writeMap2_aligned_preserves_at_other
    (s : ContractState) (slot : Nat) (k1 k2 : Address) (v : Uint256)
    (slot' : Nat) (k1' k2' : Address)
    (hcoh : MappingCoherentMap2At s slot' k1' k2')
    (hkey : StorageKey.map2 slot' k1' k2' ≠ StorageKey.map2 slot k1 k2)
    (hslot : mappingMap2Slot slot' k1' k2' ≠ mappingMap2Slot slot k1 k2) :
    MappingCoherentMap2At
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v)
      slot' k1' k2' :=
  writeMap2_aligned_other s slot k1 k2 v slot' k1' k2' hcoh hkey hslot

theorem writeMap2_aligned_preserves_on
    (s : ContractState) (pairs : List (Nat × Address × Address))
    (slot : Nat) (k1 k2 : Address) (v : Uint256)
    (hcoh : MappingCoherentMap2On s pairs)
    (hna : DerivedMap2SlotsDistinct pairs)
    (hp : (slot, k1, k2) ∈ pairs) :
    MappingCoherentMap2On
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v)
      pairs := by
  intro p hp'
  by_cases hpeq : p = (slot, k1, k2)
  · subst hpeq
    exact writeMap2_aligned_preserves_at_same s slot k1 k2 v
  · exact writeMap2_aligned_preserves_at_other s slot k1 k2 v p.1 p.2.1 p.2.2
      (hcoh p hp') (storageKey_map2_ne_of_pair_ne hpeq)
      (hna p hp' (slot, k1, k2) hp hpeq)

/-- Cross-channel: an aligned address-map write preserves a uint-keyed
    finite list when every listed derived slot is distinct from the
    written one. Not keccak injectivity. -/
theorem writeMap_aligned_preserves_uintOn
    (s : ContractState) (pairs : List (Nat × Uint256))
    (slot : Nat) (key : Address) (v : Uint256)
    (hcoh : MappingCoherentUintOn s pairs)
    (hna : ∀ p ∈ pairs, mappingUintSlot p.1 p.2 ≠ mappingAddrSlot slot key) :
    MappingCoherentUintOn
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v)
      pairs := by
  intro p hp
  have hmap :
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v).storageMapUint p.1 p.2 =
        s.storageMapUint p.1 p.2 := by
    simp [storageMapUint, writeMap, writeSlot]
  have hflat :
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v).storage
        (mappingUintSlot p.1 p.2) =
        s.storage (mappingUintSlot p.1 p.2) := by
    rw [storage_writeSlot_other (s := s.writeMap slot key v) (hna p hp) v, storage_writeMap]
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

theorem writeMap_aligned_preserves_map2On
    (s : ContractState) (pairs : List (Nat × Address × Address))
    (slot : Nat) (key : Address) (v : Uint256)
    (hcoh : MappingCoherentMap2On s pairs)
    (hna : ∀ p ∈ pairs, mappingMap2Slot p.1 p.2.1 p.2.2 ≠ mappingAddrSlot slot key) :
    MappingCoherentMap2On
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v)
      pairs := by
  intro p hp
  have hmap :
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v).storageMap2
          p.1 p.2.1 p.2.2 =
        s.storageMap2 p.1 p.2.1 p.2.2 := by
    simp [storageMap2, writeMap, writeSlot]
  have hflat :
      ((s.writeMap slot key v).writeSlot (mappingAddrSlot slot key) v).storage
        (mappingMap2Slot p.1 p.2.1 p.2.2) =
        s.storage (mappingMap2Slot p.1 p.2.1 p.2.2) := by
    rw [storage_writeSlot_other (s := s.writeMap slot key v) (hna p hp) v, storage_writeMap]
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

theorem writeMapUint_aligned_preserves_addrOn
    (s : ContractState) (pairs : List (Nat × Address))
    (slot : Nat) (key v : Uint256)
    (hcoh : MappingCoherentOn s pairs)
    (hna : ∀ p ∈ pairs, mappingAddrSlot p.1 p.2 ≠ mappingUintSlot slot key) :
    MappingCoherentOn
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v)
      pairs := by
  intro p hp
  have hmap :
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v).storageMap p.1 p.2 =
        s.storageMap p.1 p.2 := by
    simp [storageMap, writeMapUint, writeSlot]
  have hflat :
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v).storage
        (mappingAddrSlot p.1 p.2) =
        s.storage (mappingAddrSlot p.1 p.2) := by
    rw [storage_writeSlot_other (s := s.writeMapUint slot key v) (hna p hp) v,
      storage_writeMapUint]
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

theorem writeMapUint_aligned_preserves_map2On
    (s : ContractState) (pairs : List (Nat × Address × Address))
    (slot : Nat) (key v : Uint256)
    (hcoh : MappingCoherentMap2On s pairs)
    (hna : ∀ p ∈ pairs, mappingMap2Slot p.1 p.2.1 p.2.2 ≠ mappingUintSlot slot key) :
    MappingCoherentMap2On
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v)
      pairs := by
  intro p hp
  have hmap :
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v).storageMap2
          p.1 p.2.1 p.2.2 =
        s.storageMap2 p.1 p.2.1 p.2.2 := by
    simp [storageMap2, writeMapUint, writeSlot]
  have hflat :
      ((s.writeMapUint slot key v).writeSlot (mappingUintSlot slot key) v).storage
        (mappingMap2Slot p.1 p.2.1 p.2.2) =
        s.storage (mappingMap2Slot p.1 p.2.1 p.2.2) := by
    rw [storage_writeSlot_other (s := s.writeMapUint slot key v) (hna p hp) v,
      storage_writeMapUint]
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

theorem writeMap2_aligned_preserves_addrOn
    (s : ContractState) (pairs : List (Nat × Address))
    (slot : Nat) (k1 k2 : Address) (v : Uint256)
    (hcoh : MappingCoherentOn s pairs)
    (hna : ∀ p ∈ pairs, mappingAddrSlot p.1 p.2 ≠ mappingMap2Slot slot k1 k2) :
    MappingCoherentOn
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v)
      pairs := by
  intro p hp
  have hmap :
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v).storageMap p.1 p.2 =
        s.storageMap p.1 p.2 := by
    simp [storageMap, writeMap2, writeSlot]
  have hflat :
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v).storage
        (mappingAddrSlot p.1 p.2) =
        s.storage (mappingAddrSlot p.1 p.2) := by
    rw [storage_writeSlot_other (s := s.writeMap2 slot k1 k2 v) (hna p hp) v, storage_writeMap2]
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

theorem writeMap2_aligned_preserves_uintOn
    (s : ContractState) (pairs : List (Nat × Uint256))
    (slot : Nat) (k1 k2 : Address) (v : Uint256)
    (hcoh : MappingCoherentUintOn s pairs)
    (hna : ∀ p ∈ pairs, mappingUintSlot p.1 p.2 ≠ mappingMap2Slot slot k1 k2) :
    MappingCoherentUintOn
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v)
      pairs := by
  intro p hp
  have hmap :
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v).storageMapUint
          p.1 p.2 =
        s.storageMapUint p.1 p.2 := by
    simp [storageMapUint, writeMap2, writeSlot]
  have hflat :
      ((s.writeMap2 slot k1 k2 v).writeSlot (mappingMap2Slot slot k1 k2) v).storage
        (mappingUintSlot p.1 p.2) =
        s.storage (mappingUintSlot p.1 p.2) := by
    rw [storage_writeSlot_other (s := s.writeMap2 slot k1 k2 v) (hna p hp) v, storage_writeMap2]
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

/-- A lone flat `writeSlot` preserves a finite address-map list when every
    listed derived slot is distinct from the written word. Not keccak
    injectivity and not global preservation. -/
theorem writeSlot_preserves_mappingCoherentOn
    (s : ContractState) (pairs : List (Nat × Address)) (n : Nat) (v : Uint256)
    (hcoh : MappingCoherentOn s pairs)
    (hna : ∀ p ∈ pairs, mappingAddrSlot p.1 p.2 ≠ n) :
    MappingCoherentOn (s.writeSlot n v) pairs := by
  intro p hp
  have hmap :
      (s.writeSlot n v).storageMap p.1 p.2 = s.storageMap p.1 p.2 := by
    simp [storageMap, writeSlot]
  have hflat :
      (s.writeSlot n v).storage (mappingAddrSlot p.1 p.2) =
        s.storage (mappingAddrSlot p.1 p.2) :=
    storage_writeSlot_other (s := s) (hna p hp) v
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

theorem writeSlot_preserves_mappingCoherentUintOn
    (s : ContractState) (pairs : List (Nat × Uint256)) (n : Nat) (v : Uint256)
    (hcoh : MappingCoherentUintOn s pairs)
    (hna : ∀ p ∈ pairs, mappingUintSlot p.1 p.2 ≠ n) :
    MappingCoherentUintOn (s.writeSlot n v) pairs := by
  intro p hp
  have hmap :
      (s.writeSlot n v).storageMapUint p.1 p.2 = s.storageMapUint p.1 p.2 := by
    simp [storageMapUint, writeSlot]
  have hflat :
      (s.writeSlot n v).storage (mappingUintSlot p.1 p.2) =
        s.storage (mappingUintSlot p.1 p.2) :=
    storage_writeSlot_other (s := s) (hna p hp) v
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

theorem writeSlot_preserves_mappingCoherentMap2On
    (s : ContractState) (pairs : List (Nat × Address × Address)) (n : Nat) (v : Uint256)
    (hcoh : MappingCoherentMap2On s pairs)
    (hna : ∀ p ∈ pairs, mappingMap2Slot p.1 p.2.1 p.2.2 ≠ n) :
    MappingCoherentMap2On (s.writeSlot n v) pairs := by
  intro p hp
  have hmap :
      (s.writeSlot n v).storageMap2 p.1 p.2.1 p.2.2 = s.storageMap2 p.1 p.2.1 p.2.2 := by
    simp [storageMap2, writeSlot]
  have hflat :
      (s.writeSlot n v).storage (mappingMap2Slot p.1 p.2.1 p.2.2) =
        s.storage (mappingMap2Slot p.1 p.2.1 p.2.2) :=
    storage_writeSlot_other (s := s) (hna p hp) v
  exact (hmap.trans (hcoh p hp)).trans hflat.symm

end Compiler.Proofs.Storage.MappingCoherenceOn
