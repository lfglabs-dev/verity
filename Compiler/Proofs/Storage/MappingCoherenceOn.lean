/-
  C5 step 4 (finite-set preservation slice): `MappingCoherent` restricted
  to a finite list of (slot, key) pairs is preserved by an aligned
  `writeMap`+`writeSlot` when every other listed pair carries an explicit
  derived-slot inequality.

  This is not global preservation. A certificate for every address-keyed
  pair would be keccak injectivity on an unbounded preimage set.
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

end Compiler.Proofs.Storage.MappingCoherenceOn
