/-
  Mixin composition helpers.

  A mixin owns a storage footprint. Host proofs reuse mixin theorems by
  showing the host function writes only its own footprint, which is
  disjoint from the mixin's, so mixin invariants are preserved.
-/

import Verity.Core
import Verity.Core.Invariant
import Verity.Specs.Common

namespace Verity.Specs.Composition

open Verity
open Verity.Core.Invariant

/-- Named storage channels a mixin (or host function) is allowed to write. -/
structure Footprint where
  uintSlots : List Nat := []
  addrSlots : List Nat := []
  mapSlots : List Nat := []
  mapUintSlots : List Nat := []
  map2Slots : List Nat := []
  arraySlots : List Nat := []
  transientSlots : List Nat := []
  deriving Repr, DecidableEq

/-- Two footprints own disjoint slot sets on every channel. -/
def Disjoint (a b : Footprint) : Prop :=
  (∀ s, s ∈ a.uintSlots → s ∉ b.uintSlots) ∧
  (∀ s, s ∈ a.addrSlots → s ∉ b.addrSlots) ∧
  (∀ s, s ∈ a.mapSlots → s ∉ b.mapSlots) ∧
  (∀ s, s ∈ a.mapUintSlots → s ∉ b.mapUintSlots) ∧
  (∀ s, s ∈ a.map2Slots → s ∉ b.map2Slots) ∧
  (∀ s, s ∈ a.arraySlots → s ∉ b.arraySlots) ∧
  (∀ s, s ∈ a.transientSlots → s ∉ b.transientSlots)

theorem Disjoint.symm {a b : Footprint} (h : Disjoint a b) : Disjoint b a :=
  ⟨fun s hb ha => h.1 s ha hb,
    fun s hb ha => h.2.1 s ha hb,
    fun s hb ha => h.2.2.1 s ha hb,
    fun s hb ha => h.2.2.2.1 s ha hb,
    fun s hb ha => h.2.2.2.2.1 s ha hb,
    fun s hb ha => h.2.2.2.2.2.1 s ha hb,
    fun s hb ha => h.2.2.2.2.2.2 s ha hb⟩

/-- `s'` differs from `s` only inside `fp`. Context is unchanged. -/
def WritesOnly (fp : Footprint) (s s' : ContractState) : Prop :=
  (∀ slot, slot ∉ fp.uintSlots → s'.storage slot = s.storage slot) ∧
  (∀ slot, slot ∉ fp.addrSlots → s'.storageAddr slot = s.storageAddr slot) ∧
  (∀ slot, slot ∉ fp.mapSlots → ∀ k, s'.storageMap slot k = s.storageMap slot k) ∧
  (∀ slot, slot ∉ fp.mapUintSlots → ∀ k, s'.storageMapUint slot k = s.storageMapUint slot k) ∧
  (∀ slot, slot ∉ fp.map2Slots → ∀ k1 k2, s'.storageMap2 slot k1 k2 = s.storageMap2 slot k1 k2) ∧
  (∀ slot, slot ∉ fp.arraySlots → s'.storageArray slot = s.storageArray slot) ∧
  (∀ slot, slot ∉ fp.transientSlots → s'.transientStorage slot = s.transientStorage slot) ∧
  Specs.sameContext s s'

/-- `s` and `s'` agree on every slot owned by `fp`. -/
def AgreesOn (fp : Footprint) (s s' : ContractState) : Prop :=
  (∀ slot, slot ∈ fp.uintSlots → s'.storage slot = s.storage slot) ∧
  (∀ slot, slot ∈ fp.addrSlots → s'.storageAddr slot = s.storageAddr slot) ∧
  (∀ slot, slot ∈ fp.mapSlots → ∀ k, s'.storageMap slot k = s.storageMap slot k) ∧
  (∀ slot, slot ∈ fp.mapUintSlots → ∀ k, s'.storageMapUint slot k = s.storageMapUint slot k) ∧
  (∀ slot, slot ∈ fp.map2Slots → ∀ k1 k2, s'.storageMap2 slot k1 k2 = s.storageMap2 slot k1 k2) ∧
  (∀ slot, slot ∈ fp.arraySlots → s'.storageArray slot = s.storageArray slot) ∧
  (∀ slot, slot ∈ fp.transientSlots → s'.transientStorage slot = s.transientStorage slot)

/-- An invariant that only inspects `fp` is unchanged when `fp` is unchanged. -/
def InvDependsOnlyOn (Inv : ContractState → Prop) (fp : Footprint) : Prop :=
  ∀ s s', AgreesOn fp s s' → (Inv s ↔ Inv s')

theorem writesOnly_agrees_on_disjoint
    (hostFp mixinFp : Footprint)
    (hDisjoint : Disjoint hostFp mixinFp)
    (s s' : ContractState)
    (hWrite : WritesOnly hostFp s s') :
    AgreesOn mixinFp s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro slot hslot
    have : slot ∉ hostFp.uintSlots := fun hin => hDisjoint.1 slot hin hslot
    exact hWrite.1 slot this
  · intro slot hslot
    have : slot ∉ hostFp.addrSlots := fun hin => hDisjoint.2.1 slot hin hslot
    exact hWrite.2.1 slot this
  · intro slot hslot
    have : slot ∉ hostFp.mapSlots := fun hin => hDisjoint.2.2.1 slot hin hslot
    exact hWrite.2.2.1 slot this
  · intro slot hslot
    have : slot ∉ hostFp.mapUintSlots := fun hin => hDisjoint.2.2.2.1 slot hin hslot
    exact hWrite.2.2.2.1 slot this
  · intro slot hslot
    have : slot ∉ hostFp.map2Slots := fun hin => hDisjoint.2.2.2.2.1 slot hin hslot
    exact hWrite.2.2.2.2.1 slot this
  · intro slot hslot
    have : slot ∉ hostFp.arraySlots := fun hin => hDisjoint.2.2.2.2.2.1 slot hin hslot
    exact hWrite.2.2.2.2.2.1 slot this
  · intro slot hslot
    have : slot ∉ hostFp.transientSlots := fun hin => hDisjoint.2.2.2.2.2.2 slot hin hslot
    exact hWrite.2.2.2.2.2.2.1 slot this

theorem writesOnly_preserves_other_inv
    (hostFp mixinFp : Footprint)
    (hDisjoint : Disjoint hostFp mixinFp)
    (Inv : ContractState → Prop)
    (hInv : InvDependsOnlyOn Inv mixinFp)
    (s s' : ContractState)
    (hWrite : WritesOnly hostFp s s')
    (hInvS : Inv s) : Inv s' :=
  (hInv s s' (writesOnly_agrees_on_disjoint hostFp mixinFp hDisjoint s s' hWrite)).mp hInvS

/-- Address-channel and uint-channel footprints are always disjoint. -/
theorem disjoint_addr_uint (addrSlot uintSlot : Nat) :
    Disjoint { addrSlots := [addrSlot] } { uintSlots := [uintSlot] } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs; cases hs
  · intro s _ h; cases h
  · intro s hs; cases hs
  · intro s hs; cases hs
  · intro s hs; cases hs
  · intro s hs; cases hs
  · intro s hs; cases hs

theorem disjoint_uint_addr (uintSlot addrSlot : Nat) :
    Disjoint { uintSlots := [uintSlot] } { addrSlots := [addrSlot] } :=
  (disjoint_addr_uint addrSlot uintSlot).symm

end Verity.Specs.Composition
