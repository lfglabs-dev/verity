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

/-! ## Master Compositional Algebra for `Footprint`, `WritesOnly`, `AgreesOn`, and `unchangedExcept` -/

@[simp] theorem AgreesOn.refl (fp : Footprint) (s : ContractState) :
    AgreesOn fp s s :=
  ⟨fun _ _ => rfl,
   fun _ _ => rfl,
   fun _ _ _ => rfl,
   fun _ _ _ => rfl,
   fun _ _ _ _ => rfl,
   fun _ _ => rfl,
   fun _ _ => rfl⟩

theorem AgreesOn.symm {fp : Footprint} {s₁ s₂ : ContractState}
    (h : AgreesOn fp s₁ s₂) : AgreesOn fp s₂ s₁ :=
  ⟨fun slot hs => (h.1 slot hs).symm,
   fun slot hs => (h.2.1 slot hs).symm,
   fun slot hs k => (h.2.2.1 slot hs k).symm,
   fun slot hs k => (h.2.2.2.1 slot hs k).symm,
   fun slot hs k1 k2 => (h.2.2.2.2.1 slot hs k1 k2).symm,
   fun slot hs => (h.2.2.2.2.2.1 slot hs).symm,
   fun slot hs => (h.2.2.2.2.2.2 slot hs).symm⟩

theorem AgreesOn.trans {fp : Footprint} {s₁ s₂ s₃ : ContractState}
    (h₁₂ : AgreesOn fp s₁ s₂) (h₂₃ : AgreesOn fp s₂ s₃) :
    AgreesOn fp s₁ s₃ :=
  ⟨fun slot hs => (h₂₃.1 slot hs).trans (h₁₂.1 slot hs),
   fun slot hs => (h₂₃.2.1 slot hs).trans (h₁₂.2.1 slot hs),
   fun slot hs k => (h₂₃.2.2.1 slot hs k).trans (h₁₂.2.2.1 slot hs k),
   fun slot hs k => (h₂₃.2.2.2.1 slot hs k).trans (h₁₂.2.2.2.1 slot hs k),
   fun slot hs k1 k2 => (h₂₃.2.2.2.2.1 slot hs k1 k2).trans (h₁₂.2.2.2.2.1 slot hs k1 k2),
   fun slot hs => (h₂₃.2.2.2.2.2.1 slot hs).trans (h₁₂.2.2.2.2.2.1 slot hs),
   fun slot hs => (h₂₃.2.2.2.2.2.2 slot hs).trans (h₁₂.2.2.2.2.2.2 slot hs)⟩

@[simp] theorem WritesOnly.refl (fp : Footprint) (s : ContractState) :
    WritesOnly fp s s :=
  ⟨fun _ _ => rfl,
   fun _ _ => rfl,
   fun _ _ _ => rfl,
   fun _ _ _ => rfl,
   fun _ _ _ _ => rfl,
   fun _ _ => rfl,
   fun _ _ => rfl,
   Specs.sameContext_rfl s⟩

theorem WritesOnly.trans {fp : Footprint} {s₁ s₂ s₃ : ContractState}
    (h₁₂ : WritesOnly fp s₁ s₂) (h₂₃ : WritesOnly fp s₂ s₃) :
    WritesOnly fp s₁ s₃ :=
  ⟨fun slot hs => (h₂₃.1 slot hs).trans (h₁₂.1 slot hs),
   fun slot hs => (h₂₃.2.1 slot hs).trans (h₁₂.2.1 slot hs),
   fun slot hs k => (h₂₃.2.2.1 slot hs k).trans (h₁₂.2.2.1 slot hs k),
   fun slot hs k => (h₂₃.2.2.2.1 slot hs k).trans (h₁₂.2.2.2.1 slot hs k),
   fun slot hs k1 k2 => (h₂₃.2.2.2.2.1 slot hs k1 k2).trans (h₁₂.2.2.2.2.1 slot hs k1 k2),
   fun slot hs => (h₂₃.2.2.2.2.2.1 slot hs).trans (h₁₂.2.2.2.2.2.1 slot hs),
   fun slot hs => (h₂₃.2.2.2.2.2.2.1 slot hs).trans (h₁₂.2.2.2.2.2.2.1 slot hs),
   Specs.sameContext_trans h₁₂.2.2.2.2.2.2.2 h₂₃.2.2.2.2.2.2.2⟩

theorem writesOnly_two_steps_preserves_other_inv
    (hostFp mixinFp : Footprint)
    (hDisjoint : Disjoint hostFp mixinFp)
    (Inv : ContractState → Prop)
    (hInv : InvDependsOnlyOn Inv mixinFp)
    (s₁ s₂ s₃ : ContractState)
    (h₁₂ : WritesOnly hostFp s₁ s₂)
    (h₂₃ : WritesOnly hostFp s₂ s₃)
    (hInvS : Inv s₁) : Inv s₃ :=
  writesOnly_preserves_other_inv hostFp mixinFp hDisjoint Inv hInv s₁ s₃ (h₁₂.trans h₂₃) hInvS

@[simp] theorem disjoint_empty_left (fp : Footprint) :
    Disjoint {} fp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs

@[simp] theorem disjoint_empty_right (fp : Footprint) :
    Disjoint fp {} :=
  (disjoint_empty_left fp).symm

@[simp] theorem agreesOn_empty (s s' : ContractState) :
    AgreesOn {} s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs
  · intro _ hs; cases hs

/-- Pointwise union of two storage footprints. -/
def Footprint.union (a b : Footprint) : Footprint where
  uintSlots := a.uintSlots ++ b.uintSlots
  addrSlots := a.addrSlots ++ b.addrSlots
  mapSlots := a.mapSlots ++ b.mapSlots
  mapUintSlots := a.mapUintSlots ++ b.mapUintSlots
  map2Slots := a.map2Slots ++ b.map2Slots
  arraySlots := a.arraySlots ++ b.arraySlots
  transientSlots := a.transientSlots ++ b.transientSlots

theorem WritesOnly.mono_left {a b : Footprint} {s s' : ContractState}
    (h : WritesOnly a s s') : WritesOnly (Footprint.union a b) s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h.2.2.2.2.2.2.2⟩
  · intro slot hnot; exact h.1 slot (fun hm => hnot (List.mem_append_left _ hm))
  · intro slot hnot; exact h.2.1 slot (fun hm => hnot (List.mem_append_left _ hm))
  · intro slot hnot; exact h.2.2.1 slot (fun hm => hnot (List.mem_append_left _ hm))
  · intro slot hnot; exact h.2.2.2.1 slot (fun hm => hnot (List.mem_append_left _ hm))
  · intro slot hnot; exact h.2.2.2.2.1 slot (fun hm => hnot (List.mem_append_left _ hm))
  · intro slot hnot; exact h.2.2.2.2.2.1 slot (fun hm => hnot (List.mem_append_left _ hm))
  · intro slot hnot; exact h.2.2.2.2.2.2.1 slot (fun hm => hnot (List.mem_append_left _ hm))

theorem WritesOnly.mono_right {a b : Footprint} {s s' : ContractState}
    (h : WritesOnly b s s') : WritesOnly (Footprint.union a b) s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h.2.2.2.2.2.2.2⟩
  · intro slot hnot; exact h.1 slot (fun hm => hnot (List.mem_append_right _ hm))
  · intro slot hnot; exact h.2.1 slot (fun hm => hnot (List.mem_append_right _ hm))
  · intro slot hnot; exact h.2.2.1 slot (fun hm => hnot (List.mem_append_right _ hm))
  · intro slot hnot; exact h.2.2.2.1 slot (fun hm => hnot (List.mem_append_right _ hm))
  · intro slot hnot; exact h.2.2.2.2.1 slot (fun hm => hnot (List.mem_append_right _ hm))
  · intro slot hnot; exact h.2.2.2.2.2.1 slot (fun hm => hnot (List.mem_append_right _ hm))
  · intro slot hnot; exact h.2.2.2.2.2.2.1 slot (fun hm => hnot (List.mem_append_right _ hm))

theorem WritesOnly.seq_union {a b : Footprint} {s₁ s₂ s₃ : ContractState}
    (h₁₂ : WritesOnly a s₁ s₂) (h₂₃ : WritesOnly b s₂ s₃) :
    WritesOnly (Footprint.union a b) s₁ s₃ :=
  (WritesOnly.mono_left h₁₂).trans (WritesOnly.mono_right h₂₃)

theorem Disjoint.union_left {a b c : Footprint}
    (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (Footprint.union a b) c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs; cases List.mem_append.mp hs with | inl h => exact ha.1 s h | inr h => exact hb.1 s h
  · intro s hs; cases List.mem_append.mp hs with | inl h => exact ha.2.1 s h | inr h => exact hb.2.1 s h
  · intro s hs; cases List.mem_append.mp hs with | inl h => exact ha.2.2.1 s h | inr h => exact hb.2.2.1 s h
  · intro s hs; cases List.mem_append.mp hs with | inl h => exact ha.2.2.2.1 s h | inr h => exact hb.2.2.2.1 s h
  · intro s hs; cases List.mem_append.mp hs with | inl h => exact ha.2.2.2.2.1 s h | inr h => exact hb.2.2.2.2.1 s h
  · intro s hs; cases List.mem_append.mp hs with | inl h => exact ha.2.2.2.2.2.1 s h | inr h => exact hb.2.2.2.2.2.1 s h
  · intro s hs; cases List.mem_append.mp hs with | inl h => exact ha.2.2.2.2.2.2 s h | inr h => exact hb.2.2.2.2.2.2 s h

theorem Disjoint.union_right {a b c : Footprint}
    (hb : Disjoint a b) (hc : Disjoint a c) :
    Disjoint a (Footprint.union b c) :=
  (Disjoint.union_left hb.symm hc.symm).symm

theorem writesOnly_seq_union_preserves_other_inv
    (fp₁ fp₂ mixinFp : Footprint)
    (hDisjoint₁ : Disjoint fp₁ mixinFp)
    (hDisjoint₂ : Disjoint fp₂ mixinFp)
    (Inv : ContractState → Prop)
    (hInv : InvDependsOnlyOn Inv mixinFp)
    (s₁ s₂ s₃ : ContractState)
    (h₁₂ : WritesOnly fp₁ s₁ s₂)
    (h₂₃ : WritesOnly fp₂ s₂ s₃)
    (hInvS : Inv s₁) : Inv s₃ :=
  writesOnly_preserves_other_inv (Footprint.union fp₁ fp₂) mixinFp
    (Disjoint.union_left hDisjoint₁ hDisjoint₂) Inv hInv s₁ s₃
    (WritesOnly.seq_union h₁₂ h₂₃) hInvS

/-- Convert the persistent storage channels of a `Footprint` into a `List Specs.SpecStorageKey`. -/
def Footprint.toSpecKeys (fp : Footprint) : List Specs.SpecStorageKey :=
  fp.uintSlots.map .slot ++
  (fp.addrSlots.map .addr ++
  (fp.mapSlots.map .map ++
  (fp.mapUintSlots.map .mapUint ++
  (fp.map2Slots.map .map2 ++
   fp.arraySlots.map .array))))

theorem WritesOnly.to_unchangedExcept {fp : Footprint} {s s' : ContractState}
    (h : WritesOnly fp s s') :
    Specs.unchangedExcept (Footprint.toSpecKeys fp) s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.2.2.2.2.2.2.2⟩
  · intro idx hnot
    exact h.1 idx (fun hm => hnot (by
      unfold Footprint.toSpecKeys
      exact List.mem_append_left _ (List.mem_map.mpr ⟨idx, hm, rfl⟩)))
  · intro idx hnot
    exact h.2.1 idx (fun hm => hnot (by
      unfold Footprint.toSpecKeys
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨idx, hm, rfl⟩))))
  · intro idx hnot
    funext k
    exact h.2.2.1 idx (fun hm => hnot (by
      unfold Footprint.toSpecKeys
      exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ (List.mem_map.mpr ⟨idx, hm, rfl⟩))))) k
  · intro idx hnot
    funext k
    exact h.2.2.2.1 idx (fun hm => hnot (by
      unfold Footprint.toSpecKeys
      exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨idx, hm, rfl⟩)))))) k
  · intro idx hnot
    funext k1 k2
    exact h.2.2.2.2.1 idx (fun hm => hnot (by
      unfold Footprint.toSpecKeys
      exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_left _ (List.mem_map.mpr ⟨idx, hm, rfl⟩))))))) k1 k2
  · intro idx hnot
    exact h.2.2.2.2.2.1 idx (fun hm => hnot (by
      unfold Footprint.toSpecKeys
      exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_right _ (List.mem_map.mpr ⟨idx, hm, rfl⟩)))))))

end Verity.Specs.Composition
