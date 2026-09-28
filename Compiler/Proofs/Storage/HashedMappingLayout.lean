/-
  G2 residual: the Solidity keccak layout of hashed mapping chains as an
  *interpretation* of the symbolic executable channel.

  The executable plane stores nested-mapping, word-offset mapping and
  struct-mapping words under `StorageKey.mapChain base keys offset`
  (transient chains under `StorageKey.transientMapChain base keys`), so
  contract proofs separate entries by constructor injectivity alone. The
  compiler/model plane addresses the same words in the flat `.slot`
  (resp. `.transient`) channel at `mappingChainSlotLocation base keys offset`
  = `(fold keccak256(key ‖ acc) + offset) mod 2^256`.

  This file relates the two, in the same shape as the `.map` / `.mapUint` /
  `.map2` shadows in `MappingCoherence`: a coherence relation over a finite
  set of tracked entries, preserved by aligned writes (symbolic entry + flat
  slot) and by every other channel write whose flat slot avoids the tracked
  locations. Non-aliasing of the tracked Solidity slots is a hypothesis
  (`LayoutNonAlias`, dischargeable from the existing
  `StorageSlotNonAliasCertificate`), never an axiom: nothing here uses
  `solidityMappingSlot_injective`, and contract-level proofs over the
  executable plane never need this file.
-/

import Verity.Core
import Compiler.Proofs.MappingSlot

namespace Compiler.Proofs.Storage.HashedMappingLayout

open Verity
open Verity.ContractState
open Compiler.Proofs

/-- A tracked hashed-mapping word: `(baseSlot, keyWords, wordOffset)`. -/
abbrev Entry := Nat × List Nat × Nat

/-- The symbolic executable key of an entry. -/
def Entry.key (e : Entry) : StorageKey := .mapChain e.1 e.2.1 e.2.2

/-- The Solidity storage location of an entry (the compiler's slot). -/
def Entry.location (e : Entry) : Nat := mappingChainSlotLocation e.1 e.2.1 e.2.2

/-- The executable word of an entry. -/
def Entry.read (s : ContractState) (e : Entry) : Uint256 := s.readMapChain e.1 e.2.1 e.2.2

theorem Entry.key_injective {e e' : Entry} (h : e.key = e'.key) : e = e' := by
  rcases e with ⟨b, ks, o⟩
  rcases e' with ⟨b', ks', o'⟩
  simp only [Entry.key, StorageKey.mapChain.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

/-- Executable hashed words agree with the flat `.slot` channel (the channel the
    model plane reads) at the Solidity location of every tracked entry. -/
def HashedCoherentOn (tracked : List Entry) (s : ContractState) : Prop :=
  ∀ e ∈ tracked, e.read s = s.storage e.location

/-- Layout certificate: distinct tracked entries have distinct Solidity slots. -/
def LayoutNonAlias (tracked : List Entry) : Prop :=
  ∀ e ∈ tracked, ∀ e' ∈ tracked, e ≠ e' → e.location ≠ e'.location

/-- The existing finite non-alias certificate over the tracked locations is a
    layout certificate. -/
theorem layoutNonAlias_of_certificate {tracked : List Entry}
    (cert : StorageSlotNonAliasCertificate (tracked.map Entry.location)) :
    LayoutNonAlias tracked := by
  intro e he e' he' hne hloc
  exact hne (List.inj_on_of_nodup_map cert.distinct he he' hloc)

theorem defaultState_hashedCoherentOn (tracked : List Entry) :
    HashedCoherentOn tracked defaultState := by
  intro e _
  rfl

/-- Aligned write: the symbolic entry plus the compiler's flat slot. -/
def alignedWrite (s : ContractState) (e : Entry) (v : Uint256) : ContractState :=
  (s.writeMapChain e.1 e.2.1 e.2.2 v).writeSlot e.location v

/-- Reading a tracked entry is reading the flat channel at its Solidity slot. -/
theorem read_eq_storage_location {tracked : List Entry} {s : ContractState}
    (hcoh : HashedCoherentOn tracked s) {e : Entry} (he : e ∈ tracked) :
    s.readMapChain e.1 e.2.1 e.2.2 = s.storage e.location :=
  hcoh e he

/-- The aligned write makes the written entry coherent regardless of the prior world. -/
theorem alignedWrite_same (s : ContractState) (e : Entry) (v : Uint256) :
    e.read (alignedWrite s e v) = (alignedWrite s e v).storage e.location := by
  simp [Entry.read, alignedWrite]

/-- Aligned writes preserve coherence on a layout-certified tracked set. -/
theorem alignedWrite_preserves {tracked : List Entry} {s : ContractState}
    (hcoh : HashedCoherentOn tracked s) (hna : LayoutNonAlias tracked)
    {w : Entry} (hw : w ∈ tracked) (v : Uint256) :
    HashedCoherentOn tracked (alignedWrite s w v) := by
  intro e he
  by_cases hew : e = w
  · subst hew
    exact alignedWrite_same s e v
  · have hloc : e.location ≠ w.location := hna e he w hw hew
    have hkey : StorageKey.mapChain e.1 e.2.1 e.2.2 ≠ .mapChain w.1 w.2.1 w.2.2 :=
      fun h => hew (Entry.key_injective h)
    have hread : e.read (alignedWrite s w v) = e.read s := by
      simp only [Entry.read, alignedWrite, readMapChain_writeSlot]
      exact readMapChain_writeMapChain_of_ne s hkey v
    have hflat : (alignedWrite s w v).storage e.location = s.storage e.location := by
      simp only [alignedWrite]
      rw [storage_writeSlot_other _ hloc, storage_writeMapChain]
    rw [hread, hflat]
    exact hcoh e he

/-- A scalar write preserves coherence when its slot avoids every tracked
    Solidity location. This is where mapping-vs-scalar separation lives for the
    *interpretation*; the executable plane needs no such fact
    (`ContractState.readMapChain_writeSlot`). -/
theorem writeSlot_preserves {tracked : List Entry} {s : ContractState}
    (hcoh : HashedCoherentOn tracked s) {n : Nat} (havoid : ∀ e ∈ tracked, e.location ≠ n)
    (v : Uint256) : HashedCoherentOn tracked (s.writeSlot n v) := by
  intro e he
  simp only [Entry.read, readMapChain_writeSlot]
  rw [storage_writeSlot_other _ (havoid e he)]
  exact hcoh e he

theorem writeTransient_preserves {tracked : List Entry} {s : ContractState}
    (hcoh : HashedCoherentOn tracked s) (n : Nat) (v : Uint256) :
    HashedCoherentOn tracked (s.writeTransient n v) := by
  intro e he
  have := hcoh e he
  simp only [Entry.read] at this ⊢
  simpa [storage, writeTransient, readMapChain, storageMapChain] using this

theorem writeTransientMapChain_preserves {tracked : List Entry} {s : ContractState}
    (hcoh : HashedCoherentOn tracked s) (n : Nat) (keys : List Nat) (v : Uint256) :
    HashedCoherentOn tracked (s.writeTransientMapChain n keys v) := by
  intro e he
  simp only [Entry.read, readMapChain_writeTransientMapChain, storage_writeTransientMapChain]
  exact hcoh e he

theorem writeAddrSlot_preserves {tracked : List Entry} {s : ContractState}
    (hcoh : HashedCoherentOn tracked s) (n : Nat) (v : Address) :
    HashedCoherentOn tracked (s.writeAddrSlot n v) := by
  intro e he
  have := hcoh e he
  simp only [Entry.read] at this ⊢
  simpa [storage, writeAddrSlot, readMapChain, storageMapChain] using this

/-! ### Transient chains

Transient chains are interpreted in the flat `.transient` channel at the same
folded keccak location (word offset `0`). -/

/-- A tracked transient hashed word: `(baseSlot, keyWords)`. -/
abbrev TEntry := Nat × List Nat

def TEntry.location (e : TEntry) : Nat := mappingChainSlotLocation e.1 e.2 0

def TransientHashedCoherentOn (tracked : List TEntry) (s : ContractState) : Prop :=
  ∀ e ∈ tracked, s.readTransientMapChain e.1 e.2 = s.transientStorage e.location

def alignedTransientWrite (s : ContractState) (e : TEntry) (v : Uint256) : ContractState :=
  (s.writeTransientMapChain e.1 e.2 v).writeTransient e.location v

theorem alignedTransientWrite_preserves {tracked : List TEntry} {s : ContractState}
    (hcoh : TransientHashedCoherentOn tracked s)
    (hna : ∀ e ∈ tracked, ∀ e' ∈ tracked, e ≠ e' → e.location ≠ e'.location)
    {w : TEntry} (hw : w ∈ tracked) (v : Uint256) :
    TransientHashedCoherentOn tracked (alignedTransientWrite s w v) := by
  intro e he
  rcases e with ⟨b, ks⟩
  rcases w with ⟨b', ks'⟩
  by_cases hew : (b, ks) = (b', ks')
  · simp only [Prod.mk.injEq] at hew
    rcases hew with ⟨rfl, rfl⟩
    simp [alignedTransientWrite, readTransientMapChain, transientStorageMapChain,
      transientStorage, writeTransient]
  · have hloc := hna _ he _ hw hew
    have hne : ¬ (b = b' ∧ ks = ks') := fun h => hew (by rw [h.1, h.2])
    have := hcoh _ he
    have hloc' : mappingChainSlotLocation b ks 0 ≠ mappingChainSlotLocation b' ks' 0 := hloc
    simp only [TEntry.location] at this ⊢
    simp [alignedTransientWrite, readTransientMapChain, transientStorageMapChain,
      transientStorage, writeTransient, TEntry.location, hloc', hne] at this ⊢
    exact this

end Compiler.Proofs.Storage.HashedMappingLayout
