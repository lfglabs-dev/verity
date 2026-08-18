/-
  C5 step 4 (contract-level slice): `OwnedCounter` end-to-end shadow-vs-flat
  storage coherence.

  `MappingCoherentAllKeys` (see `Compiler/Proofs/Storage/MappingCoherentAllKeys.lean`)
  is the global invariant saying every source `StorageKey` that the declared
  layout collapses to a flat channel holds the same word as that channel.
  Until now it was only known to be preserved by individual write helpers.
  This file discharges it for a real contract, over real entrypoint
  execution, with no hypotheses left open:

  * `ownedCounterFields` is `OwnedCounter`'s declared layout;
  * `mappingBasesNotDerived` and `derivedMappingSlotsAvoid` discharge the two
    layout certificates the write laws take — here from the layout itself,
    not from any keccak assumption (see the note on scope below);
  * every entrypoint is shown to preserve coherence, and
    `coherent_of_genesis` runs an arbitrary sequence of entrypoints from
    `defaultState` and concludes coherence of the final state.

  ## Scope: why this contract

  `OwnedCounter` declares no mapping field. That makes both certificates
  provable *outright* rather than assumed: `fieldMapKindAt` is `none` at
  every slot (`fieldMapKindAt_eq_none`), so no source key collapses to a
  keccak-derived slot and there is nothing for a flat write to collide with.

  That is not an accident of this contract, and it is worth stating plainly
  what it does and does not buy. For a layout that *does* declare a mapping
  at base slot `b`, `MappingBasesNotDerived` requires
  `solidityMappingSlot _ _ ≠ b` — the derived-slot image must miss the small
  declared-slot region. The in-tree axiom set gives collision resistance
  (`solidityMappingSlot_injective`) and an upper bound
  (`solidityMappingSlot_lt_evmModulus`), and neither implies that. So the
  certificates are dischargeable exactly for mapping-free layouts today; a
  mapping-bearing contract still has to take them as explicit hypotheses.
  The execution-threading in `MappingCoherentExec` is what generalises: it is
  layout-agnostic, and a mapping-bearing contract reuses it verbatim once the
  certificates are available.
-/

import Contracts.OwnedCounter.Proofs.Basic
import Compiler.Proofs.Storage.MappingCoherentExec

namespace Contracts.OwnedCounter.Proofs.StorageCoherence

open Verity
open Contracts.OwnedCounter
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.Proofs.Storage.MappingCoherentGlobal
open Compiler.Proofs.Storage.MappingCoherentExec

/-! ## Declared layout

Mirrors the `storage` block of `verity_contract OwnedCounter`:
`owner : Address := slot 0`, `count : Uint256 := slot 1`. -/

-- `slot` is a keyword of the `verity_contract` storage DSL, which this module
-- transitively imports; the escaped form names the `Field` projection.
def ownedCounterFields : List Field :=
  [ { name := "owner", ty := .address, «slot» := some 0 },
    { name := "count", ty := .uint256, «slot» := some 1 } ]

/-! ## Layout certificates

Both certificates reduce to one fact: `OwnedCounter` declares no mapping, so
`fieldMapKindAt` is `none` everywhere. Proving that needs to know that slot
resolution only ever returns a *declared* field, which is the membership
lemma below. -/

/-- Slot resolution returns a field drawn from the list it scanned. -/
theorem findResolvedFieldAtStorageSlot_go_mem (isTransient : Bool) (n : Nat) :
    ∀ (remaining : List Field) (idx : Nat) {f : Field},
      findResolvedFieldAtStorageSlot.go isTransient n remaining idx = some f →
      f ∈ remaining
  | [], _, _, h => by
      simp [findResolvedFieldAtStorageSlot.go] at h
  | g :: rest, idx, f, h => by
      simp only [findResolvedFieldAtStorageSlot.go] at h
      split at h
      · exact (Option.some.inj h) ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _
          (findResolvedFieldAtStorageSlot_go_mem isTransient n rest (idx + 1) h)

theorem findResolvedFieldAtSlot_mem {fs : List Field} {n : Nat} {f : Field}
    (h : findResolvedFieldAtSlot fs n = some f) : f ∈ fs :=
  findResolvedFieldAtStorageSlot_go_mem false n fs 0 h

/-- No slot of `OwnedCounter` carries a declared mapping shape. -/
theorem fieldMapKindAt_eq_none (n : Nat) : fieldMapKindAt ownedCounterFields n = none := by
  unfold fieldMapKindAt
  cases h : findResolvedFieldAtSlot ownedCounterFields n with
  | none => rfl
  | some f =>
      have hmem := findResolvedFieldAtSlot_mem h
      simp only [ownedCounterFields, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> rfl

/-- No source key of `OwnedCounter` collapses to a keccak-derived slot. -/
theorem storageKeySlot_not_mappingEntry {k : Verity.StorageKey} {ch : Channel} {m : Nat}
    (hk : storageKeySlot ownedCounterFields k = some (ch, m))
    (hmap : isMappingEntryKey k = true) : False := by
  cases k with
  | «slot» _ => simp [isMappingEntryKey] at hmap
  | addr _ => simp [isMappingEntryKey] at hmap
  | «transient» _ => simp [isMappingEntryKey] at hmap
  | contractSlot _ _ => simp [isMappingEntryKey] at hmap
  | map b key =>
      obtain ⟨hkind, _, _⟩ := storageKeySlot_map_eq hk
      rw [fieldMapKindAt_eq_none] at hkind
      simp at hkind
  | mapUint b key =>
      obtain ⟨hkind, _, _⟩ := storageKeySlot_mapUint_eq hk
      rw [fieldMapKindAt_eq_none] at hkind
      simp at hkind
  | map2 b k1 k2 =>
      obtain ⟨hkind, _, _⟩ := storageKeySlot_map2_eq hk
      rw [fieldMapKindAt_eq_none] at hkind
      simp at hkind

/-- **Certificate 1.** No declared mapping base slot is keccak-derived —
    vacuous here, since no base slot carries a mapping shape. -/
theorem mappingBasesNotDerived : MappingBasesNotDerived ownedCounterFields := by
  intro n hn
  rw [fieldMapKindAt_eq_none] at hn
  exact absurd hn (by simp)

/-- **Certificate 2.** No flat slot is the image of a derived mapping entry.
    Holds at *every* slot, so no `OwnedCounter` word write needs a side
    condition. -/
theorem derivedMappingSlotsAvoid (n : Nat) : DerivedMappingSlotsAvoid ownedCounterFields n := by
  intro k ch m hk hmap
  exact (storageKeySlot_not_mappingEntry hk hmap).elim

/-! ## Entrypoint preservation

Each entrypoint is discharged compositionally from `MappingCoherentExec`:
guards and reads are stateless, `setStorageAddr` lands on the address
channel, and `setStorage` uses `derivedMappingSlotsAvoid`. -/

abbrev Coherent (s : ContractState) : Prop := MappingCoherentAllKeys ownedCounterFields s

theorem constructor_preservesCoherence (initialOwner : Address) :
    PreservesCoherence ownedCounterFields (setStorageAddr owner initialOwner) :=
  preservesCoherence_setStorageAddr owner initialOwner

theorem increment_preservesCoherence : PreservesCoherence ownedCounterFields increment := by
  refine preservesCoherence_bind preservesCoherence_msgSender (fun sender => ?_)
  refine preservesCoherence_bind (preservesCoherence_getStorageAddr owner) (fun cur => ?_)
  refine preservesCoherence_bind (preservesCoherence_require _ _) (fun _ => ?_)
  refine preservesCoherence_bind (preservesCoherence_getStorage count) (fun c => ?_)
  exact preservesCoherence_setStorage count _ (derivedMappingSlotsAvoid _)

theorem decrement_preservesCoherence : PreservesCoherence ownedCounterFields decrement := by
  refine preservesCoherence_bind preservesCoherence_msgSender (fun sender => ?_)
  refine preservesCoherence_bind (preservesCoherence_getStorageAddr owner) (fun cur => ?_)
  refine preservesCoherence_bind (preservesCoherence_require _ _) (fun _ => ?_)
  refine preservesCoherence_bind (preservesCoherence_getStorage count) (fun c => ?_)
  exact preservesCoherence_setStorage count _ (derivedMappingSlotsAvoid _)

theorem transferOwnership_preservesCoherence (newOwner : Address) :
    PreservesCoherence ownedCounterFields (transferOwnership newOwner) := by
  refine preservesCoherence_bind preservesCoherence_msgSender (fun sender => ?_)
  refine preservesCoherence_bind (preservesCoherence_getStorageAddr owner) (fun cur => ?_)
  refine preservesCoherence_bind (preservesCoherence_require _ _) (fun _ => ?_)
  exact preservesCoherence_setStorageAddr owner newOwner

theorem getCount_preservesCoherence : PreservesCoherence ownedCounterFields getCount := by
  refine preservesCoherence_bind (preservesCoherence_getStorage count) (fun c => ?_)
  exact preservesCoherence_pure c

theorem getOwner_preservesCoherence : PreservesCoherence ownedCounterFields getOwner := by
  refine preservesCoherence_bind (preservesCoherence_getStorageAddr owner) (fun o => ?_)
  exact preservesCoherence_pure o

/-! ## Whole-contract execution

`Call` is the contract's external surface. `run` executes a call sequence
through `Contract.run`, i.e. with EVM revert semantics, and the closure
theorem covers reverting calls as well as successful ones. -/

/-- Every externally callable entrypoint of `OwnedCounter`. -/
inductive Call where
  | «constructor» (initialOwner : Address)
  | increment
  | decrement
  | transferOwnership (newOwner : Address)
  | getCount
  | getOwner

/-- One call, executed under `Contract.run` (revert rolls back to the
    pre-call snapshot). -/
def Call.step : Call → ContractState → ContractState
  | .«constructor» o, s => ((setStorageAddr owner o).run s).snd
  | .increment, s => (OwnedCounter.increment.run s).snd
  | .decrement, s => (OwnedCounter.decrement.run s).snd
  | .transferOwnership o, s => ((OwnedCounter.transferOwnership o).run s).snd
  | .getCount, s => (OwnedCounter.getCount.run s).snd
  | .getOwner, s => (OwnedCounter.getOwner.run s).snd

theorem Call.step_preservesCoherence (c : Call) {s : ContractState} (hs : Coherent s) :
    Coherent (c.step s) := by
  cases c with
  | «constructor» o => exact preservesCoherence_run (constructor_preservesCoherence o) s hs
  | increment => exact preservesCoherence_run increment_preservesCoherence s hs
  | decrement => exact preservesCoherence_run decrement_preservesCoherence s hs
  | transferOwnership o =>
      exact preservesCoherence_run (transferOwnership_preservesCoherence o) s hs
  | getCount => exact preservesCoherence_run getCount_preservesCoherence s hs
  | getOwner => exact preservesCoherence_run getOwner_preservesCoherence s hs

/-- Execute a whole transaction sequence. -/
def run : List Call → ContractState → ContractState
  | [], s => s
  | c :: rest, s => run rest (c.step s)

/-- **Whole-contract preservation.** Any sequence of `OwnedCounter` calls
    maps a coherent state to a coherent state. -/
theorem run_preservesCoherence :
    ∀ (calls : List Call) {s : ContractState}, Coherent s → Coherent (run calls s)
  | [], _, hs => hs
  | c :: rest, _, hs => run_preservesCoherence rest (c.step_preservesCoherence hs)

/-- **End-to-end: init → final.** From contract genesis, every reachable
    `OwnedCounter` state has its shadow storage channels in agreement with
    the flat word channel under the declared layout. No hypotheses. -/
theorem coherent_of_genesis (calls : List Call) : Coherent (run calls defaultState) :=
  run_preservesCoherence calls (defaultState_mappingCoherentAllKeys ownedCounterFields)

end Contracts.OwnedCounter.Proofs.StorageCoherence
