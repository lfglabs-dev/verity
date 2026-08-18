/-
  C5 step 4 (contract-level slice): threading `MappingCoherentAllKeys`
  through `Contract` execution.

  `MappingCoherentAllKeys` is preserved by the individual write helpers
  (`MappingCoherentAllKeys.lean`). That is a statement about single state
  updates; it says nothing about running a whole contract entrypoint, which
  is a `Contract α = ContractState → ContractResult α` built from `bind`,
  guards and the storage primitives.

  This file closes that distance. `PreservesCoherence fields c` says the
  action `c` maps coherent pre-states to coherent post-states, and the
  lemmas below make it compositional:

  * `preservesCoherence_bind` — closure under `do` sequencing, covering the
    revert branch as well as the success branch;
  * `preservesCoherence_of_stateless` — every read-only primitive
    (`msgSender`, `getStorage`, `require`, ...) discharges in one step;
  * `preservesCoherence_setStorage` / `_setStorageAddr` / `_setTransient` —
    the write primitives, reduced to the write-helper laws.

  The `setStorage` case is the only one carrying a layout side condition
  (`DerivedMappingSlotsAvoid`): a flat word write is invisible to the
  shadow channels exactly when it does not land on a derived mapping slot.
  `setStorageAddr` and transient writes land on other `StorageKey`
  constructors and need no side condition at all.

  Nothing here is contract-specific; `Contracts/*/Proofs/StorageCoherence.lean`
  instantiates it against a declared layout.
-/

import Compiler.Proofs.Storage.MappingCoherentAllKeys

namespace Compiler.Proofs.Storage.MappingCoherentExec

open Verity
open Verity.ContractState
open Compiler.CompilationModel
open Compiler.Proofs.Storage.MappingCoherentGlobal

variable {α β : Type}

/-- **Contract-level coherence preservation.** Running `c` from a state whose
    shadow channels agree with the flat channels under `fields` lands in a
    state where they still agree.

    Stated on the raw action `c s` rather than `Contract.run c s` so that it
    composes across `bind`; `preservesCoherence_run` transfers it to
    `Contract.run`, whose revert branch restores the (coherent) pre-state. -/
def PreservesCoherence (fields : List Field) (c : Contract α) : Prop :=
  ∀ s : ContractState,
    MappingCoherentAllKeys fields s → MappingCoherentAllKeys fields (c s).snd

/-! ### Compositional structure -/

/-- An action that never changes the state preserves coherence. This covers
    every read-only primitive and both branches of a guard. -/
theorem preservesCoherence_of_stateless {fields : List Field} {c : Contract α}
    (h : ∀ s : ContractState, (c s).snd = s) : PreservesCoherence fields c := by
  intro s hs
  rw [h s]
  exact hs

theorem preservesCoherence_pure {fields : List Field} (a : α) :
    PreservesCoherence fields (Pure.pure a : Contract α) :=
  preservesCoherence_of_stateless (fun _ => rfl)

/-- `do` sequencing. The revert branch of `bind` forwards the state produced
    by `ma`, so it is covered by `ma`'s own preservation.

    Stated on `>>=` rather than `Verity.bind` so that it matches an entrypoint's
    `do` block head-on: unifying against the raw `Verity.bind` makes the
    elaborator reduce through the stateless prefix and bind the wrong action. -/
theorem preservesCoherence_bind {fields : List Field} {ma : Contract α}
    {f : α → Contract β} (hma : PreservesCoherence fields ma)
    (hf : ∀ a, PreservesCoherence fields (f a)) :
    PreservesCoherence fields (ma >>= f) := by
  intro s hs
  have hstep := hma s hs
  show MappingCoherentAllKeys fields (Verity.bind ma f s).snd
  simp only [Verity.bind]
  cases hcase : ma s with
  | success a s' =>
      rw [hcase] at hstep
      exact hf a s' hstep
  | revert msg s' =>
      rw [hcase] at hstep
      exact hstep

/-- Transfer to `Contract.run`, which normalises a revert to the pre-call
    snapshot. Both branches are coherent, so the guarantee is unconditional
    on success or revert. -/
theorem preservesCoherence_run {fields : List Field} {c : Contract α}
    (h : PreservesCoherence fields c) (s : ContractState)
    (hs : MappingCoherentAllKeys fields s) :
    MappingCoherentAllKeys fields (c.run s).snd := by
  have hstep := h s hs
  simp only [Contract.run]
  cases hcase : c s with
  | success a s' =>
      rw [hcase] at hstep
      exact hstep
  | revert msg s' => exact hs

/-! ### Read-only primitives -/

theorem preservesCoherence_getStorage {fields : List Field} (sl : StorageSlot Uint256) :
    PreservesCoherence fields (getStorage sl) :=
  preservesCoherence_of_stateless (fun _ => rfl)

theorem preservesCoherence_getStorageAddr {fields : List Field} (sl : StorageSlot Address) :
    PreservesCoherence fields (getStorageAddr sl) :=
  preservesCoherence_of_stateless (fun _ => rfl)

theorem preservesCoherence_getMapping {fields : List Field}
    (sl : StorageSlot (Address → Uint256)) (key : Address) :
    PreservesCoherence fields (getMapping sl key) :=
  preservesCoherence_of_stateless (fun _ => rfl)

theorem preservesCoherence_msgSender {fields : List Field} :
    PreservesCoherence fields msgSender :=
  preservesCoherence_of_stateless (fun _ => rfl)

/-- Guards keep the state on both branches: `success` forwards it and
    `revert` carries it unchanged. -/
theorem preservesCoherence_require {fields : List Field} (cond : Bool) (msg : String) :
    PreservesCoherence fields (require cond msg) := by
  refine preservesCoherence_of_stateless (fun s => ?_)
  simp only [require]
  cases cond <;> rfl

/-! ### Write primitives -/

/-- A flat word write. The layout side condition is exactly the statement
    that slot `sl.slot` is not the image of any derived mapping entry. -/
theorem preservesCoherence_setStorage {fields : List Field} (sl : StorageSlot Uint256)
    (v : Uint256) (havoid : DerivedMappingSlotsAvoid fields sl.slot) :
    PreservesCoherence fields (setStorage sl v) := by
  intro s hs
  exact writeSlot_preserves_mappingCoherentAllKeys fields s sl.slot v havoid hs

/-- An address-channel write needs no layout side condition: it lands on
    `StorageKey.addr`, a different constructor from every derived slot. -/
theorem preservesCoherence_setStorageAddr {fields : List Field} (sl : StorageSlot Address)
    (a : Address) : PreservesCoherence fields (setStorageAddr sl a) := by
  intro s hs
  exact writeAddrSlot_preserves_mappingCoherentAllKeys fields s sl.slot a hs

/-! ### Why there is no `preservesCoherence_setMapping`

`setMapping` is shadow-only: it goes through `ContractState.writeMap`, which
updates `storageWords (.map slot key)` and nothing else. Coherence at that key
demands agreement with `storage (solidityMappingSlot slot key)`, so a single
`setMapping` falsifies the invariant — the missing lemma is not hard, it is
false under current semantics.

The corresponding law on main,
`writeMap_aligned_preserves_mappingCoherentAllKeys`, is stated for the
*aligned* write `(s.writeMap ..).writeSlot (solidityMappingSlot ..) v`, which
is the post-flip shape no EDSL primitive emits yet. Until the storage
representation flip makes `setMapping` aligned, this file can thread coherence
only through mapping-free entrypoints. -/

end Compiler.Proofs.Storage.MappingCoherentExec
