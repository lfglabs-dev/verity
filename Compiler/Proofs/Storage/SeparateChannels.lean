/-
  C5 residual: `storageArray` and `knownAddresses` remain separate
  `ContractState` fields. This module packages the independence and
  coherence laws that make that an evidenced status, not a comment-only
  leftover.

  Not a fold into `storageWords`. Dynamic-array length-plus-keccak(slot)
  layout is a later representation change. Mapping-key tracking
  (`knownAddresses`) is only mutated by `setMapping`.

  These theorems live here, not in `Verity.Core`, so they are not on
  the default `simp` surface (eta-expanding `ContractState` there
  breaks Frames and contract Basic proofs).
-/

import Compiler.Proofs.Storage.MappingCoherence
import Compiler.Proofs.Storage.MappingCoherenceOn

namespace Compiler.Proofs.Storage.SeparateChannels

open Verity
open Verity.ContractState
open Compiler.Proofs.Storage.MappingCoherence
open Compiler.Proofs.Storage.MappingCoherenceOn

/-- Word-channel writes leave the array field unchanged. -/
theorem storageArray_independent_of_writeSlot
    (s : ContractState) (n : Nat) (v : Uint256) :
    (s.writeSlot n v).storageArray = s.storageArray :=
  rfl

theorem storageArray_independent_of_writeAddrSlot
    (s : ContractState) (n : Nat) (v : Address) :
    (s.writeAddrSlot n v).storageArray = s.storageArray :=
  rfl

theorem storageArray_independent_of_writeTransient
    (s : ContractState) (n : Nat) (v : Uint256) :
    (s.writeTransient n v).storageArray = s.storageArray :=
  rfl

theorem storageArray_independent_of_writeMap
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    (s.writeMap slot key v).storageArray = s.storageArray :=
  rfl

/-- Array writes leave the word backing and every word-channel view
    unchanged. -/
theorem storageWords_independent_of_writeArray
    (s : ContractState) (n : Nat) (vs : List Uint256) :
    (s.writeArray n vs).storageWords = s.storageWords :=
  rfl

theorem storage_independent_of_writeArray
    (s : ContractState) (n : Nat) (vs : List Uint256) :
    (s.writeArray n vs).storage = s.storage :=
  rfl

/-- Mapping-key tracking is independent of word, address, transient,
    and array writes. Only `setMapping` inserts keys. -/
theorem knownAddresses_independent_of_writeSlot
    (s : ContractState) (n : Nat) (v : Uint256) :
    (s.writeSlot n v).knownAddresses = s.knownAddresses :=
  rfl

theorem knownAddresses_independent_of_writeAddrSlot
    (s : ContractState) (n : Nat) (v : Address) :
    (s.writeAddrSlot n v).knownAddresses = s.knownAddresses :=
  rfl

theorem knownAddresses_independent_of_writeTransient
    (s : ContractState) (n : Nat) (v : Uint256) :
    (s.writeTransient n v).knownAddresses = s.knownAddresses :=
  rfl

theorem knownAddresses_independent_of_writeArray
    (s : ContractState) (n : Nat) (vs : List Uint256) :
    (s.writeArray n vs).knownAddresses = s.knownAddresses :=
  rfl

theorem knownAddresses_independent_of_writeMap
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    (s.writeMap slot key v).knownAddresses = s.knownAddresses :=
  rfl

/-- Non-mapping writes that never touch `StorageKey.slot` preserve
    global mapping coherence with no image-avoidance `∀`. -/
theorem writeAddrSlot_preserves_mappingCoherent_no_avoidance
    (s : ContractState) (n : Nat) (v : Address)
    (hcoh : MappingCoherent s) :
    MappingCoherent (s.writeAddrSlot n v) :=
  writeAddrSlot_preserves_mappingCoherent s n v hcoh

theorem writeArray_preserves_mappingCoherent_no_avoidance
    (s : ContractState) (n : Nat) (vs : List Uint256)
    (hcoh : MappingCoherent s) :
    MappingCoherent (s.writeArray n vs) :=
  writeArray_preserves_mappingCoherent s n vs hcoh

theorem writeTransient_preserves_mappingCoherent_no_avoidance
    (s : ContractState) (n : Nat) (v : Uint256)
    (hcoh : MappingCoherent s) :
    MappingCoherent (s.writeTransient n v) :=
  writeTransient_preserves_mappingCoherent s n v hcoh

/-- Finite listed-pair versions of the same discharge. -/
theorem writeAddrSlot_preserves_mappingCoherentOn_no_avoidance
    (s : ContractState) (pairs : List (Nat × Address)) (n : Nat) (v : Address)
    (hcoh : MappingCoherentOn s pairs) :
    MappingCoherentOn (s.writeAddrSlot n v) pairs :=
  writeAddrSlot_preserves_mappingCoherentOn s pairs n v hcoh

theorem writeArray_preserves_mappingCoherentOn_no_avoidance
    (s : ContractState) (pairs : List (Nat × Address)) (n : Nat)
    (vs : List Uint256) (hcoh : MappingCoherentOn s pairs) :
    MappingCoherentOn (s.writeArray n vs) pairs :=
  writeArray_preserves_mappingCoherentOn s pairs n vs hcoh

end Compiler.Proofs.Storage.SeparateChannels
