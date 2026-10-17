import Compiler.Proofs.IRGeneration.NativeCreate2CallerValue

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory

/-- Canonical prepared byte extent is exactly the native updated word extent,
including zero-size windows and already-active memory. -/
theorem caller_prepared_memory_size (pre : EVM.State) (offset size : UInt256) :
    (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat).size =
      MachineState.M pre.activeWords.toNat offset.toNat size.toNat * 32 := by
  cases sizeValue : size.toNat with
  | zero => simp only [MidnightInitcode.returnMemory, true_or, if_true, MachineState.M, CreationBytecode.callerMemory]
  | succ count =>
    simp only [MidnightInitcode.returnMemory, MachineState.M, Nat.succ_ne_zero, false_or, CreationBytecode.callerMemory]
    by_cases active : offset.toNat + (count + 1) ≤ pre.activeWords.toNat * 32
    · rw [if_pos active]
      change pre.activeWords.toNat * 32 = max pre.activeWords.toNat ((offset.toNat + (count + 1) + 31) / 32) * 32
      rw [Nat.max_eq_left (by omega)]
    · rw [if_neg active]
      change max (pre.activeWords.toNat * 32) (expandedLength (offset.toNat + (count + 1))) = _
      have nonzero : offset.toNat + (count + 1) ≠ 0 := by omega
      rw [expandedLength, if_neg nonzero]
      omega

/-- Actual CREATE2 continuation retains allocated-byte validity after expansion. -/
theorem caller_result_allocated (pre next : EVM.State) (rest : Stack UInt256)
    (offset size : UInt256) (value : Verity.Core.Uint256) (allocated : CallerAllocated pre)
    (observed : CallerResultObservations pre next rest offset size value) : CallerAllocated next := by
  unfold CallerAllocated
  rw [observed.memory, observed.activeWords]
  have exactWords : (UInt256.ofNat (MachineState.M pre.activeWords.toNat offset.toNat size.toNat)).toNat =
      MachineState.M pre.activeWords.toNat offset.toNat size.toNat :=
    Nat.mod_eq_of_lt (native_memory_words_nowrap pre.activeWords offset size)
  rw [exactWords]
  have grows : pre.activeWords.toNat ≤ MachineState.M pre.activeWords.toNat offset.toNat size.toNat := by
    unfold MachineState.M
    split
    · exact Nat.le_refl _
    · exact Nat.le_max_left _ _
  exact Nat.le_trans allocated (Nat.mul_le_mul_right 32 grows)

/-- All physical byte observations survive actual caller memory expansion,
including every zero-filled byte beyond the old active extent. -/
theorem caller_result_memory_byte (pre next : EVM.State) (rest : Stack UInt256)
    (offset size : UInt256) (value : Verity.Core.Uint256) (allocated : CallerAllocated pre)
    (observed : CallerResultObservations pre next rest offset size value) (index : Nat) :
    (CreationBytecode.callerMemory next).readByte index = (CreationBytecode.callerMemory pre).readByte index := by
  have nextAllocated := caller_result_allocated pre next rest offset size value allocated observed
  have before := caller_memory_byte pre allocated index
  have after := caller_memory_byte next nextAllocated index
  rw [observed.memory] at after
  have same := after.trans before.symm
  apply Fin.ext
  have sameNat := congrArg UInt8.toNat same
  change ((CreationBytecode.callerMemory next).readByte index).val % 256 =
    ((CreationBytecode.callerMemory pre).readByte index).val % 256 at sameNat
  simpa only [Nat.mod_eq_of_lt ((CreationBytecode.callerMemory next).readByte index).isLt,
    Nat.mod_eq_of_lt ((CreationBytecode.callerMemory pre).readByte index).isLt] using sameNat

/-- Creation commit changes accounts/storage only, retaining exact physical memory. -/
theorem creation_commit_physical_memory (world committed : Verity.ContractState)
    (outcome : Create2Runtime.Outcome) (commit : CreationStorage.commit world outcome = .ok committed) :
    committed.byteMemory = world.byteMemory := by
  have framed := congrArg Verity.ContractState.byteMemory (CreationStorage.commit_frame world outcome committed commit)
  exact framed

/-- Complete physical-memory observation, including active extent and every byte. -/
structure CallerPhysicalMemoryAgreement (world : Verity.ContractState) (machine : EVM.State) : Prop where
  size : world.byteMemory.size = machine.activeWords.toNat * 32
  byte : ∀ index, world.byteMemory.readByte index = (CreationBytecode.callerMemory machine).readByte index

/-- The canonical prepared memory agrees with every actual final native byte
and active word, not merely the initcode window used for the address hash. -/
theorem caller_prepared_physical_memory (world : Verity.ContractState) (pre next : EVM.State)
    (rest : Stack UInt256) (offset size : UInt256) (value : Verity.Core.Uint256)
    (allocated : CallerAllocated pre) (observed : CallerResultObservations pre next rest offset size value) :
    CallerPhysicalMemoryAgreement (callerPreparedWorld world pre offset size) next := by
  constructor
  · change (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat).size = _
    rw [caller_prepared_memory_size, observed.activeWords]
    have exactWords : (UInt256.ofNat (MachineState.M pre.activeWords.toNat offset.toNat size.toNat)).toNat =
        MachineState.M pre.activeWords.toNat offset.toNat size.toNat :=
      Nat.mod_eq_of_lt (native_memory_words_nowrap pre.activeWords offset size)
    rw [exactWords]
  · intro index
    change (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat).readByte index = _
    rw [prepared_memory_read]
    exact (caller_result_memory_byte pre next rest offset size value allocated observed index).symm

/-- Transport complete actual physical memory through the real storage commit. -/
theorem caller_committed_physical_memory (world committed : Verity.ContractState) (pre next : EVM.State)
    (rest : Stack UInt256) (offset size : UInt256) (value : Verity.Core.Uint256)
    (allocated : CallerAllocated pre) (observed : CallerResultObservations pre next rest offset size value)
    (outcome : Create2Runtime.Outcome)
    (commit : CreationStorage.commit (callerPreparedWorld world pre offset size) outcome = .ok committed) :
    CallerPhysicalMemoryAgreement committed next := by
  have prepared := caller_prepared_physical_memory world pre next rest offset size value allocated observed
  have memory := creation_commit_physical_memory _ _ _ commit
  exact ⟨memory ▸ prepared.size, fun index => memory ▸ prepared.byte index⟩

/-- Canonical caller nonce legality follows from the actual owner agreement. -/
theorem caller_world_legal_nonce (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1) :
    (world.creationAccounts world.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce := by
  rw [agrees.caller]
  exact caller_legal_nonce world pre warm agrees nonce

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
