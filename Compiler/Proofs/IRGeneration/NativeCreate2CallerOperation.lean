import Compiler.Proofs.IRGeneration.NativeCreate2CallerFrames

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Initial native CREATE2 inputs only: no selected outcomes or final-state certificates. -/
structure CallerOperationGuards (pre : EVM.State) (payload : ByteArray) (fuel : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256) : Prop where
  bounded : payload.size ≤ 49152
  cap : size.toNat ≤ 49152
  enough : 10 ≤ fuel
  stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest
  code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload
  nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1
  depth : pre.executionEnv.depth < 1024
  valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas
  mutable : pre.executionEnv.perm = true
  funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat
  vacant : let machine := create2MemoryDebited pre
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ((create2ChildEntry machine (EVM.C' machine .CREATE2)).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
    ((create2ChildEntry machine (EVM.C' machine .CREATE2)).accountMap.getD target default).code.size = 0
  inner : ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat) =
    KeccakEngine.keccak256 (pre.memory.readWithPadding offset.toNat size.toNat)
  outer : ffi.KEC (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
      ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat)) =
    KeccakEngine.keccak256 (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
      ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat))

/-- Exact forwarded budget computed from the real two native charges. -/
def callerForwarded (pre : EVM.State) (offset size : UInt256) : Create2Entry.Forwarded :=
  let machine := create2MemoryDebited pre
  let gas := (machine.gasAvailable - UInt256.ofNat (EVM.C' machine .CREATE2)).toNat
  { memory := MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat
    retainedGas := gas / 64, childGas := EVM.L gas }

private theorem caller_boundary_prepare (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (payload : ByteArray) (fuel : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerOperationGuards pre payload fuel rest offset size salt) :
    Create2Entry.prepare (CreationBytecode.atBoundary ⟨world, pre, warm⟩).world.byteMemory
      (CreationBytecode.atBoundary ⟨world, pre, warm⟩).context
      (Verity.Core.Uint256.ofNat offset.toNat).val (Verity.Core.Uint256.ofNat size.toNat).val =
        .ok (.forwarded (callerForwarded pre offset size)) := by
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  rw [offsetValue, sizeValue]
  exact caller_prepare_funded pre (UInt256.ofNat 0) offset size salt rest guards.stack
    guards.valid guards.mutable guards.cap guards.funded guards.depth

private theorem caller_completed_gas (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre next : EVM.State) (cost fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (enough : 10 ≤ fuel) (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (child : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next)
    (memory : Compiler.CompilationModel.DenoteMemory.Memory) :
    next.gasAvailable.toNat = Create2Entry.completeGas
      { memory := memory, retainedGas := (pre.gasAvailable - UInt256.ofNat cost).toNat / 64,
        childGas := EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat } result.2.2.2.1.toNat := by
  have observed := native_create2_caller_frame (fuel + 2) cost pre next rest offset size salt result
    popped nonce entry child stepped
  have returned := native_create2_returned_gas_le payload bounded pre cost offset size salt code fuel enough result child
  exact native_create2_complete_gas pre next cost rest offset size result observed returned memory

/-- Full canonical/native operation result from the original funded caller. -/
theorem caller_operation_completed (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (payload : ByteArray) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerOperationGuards pre payload fuel rest offset size salt) :
    ∃ next value final,
      EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited pre) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next ∧
      Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued value final) ∧
      Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations pre next rest offset size value ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement world final.world pre.substate next.substate
        (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)) := by
  let machine := create2MemoryDebited pre
  let cost := EVM.C' machine .CREATE2
  let prepared := callerPreparedWorld world pre offset size
  have agreement := caller_prepared_agreement world machine warm
    (caller_debited_agreement world pre warm agrees) offset size
  have popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt) := by rw [guards.stack]; rfl
  obtain ⟨next, stepped⟩ := caller_funded_completed payload guards.bounded fuel pre rest offset size salt
    guards.enough guards.code popped guards.nonce guards.cap guards.depth guards.valid guards.funded
  obtain ⟨result, reserved, committed, child, entered, commit, transport, _, _⟩ := native_create2_entered_world
    prepared machine next warm agreement payload guards.bounded fuel cost rest offset size salt guards.enough
      guards.code popped guards.nonce (caller_zero_entry machine offset size guards.cap guards.depth) guards.vacant stepped
  have entry := caller_enterCode_eq_runEntered world machine warm
    (caller_debited_agreement world pre warm agrees) (caller_debited_allocation pre allocated)
    payload cost offset size salt (EVM.L (machine.gasAvailable - UInt256.ofNat cost).toNat) guards.cap guards.code guards.nonce guards.vacant guards.inner guards.outer
  have prepare := caller_boundary_prepare world pre warm payload fuel rest offset size salt guards
  have legal := caller_world_legal_nonce world pre warm agrees guards.nonce
  have operation := Create2Operation.run_forwarded (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
    (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
    (Verity.Core.Uint256.ofNat salt.toNat) (callerForwarded pre offset size) _ committed prepare legal (entry.trans entered) commit
  have target := native_create2_prepared_address world pre warm agrees allocated offset size salt guards.cap guards.inner guards.outer
  rw [guards.code] at target
  have gas := caller_completed_gas payload guards.bounded machine next cost fuel rest offset size salt guards.code
    guards.enough popped guards.nonce (caller_zero_entry machine offset size guards.cap guards.depth) result child stepped
    (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat)
  have continuation := native_create2_result_observations payload guards.bounded machine next cost fuel rest offset size salt
    guards.code guards.vacant guards.enough popped guards.nonce (caller_zero_entry machine offset size guards.cap guards.depth) result child stepped prepared.creationAccounts reserved
  have physical := caller_committed_physical_memory world committed machine next rest offset size _
    (caller_debited_allocation pre allocated) continuation _ commit
  have frames := native_create2_committed_frames world committed machine next payload guards.bounded cost fuel rest offset size salt
    guards.code guards.vacant guards.enough popped guards.nonce (caller_zero_entry machine offset size guards.cap guards.depth) result child stepped prepared.creationAccounts reserved commit
  refine ⟨next, _, _, stepped, operation, ?_, gas, caller_observations_debited pre next rest offset size _ continuation, physical, frames⟩
  exact (congrArg (fun address => Agreement committed next (Create2Access.warm warm address)) target).mp transport

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
