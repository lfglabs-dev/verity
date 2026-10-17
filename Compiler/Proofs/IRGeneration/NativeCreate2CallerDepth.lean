import Compiler.Proofs.IRGeneration.NativeCreate2CallerChecks

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeCreationWorld
open Verity.Core.Model

/-- At depth refusal the actual checked opcode refunds all forwarded child gas. -/
theorem caller_create2_depth_rejected (pre : EVM.State) (fuel : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (depth : 1024 ≤ pre.executionEnv.depth) :
    EVM.step (fuel + 1) (EVM.C' (create2MemoryDebited pre) .CREATE2)
      (some (.CREATE2, none)) (create2MemoryDebited pre) =
      .ok (create2RejectedState (create2MemoryDebited pre)
        (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size) := by
  have popped : (create2MemoryDebited pre).stack.pop4 =
      some (rest, UInt256.ofNat 0, offset, size, salt) := by
    change pre.stack.pop4 = _
    rw [stack]
    rfl
  have refused : ¬ (UInt256.ofNat 0 ≤
      ((create2MemoryDebited pre).accountMap.get? (create2MemoryDebited pre).executionEnv.codeOwner
        |>.option (UInt256.ofNat 0) (·.balance)) ∧
      (create2MemoryDebited pre).executionEnv.depth < 1024 ∧
      ((create2MemoryDebited pre).memory.readWithPadding offset.toNat size.toNat).size ≤ 49152) := by
    rintro ⟨_, entered, _⟩
    change pre.executionEnv.depth < 1024 at entered
    omega
  exact native_create2_entry_rejected fuel _ _ rest offset size salt popped nonce refused
    (create2_debited_gas_bound pre valid funded)

/-- The canonical depth gate uses the same actual total charge and physical memory. -/
theorem caller_create2_prepare_depth (pre : EVM.State)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (depth : 1024 ≤ pre.executionEnv.depth) :
    Create2Entry.prepare (CreationBytecode.callerMemory pre)
      { gas := pre.gasAvailable.toNat, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
      offset.toNat size.toNat = .ok (.depthFailure
        (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat)
        (pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 - EVM.C' pre .CREATE2)) := by
  have nowrap := native_memory_words_nowrap pre.activeWords offset size
  have charge := native_create2_entry_cost pre (UInt256.ofNat 0) offset size salt rest stack nowrap
  have enough : Create2Entry.entryCost (CreationBytecode.callerMemory pre) offset.toNat size.toNat ≤
      pre.gasAvailable.toNat := by rw [charge]; exact funded
  have prepared := Create2Entry.prepare_depth_failure (CreationBytecode.callerMemory pre)
    { gas := pre.gasAvailable.toNat, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
    offset.toNat size.toNat valid (by simp [mutable]) cap enough depth
  rw [charge] at prepared
  simpa only [Nat.sub_sub] using prepared

/-- Depth refusal is a checked continuation returning ZERO, not an exceptional halt. -/
theorem caller_create2_depth_X (pre : EVM.State) (jumps : Array UInt256) (fuel : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (decoded : decodeAt pre = (.CREATE2, none))
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152) (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (depth : 1024 ≤ pre.executionEnv.depth) :
    EVM.X (fuel + 4) jumps pre = EVM.X (fuel + 3) jumps
      (create2RejectedState (create2MemoryDebited pre)
        (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size) := by
  have stepped := caller_create2_depth_rejected pre (fuel + 2) rest offset size salt stack valid funded nonce depth
  exact caller_create2_X_continue pre _ jumps fuel rest offset size salt decoded stack limit mutable cap funded stepped

/-- Exact canonical depth-refusal frame, with expanded memory and refunded gas. -/
def callerDepthFinal (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (offset size : UInt256) : Create2Operation.Frame :=
  { world := { callerPreparedWorld world pre offset size with returndata := [] }
    context := { gas := pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 - EVM.C' pre .CREATE2, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
    warm := warm }

/-- Canonical run derives depth refusal without inspecting constructor bytes or hashes. -/
theorem caller_create2_depth_run (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (depth : 1024 ≤ pre.executionEnv.depth) :
    Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) =
        .ok (.continued 0 (callerDepthFinal world pre warm offset size)) := by
  have prepared := caller_create2_prepare_depth pre rest offset size salt stack valid mutable cap funded depth
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  have actual : Create2Entry.prepare (CreationBytecode.atBoundary ⟨world, pre, warm⟩).world.byteMemory
      (CreationBytecode.atBoundary ⟨world, pre, warm⟩).context
      (Verity.Core.Uint256.ofNat offset.toNat).val (Verity.Core.Uint256.ofNat size.toNat).val =
      .ok (.depthFailure
        (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat)
        (pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 - EVM.C' pre .CREATE2)) := by
    rw [offsetValue, sizeValue]
    exact prepared
  have result := Create2Operation.run_depth_failure (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
    (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
    (Verity.Core.Uint256.ofNat salt.toNat) _ _ actual
  exact result

/-- Entry refusal has every actual caller observation, including its zero stack value. -/
theorem caller_rejected_observations (pre : EVM.State) (cost : Nat)
    (rest : Stack UInt256) (offset size : UInt256) :
    CallerResultObservations pre (create2RejectedState pre cost rest offset size) rest offset size 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Depth refusal preserves complete raw account/storage agreement. -/
theorem caller_depth_agreement (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (rest : Stack UInt256) (offset size : UInt256) :
    Agreement (callerDepthFinal world pre warm offset size).world
      (create2RejectedState (create2MemoryDebited pre)
        (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size) warm := by
  have prepared := caller_prepared_agreement world pre warm agrees offset size
  have raw : Agreement (callerDepthFinal world pre warm offset size).world pre warm := { prepared with }
  exact agreement_frame_transport _ pre _ warm raw rfl rfl rfl

/-- The canonical and native depth-refusal continuations have identical gas. -/
theorem caller_depth_gas (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (rest : Stack UInt256) (offset size : UInt256)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    (create2RejectedState (create2MemoryDebited pre)
      (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size).gasAvailable.toNat =
      (callerDepthFinal world pre warm offset size).context.gas := by
  exact create2_debited_gas pre funded

/-- Exact expanded physical memory also agrees when no child is entered. -/
theorem caller_depth_physical_memory (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (allocated : CallerAllocated pre)
    (rest : Stack UInt256) (offset size : UInt256) :
    CallerPhysicalMemoryAgreement (callerDepthFinal world pre warm offset size).world
      (create2RejectedState (create2MemoryDebited pre)
        (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size) := by
  have observations := caller_rejected_observations (create2MemoryDebited pre)
    (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size
  have physical := caller_prepared_physical_memory world pre _ rest offset size 0 allocated
    (caller_observations_debited pre _ rest offset size 0 observations)
  exact ⟨physical.size, physical.byte⟩

private theorem caller_returndata_frame (world : Verity.ContractState) :
    callerWorldFrame { world with returndata := [] } = callerWorldFrame world := rfl

/-- No account, substate, event, or storage channel changes on depth refusal. -/
theorem caller_depth_frames (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (rest : Stack UInt256) (offset size : UInt256)
    (target : AccountAddress) :
    CallerFrameAgreement world (callerDepthFinal world pre warm offset size).world pre.substate
      (create2RejectedState (create2MemoryDebited pre)
        (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size).substate target := by
  constructor
  · change callerWorldFrame { callerPreparedWorld world pre offset size with returndata := [] } = _
    exact (caller_returndata_frame _).trans (caller_prepared_world_frame world pre offset size)
  · change { pre.substate with accessedAccounts := pre.substate.accessedAccounts } = pre.substate
    cases pre.substate; rfl
  · intro key _
    change world.storageWords key = world.storageWords key
    rfl

/-- Complete checked/native/canonical depth result, including every prior observation. -/
theorem caller_depth_operation_completed (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (jumps : Array UInt256) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (decoded : decodeAt pre = (.CREATE2, none))
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152) (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (depth : 1024 ≤ pre.executionEnv.depth) (target : AccountAddress) :
    ∃ next final,
      EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited pre) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next ∧
      EVM.X (fuel + 4) jumps pre = EVM.X (fuel + 3) jumps next ∧
      Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued 0 final) ∧
      Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations pre next rest offset size 0 ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement world final.world pre.substate next.substate target ∧
      next.accountMap = pre.accountMap ∧ next.substate = pre.substate ∧ final.warm = warm := by
  refine ⟨_, callerDepthFinal world pre warm offset size,
    caller_create2_depth_rejected pre (fuel + 2) rest offset size salt stack valid funded nonce depth,
    caller_create2_depth_X pre jumps fuel rest offset size salt decoded stack limit mutable cap valid funded nonce depth,
    caller_create2_depth_run world pre warm rest offset size salt stack valid mutable cap funded depth,
    caller_depth_agreement world pre warm agrees rest offset size,
    caller_depth_gas world pre warm rest offset size funded, ?_,
    caller_depth_physical_memory world pre warm allocated rest offset size,
    caller_depth_frames world pre warm rest offset size target, rfl, rfl, rfl⟩
  exact caller_observations_debited pre _ rest offset size 0
    (caller_rejected_observations (create2MemoryDebited pre)
      (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size)

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
