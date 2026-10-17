import Compiler.Proofs.IRGeneration.NativeCreate2CallerExceptional

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeCreationWorld
open Verity.Core.Model

/-- Actual nonce refusal follows from the initial projected nonce limit. -/
theorem caller_create2_nonce_rejected (pre : EVM.State) (fuel : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (nonce : ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1) :
    EVM.step (fuel + 1) (EVM.C' (create2MemoryDebited pre) .CREATE2)
      (some (.CREATE2, none)) (create2MemoryDebited pre) =
      .ok (create2RejectedState (create2MemoryDebited pre)
        (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size) := by
  have popped : (create2MemoryDebited pre).stack.pop4 =
      some (rest, UInt256.ofNat 0, offset, size, salt) := by
    change pre.stack.pop4 = _
    rw [stack]
    rfl
  exact native_create2_nonce_rejected fuel _ _ rest offset size salt popped nonce
    (create2_debited_gas_bound pre valid funded)

/-- Actual world agreement transfers the uint64-limit nonce exactly. -/
theorem caller_world_nonce_limit (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (nonce : ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat = 2^64 - 1) :
    (world.creationAccounts world.thisAddress.val).nonce = Create2NonceEntry.maxCreatorNonce := by
  have projected := congrArg Create2Accounts.Account.nonce (agrees.accounts pre.executionEnv.codeOwner)
  change (world.creationAccounts pre.executionEnv.codeOwner.val).nonce =
    ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat at projected
  rw [agrees.caller, projected, nonce]
  rfl

/-- Full refund is exactly the actual gas after both metering charges. -/
theorem caller_forwarded_full_refund (pre : EVM.State) (offset size : UInt256)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    Create2Entry.completeGas (callerForwarded pre offset size) (callerForwarded pre offset size).childGas =
      pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 - EVM.C' pre .CREATE2 := by
  let gas := ((create2MemoryDebited pre).gasAvailable - UInt256.ofNat (EVM.C' (create2MemoryDebited pre) .CREATE2)).toNat
  have split : gas / 64 + EVM.L gas = gas := by
    unfold EVM.L
    have bound := Nat.div_le_self gas 64
    omega
  change gas / 64 + EVM.L gas = _
  rw [split]
  exact create2_debited_gas pre funded

/-- Canonical nonce refusal returns zero without inspecting constructor bytes. -/
theorem caller_create2_nonce_run (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (depth : pre.executionEnv.depth < 1024)
    (nonce : ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat = 2^64 - 1) :
    Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued 0 (callerDepthFinal world pre warm offset size)) := by
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  have actual : Create2Entry.prepare (CreationBytecode.atBoundary ⟨world, pre, warm⟩).world.byteMemory
      (CreationBytecode.atBoundary ⟨world, pre, warm⟩).context
      (Verity.Core.Uint256.ofNat offset.toNat).val (Verity.Core.Uint256.ofNat size.toNat).val =
        .ok (.forwarded (callerForwarded pre offset size)) := by
    rw [offsetValue, sizeValue]
    exact caller_prepare_funded pre (UInt256.ofNat 0) offset size salt rest stack valid mutable cap funded depth
  have boundary : Agreement (CreationBytecode.atBoundary ⟨world, pre, warm⟩).world pre warm := { agrees with }
  have overflow := caller_world_nonce_limit _ pre warm boundary nonce
  have result := Create2Operation.run_nonce_overflow (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
    (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
    (Verity.Core.Uint256.ofNat salt.toNat) (callerForwarded pre offset size) actual overflow
  rw [caller_forwarded_full_refund pre offset size funded] at result
  exact result

/-- Checked nonce refusal and the full canonical continuation share every observation. -/
theorem caller_nonce_operation_completed (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (jumps : Array UInt256) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (decoded : decodeAt pre = (.CREATE2, none))
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152) (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (depth : pre.executionEnv.depth < 1024)
    (nonce : ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat = 2^64 - 1)
    (target : AccountAddress) :
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
  have rejected := caller_create2_nonce_rejected pre (fuel + 2) rest offset size salt stack valid funded (by omega)
  refine ⟨_, callerDepthFinal world pre warm offset size, rejected,
    caller_create2_X_continue pre _ jumps fuel rest offset size salt decoded stack limit mutable cap funded rejected,
    caller_create2_nonce_run world pre warm agrees rest offset size salt stack valid mutable cap funded depth nonce,
    caller_depth_agreement world pre warm agrees rest offset size,
    caller_depth_gas world pre warm rest offset size funded, ?_,
    caller_depth_physical_memory world pre warm allocated rest offset size,
    caller_depth_frames world pre warm rest offset size target, rfl, rfl, rfl⟩
  exact caller_observations_debited pre _ rest offset size 0
    (caller_rejected_observations (create2MemoryDebited pre)
      (EVM.C' (create2MemoryDebited pre) .CREATE2) rest offset size)

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
