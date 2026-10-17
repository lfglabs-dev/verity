import Compiler.Proofs.IRGeneration.NativeCreate2CallerOperation

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeCreationWorld
open Verity.Core.Model

/-- Both gas gates of native Z follow from the actual combined charge. -/
theorem caller_create2_gas_checks (pre : EVM.State)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    EVM.memoryExpansionCost pre .CREATE2 ≤ pre.gasAvailable.toNat ∧
      EVM.C' (create2MemoryDebited pre) .CREATE2 ≤ (create2MemoryDebited pre).gasAvailable.toNat := by
  have memory : EVM.memoryExpansionCost pre .CREATE2 ≤ pre.gasAvailable.toNat := by omega
  have debit := gas_sub_toNat pre.gasAvailable (EVM.memoryExpansionCost pre .CREATE2) memory
  constructor
  · exact memory
  · change EVM.C' pre .CREATE2 ≤ (pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre .CREATE2)).toNat
    rw [debit]
    omega

/-- Native CREATE2 passes the real exceptional checks under initial guards. -/
theorem caller_create2_checked (pre : EVM.State) (jumps : Array UInt256)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    Z jumps .CREATE2 pre = .ok (create2MemoryDebited pre, EVM.C' (create2MemoryDebited pre) .CREATE2) := by
  obtain ⟨memory, instruction⟩ := caller_create2_gas_checks pre funded
  have underflow : ¬ pre.stack.length < 4 := by rw [stack]; simp
  have overflow : ¬ pre.stack.length - 4 + 1 > 1024 := by omega
  have sizeGuard : ¬ size > UInt256.ofNat 49152 := by
    change ¬ 49152 < size.toNat
    omega
  change ¬ size > (⟨49152⟩ : UInt256) at sizeGuard
  change EVM.C' { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre .CREATE2) } .CREATE2 ≤
    (pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre .CREATE2)).toNat at instruction
  simp [Z, Nat.not_lt.mpr memory, Nat.not_lt.mpr instruction, EVM.δ, EVM.α,
    underflow, overflow, mutable, Operation.isCreate, create2MemoryDebited]
  simp [stack, sizeGuard]
  rfl


/-- The actual interpreter continues from the same CREATE2 result at one less fuel. -/
theorem caller_create2_X_continue (pre next : EVM.State) (jumps : Array UInt256)
    (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (decoded : decodeAt pre = (.CREATE2, none))
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (stepped : EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited pre) .CREATE2)
      (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next) :
    EVM.X (fuel + 4) jumps pre = EVM.X (fuel + 3) jumps next := by
  have checked := caller_create2_checked pre jumps rest offset size salt stack limit mutable cap funded
  exact X_succ_of_continue decoded checked stepped (by rfl)

/-- Checked native execution and the canonical operation share one complete result. -/
theorem caller_checked_operation_completed (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (payload : ByteArray) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerOperationGuards pre payload fuel rest offset size salt)
    (jumps : Array UInt256) (decoded : decodeAt pre = (.CREATE2, none))
    (limit : pre.stack.length ≤ 1024) :
    ∃ next value final,
      EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited pre) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next ∧
      EVM.X (fuel + 4) jumps pre = EVM.X (fuel + 3) jumps next ∧
      Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued value final) ∧
      Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations pre next rest offset size value ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement world final.world pre.substate next.substate
        (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)) := by
  obtain ⟨next, value, final, stepped, operation, agreement, gas, observations, physical, frames⟩ :=
    caller_operation_completed world pre warm agrees allocated payload fuel rest offset size salt guards
  have continuation := caller_create2_X_continue pre next jumps fuel rest offset size salt decoded
    guards.stack limit guards.mutable guards.cap guards.funded stepped
  exact ⟨next, value, final, stepped, continuation, operation, agreement, gas, observations, physical, frames⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
