import Compiler.Proofs.IRGeneration.NativeCreate2PreparedAddress
import Compiler.Proofs.IRGeneration.NativeCreate2GasDebit

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Actual memory metering changes gas only and preserves raw world agreement. -/
theorem caller_debited_agreement (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) :
    Agreement world (create2MemoryDebited pre) warm := by
  exact { agrees with }

/-- Actual gas metering preserves the proved caller-memory allocation invariant. -/
theorem caller_debited_allocation (pre : EVM.State) (allocated : CallerAllocated pre) :
    CallerAllocated (create2MemoryDebited pre) := allocated

/-- Canonical preparation follows from the actual initial machine guards.
The active-word no-wrap condition is derived universally, not supplied. -/
theorem caller_prepare_funded (pre : EVM.State) (value offset size salt : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = value :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (depth : pre.executionEnv.depth < 1024) :
    let gas := ((create2MemoryDebited pre).gasAvailable -
      UInt256.ofNat (EVM.C' (create2MemoryDebited pre) .CREATE2)).toNat
    Create2Entry.prepare (CreationBytecode.callerMemory pre)
      { gas := pre.gasAvailable.toNat, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
      offset.toNat size.toNat = .ok (.forwarded
        { memory := MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat,
          retainedGas := gas / 64, childGas := EVM.L gas }) := by
  exact create2_prepare_debited pre value offset size salt rest stack
    (native_memory_words_nowrap pre.activeWords offset size) valid mutable cap funded depth

/-- The actual padded window has exactly the requested length within the cap. -/
theorem caller_padded_size (pre : EVM.State) (offset size : UInt256)
    (cap : size.toNat ≤ 49152) :
    (pre.memory.readWithPadding offset.toNat size.toNat).size = size.toNat := by
  rw [native_padded_slice pre.memory offset.toNat size.toNat cap]
  simp only [ByteArray.size, List.size_toArray, List.length_map, List.length_range]

/-- Zero-value CREATE2 entry guards follow from depth and the actual size cap.
No separate child-entry success certificate is required. -/
theorem caller_zero_entry (pre : EVM.State) (offset size : UInt256)
    (cap : size.toNat ≤ 49152) (depth : pre.executionEnv.depth < 1024) :
    UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152 := by
  refine ⟨?_, depth, ?_⟩
  · change 0 ≤ _
    exact Nat.zero_le _
  · rw [caller_padded_size pre offset size cap]
    exact cap

/-- Derive an actual completed native parent from initial guards only.
The child entry and charged-gas no-wrap obligations are discharged internally. -/
theorem caller_funded_completed (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (fuel : Nat) (pre : EVM.State) (rest : Stack UInt256) (offset size salt : UInt256)
    (adequate : 10 ≤ fuel)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (cap : size.toNat ≤ 49152) (depth : pre.executionEnv.depth < 1024)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    ∃ next, EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited pre) .CREATE2)
      (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next := by
  exact native_create2_funded_completed payload bounded fuel pre rest offset size salt
    adequate code popped nonce (caller_zero_entry pre offset size cap depth) valid funded

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
