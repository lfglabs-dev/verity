import Compiler.Proofs.IRGeneration.NativeCreate2RejectedEntry

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model

/-- The actual final native word gas equals EIP-150 retained gas plus actual
child return, without modular wrapping or a supplied final gas certificate. -/
theorem native_create2_caller_gas (pre next : EVM.State) (cost : Nat)
    (rest : Stack UInt256) (offset size : UInt256)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (observed : Create2CallerObservations pre next cost rest offset size result)
    (returned : result.2.2.2.1.toNat ≤ EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat) :
    next.gasAvailable.toNat = (pre.gasAvailable - UInt256.ofNat cost).toNat / 64 + result.2.2.2.1.toNat := by
  let gas := pre.gasAvailable - UInt256.ofNat cost
  have divided : gas.toNat / 64 ≤ gas.toNat := Nat.div_le_self _ _
  have forwarded : EVM.L gas.toNat = gas.toNat - gas.toNat / 64 := rfl
  have retained : gas.toNat - EVM.L gas.toNat = gas.toNat / 64 := by omega
  have bounded : gas.toNat / 64 + result.2.2.2.1.toNat < UInt256.size := by
    have wordBound : gas.toNat < UInt256.size := gas.val.isLt
    change result.2.2.2.1.toNat ≤ gas.toNat - gas.toNat / 64 at returned
    omega
  rw [observed.2.1]
  change ((gas.toNat - EVM.L gas.toNat + result.2.2.2.1.toNat) % UInt256.size) = _
  rw [retained, Nat.mod_eq_of_lt bounded]

/-- Actual native gas agrees with canonical completeGas for the canonical
EIP-150 split of this charged parent budget. -/
theorem native_create2_complete_gas (pre next : EVM.State) (cost : Nat)
    (rest : Stack UInt256) (offset size : UInt256)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (observed : Create2CallerObservations pre next cost rest offset size result)
    (returned : result.2.2.2.1.toNat ≤ EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat)
    (memory : Compiler.CompilationModel.DenoteMemory.Memory) :
    next.gasAvailable.toNat = Create2Entry.completeGas
      { memory := memory, retainedGas := (pre.gasAvailable - UInt256.ofNat cost).toNat / 64,
        childGas := EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat } result.2.2.2.1.toNat := by
  exact native_create2_caller_gas pre next cost rest offset size result observed returned

/-- Derive exact native parent gas from its actual successful step and the
actual adequate child invocation; no return bound or observation is supplied. -/
theorem native_create2_observed_gas (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (fuel cost : Nat) (pre next : EVM.State) (rest : Stack UInt256) (offset size salt : UInt256)
    (enough : 10 ≤ fuel)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next) :
    ∃ result, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      next.gasAvailable.toNat = (pre.gasAvailable - UInt256.ofNat cost).toNat / 64 + result.2.2.2.1.toNat := by
  obtain ⟨result, completed⟩ := native_create2_child_completed payload bounded pre cost offset size salt code fuel enough
  have returned := native_create2_returned_gas_le payload bounded pre cost offset size salt code fuel enough result completed
  have observed := native_create2_caller_frame (fuel + 2) cost pre next rest offset size salt result
    popped nonce entry completed stepped
  exact ⟨result, completed, native_create2_caller_gas pre next cost rest offset size result observed returned⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
