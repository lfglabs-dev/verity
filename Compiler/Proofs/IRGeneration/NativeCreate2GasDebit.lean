import Compiler.Proofs.IRGeneration.NativeCreate2EntryCost

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model

/-- Actual native memory gas debit before EVM.step charges instruction gas. -/
def create2MemoryDebited (pre : EVM.State) : EVM.State :=
  { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre .CREATE2) }

/-- CREATE2 instruction gas depends on its actual stack, not remaining gas. -/
theorem create2_debited_instruction_cost (pre : EVM.State) :
    EVM.C' (create2MemoryDebited pre) .CREATE2 = EVM.C' pre .CREATE2 := rfl

/-- Both actual native word subtractions equal natural subtraction when the
real combined charge fits. No modular-underflow result is projected as gas. -/
theorem create2_debited_gas (pre : EVM.State)
    (enough : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    ((create2MemoryDebited pre).gasAvailable - UInt256.ofNat (EVM.C' (create2MemoryDebited pre) .CREATE2)).toNat =
      pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 - EVM.C' pre .CREATE2 := by
  have memoryEnough : EVM.memoryExpansionCost pre .CREATE2 ≤ pre.gasAvailable.toNat := by omega
  have memoryGas : (create2MemoryDebited pre).gasAvailable.toNat =
      pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 :=
    gas_sub_toNat pre.gasAvailable _ memoryEnough
  have instructionEnough : EVM.C' (create2MemoryDebited pre) .CREATE2 ≤ (create2MemoryDebited pre).gasAvailable.toNat := by
    rw [create2_debited_instruction_cost, memoryGas]
    omega
  rw [gas_sub_toNat _ _ instructionEnough, memoryGas, create2_debited_instruction_cost]

/-- The canonical actual uint64 gas domain implies the parent's no-wrap bound;
this bound need not be independently supplied by the importer. -/
theorem create2_debited_gas_bound (pre : EVM.State)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (enough : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    ((create2MemoryDebited pre).gasAvailable - UInt256.ofNat (EVM.C' (create2MemoryDebited pre) .CREATE2)).toNat < 2^255 := by
  rw [create2_debited_gas pre enough]
  have wide : Create2Entry.maxGas < 2^255 := by decide
  omega

/-- Canonical prepare's split is exactly the actual native debited word gas.
The real opcode/memory charges and their successful guards are retained. -/
theorem create2_prepare_debited (pre : EVM.State) (value offset size salt : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = value :: offset :: size :: salt :: rest)
    (bounded : MachineState.M pre.activeWords.toNat offset.toNat size.toNat < UInt256.size)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (enough : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (depth : pre.executionEnv.depth < 1024) :
    let gas := ((create2MemoryDebited pre).gasAvailable - UInt256.ofNat (EVM.C' (create2MemoryDebited pre) .CREATE2)).toNat
    Create2Entry.prepare (CreationBytecode.callerMemory pre)
      { gas := pre.gasAvailable.toNat, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
      offset.toNat size.toNat = .ok (.forwarded
        { memory := MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat,
          retainedGas := gas / 64, childGas := EVM.L gas }) := by
  dsimp only
  rw [create2_debited_gas pre enough]
  exact native_create2_prepare_forwarded pre value offset size salt rest stack bounded valid mutable cap enough depth

/-- Actual funded CREATE2 parent completion after native memory metering.
The uint64 input-gas guard derives the prior anti-wrap premise internally. -/
theorem native_create2_funded_completed (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (fuel : Nat) (pre : EVM.State) (rest : Stack UInt256) (offset size salt : UInt256)
    (adequate : 10 ≤ fuel)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (enough : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat) :
    ∃ next, EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited pre) .CREATE2)
      (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next := by
  exact native_create2_parent_completed payload bounded fuel _ (create2MemoryDebited pre) rest offset size salt
    adequate code popped nonce entry (create2_debited_gas_bound pre valid enough)

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
