import Compiler.Proofs.IRGeneration.NativeCreate2CallerGas
import Compiler.Proofs.IRGeneration.CreationBytecode

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model MidnightInitcode
open Compiler.CompilationModel.DenoteMemory

/-- Rounded canonical physical memory matches the actual native word counter. -/
theorem caller_memory_words (pre : EVM.State) :
    words (CreationBytecode.callerMemory pre).size = pre.activeWords.toNat := by
  change (pre.activeWords.toNat * 32 + 31) / 32 = pre.activeWords.toNat
  omega

/-- Actual CREATE2 base/hash/initcode metering, before memory expansion. -/
theorem native_create2_instruction_cost (pre : EVM.State) (value offset size salt : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = value :: offset :: size :: salt :: rest) :
    EVM.C' pre .CREATE2 = 32000 + 8 * words size.toNat := by
  simp only [EVM.C', stack, List.getElem!_cons_succ, List.getElem!_cons_zero,
    EVM.R, GasConstants.Gcreate, GasConstants.Gkeccak256word, GasConstants.Ginitcodeword, words]
  omega

/-- Exact native expansion cost agrees with canonical physical memory cost,
including zero-length windows. Counter no-wrap is an explicit obligation. -/
theorem native_create2_memory_cost (pre : EVM.State) (value offset size salt : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = value :: offset :: size :: salt :: rest)
    (bounded : MachineState.M pre.activeWords.toNat offset.toNat size.toNat < UInt256.size) :
    EVM.memoryExpansionCost pre .CREATE2 = expansionCost (CreationBytecode.callerMemory pre) offset.toNat size.toNat := by
  simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', stack,
    List.getElem!_cons_succ, List.getElem!_cons_zero]
  rw [native_memory_cost _ bounded]
  have counter : EVM.Cₘ pre.activeWords = memoryCost pre.activeWords.toNat := rfl
  rw [counter]
  unfold expansionCost
  rw [caller_memory_words]
  cases size.toNat with
  | zero => simp only [MachineState.M, if_true, Nat.sub_self]
  | succ n => simp only [MachineState.M, Nat.succ_ne_zero, if_false, words]

/-- Total canonical entry charge is the actual native memory and instruction
charges together, not an independently supplied gas cost. -/
theorem native_create2_entry_cost (pre : EVM.State) (value offset size salt : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = value :: offset :: size :: salt :: rest)
    (bounded : MachineState.M pre.activeWords.toNat offset.toNat size.toNat < UInt256.size) :
    Create2Entry.entryCost (CreationBytecode.callerMemory pre) offset.toNat size.toNat =
      EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 := by
  rw [native_create2_memory_cost pre value offset size salt rest stack bounded,
    native_create2_instruction_cost pre value offset size salt rest stack]
  unfold Create2Entry.entryCost
  omega

/-- Canonical prepare uses exactly the actual native instruction+memory
charges to compute its EIP-150 split. Static/size/gas/depth guards are retained. -/
theorem native_create2_prepare_forwarded (pre : EVM.State) (value offset size salt : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = value :: offset :: size :: salt :: rest)
    (bounded : MachineState.M pre.activeWords.toNat offset.toNat size.toNat < UInt256.size)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas) (mutable : pre.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152)
    (enough : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat)
    (depth : pre.executionEnv.depth < 1024) :
    Create2Entry.prepare (CreationBytecode.callerMemory pre)
      { gas := pre.gasAvailable.toNat, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
      offset.toNat size.toNat = .ok (.forwarded
        { memory := returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat,
          retainedGas := (pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 - EVM.C' pre .CREATE2) / 64,
          childGas := EVM.L (pre.gasAvailable.toNat - EVM.memoryExpansionCost pre .CREATE2 - EVM.C' pre .CREATE2) }) := by
  have charge := native_create2_entry_cost pre value offset size salt rest stack bounded
  have funded : Create2Entry.entryCost (CreationBytecode.callerMemory pre) offset.toNat size.toNat ≤ pre.gasAvailable.toNat := by
    rw [charge]
    exact enough
  have prepared := Create2Entry.prepare_forwarded (CreationBytecode.callerMemory pre)
    { gas := pre.gasAvailable.toNat, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
    offset.toNat size.toNat valid (by simp only [mutable, Bool.not_true]) cap funded depth
  rw [charge] at prepared
  simpa only [Nat.sub_sub, EVM.L] using prepared

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
