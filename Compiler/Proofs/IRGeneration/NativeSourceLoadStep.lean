import Compiler.Proofs.IRGeneration.NativeSourceFirstCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceLoadStep
open EvmYul EVM.Proof

def loaded (gasCost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256) : EVM.State :=
  let charged := stepPre gasCost pre
  let pair := charged.toMachineState.mload address
  ({ charged with toMachineState := pair.2 } : EVM.State).replaceStackAndIncrPC (pair.1 :: rest)

theorem step (fuel gasCost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256)
    (stack : pre.stack = address :: rest) :
    EVM.step (fuel + 1) gasCost (some (.MLOAD, none)) pre = .ok (loaded gasCost pre address rest) := by
  change EvmYul.step (τ := .EVM) .MLOAD none (stepPre gasCost pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem stack (gasCost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256) :
    (loaded gasCost pre address rest).stack = pre.toMachineState.lookupMemory address :: rest := by rfl

theorem memory (gasCost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256) :
    (loaded gasCost pre address rest).memory = pre.memory := by rfl

/-- Native MLOAD consults the actual allocated carrier and active-word guard. -/
theorem value (gasCost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256)
    (carrier : address.toNat < pre.memory.size) (active : ¬address ≥ pre.activeWords * ⟨32⟩) :
    (loaded gasCost pre address rest).stack =
      UInt256.ofNat (fromByteArrayBigEndian (pre.memory.readWithPadding address.toNat 32)) :: rest := by
  rw [stack]
  unfold MachineState.lookupMemory
  rw [if_neg (by exact not_or_intro (by omega) active)]

end Compiler.Proofs.IRGeneration.NativeSourceLoadStep
