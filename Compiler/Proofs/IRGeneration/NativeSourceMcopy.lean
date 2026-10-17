import EvmYul.EVM.Proof.MemoryStep

/-! Exact native MCOPY step equations. No canonical surrogate interpreter. -/
namespace Compiler.Proofs.IRGeneration.NativeSourceMcopy
open EvmYul EVM.Proof

/-- Native MCOPY dispatches to the actual shared-state copy primitive. -/
theorem step_MCOPY (fuel gasCost : Nat) (pre : EVM.State) (rest : Stack UInt256)
    (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size)) :
    StepOk (fuel + 1) gasCost (.MCOPY, none) pre
      (EVM.State.replaceStackAndIncrPC
        { stepPre gasCost pre with
          toMachineState := (stepPre gasCost pre).toMachineState.mcopy dest source size } rest) := by
  show EvmYul.step (τ := .EVM) .MCOPY none (stepPre gasCost pre) = _
  show EVM.ternaryMachineStateOp MachineState.mcopy (stepPre gasCost pre) = _
  unfold EVM.ternaryMachineStateOp
  rw [show (stepPre gasCost pre).stack = pre.stack from rfl, popped]
  rfl

/-- Snapshot source bytes, including overlapping regions, and destination memory in the native post-state. -/
theorem memory_step_MCOPY (fuel gasCost : Nat) (pre post : EVM.State)
    (rest : Stack UInt256) (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size))
    (success : EVM.step (fuel + 1) gasCost (some (.MCOPY, none)) pre = .ok post) :
    post.memory = pre.memory.write source.toNat pre.memory dest.toNat size.toNat := by
  have exactStep := step_MCOPY fuel gasCost pre rest dest source size popped
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  rfl

/-- MCOPY charges the native memory extent, leaving this explicit for the
subsequent RETURN memory-expansion/gas calculation. -/
theorem activeWords_step_MCOPY (fuel gasCost : Nat) (pre post : EVM.State)
    (rest : Stack UInt256) (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size))
    (success : EVM.step (fuel + 1) gasCost (some (.MCOPY, none)) pre = .ok post) :
    post.activeWords = UInt256.ofNat
      (MachineState.M pre.activeWords.toNat (max dest.toNat source.toNat) size.toNat) := by
  have exactStep := step_MCOPY fuel gasCost pre rest dest source size popped
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceMcopy
