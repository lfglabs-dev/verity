import EvmYul.EVM.Proof.MemoryStep

/-! Exact native CODECOPY step equations. No canonical surrogate interpreter. -/
namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof

/-- Native CODECOPY dispatches to the actual shared-state copy primitive. -/
theorem step_CODECOPY (fuel gasCost : Nat) (pre : EVM.State) (rest : Stack UInt256)
    (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size)) :
    StepOk (fuel + 1) gasCost (.CODECOPY, none) pre
      (EVM.State.replaceStackAndIncrPC
        { stepPre gasCost pre with
          toSharedState := (stepPre gasCost pre).toSharedState.codeCopy dest source size } rest) := by
  show EvmYul.step (τ := .EVM) .CODECOPY none (stepPre gasCost pre) = _
  show EVM.ternaryCopyOp SharedState.codeCopy (stepPre gasCost pre) = _
  unfold EVM.ternaryCopyOp
  rw [show (stepPre gasCost pre).stack = pre.stack from rfl, popped]
  rfl

/-- Source bytes, offsets and destination memory in the native post-state. -/
theorem memory_step_CODECOPY (fuel gasCost : Nat) (pre post : EVM.State)
    (rest : Stack UInt256) (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size))
    (success : EVM.step (fuel + 1) gasCost (some (.CODECOPY, none)) pre = .ok post) :
    post.memory = pre.executionEnv.code.write source.toNat pre.memory dest.toNat size.toNat := by
  have exactStep := step_CODECOPY fuel gasCost pre rest dest source size popped
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  rfl

/-- CODECOPY charges the native memory extent, leaving this explicit for the
subsequent RETURN memory-expansion/gas calculation. -/
theorem activeWords_step_CODECOPY (fuel gasCost : Nat) (pre post : EVM.State)
    (rest : Stack UInt256) (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size))
    (success : EVM.step (fuel + 1) gasCost (some (.CODECOPY, none)) pre = .ok post) :
    post.activeWords = UInt256.ofNat
      (MachineState.M pre.activeWords.toNat dest.toNat size.toNat) := by
  have exactStep := step_CODECOPY fuel gasCost pre rest dest source size popped
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
