import EvmYul.EVM.Proof.Execution

/-! Bounded native primitive equations for the Midnight header's stack.
These equations retain exact native gas subtraction in stepPre. -/
namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof

/-- PUSH1 uses the decoder's real one-byte immediate. -/
theorem step_PUSH1 (fuel gasCost : Nat) (pre : EVM.State) (word : UInt256) :
    StepOk (fuel + 1) gasCost (.Push .PUSH1, some (word, 1)) pre
      ((stepPre gasCost pre).replaceStackAndIncrPC (word :: pre.stack) 2) := by
  rfl

/-- CODESIZE uses the complete code, including the runtime payload. -/
theorem step_CODESIZE (fuel gasCost : Nat) (pre : EVM.State) :
    StepOk (fuel + 1) gasCost (.CODESIZE, none) pre
      ((stepPre gasCost pre).replaceStackAndIncrPC
        (UInt256.ofNat pre.executionEnv.code.size :: pre.stack)) := by
  rfl

/-- Native SUB operand order is top minus second; no arithmetic approximation. -/
theorem step_SUB (fuel gasCost : Nat) (pre : EVM.State) (rest : Stack UInt256)
    (left right : UInt256) (popped : pre.stack.pop2 = some (rest, left, right)) :
    StepOk (fuel + 1) gasCost (.SUB, none) pre
      ((stepPre gasCost pre).replaceStackAndIncrPC ((left - right) :: rest)) := by
  show EVM.execBinOp UInt256.sub (stepPre gasCost pre) = _
  unfold EVM.execBinOp
  rw [show (stepPre gasCost pre).stack = pre.stack from rfl, popped]
  rfl

/-- DUP1 reproduces the actual top word. -/
theorem step_DUP1 (fuel gasCost : Nat) (pre : EVM.State) (word : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = word :: rest) :
    StepOk (fuel + 1) gasCost (.DUP1, none) pre
      ((stepPre gasCost pre).replaceStackAndIncrPC (word :: word :: rest)) := by
  change EvmYul.dup 1 (stepPre gasCost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre gasCost pre).stack = pre.stack from rfl, stack]
  rfl

/-- PUSH0 publishes zero and advances one byte. -/
theorem step_PUSH0 (fuel gasCost : Nat) (pre : EVM.State) :
    StepOk (fuel + 1) gasCost (.Push .PUSH0, none) pre
      ((stepPre gasCost pre).replaceStackAndIncrPC (UInt256.ofNat 0 :: pre.stack)) := by
  rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
