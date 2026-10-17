import Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupOperands
open EvmYul EVM EVM.Proof

theorem step296 (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 296)
    (stack : pre.stack = tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 32 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode296]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
  rw [stack]

theorem step298 (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 298)
    (stack : pre.stack = tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 4 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 4, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode298]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
  rw [stack]

theorem step300 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 300)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (b :: a :: b :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode300]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre 3 pre) = _
  unfold EvmYul.dup
  simp only [stepPre, stack]
  rfl

theorem step301 (fuel : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 301)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (g :: a :: b :: c :: d :: e :: f :: g :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP7, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode301]; rfl
  rw [decoded]
  change EvmYul.dup 7 (stepPre 3 pre) = _
  unfold EvmYul.dup
  simp only [stepPre, stack]
  rfl

theorem step302 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 302)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode302]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre 3 pre) = _
  unfold EVM.execBinOp
  simp only [stepPre, stack]
  rfl

theorem step303 (fuel : Nat) (pre : EVM.State) (a b c d e : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 303)
    (stack : pre.stack = a :: b :: c :: d :: e :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (e :: b :: c :: d :: a :: tail) 1) := by
  have decoded : decodeAt pre = (.SWAP4, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayLoopSetupDecodes.decode303]; rfl
  rw [decoded]
  change EvmYul.swap 4 (stepPre 3 pre) = _
  unfold EvmYul.swap
  simp only [stepPre, stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupOperands
