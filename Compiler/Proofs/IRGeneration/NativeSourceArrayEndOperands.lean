import Compiler.Proofs.IRGeneration.NativeSourceArrayEndDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayEndOperands
open EvmYul EVM EVM.Proof

theorem step304 (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 304)
    (stack : pre.stack = tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 7 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 7, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayEndDecodes.decode304]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
  rw [stack]

theorem step306 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 306)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((b <<< a) :: tail) 1) := by
  have decoded : decodeAt pre = (.SHL, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayEndDecodes.decode306]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .SHL none (stepPre 3 pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem step307 (fuel : Nat) (pre : EVM.State) (a b c d : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 307)
    (stack : pre.stack = a :: b :: c :: d :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (d :: a :: b :: c :: d :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP4, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayEndDecodes.decode307]; rfl
  rw [decoded]
  change EvmYul.dup 4 (stepPre 3 pre) = _
  unfold EvmYul.dup
  simp only [stepPre, stack]
  rfl

theorem step308 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 308)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayEndDecodes.decode308]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre 3 pre) = _
  unfold EVM.execBinOp
  simp only [stepPre, stack]
  rfl

theorem step309 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 309)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayEndDecodes.decode309]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre 3 pre) = _
  unfold EVM.execBinOp
  simp only [stepPre, stack]
  rfl

theorem step310 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 310)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayEndDecodes.decode310]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre 3 pre) = _
  unfold EVM.execBinOp
  simp only [stepPre, stack]
  rfl

theorem step311 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 311)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (b :: a :: tail) 1) := by
  have decoded : decodeAt pre = (.SWAP1, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayEndDecodes.decode311]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre 3 pre) = _
  unfold EvmYul.swap
  simp only [stepPre, stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayEndOperands
