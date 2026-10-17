import Compiler.Proofs.IRGeneration.NativeSourceArrayAllocationDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCallOperands
open EvmYul EVM EVM.Proof

theorem step277 (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 277)
    (stack : pre.stack = tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 292 :: tail) 3) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 292, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode277]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
  rw [stack]

theorem step280 (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 280)
    (stack : pre.stack = tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 32 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode280]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
  rw [stack]

theorem step282 (fuel : Nat) (pre : EVM.State) (a b c d : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 282)
    (stack : pre.stack = a :: b :: c :: d :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (d :: a :: b :: c :: d :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP4, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode282]; rfl
  rw [decoded]
  change EvmYul.dup 4 (stepPre 3 pre) = _
  unfold EvmYul.dup
  simp only [stepPre, stack]
  rfl

theorem step283 (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 283)
    (stack : pre.stack = tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 5 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 5, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode283]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
  rw [stack]

theorem step285 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 285)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((b <<< a) :: tail) 1) := by
  have decoded : decodeAt pre = (.SHL, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode285]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .SHL none (stepPre 3 pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem step286 (fuel : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 286)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode286]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ADD none (stepPre 3 pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem step287 (fuel : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 287)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (f :: a :: b :: c :: d :: e :: f :: tail) 1) := by
  have decoded : decodeAt pre = (.DUP6, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode287]; rfl
  rw [decoded]
  change EvmYul.dup 6 (stepPre 3 pre) = _
  unfold EvmYul.dup
  simp only [stepPre, stack]
  rfl

theorem step288 (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 288)
    (stack : pre.stack = tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 910 :: tail) 3) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 910, 2)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode288]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
  rw [stack]

end Compiler.Proofs.IRGeneration.NativeSourceArrayCallOperands
