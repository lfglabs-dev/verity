import Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetMaskedFirst

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetMaskedSecond
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate520 : NativeSourceAbiWrite.code.extract' 521 522 = ⟨#[128]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[521]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (521 < 2^64 && 522 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 521 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode520 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 520) = some (.Push .PUSH1, some (UInt256.ofNat 128, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 520 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 520).toNat = 520 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 521 522), 1)) = _
  rw [immediate520]
  decide

theorem decode518 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 518) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 518 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 518).toNat = 518 by decide, byte]
  decide

theorem decode519 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 519) = some (.AND, none) := by
  have byte : NativeSourceAbiWrite.code.get? 519 = some 22 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 519).toNat = 519 by decide, byte]
  decide

theorem decode522 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 522) = some (.DUP10, none) := by
  have byte : NativeSourceAbiWrite.code.get? 522 = some 137 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 522).toNat = 522 by decide, byte]
  decide

theorem decode523 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 523) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 523 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 523).toNat = 523 by decide, byte]
  decide

theorem decode524 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 524) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 524 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 524).toNat = 524 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) := NativeSourceLoadStep.loaded cost pre x0 (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail)
def s2 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (((pre.toMachineState.lookupMemory x0).land x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s3 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (UInt256.ofNat 128 :: ((pre.toMachineState.lookupMemory x0).land x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 2
def s4 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (x9 :: UInt256.ofNat 128 :: ((pre.toMachineState.lookupMemory x0).land x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s5 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC ((x9 + UInt256.ofNat 128) :: ((pre.toMachineState.lookupMemory x0).land x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s6 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  let charged := stepPre cost (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)
  ({ charged with toMachineState := charged.toMachineState.mstore (x9 + UInt256.ofNat 128) ((pre.toMachineState.lookupMemory x0).land x1) } : EVM.State).replaceStackAndIncrPC (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail)

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 518)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : pre.pc = UInt256.ofNat 518 := by
    exact pc
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode518]; rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost pre x0 _ stack

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 518)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 519 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.AND, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode519]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.land (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 518)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 520 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.Push .PUSH1, some (UInt256.ofNat 128, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode520]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 128)

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 518)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 522 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.DUP10, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode522]; rfl
  rw [decoded]
  change EvmYul.dup 10 (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 518)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 523 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode523]; rfl
  rw [decoded]
  rfl

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 518)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 524 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode524]; rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) (x9 + UInt256.ofNat 128) _ (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 518)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) : run fuel cost 6 pre = .ok (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  rw [run, transition1 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) : (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).memory = (pre.toMachineState.mstore (x9 + UInt256.ofNat 128) ((pre.toMachineState.lookupMemory x0).land x1)).memory := by
  rfl

theorem target_register (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) : (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).stack[9]? = some x11 := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetMaskedSecond
