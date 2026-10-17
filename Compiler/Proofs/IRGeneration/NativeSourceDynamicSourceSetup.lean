import Compiler.Proofs.IRGeneration.NativeSourceDynamicTransportReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicSourceSetup
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate490 : NativeSourceAbiWrite.code.extract' 491 492 = ⟨#[32]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[491]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (491 < 2^64 && 492 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 491 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode490 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 490) = some (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 490 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 490).toNat = 490 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 491 492), 1)) = _
  rw [immediate490]
  decide

theorem immediate495 : NativeSourceAbiWrite.code.extract' 496 497 = ⟨#[32]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[496]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (496 < 2^64 && 497 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 496 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode495 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 495) = some (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 495 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 495).toNat = 495 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 496 497), 1)) = _
  rw [immediate495]
  decide

theorem decode489 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 489) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 489 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 489).toNat = 489 by decide, byte]
  decide

theorem decode492 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 492) = some (.DUP12, none) := by
  have byte : NativeSourceAbiWrite.code.get? 492 = some 139 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 492).toNat = 492 by decide, byte]
  decide

theorem decode493 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 493) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 493 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 493).toNat = 493 by decide, byte]
  decide

theorem decode494 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 494) = some (.SWAP9, none) := by
  have byte : NativeSourceAbiWrite.code.get? 494 = some 152 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 494).toNat = 494 by decide, byte]
  decide

theorem decode497 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 497) = some (.DUP11, none) := by
  have byte : NativeSourceAbiWrite.code.get? 497 = some 138 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 497).toNat = 497 by decide, byte]
  decide

theorem decode498 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 498) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 498 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 498).toNat = 498 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC (x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s2 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (UInt256.ofNat 32 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 2
def s3 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (x9 :: UInt256.ofNat 32 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s4 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC ((x9 + UInt256.ofNat 32) :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s5 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (x7 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: (x9 + UInt256.ofNat 32) :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s6 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (UInt256.ofNat 32 :: x7 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: (x9 + UInt256.ofNat 32) :: x8 :: x9 :: x10 :: x11 :: tail) 2
def s7 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC ((x9 + UInt256.ofNat 32) :: UInt256.ofNat 32 :: x7 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: (x9 + UInt256.ofNat 32) :: x8 :: x9 :: x10 :: x11 :: tail) 1
def s8 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) :=
  let charged := stepPre cost (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)
  ({ charged with toMachineState := charged.toMachineState.mstore (x9 + UInt256.ofNat 32) (UInt256.ofNat 32) } : EVM.State).replaceStackAndIncrPC (x7 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: (x9 + UInt256.ofNat 32) :: x8 :: x9 :: x10 :: x11 :: tail)

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : pre.pc = UInt256.ofNat 489 := by
    exact pc
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode489]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail from stack]
  rfl

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 490 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode490]; rfl
  rw [decoded]
  change Except.ok ((stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (UInt256.ofNat 32 :: (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).stack) 2) = _
  rfl

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 492 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.DUP12, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode492]; rfl
  rw [decoded]
  change EvmYul.dup 12 (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 493 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode493]; rfl
  rw [decoded]
  rfl

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 494 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.SWAP9, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode494]; rfl
  rw [decoded]
  change EvmYul.swap 9 (stepPre cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 495 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode495]; rfl
  rw [decoded]
  change Except.ok ((stepPre cost (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)).replaceStackAndIncrPC (UInt256.ofNat 32 :: (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).stack) 2) = _
  rfl

theorem transition7 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 497 := by
    change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.DUP11, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode497]; rfl
  rw [decoded]
  change EvmYul.dup 11 (stepPre cost (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition8 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail))) (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = .ok (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
  have atPC : (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc = UInt256.ofNat 498 := by
    change (((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).pc).getD _ = _
    rw [code, atPC, decode498]; rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) (x7 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: (x9 + UInt256.ofNat 32) :: x8 :: x9 :: x10 :: x11 :: tail) (x9 + UInt256.ofNat 32) (UInt256.ofNat 32) (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: tail) : run fuel cost 8 pre = .ok (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail) := by
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
  rw [run, transition7 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem source_relation (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (tail : Stack UInt256) : (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).stack[9]? = ((s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 tail).stack[11]?).map (fun base => base + UInt256.ofNat 32) := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicSourceSetup
