import Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetMaskedPair

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetSuffix
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate527 : NativeSourceAbiWrite.code.extract' 528 530 = ⟨#[1, 0]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[528]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[529]? = some 0 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (528 < 2^64 && 530 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 528 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 529 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode527 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 527) = some (.Push .PUSH2, some (UInt256.ofNat 256, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 527 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 527).toNat = 527 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 528 530), 2)) = _
  rw [immediate527]
  decide

theorem immediate530 : NativeSourceAbiWrite.code.extract' 531 532 = ⟨#[160]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[531]? = some 160 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (531 < 2^64 && 532 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 531 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode530 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 530) = some (.Push .PUSH1, some (UInt256.ofNat 160, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 530 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 530).toNat = 530 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 531 532), 1)) = _
  rw [immediate530]
  decide

theorem decode525 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 525) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 525 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 525).toNat = 525 by decide, byte]
  decide

theorem decode526 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 526) = some (.SWAP9, none) := by
  have byte : NativeSourceAbiWrite.code.get? 526 = some 152 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 526).toNat = 526 by decide, byte]
  decide

theorem decode532 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 532) = some (.DUP10, none) := by
  have byte : NativeSourceAbiWrite.code.get? 532 = some 137 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 532).toNat = 532 by decide, byte]
  decide

theorem decode533 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 533) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 533 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 533).toNat = 533 by decide, byte]
  decide

theorem decode534 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 534) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 534 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 534).toNat = 534 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) := NativeSourceLoadStep.loaded cost pre x0 (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail)
def s2 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)).replaceStackAndIncrPC (x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail) 1
def s3 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)).replaceStackAndIncrPC (UInt256.ofNat 256 :: x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail) 3
def s4 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)).replaceStackAndIncrPC (UInt256.ofNat 160 :: UInt256.ofNat 256 :: x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail) 2
def s5 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)).replaceStackAndIncrPC (x7 :: UInt256.ofNat 160 :: UInt256.ofNat 256 :: x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail) 1
def s6 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)).replaceStackAndIncrPC ((x7 + UInt256.ofNat 160) :: UInt256.ofNat 256 :: x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail) 1
def s7 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  let charged := stepPre cost (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)
  ({ charged with toMachineState := charged.toMachineState.mstore (x7 + UInt256.ofNat 160) (UInt256.ofNat 256) } : EVM.State).replaceStackAndIncrPC (x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail)

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : pre.pc = UInt256.ofNat 525 := by
    exact pc
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode525]; rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost pre x0 _ stack

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 526 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.SWAP9, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode526]; rfl
  rw [decoded]
  change EvmYul.swap 9 (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 527 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.Push .PUSH2, some (UInt256.ofNat 256, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode527]; rfl
  rw [decoded]
  rfl

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 530 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.Push .PUSH1, some (UInt256.ofNat 160, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode530]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 160)

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 532 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.DUP10, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode532]; rfl
  rw [decoded]
  change EvmYul.dup 10 (stepPre cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 533 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode533]; rfl
  rw [decoded]
  rfl

theorem transition7 (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 534 := by
    change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode534]; rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) (x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail) (x7 + UInt256.ofNat 160) _ (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 525)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) : run fuel cost 7 pre = .ok (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  rw [run, transition1 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem output_stack (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) : (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).stack = x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: (pre.toMachineState.lookupMemory x0) :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetSuffix
