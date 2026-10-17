import Compiler.Proofs.IRGeneration.NativeSourceFieldLoad

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate592 : NativeSourceAbiWrite.code.extract' 593 594 = ⟨#[192]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[593]? = some 192 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (593 < 2^64 && 594 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 593 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)

theorem decode592 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 592) =
    some (.Push .PUSH1, some (UInt256.ofNat 192, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 592 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 592).toNat = 592 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 593 594), 1)) = _
  rw [immediate592]
  decide


def s1 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 192 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) 2

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 592)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c d e f g h i tail) := by
  have atPC : pre.pc = UInt256.ofNat 592 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 192, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode592]
    rfl
  rw [decoded]
  change Except.ok ((stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 192 :: pre.stack) 2) = _
  rw [stack]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre a b c d e f g h i tail)).replaceStackAndIncrPC (h :: UInt256.ofNat 192 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: tail)

theorem decode594 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 594) = some (.DUP9, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 594).toNat = some 136 := by
    have index : (UInt256.ofNat 594).toNat = 594 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 592)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c d e f g h i tail))) (s1 cost pre a b c d e f g h i tail) = .ok (s2 cost pre a b c d e f g h i tail) := by
  have atPC : (s1 cost pre a b c d e f g h i tail).pc = UInt256.ofNat 594 := by
    change (pre.pc + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c d e f g h i tail) = (.DUP9, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c d e f g h i tail).pc).getD _ = _
    rw [code, atPC, decode594]
    rfl
  rw [decoded]
  change EvmYul.dup 9 (stepPre cost (s1 cost pre a b c d e f g h i tail)) = _
  unfold EvmYul.dup
  rfl

def s3 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre a b c d e f g h i tail)).replaceStackAndIncrPC ((h + UInt256.ofNat 192) :: a :: b :: c :: d :: e :: f :: g :: h :: i :: tail)

theorem decode595 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 595) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 595).toNat = some 1 := by
    have index : (UInt256.ofNat 595).toNat = 595 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 592)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c d e f g h i tail))) (s2 cost pre a b c d e f g h i tail) = .ok (s3 cost pre a b c d e f g h i tail) := by
  have atPC : (s2 cost pre a b c d e f g h i tail).pc = UInt256.ofNat 595 := by
    change ((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c d e f g h i tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c d e f g h i tail).pc).getD _ = _
    rw [code, atPC, decode595]
    rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s2 cost pre a b c d e f g h i tail)) = _
  unfold EVM.execBinOp
  rfl

def s4 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  EVM.State.replaceStackAndIncrPC { stepPre cost (s3 cost pre a b c d e f g h i tail) with toMachineState := (stepPre cost (s3 cost pre a b c d e f g h i tail)).toMachineState.mstore (h + UInt256.ofNat 192) a } (b :: c :: d :: e :: f :: g :: h :: i :: tail)

theorem decode596 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 596) = some (.MSTORE, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 596).toNat = some 82 := by
    have index : (UInt256.ofNat 596).toNat = 596 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 592)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c d e f g h i tail))) (s3 cost pre a b c d e f g h i tail) = .ok (s4 cost pre a b c d e f g h i tail) := by
  have atPC : (s3 cost pre a b c d e f g h i tail).pc = UInt256.ofNat 596 := by
    change (((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c d e f g h i tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c d e f g h i tail).pc).getD _ = _
    rw [code, atPC, decode596]
    rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s3 cost pre a b c d e f g h i tail) _ _ a (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 592)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    run fuel cost 4 pre = .ok (s4 cost pre a b c d e f g h i tail) := by
  rw [run, transition1 fuel cost pre a b c d e f g h i tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre a b c d e f g h i tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre a b c d e f g h i tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre a b c d e f g h i tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceFieldStore
