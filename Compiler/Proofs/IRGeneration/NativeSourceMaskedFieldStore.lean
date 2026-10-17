import Compiler.Proofs.IRGeneration.NativeSourceFieldLoad

namespace Compiler.Proofs.IRGeneration.NativeSourceMaskedFieldStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate605 : NativeSourceAbiWrite.code.extract' 606 608 = ⟨#[1, 0]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[606]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[607]? = some 0 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (606 < 2^64 && 608 < 2^64) = true by decide, if_true,
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
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 606 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 607 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode605 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 605) =
    some (.Push .PUSH2, some (UInt256.ofNat 256, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 605 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 605).toNat = 605 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 606 608), 2)) = _
  rw [immediate605]
  decide


def s1 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 256 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) 3

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 605)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c d e f g h i tail) := by
  have atPC : pre.pc = UInt256.ofNat 605 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 256, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode605]
    rfl
  rw [decoded]
  change Except.ok ((stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 256 :: pre.stack) 3) = _
  rw [stack]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre a b c d e f g h i tail)).replaceStackAndIncrPC (e :: UInt256.ofNat 256 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: tail)

theorem decode608 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 608) = some (.DUP6, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 608).toNat = some 133 := by
    have index : (UInt256.ofNat 608).toNat = 608 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 605)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c d e f g h i tail))) (s1 cost pre a b c d e f g h i tail) = .ok (s2 cost pre a b c d e f g h i tail) := by
  have atPC : (s1 cost pre a b c d e f g h i tail).pc = UInt256.ofNat 608 := by
    change (pre.pc + UInt256.ofNat 3) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c d e f g h i tail) = (.DUP6, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c d e f g h i tail).pc).getD _ = _
    rw [code, atPC, decode608]
    rfl
  rw [decoded]
  change EvmYul.dup 6 (stepPre cost (s1 cost pre a b c d e f g h i tail)) = _
  unfold EvmYul.dup
  rfl

def s3 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre a b c d e f g h i tail)).replaceStackAndIncrPC ((e + UInt256.ofNat 256) :: a :: b :: c :: d :: e :: f :: g :: h :: i :: tail)

theorem decode609 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 609) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 609).toNat = some 1 := by
    have index : (UInt256.ofNat 609).toNat = 609 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 605)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c d e f g h i tail))) (s2 cost pre a b c d e f g h i tail) = .ok (s3 cost pre a b c d e f g h i tail) := by
  have atPC : (s2 cost pre a b c d e f g h i tail).pc = UInt256.ofNat 609 := by
    change ((pre.pc + UInt256.ofNat 3) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c d e f g h i tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c d e f g h i tail).pc).getD _ = _
    rw [code, atPC, decode609]
    rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s2 cost pre a b c d e f g h i tail)) = _
  unfold EVM.execBinOp
  rfl

def s4 (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256) : EVM.State :=
  EVM.State.replaceStackAndIncrPC { stepPre cost (s3 cost pre a b c d e f g h i tail) with toMachineState := (stepPre cost (s3 cost pre a b c d e f g h i tail)).toMachineState.mstore (e + UInt256.ofNat 256) a } (b :: c :: d :: e :: f :: g :: h :: i :: tail)

theorem decode610 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 610) = some (.MSTORE, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 610).toNat = some 82 := by
    have index : (UInt256.ofNat 610).toNat = 610 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 605)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c d e f g h i tail))) (s3 cost pre a b c d e f g h i tail) = .ok (s4 cost pre a b c d e f g h i tail) := by
  have atPC : (s3 cost pre a b c d e f g h i tail).pc = UInt256.ofNat 610 := by
    change (((pre.pc + UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c d e f g h i tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c d e f g h i tail).pc).getD _ = _
    rw [code, atPC, decode610]
    rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s3 cost pre a b c d e f g h i tail) _ _ a (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 605)
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

end Compiler.Proofs.IRGeneration.NativeSourceMaskedFieldStore
