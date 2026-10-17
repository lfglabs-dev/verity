import Compiler.Proofs.IRGeneration.NativeSourceDynamicTwoStores

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicThirdStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate756 : NativeSourceAbiWrite.code.extract' 757 758 = ⟨#[64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[757]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (757 < 2^64 && 758 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 757 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode756 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 756) =
    some (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 756 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 756).toNat = 756 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 757 758), 1)) = _
  rw [immediate756]
  decide


theorem decode758 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 758) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 758 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 758).toNat = 758 by decide, byte]
  decide

theorem decode759 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 759) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 759 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 759).toNat = 759 by decide, byte]
  decide

theorem decode760 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 760) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 760 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 760).toNat = 760 by decide, byte]
  decide

theorem immediate761 : NativeSourceAbiWrite.code.extract' 762 763 = ⟨#[64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[762]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (762 < 2^64 && 763 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 762 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode761 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 761) =
    some (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 761 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 761).toNat = 761 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 762 763), 1)) = _
  rw [immediate761]
  decide


theorem decode763 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 763) = some (.DUP6, none) := by
  have byte : NativeSourceAbiWrite.code.get? 763 = some 133 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 763).toNat = 763 by decide, byte]
  decide

theorem decode764 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 764) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 764 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 764).toNat = 764 by decide, byte]
  decide

theorem decode765 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 765) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 765 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 765).toNat = 765 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC
    (UInt256.ofNat 64 :: a :: b :: c :: d :: e :: f :: tail) 2

def s2 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre a b c d e f tail)).replaceStackAndIncrPC
    (a :: UInt256.ofNat 64 :: a :: b :: c :: d :: e :: f :: tail)

def s3 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre a b c d e f tail)).replaceStackAndIncrPC
    ((a + UInt256.ofNat 64) :: a :: b :: c :: d :: e :: f :: tail)

def s4 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoadStep.loaded cost (s3 cost pre a b c d e f tail) (a + UInt256.ofNat 64) (a :: b :: c :: d :: e :: f :: tail)

def s5 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre a b c d e f tail)).replaceStackAndIncrPC
    (UInt256.ofNat 64 :: ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + UInt256.ofNat 64)) :: a :: b :: c :: d :: e :: f :: tail) 2

def s6 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s5 cost pre a b c d e f tail)).replaceStackAndIncrPC
    (d :: UInt256.ofNat 64 :: ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + UInt256.ofNat 64)) :: a :: b :: c :: d :: e :: f :: tail)

def s7 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s6 cost pre a b c d e f tail)).replaceStackAndIncrPC
    ((d + UInt256.ofNat 64) :: ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + UInt256.ofNat 64)) :: a :: b :: c :: d :: e :: f :: tail)

def s8 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  let charged := stepPre cost (s7 cost pre a b c d e f tail)
  ({ charged with toMachineState := (charged.toMachineState.mstore (d + UInt256.ofNat 64) ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + UInt256.ofNat 64))) } : EVM.State).replaceStackAndIncrPC
    (a :: b :: c :: d :: e :: f :: tail)

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c d e f tail) := by
  have atPC : pre.pc = UInt256.ofNat 756 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode756]; rfl
  rw [decoded]
  rw [NativeMidnightConstructor.step_PUSH1]
  simp only [stepPre, stack]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c d e f tail))) (s1 cost pre a b c d e f tail) = .ok (s2 cost pre a b c d e f tail) := by
  have atPC : (s1 cost pre a b c d e f tail).pc = UInt256.ofNat 758 := by
    change (pre.pc + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c d e f tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode758]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre cost (s1 cost pre a b c d e f tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c d e f tail))) (s2 cost pre a b c d e f tail) = .ok (s3 cost pre a b c d e f tail) := by
  have atPC : (s2 cost pre a b c d e f tail).pc = UInt256.ofNat 759 := by
    change ((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c d e f tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode759]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s2 cost pre a b c d e f tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c d e f tail))) (s3 cost pre a b c d e f tail) = .ok (s4 cost pre a b c d e f tail) := by
  have atPC : (s3 cost pre a b c d e f tail).pc = UInt256.ofNat 760 := by
    change (((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c d e f tail) = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode760]; rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost (s3 cost pre a b c d e f tail) (a + UInt256.ofNat 64) _ (by rfl)

theorem transition5 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre a b c d e f tail))) (s4 cost pre a b c d e f tail) = .ok (s5 cost pre a b c d e f tail) := by
  have atPC : (s4 cost pre a b c d e f tail).pc = UInt256.ofNat 761 := by
    change ((((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre a b c d e f tail) = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode761]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 64)

theorem transition6 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre a b c d e f tail))) (s5 cost pre a b c d e f tail) = .ok (s6 cost pre a b c d e f tail) := by
  have atPC : (s5 cost pre a b c d e f tail).pc = UInt256.ofNat 763 := by
    change (((((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre a b c d e f tail) = (.DUP6, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode763]; rfl
  rw [decoded]
  change EvmYul.dup 6 (stepPre cost (s5 cost pre a b c d e f tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition7 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre a b c d e f tail))) (s6 cost pre a b c d e f tail) = .ok (s7 cost pre a b c d e f tail) := by
  have atPC : (s6 cost pre a b c d e f tail).pc = UInt256.ofNat 764 := by
    change ((((((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre a b c d e f tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode764]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s6 cost pre a b c d e f tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition8 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s7 cost pre a b c d e f tail))) (s7 cost pre a b c d e f tail) = .ok (s8 cost pre a b c d e f tail) := by
  have atPC : (s7 cost pre a b c d e f tail).pc = UInt256.ofNat 765 := by
    change (((((((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre a b c d e f tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode765]; rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s7 cost pre a b c d e f tail) (a :: b :: c :: d :: e :: f :: tail) (d + UInt256.ofNat 64) _ (by rfl)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 756)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    run fuel cost 8 pre = .ok (s8 cost pre a b c d e f tail) := by
  rw [run, transition1 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :
    (s8 cost pre a b c d e f tail).memory =
      (pre.toMachineState.mstore (d + UInt256.ofNat 64) (pre.toMachineState.lookupMemory (a + UInt256.ofNat 64))).memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicThirdStore
