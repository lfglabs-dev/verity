import Compiler.Proofs.IRGeneration.NativeSourcePackingCopies

namespace Compiler.Proofs.IRGeneration.NativeSourcePackingSize
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC ((a + b) :: c :: d :: e :: f :: g :: h :: tail)

theorem decode663 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 663) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 663).toNat = some 1 := by
    have index : (UInt256.ofNat 663).toNat = 663 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 663)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c d e f g h tail) := by
  have atPC : pre.pc = UInt256.ofNat 663 := by
    exact pc
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode663]
    rfl
  rw [decoded]
  have shape : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail := stack
  change EVM.execBinOp UInt256.add (stepPre cost pre) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre a b c d e f g h tail)).replaceStackAndIncrPC (((a + b) + c) :: d :: e :: f :: g :: h :: tail)

theorem decode664 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 664) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 664).toNat = some 1 := by
    have index : (UInt256.ofNat 664).toNat = 664 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 663)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c d e f g h tail))) (s1 cost pre a b c d e f g h tail) = .ok (s2 cost pre a b c d e f g h tail) := by
  have atPC : (s1 cost pre a b c d e f g h tail).pc = UInt256.ofNat 664 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c d e f g h tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, decode664]
    rfl
  rw [decoded]
  have shape : (s1 cost pre a b c d e f g h tail).stack = (a + b) :: c :: d :: e :: f :: g :: h :: tail := rfl
  change EVM.execBinOp UInt256.add (stepPre cost (s1 cost pre a b c d e f g h tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s1 cost pre a b c d e f g h tail)).stack = (s1 cost pre a b c d e f g h tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre a b c d e f g h tail)).replaceStackAndIncrPC (h :: ((a + b) + c) :: d :: e :: f :: g :: h :: tail)

theorem decode665 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 665) = some (.DUP6, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 665).toNat = some 133 := by
    have index : (UInt256.ofNat 665).toNat = 665 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 663)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c d e f g h tail))) (s2 cost pre a b c d e f g h tail) = .ok (s3 cost pre a b c d e f g h tail) := by
  have atPC : (s2 cost pre a b c d e f g h tail).pc = UInt256.ofNat 665 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c d e f g h tail) = (.DUP6, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, decode665]
    rfl
  rw [decoded]
  have shape : (s2 cost pre a b c d e f g h tail).stack = ((a + b) + c) :: d :: e :: f :: g :: h :: tail := rfl
  change EvmYul.dup 6 (stepPre cost (s2 cost pre a b c d e f g h tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s2 cost pre a b c d e f g h tail)).stack = (s2 cost pre a b c d e f g h tail).stack from rfl, shape]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre a b c d e f g h tail)).replaceStackAndIncrPC (((a + b) + c) :: h :: ((a + b) + c) :: d :: e :: f :: g :: h :: tail)

theorem decode666 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 666) = some (.DUP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 666).toNat = some 129 := by
    have index : (UInt256.ofNat 666).toNat = 666 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 663)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c d e f g h tail))) (s3 cost pre a b c d e f g h tail) = .ok (s4 cost pre a b c d e f g h tail) := by
  have atPC : (s3 cost pre a b c d e f g h tail).pc = UInt256.ofNat 666 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c d e f g h tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, decode666]
    rfl
  rw [decoded]
  have shape : (s3 cost pre a b c d e f g h tail).stack = h :: ((a + b) + c) :: d :: e :: f :: g :: h :: tail := rfl
  change EvmYul.dup 2 (stepPre cost (s3 cost pre a b c d e f g h tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s3 cost pre a b c d e f g h tail)).stack = (s3 cost pre a b c d e f g h tail).stack from rfl, shape]
  rfl

def s5 (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  EVM.State.replaceStackAndIncrPC
    { stepPre cost (s4 cost pre a b c d e f g h tail) with
      toMachineState := (stepPre cost (s4 cost pre a b c d e f g h tail)).toMachineState.mstore ((a + b) + c) h }
    (((a + b) + c) :: d :: e :: f :: g :: h :: tail)

theorem decode667 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 667) = some (.MSTORE, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 667).toNat = some 82 := by
    have index : (UInt256.ofNat 667).toNat = 667 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 663)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre a b c d e f g h tail))) (s4 cost pre a b c d e f g h tail) = .ok (s5 cost pre a b c d e f g h tail) := by
  have atPC : (s4 cost pre a b c d e f g h tail).pc = UInt256.ofNat 667 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre a b c d e f g h tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, decode667]
    rfl
  rw [decoded]
  exact step_MSTORE fuel cost _ _ _ h (by rfl)

def s6 (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s5 cost pre a b c d e f g h tail)).replaceStackAndIncrPC ((((a + b) + c) - d) :: e :: f :: g :: h :: tail)

theorem decode668 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 668) = some (.SUB, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 668).toNat = some 3 := by
    have index : (UInt256.ofNat 668).toNat = 668 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 663)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre a b c d e f g h tail))) (s5 cost pre a b c d e f g h tail) = .ok (s6 cost pre a b c d e f g h tail) := by
  have atPC : (s5 cost pre a b c d e f g h tail).pc = UInt256.ofNat 668 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre a b c d e f g h tail) = (.SUB, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, decode668]
    rfl
  rw [decoded]
  have shape : (s5 cost pre a b c d e f g h tail).stack = ((a + b) + c) :: d :: e :: f :: g :: h :: tail := rfl
  change EVM.execBinOp UInt256.sub (stepPre cost (s5 cost pre a b c d e f g h tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s5 cost pre a b c d e f g h tail)).stack = (s5 cost pre a b c d e f g h tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 663)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 6 pre = .ok (s6 cost pre a b c d e f g h tail) := by
  rw [run, transition1 fuel cost pre a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre a b c d e f g h tail code pc stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourcePackingSize
