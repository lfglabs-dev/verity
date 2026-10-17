import Compiler.Proofs.IRGeneration.NativeSourceRoundingEntry

namespace Compiler.Proofs.IRGeneration.NativeSourceRoundingStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (size :: mask :: size :: a :: b :: c :: tail)

theorem decode672 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 672) = some (.DUP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 672).toNat = some 129 := by
    have index : (UInt256.ofNat 672).toNat = 672 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 672)
    (stack : pre.stack = mask :: size :: a :: b :: c :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre mask size a b c tail) := by
  have atPC : pre.pc = UInt256.ofNat 672 := by
    exact pc
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode672]
    rfl
  rw [decoded]
  have shape : pre.stack = mask :: size :: a :: b :: c :: tail := stack
  change EvmYul.dup 2 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre mask size a b c tail)).replaceStackAndIncrPC ((size + mask) :: size :: a :: b :: c :: tail)

theorem decode673 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 673) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 673).toNat = some 1 := by
    have index : (UInt256.ofNat 673).toNat = 673 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 672)
    (_stack : pre.stack = mask :: size :: a :: b :: c :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre mask size a b c tail))) (s1 cost pre mask size a b c tail) = .ok (s2 cost pre mask size a b c tail) := by
  have atPC : (s1 cost pre mask size a b c tail).pc = UInt256.ofNat 673 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre mask size a b c tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre mask size a b c tail).pc).getD _ = _
    rw [code, atPC, decode673]
    rfl
  rw [decoded]
  have shape : (s1 cost pre mask size a b c tail).stack = size :: mask :: size :: a :: b :: c :: tail := rfl
  change EVM.execBinOp UInt256.add (stepPre cost (s1 cost pre mask size a b c tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s1 cost pre mask size a b c tail)).stack = (s1 cost pre mask size a b c tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre mask size a b c tail)).replaceStackAndIncrPC (b :: (size + mask) :: size :: a :: b :: c :: tail)

theorem decode674 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 674) = some (.DUP4, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 674).toNat = some 131 := by
    have index : (UInt256.ofNat 674).toNat = 674 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 672)
    (_stack : pre.stack = mask :: size :: a :: b :: c :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre mask size a b c tail))) (s2 cost pre mask size a b c tail) = .ok (s3 cost pre mask size a b c tail) := by
  have atPC : (s2 cost pre mask size a b c tail).pc = UInt256.ofNat 674 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre mask size a b c tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre mask size a b c tail).pc).getD _ = _
    rw [code, atPC, decode674]
    rfl
  rw [decoded]
  have shape : (s2 cost pre mask size a b c tail).stack = (size + mask) :: size :: a :: b :: c :: tail := rfl
  change EvmYul.dup 4 (stepPre cost (s2 cost pre mask size a b c tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s2 cost pre mask size a b c tail)).stack = (s2 cost pre mask size a b c tail).stack from rfl, shape]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256) : EVM.State :=
  EVM.State.replaceStackAndIncrPC
    { stepPre cost (s3 cost pre mask size a b c tail) with
      toMachineState := (stepPre cost (s3 cost pre mask size a b c tail)).toMachineState.mstore b (size + mask) }
    (size :: a :: b :: c :: tail)

theorem decode675 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 675) = some (.MSTORE, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 675).toNat = some 82 := by
    have index : (UInt256.ofNat 675).toNat = 675 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 672)
    (_stack : pre.stack = mask :: size :: a :: b :: c :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre mask size a b c tail))) (s3 cost pre mask size a b c tail) = .ok (s4 cost pre mask size a b c tail) := by
  have atPC : (s3 cost pre mask size a b c tail).pc = UInt256.ofNat 675 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre mask size a b c tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre mask size a b c tail).pc).getD _ = _
    rw [code, atPC, decode675]
    rfl
  rw [decoded]
  exact step_MSTORE fuel cost _ _ b (size + mask) (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 672)
    (stack : pre.stack = mask :: size :: a :: b :: c :: tail) :
    run fuel cost 4 pre = .ok (s4 cost pre mask size a b c tail) := by
  rw [run, transition1 fuel cost pre mask size a b c tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre mask size a b c tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre mask size a b c tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre mask size a b c tail code pc stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceRoundingStore
