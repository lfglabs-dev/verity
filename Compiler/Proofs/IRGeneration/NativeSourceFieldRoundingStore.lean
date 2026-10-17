import Compiler.Proofs.IRGeneration.NativeSourceFieldRoundingEntry

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldRoundingStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (size :: mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail)

theorem decode623 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 623) = some (.DUP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 623).toNat = some 129 := by
    have index : (UInt256.ofNat 623).toNat = 623 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 623)
    (stack : pre.stack = mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre mask size a b c d e f g tail) := by
  have atPC : pre.pc = UInt256.ofNat 623 := by
    exact pc
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode623]
    rfl
  rw [decoded]
  have shape : pre.stack = mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail := stack
  change EvmYul.dup 2 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre mask size a b c d e f g tail)).replaceStackAndIncrPC ((size + mask) :: size :: a :: b :: c :: d :: e :: f :: g :: tail)

theorem decode624 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 624) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 624).toNat = some 1 := by
    have index : (UInt256.ofNat 624).toNat = 624 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 623)
    (_stack : pre.stack = mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre mask size a b c d e f g tail))) (s1 cost pre mask size a b c d e f g tail) = .ok (s2 cost pre mask size a b c d e f g tail) := by
  have atPC : (s1 cost pre mask size a b c d e f g tail).pc = UInt256.ofNat 624 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre mask size a b c d e f g tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre mask size a b c d e f g tail).pc).getD _ = _
    rw [code, atPC, decode624]
    rfl
  rw [decoded]
  have shape : (s1 cost pre mask size a b c d e f g tail).stack = size :: mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail := rfl
  change EVM.execBinOp UInt256.add (stepPre cost (s1 cost pre mask size a b c d e f g tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s1 cost pre mask size a b c d e f g tail)).stack = (s1 cost pre mask size a b c d e f g tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre mask size a b c d e f g tail)).replaceStackAndIncrPC (f :: (size + mask) :: size :: a :: b :: c :: d :: e :: f :: g :: tail)

theorem decode625 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 625) = some (.DUP8, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 625).toNat = some 135 := by
    have index : (UInt256.ofNat 625).toNat = 625 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 623)
    (_stack : pre.stack = mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre mask size a b c d e f g tail))) (s2 cost pre mask size a b c d e f g tail) = .ok (s3 cost pre mask size a b c d e f g tail) := by
  have atPC : (s2 cost pre mask size a b c d e f g tail).pc = UInt256.ofNat 625 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre mask size a b c d e f g tail) = (.DUP8, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre mask size a b c d e f g tail).pc).getD _ = _
    rw [code, atPC, decode625]
    rfl
  rw [decoded]
  have shape : (s2 cost pre mask size a b c d e f g tail).stack = (size + mask) :: size :: a :: b :: c :: d :: e :: f :: g :: tail := rfl
  change EvmYul.dup 8 (stepPre cost (s2 cost pre mask size a b c d e f g tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s2 cost pre mask size a b c d e f g tail)).stack = (s2 cost pre mask size a b c d e f g tail).stack from rfl, shape]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256) : EVM.State :=
  EVM.State.replaceStackAndIncrPC
    { stepPre cost (s3 cost pre mask size a b c d e f g tail) with
      toMachineState := (stepPre cost (s3 cost pre mask size a b c d e f g tail)).toMachineState.mstore f (size + mask) }
    (size :: a :: b :: c :: d :: e :: f :: g :: tail)

theorem decode626 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 626) = some (.MSTORE, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 626).toNat = some 82 := by
    have index : (UInt256.ofNat 626).toNat = 626 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 623)
    (_stack : pre.stack = mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre mask size a b c d e f g tail))) (s3 cost pre mask size a b c d e f g tail) = .ok (s4 cost pre mask size a b c d e f g tail) := by
  have atPC : (s3 cost pre mask size a b c d e f g tail).pc = UInt256.ofNat 626 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre mask size a b c d e f g tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre mask size a b c d e f g tail).pc).getD _ = _
    rw [code, atPC, decode626]
    rfl
  rw [decoded]
  exact step_MSTORE fuel cost _ _ f (size + mask) (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 623)
    (stack : pre.stack = mask :: size :: a :: b :: c :: d :: e :: f :: g :: tail) :
    run fuel cost 4 pre = .ok (s4 cost pre mask size a b c d e f g tail) := by
  rw [run, transition1 fuel cost pre mask size a b c d e f g tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre mask size a b c d e f g tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre mask size a b c d e f g tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre mask size a b c d e f g tail code pc stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceFieldRoundingStore
