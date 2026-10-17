import Compiler.Proofs.IRGeneration.NativeSourceDecodedPackingStart

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondCopyHead
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (e :: length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode648 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 648) = some (.DUP5, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 648).toNat = some 132 := by
    have index : (UInt256.ofNat 648).toNat = 648 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre length b c d e f g dest x y tail) := by
  have atPC : pre.pc = UInt256.ofNat 648 := by
    exact pc
  have decoded : decodeAt pre = (.DUP5, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode648]
    rfl
  rw [decoded]
  have shape : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := stack
  change EvmYul.dup 5 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC ((e + length) :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode649 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 649) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 649).toNat = some 1 := by
    have index : (UInt256.ofNat 649).toNat = 649 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre length b c d e f g dest x y tail))) (s1 cost pre length b c d e f g dest x y tail) = .ok (s2 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s1 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 649 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre length b c d e f g dest x y tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode649]
    rfl
  rw [decoded]
  have shape : (s1 cost pre length b c d e f g dest x y tail).stack = e :: length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EVM.execBinOp UInt256.add (stepPre cost (s1 cost pre length b c d e f g dest x y tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s1 cost pre length b c d e f g dest x y tail)).stack = (s1 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC (b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode650 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 650) = some (.SWAP1, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 650).toNat = some 144 := by
    have index : (UInt256.ofNat 650).toNat = 650 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre length b c d e f g dest x y tail))) (s2 cost pre length b c d e f g dest x y tail) = .ok (s3 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s2 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 650 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre length b c d e f g dest x y tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode650]
    rfl
  rw [decoded]
  have shape : (s2 cost pre length b c d e f g dest x y tail).stack = (e + length) :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EvmYul.swap 1 (stepPre cost (s2 cost pre length b c d e f g dest x y tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s2 cost pre length b c d e f g dest x y tail)).stack = (s2 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC (d :: b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode651 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 651) = some (.DUP4, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 651).toNat = some 131 := by
    have index : (UInt256.ofNat 651).toNat = 651 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre length b c d e f g dest x y tail))) (s3 cost pre length b c d e f g dest x y tail) = .ok (s4 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s3 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 651 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre length b c d e f g dest x y tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode651]
    rfl
  rw [decoded]
  have shape : (s3 cost pre length b c d e f g dest x y tail).stack = b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EvmYul.dup 4 (stepPre cost (s3 cost pre length b c d e f g dest x y tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s3 cost pre length b c d e f g dest x y tail)).stack = (s3 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

def s5 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s4 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC ((e + length) :: d :: b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode652 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 652) = some (.DUP3, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 652).toNat = some 130 := by
    have index : (UInt256.ofNat 652).toNat = 652 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre length b c d e f g dest x y tail))) (s4 cost pre length b c d e f g dest x y tail) = .ok (s5 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s4 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 652 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre length b c d e f g dest x y tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode652]
    rfl
  rw [decoded]
  have shape : (s4 cost pre length b c d e f g dest x y tail).stack = d :: b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EvmYul.dup 3 (stepPre cost (s4 cost pre length b c d e f g dest x y tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s4 cost pre length b c d e f g dest x y tail)).stack = (s4 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

def s6 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s5 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC (((e + length) + d) :: b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode653 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 653) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 653).toNat = some 1 := by
    have index : (UInt256.ofNat 653).toNat = 653 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre length b c d e f g dest x y tail))) (s5 cost pre length b c d e f g dest x y tail) = .ok (s6 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s5 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 653 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre length b c d e f g dest x y tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode653]
    rfl
  rw [decoded]
  have shape : (s5 cost pre length b c d e f g dest x y tail).stack = (e + length) :: d :: b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EVM.execBinOp UInt256.add (stepPre cost (s5 cost pre length b c d e f g dest x y tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s5 cost pre length b c d e f g dest x y tail)).stack = (s5 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

def s7 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s6 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC (b :: ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode654 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 654) = some (.SWAP1, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 654).toNat = some 144 := by
    have index : (UInt256.ofNat 654).toNat = 654 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition7 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre length b c d e f g dest x y tail))) (s6 cost pre length b c d e f g dest x y tail) = .ok (s7 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s6 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 654 := by
    change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre length b c d e f g dest x y tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode654]
    rfl
  rw [decoded]
  have shape : (s6 cost pre length b c d e f g dest x y tail).stack = ((e + length) + d) :: b :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EvmYul.swap 1 (stepPre cost (s6 cost pre length b c d e f g dest x y tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s6 cost pre length b c d e f g dest x y tail)).stack = (s6 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

def s8 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s7 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC (x :: b :: ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode655 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 655) = some (.DUP10, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 655).toNat = some 137 := by
    have index : (UInt256.ofNat 655).toNat = 655 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition8 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s7 cost pre length b c d e f g dest x y tail))) (s7 cost pre length b c d e f g dest x y tail) = .ok (s8 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s7 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 655 := by
    change (((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre length b c d e f g dest x y tail) = (.DUP10, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode655]
    rfl
  rw [decoded]
  have shape : (s7 cost pre length b c d e f g dest x y tail).stack = b :: ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EvmYul.dup 10 (stepPre cost (s7 cost pre length b c d e f g dest x y tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s7 cost pre length b c d e f g dest x y tail)).stack = (s7 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

def s9 (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s8 cost pre length b c d e f g dest x y tail)).replaceStackAndIncrPC (((e + length) + d) :: x :: b :: ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem decode656 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 656) = some (.DUP3, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 656).toNat = some 130 := by
    have index : (UInt256.ofNat 656).toNat = 656 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition9 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (_stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s8 cost pre length b c d e f g dest x y tail))) (s8 cost pre length b c d e f g dest x y tail) = .ok (s9 cost pre length b c d e f g dest x y tail) := by
  have atPC : (s8 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 656 := by
    change ((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s8 cost pre length b c d e f g dest x y tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s8 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode656]
    rfl
  rw [decoded]
  have shape : (s8 cost pre length b c d e f g dest x y tail).stack = x :: b :: ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := rfl
  change EvmYul.dup 3 (stepPre cost (s8 cost pre length b c d e f g dest x y tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s8 cost pre length b c d e f g dest x y tail)).stack = (s8 cost pre length b c d e f g dest x y tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 648)
    (stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    run fuel cost 9 pre = .ok (s9 cost pre length b c d e f g dest x y tail) := by
  rw [run, transition1 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition9 fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem operands (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) :
    (s9 cost pre length b c d e f g dest x y tail).stack.pop2 =
      some (b :: ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail,
        (e + length) + d, x) := by rfl

theorem memory (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) : (s9 cost pre length b c d e f g dest x y tail).memory = pre.memory := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceSecondCopyHead
