import Compiler.Proofs.IRGeneration.NativeSourcePreCreate

namespace Compiler.Proofs.IRGeneration.NativeSourceZeroShuffles
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 0 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail)

theorem decode573 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 573) = some (.PUSH0, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 573).toNat = some 95 := by
    have index : (UInt256.ofNat 573).toNat = 573 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c d e f g h i j k tail) := by
  have atPC : pre.pc = UInt256.ofNat 573 := by
    exact pc
  have decoded : decodeAt pre = (.PUSH0, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode573]
    rfl
  rw [decoded]
  change Except.ok ((stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 0 :: pre.stack)) = _
  rw [stack]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (k :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: UInt256.ofNat 0 :: tail)

theorem decode574 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 574) = some (.SWAP11, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 574).toNat = some 154 := by
    have index : (UInt256.ofNat 574).toNat = 574 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c d e f g h i j k tail))) (s1 cost pre a b c d e f g h i j k tail) = .ok (s2 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s1 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 574 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c d e f g h i j k tail) = (.SWAP11, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode574]
    rfl
  rw [decoded]
  have shape : (s1 cost pre a b c d e f g h i j k tail).stack = UInt256.ofNat 0 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail := rfl
  change EvmYul.swap 11 (stepPre cost (s1 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s1 cost pre a b c d e f g h i j k tail)).stack = (s1 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (j :: a :: b :: c :: d :: e :: f :: g :: h :: i :: k :: UInt256.ofNat 0 :: tail)

theorem decode575 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 575) = some (.SWAP10, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 575).toNat = some 153 := by
    have index : (UInt256.ofNat 575).toNat = 575 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c d e f g h i j k tail))) (s2 cost pre a b c d e f g h i j k tail) = .ok (s3 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s2 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 575 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c d e f g h i j k tail) = (.SWAP10, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode575]
    rfl
  rw [decoded]
  have shape : (s2 cost pre a b c d e f g h i j k tail).stack = k :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: UInt256.ofNat 0 :: tail := rfl
  change EvmYul.swap 10 (stepPre cost (s2 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s2 cost pre a b c d e f g h i j k tail)).stack = (s2 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (i :: a :: b :: c :: d :: e :: f :: g :: h :: j :: k :: UInt256.ofNat 0 :: tail)

theorem decode576 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 576) = some (.SWAP9, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 576).toNat = some 152 := by
    have index : (UInt256.ofNat 576).toNat = 576 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c d e f g h i j k tail))) (s3 cost pre a b c d e f g h i j k tail) = .ok (s4 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s3 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 576 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c d e f g h i j k tail) = (.SWAP9, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode576]
    rfl
  rw [decoded]
  have shape : (s3 cost pre a b c d e f g h i j k tail).stack = j :: a :: b :: c :: d :: e :: f :: g :: h :: i :: k :: UInt256.ofNat 0 :: tail := rfl
  change EvmYul.swap 9 (stepPre cost (s3 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s3 cost pre a b c d e f g h i j k tail)).stack = (s3 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

def s5 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s4 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (g :: a :: b :: c :: d :: e :: f :: i :: h :: j :: k :: UInt256.ofNat 0 :: tail)

theorem decode577 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 577) = some (.SWAP7, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 577).toNat = some 150 := by
    have index : (UInt256.ofNat 577).toNat = 577 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre a b c d e f g h i j k tail))) (s4 cost pre a b c d e f g h i j k tail) = .ok (s5 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s4 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 577 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre a b c d e f g h i j k tail) = (.SWAP7, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode577]
    rfl
  rw [decoded]
  have shape : (s4 cost pre a b c d e f g h i j k tail).stack = i :: a :: b :: c :: d :: e :: f :: g :: h :: j :: k :: UInt256.ofNat 0 :: tail := rfl
  change EvmYul.swap 7 (stepPre cost (s4 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s4 cost pre a b c d e f g h i j k tail)).stack = (s4 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

def s6 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s5 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (a :: g :: a :: b :: c :: d :: e :: f :: i :: h :: j :: k :: UInt256.ofNat 0 :: tail)

theorem decode578 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 578) = some (.DUP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 578).toNat = some 129 := by
    have index : (UInt256.ofNat 578).toNat = 578 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre a b c d e f g h i j k tail))) (s5 cost pre a b c d e f g h i j k tail) = .ok (s6 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s5 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 578 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre a b c d e f g h i j k tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode578]
    rfl
  rw [decoded]
  have shape : (s5 cost pre a b c d e f g h i j k tail).stack = g :: a :: b :: c :: d :: e :: f :: i :: h :: j :: k :: UInt256.ofNat 0 :: tail := rfl
  change EvmYul.dup 2 (stepPre cost (s5 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s5 cost pre a b c d e f g h i j k tail)).stack = (s5 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 6 pre = .ok (s6 cost pre a b c d e f g h i j k tail) := by
  rw [run, transition1 fuel cost pre a b c d e f g h i j k tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre a b c d e f g h i j k tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre a b c d e f g h i j k tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre a b c d e f g h i j k tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre a b c d e f g h i j k tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre a b c d e f g h i j k tail code pc stack]
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : (s6 cost pre a b c d e f g h i j k tail).stack = a :: g :: a :: b :: c :: d :: e :: f :: i :: h :: j :: k :: UInt256.ofNat 0 :: tail := by
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : (s6 cost pre a b c d e f g h i j k tail).memory = pre.memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceZeroShuffles
