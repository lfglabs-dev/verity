import Compiler.Proofs.IRGeneration.NativeSourceReturnConstants

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnShuffles
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 32 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) 2

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c d e f g h i j k tail) := by
  have atPC : pre.pc = UInt256.ofNat 579 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, NativeSourceReturnConstants.decode579]
    rfl
  rw [decoded]
  change Except.ok ((stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 32 :: pre.stack) 2) = _
  rw [stack]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (h :: a :: b :: c :: d :: e :: f :: g :: UInt256.ofNat 32 :: i :: j :: k :: tail) 1

theorem decode581 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 581) = some (.SWAP8, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 581).toNat = some 151 := by
    have index : (UInt256.ofNat 581).toNat = 581 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c d e f g h i j k tail))) (s1 cost pre a b c d e f g h i j k tail) = .ok (s2 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s1 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 581 := by
    change (pre.pc + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c d e f g h i j k tail) = (.SWAP8, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode581]
    rfl
  rw [decoded]
  have shape : (s1 cost pre a b c d e f g h i j k tail).stack = UInt256.ofNat 32 :: a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail := rfl
  change EvmYul.swap 8 (stepPre cost (s1 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s1 cost pre a b c d e f g h i j k tail)).stack = (s1 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (UInt256.ofNat 681 :: h :: a :: b :: c :: d :: e :: f :: g :: UInt256.ofNat 32 :: i :: j :: k :: tail) 3

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c d e f g h i j k tail))) (s2 cost pre a b c d e f g h i j k tail) = .ok (s3 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s2 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 582 := by
    change ((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c d e f g h i j k tail) = (.Push .PUSH2, some (UInt256.ofNat 681, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, NativeSourceReturnConstants.decode582]
    rfl
  rw [decoded]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (j :: h :: a :: b :: c :: d :: e :: f :: g :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: k :: tail) 1

theorem decode585 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 585) = some (.SWAP11, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 585).toNat = some 154 := by
    have index : (UInt256.ofNat 585).toNat = 585 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c d e f g h i j k tail))) (s3 cost pre a b c d e f g h i j k tail) = .ok (s4 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s3 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 585 := by
    change (((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 3) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c d e f g h i j k tail) = (.SWAP11, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode585]
    rfl
  rw [decoded]
  have shape : (s3 cost pre a b c d e f g h i j k tail).stack = UInt256.ofNat 681 :: h :: a :: b :: c :: d :: e :: f :: g :: UInt256.ofNat 32 :: i :: j :: k :: tail := rfl
  change EvmYul.swap 11 (stepPre cost (s3 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s3 cost pre a b c d e f g h i j k tail)).stack = (s3 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

def s5 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s4 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (g :: h :: a :: b :: c :: d :: e :: f :: j :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: k :: tail) 1

theorem decode586 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 586) = some (.SWAP8, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 586).toNat = some 151 := by
    have index : (UInt256.ofNat 586).toNat = 586 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre a b c d e f g h i j k tail))) (s4 cost pre a b c d e f g h i j k tail) = .ok (s5 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s4 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 586 := by
    change ((((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre a b c d e f g h i j k tail) = (.SWAP8, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode586]
    rfl
  rw [decoded]
  have shape : (s4 cost pre a b c d e f g h i j k tail).stack = j :: h :: a :: b :: c :: d :: e :: f :: g :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: k :: tail := rfl
  change EvmYul.swap 8 (stepPre cost (s4 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s4 cost pre a b c d e f g h i j k tail)).stack = (s4 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

def s6 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s5 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (UInt256.ofNat 632 :: g :: h :: a :: b :: c :: d :: e :: f :: j :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: k :: tail) 3

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre a b c d e f g h i j k tail))) (s5 cost pre a b c d e f g h i j k tail) = .ok (s6 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s5 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 587 := by
    change (((((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre a b c d e f g h i j k tail) = (.Push .PUSH2, some (UInt256.ofNat 632, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, NativeSourceReturnConstants.decode587]
    rfl
  rw [decoded]
  rfl

def s7 (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s6 cost pre a b c d e f g h i j k tail)).replaceStackAndIncrPC (f :: g :: h :: a :: b :: c :: d :: e :: UInt256.ofNat 632 :: j :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: k :: tail) 1

theorem decode590 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 590) = some (.SWAP8, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 590).toNat = some 151 := by
    have index : (UInt256.ofNat 590).toNat = 590 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition7 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (_stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre a b c d e f g h i j k tail))) (s6 cost pre a b c d e f g h i j k tail) = .ok (s7 cost pre a b c d e f g h i j k tail) := by
  have atPC : (s6 cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 590 := by
    change ((((((pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre a b c d e f g h i j k tail) = (.SWAP8, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre a b c d e f g h i j k tail).pc).getD _ = _
    rw [code, atPC, decode590]
    rfl
  rw [decoded]
  have shape : (s6 cost pre a b c d e f g h i j k tail).stack = UInt256.ofNat 632 :: g :: h :: a :: b :: c :: d :: e :: f :: j :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: k :: tail := rfl
  change EvmYul.swap 8 (stepPre cost (s6 cost pre a b c d e f g h i j k tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s6 cost pre a b c d e f g h i j k tail)).stack = (s6 cost pre a b c d e f g h i j k tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 579)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 7 pre = .ok (s7 cost pre a b c d e f g h i j k tail) := by
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
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre a b c d e f g h i j k tail code pc stack]
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : (s7 cost pre a b c d e f g h i j k tail).stack = f :: g :: h :: a :: b :: c :: d :: e :: UInt256.ofNat 632 :: j :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: k :: tail := by
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) : (s7 cost pre a b c d e f g h i j k tail).memory = pre.memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceReturnShuffles
