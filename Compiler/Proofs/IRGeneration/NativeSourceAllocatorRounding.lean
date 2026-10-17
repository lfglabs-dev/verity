import Compiler.Proofs.IRGeneration.NativeSourceAllocatorStart

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorRounding
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (word :: word :: size :: base :: tail)

theorem decode914 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 914) = some (.DUP1, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 914).toNat = some 128 := by
    have index : (UInt256.ofNat 914).toNat = 914 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre word size base tail) := by
  have atPC : pre.pc = UInt256.ofNat 914 := by
    exact pc
  have decoded : decodeAt pre = (.DUP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode914]
    rfl
  rw [decoded]
  have shape : pre.stack = word :: size :: base :: tail := stack
  change EvmYul.dup 1 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre word size base tail)).replaceStackAndIncrPC (UInt256.lnot word :: word :: size :: base :: tail)

theorem decode915 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 915) = some (.NOT, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 915).toNat = some 25 := by
    have index : (UInt256.ofNat 915).toNat = 915 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (_stack : pre.stack = word :: size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre word size base tail))) (s1 cost pre word size base tail) = .ok (s2 cost pre word size base tail) := by
  have atPC : (s1 cost pre word size base tail).pc = UInt256.ofNat 915 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre word size base tail) = (.NOT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode915]
    rfl
  rw [decoded]
  have shape : (s1 cost pre word size base tail).stack = word :: word :: size :: base :: tail := rfl
  change EVM.execUnOp UInt256.lnot (stepPre cost (s1 cost pre word size base tail)) = _
  unfold EVM.execUnOp
  rw [show (stepPre cost (s1 cost pre word size base tail)).stack = (s1 cost pre word size base tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre word size base tail)).replaceStackAndIncrPC (size :: word :: UInt256.lnot word :: base :: tail)

theorem decode916 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 916) = some (.SWAP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 916).toNat = some 145 := by
    have index : (UInt256.ofNat 916).toNat = 916 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (_stack : pre.stack = word :: size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre word size base tail))) (s2 cost pre word size base tail) = .ok (s3 cost pre word size base tail) := by
  have atPC : (s2 cost pre word size base tail).pc = UInt256.ofNat 916 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre word size base tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode916]
    rfl
  rw [decoded]
  have shape : (s2 cost pre word size base tail).stack = UInt256.lnot word :: word :: size :: base :: tail := rfl
  change EvmYul.swap 2 (stepPre cost (s2 cost pre word size base tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s2 cost pre word size base tail)).stack = (s2 cost pre word size base tail).stack from rfl, shape]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre word size base tail)).replaceStackAndIncrPC ((size + word) :: UInt256.lnot word :: base :: tail)

theorem decode917 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 917) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 917).toNat = some 1 := by
    have index : (UInt256.ofNat 917).toNat = 917 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (_stack : pre.stack = word :: size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre word size base tail))) (s3 cost pre word size base tail) = .ok (s4 cost pre word size base tail) := by
  have atPC : (s3 cost pre word size base tail).pc = UInt256.ofNat 917 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre word size base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode917]
    rfl
  rw [decoded]
  have shape : (s3 cost pre word size base tail).stack = size :: word :: UInt256.lnot word :: base :: tail := rfl
  change EVM.execBinOp UInt256.add (stepPre cost (s3 cost pre word size base tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s3 cost pre word size base tail)).stack = (s3 cost pre word size base tail).stack from rfl, shape]
  rfl

def s5 (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s4 cost pre word size base tail)).replaceStackAndIncrPC (UInt256.land (size + word) (UInt256.lnot word) :: base :: tail)

theorem decode918 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 918) = some (.AND, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 918).toNat = some 22 := by
    have index : (UInt256.ofNat 918).toNat = 918 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (_stack : pre.stack = word :: size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre word size base tail))) (s4 cost pre word size base tail) = .ok (s5 cost pre word size base tail) := by
  have atPC : (s4 cost pre word size base tail).pc = UInt256.ofNat 918 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre word size base tail) = (.AND, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre word size base tail).pc).getD _ = _
    rw [code, atPC, decode918]
    rfl
  rw [decoded]
  have shape : (s4 cost pre word size base tail).stack = (size + word) :: UInt256.lnot word :: base :: tail := rfl
  change EVM.execBinOp UInt256.land (stepPre cost (s4 cost pre word size base tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s4 cost pre word size base tail)).stack = (s4 cost pre word size base tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 914)
    (stack : pre.stack = word :: size :: base :: tail) :
    run fuel cost 5 pre = .ok (s5 cost pre word size base tail) := by
  rw [run, transition1 fuel cost pre word size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre word size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre word size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre word size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre word size base tail code pc stack]
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256) :
    (s5 cost pre word size base tail).stack = UInt256.land (size + word) (UInt256.lnot word) :: base :: tail := by
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (word size base : UInt256) (tail : Stack UInt256) : (s5 cost pre word size base tail).memory = pre.memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorRounding
