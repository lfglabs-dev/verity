import Compiler.Proofs.IRGeneration.NativeSourceAllocatorRoundedEntry

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorPointer
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (base :: size :: base :: tail)

theorem decode919 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 919) = some (.DUP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 919).toNat = some 129 := by
    have index : (UInt256.ofNat 919).toNat = 919 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 919)
    (stack : pre.stack = size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre size base tail) := by
  have atPC : pre.pc = UInt256.ofNat 919 := by
    exact pc
  have decoded : decodeAt pre = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode919]
    rfl
  rw [decoded]
  have shape : pre.stack = size :: base :: tail := stack
  change EvmYul.dup 2 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre size base tail)).replaceStackAndIncrPC ((base + size) :: base :: tail)

theorem decode920 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 920) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 920).toNat = some 1 := by
    have index : (UInt256.ofNat 920).toNat = 920 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 919)
    (_stack : pre.stack = size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre size base tail))) (s1 cost pre size base tail) = .ok (s2 cost pre size base tail) := by
  have atPC : (s1 cost pre size base tail).pc = UInt256.ofNat 920 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre size base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre size base tail).pc).getD _ = _
    rw [code, atPC, decode920]
    rfl
  rw [decoded]
  have shape : (s1 cost pre size base tail).stack = base :: size :: base :: tail := rfl
  change EVM.execBinOp UInt256.add (stepPre cost (s1 cost pre size base tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s1 cost pre size base tail)).stack = (s1 cost pre size base tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre size base tail)).replaceStackAndIncrPC (base :: (base + size) :: tail)

theorem decode921 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 921) = some (.SWAP1, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 921).toNat = some 144 := by
    have index : (UInt256.ofNat 921).toNat = 921 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 919)
    (_stack : pre.stack = size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre size base tail))) (s2 cost pre size base tail) = .ok (s3 cost pre size base tail) := by
  have atPC : (s2 cost pre size base tail).pc = UInt256.ofNat 921 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre size base tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre size base tail).pc).getD _ = _
    rw [code, atPC, decode921]
    rfl
  rw [decoded]
  have shape : (s2 cost pre size base tail).stack = (base + size) :: base :: tail := rfl
  change EvmYul.swap 1 (stepPre cost (s2 cost pre size base tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s2 cost pre size base tail)).stack = (s2 cost pre size base tail).stack from rfl, shape]
  rfl

def s4 (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre size base tail)).replaceStackAndIncrPC ((base + size) :: base :: (base + size) :: tail)

theorem decode922 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 922) = some (.DUP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 922).toNat = some 129 := by
    have index : (UInt256.ofNat 922).toNat = 922 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 919)
    (_stack : pre.stack = size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre size base tail))) (s3 cost pre size base tail) = .ok (s4 cost pre size base tail) := by
  have atPC : (s3 cost pre size base tail).pc = UInt256.ofNat 922 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre size base tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre size base tail).pc).getD _ = _
    rw [code, atPC, decode922]
    rfl
  rw [decoded]
  have shape : (s3 cost pre size base tail).stack = base :: (base + size) :: tail := rfl
  change EvmYul.dup 2 (stepPre cost (s3 cost pre size base tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s3 cost pre size base tail)).stack = (s3 cost pre size base tail).stack from rfl, shape]
  rfl

def s5 (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s4 cost pre size base tail)).replaceStackAndIncrPC (UInt256.lt (base + size) base :: (base + size) :: tail)

theorem decode923 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 923) = some (.LT, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 923).toNat = some 16 := by
    have index : (UInt256.ofNat 923).toNat = 923 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 919)
    (_stack : pre.stack = size :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre size base tail))) (s4 cost pre size base tail) = .ok (s5 cost pre size base tail) := by
  have atPC : (s4 cost pre size base tail).pc = UInt256.ofNat 923 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre size base tail) = (.LT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre size base tail).pc).getD _ = _
    rw [code, atPC, decode923]
    rfl
  rw [decoded]
  have shape : (s4 cost pre size base tail).stack = (base + size) :: base :: (base + size) :: tail := rfl
  change EVM.execBinOp UInt256.lt (stepPre cost (s4 cost pre size base tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s4 cost pre size base tail)).stack = (s4 cost pre size base tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 919)
    (stack : pre.stack = size :: base :: tail) :
    run fuel cost 5 pre = .ok (s5 cost pre size base tail) := by
  rw [run, transition1 fuel cost pre size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre size base tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre size base tail code pc stack]
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) :
    (s5 cost pre size base tail).stack = UInt256.lt (base + size) base :: (base + size) :: tail := by
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (size base : UInt256) (tail : Stack UInt256) : (s5 cost pre size base tail).memory = pre.memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorPointer
