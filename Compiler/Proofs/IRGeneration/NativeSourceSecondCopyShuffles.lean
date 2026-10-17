import Compiler.Proofs.IRGeneration.NativeSourceSecondCopyStore

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondCopyShuffles
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (source :: dest :: finish :: length :: tail)

theorem decode659 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 659) = some (.SWAP3, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 659).toNat = some 146 := by
    have index : (UInt256.ofNat 659).toNat = 659 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 659)
    (stack : pre.stack = length :: dest :: finish :: source :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre length dest finish source tail) := by
  have atPC : pre.pc = UInt256.ofNat 659 := by
    exact pc
  have decoded : decodeAt pre = (.SWAP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode659]
    rfl
  rw [decoded]
  have shape : pre.stack = length :: dest :: finish :: source :: tail := stack
  change EvmYul.swap 3 (stepPre cost pre) = _
  unfold EvmYul.swap
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre length dest finish source tail)).replaceStackAndIncrPC (length :: source :: dest :: finish :: length :: tail)

theorem decode660 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 660) = some (.DUP4, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 660).toNat = some 131 := by
    have index : (UInt256.ofNat 660).toNat = 660 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 659)
    (_stack : pre.stack = length :: dest :: finish :: source :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre length dest finish source tail))) (s1 cost pre length dest finish source tail) = .ok (s2 cost pre length dest finish source tail) := by
  have atPC : (s1 cost pre length dest finish source tail).pc = UInt256.ofNat 660 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre length dest finish source tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre length dest finish source tail).pc).getD _ = _
    rw [code, atPC, decode660]
    rfl
  rw [decoded]
  have shape : (s1 cost pre length dest finish source tail).stack = source :: dest :: finish :: length :: tail := rfl
  change EvmYul.dup 4 (stepPre cost (s1 cost pre length dest finish source tail)) = _
  unfold EvmYul.dup
  rw [show (stepPre cost (s1 cost pre length dest finish source tail)).stack = (s1 cost pre length dest finish source tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre length dest finish source tail)).replaceStackAndIncrPC (dest :: source :: length :: finish :: length :: tail)

theorem decode661 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 661) = some (.SWAP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 661).toNat = some 145 := by
    have index : (UInt256.ofNat 661).toNat = 661 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 659)
    (_stack : pre.stack = length :: dest :: finish :: source :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre length dest finish source tail))) (s2 cost pre length dest finish source tail) = .ok (s3 cost pre length dest finish source tail) := by
  have atPC : (s2 cost pre length dest finish source tail).pc = UInt256.ofNat 661 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre length dest finish source tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre length dest finish source tail).pc).getD _ = _
    rw [code, atPC, decode661]
    rfl
  rw [decoded]
  have shape : (s2 cost pre length dest finish source tail).stack = length :: source :: dest :: finish :: length :: tail := rfl
  change EvmYul.swap 2 (stepPre cost (s2 cost pre length dest finish source tail)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s2 cost pre length dest finish source tail)).stack = (s2 cost pre length dest finish source tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 659)
    (stack : pre.stack = length :: dest :: finish :: source :: tail) :
    run fuel cost 3 pre = .ok (s3 cost pre length dest finish source tail) := by
  rw [run, transition1 fuel cost pre length dest finish source tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre length dest finish source tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre length dest finish source tail code pc stack]
  rfl

theorem operands (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256) :
    (s3 cost pre length dest finish source tail).stack.pop3 = some (finish :: length :: tail, dest, source, length) := by
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (length dest finish source : UInt256) (tail : Stack UInt256) : (s3 cost pre length dest finish source tail).memory = pre.memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceSecondCopyShuffles
