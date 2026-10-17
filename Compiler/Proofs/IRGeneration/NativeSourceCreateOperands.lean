import Compiler.Proofs.IRGeneration.NativeSourceOriginalAllocation

namespace Compiler.Proofs.IRGeneration.NativeSourceCreateOperands
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) := (stepPre cost pre).incrPC
def s2 (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256) := NativeSourceLoadStep.loaded cost (s1 cost pre) pointer (offset :: value :: salt :: tail)
def s3 (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256) := (stepPre cost (s2 cost pre pointer offset value salt tail)).replaceStackAndIncrPC
  (offset :: (s1 cost pre).toMachineState.lookupMemory pointer :: value :: salt :: tail)
def s4 (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256) := (stepPre cost (s3 cost pre pointer offset value salt tail)).replaceStackAndIncrPC
  (value :: offset :: (s1 cost pre).toMachineState.lookupMemory pointer :: value :: salt :: tail)

theorem decode681 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 681) = some (.JUMPDEST, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 681).toNat = some 91 := by
    have index : (UInt256.ofNat 681).toNat = 681 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 681)
    (_stack : pre.stack = pointer :: offset :: value :: salt :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre) := by
  have atPC : pre.pc = UInt256.ofNat 681 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode681]
    rfl
  rw [decoded]
  rfl

theorem decode682 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 682) = some (.MLOAD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 682).toNat = some 81 := by
    have index : (UInt256.ofNat 682).toNat = 682 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 681)
    (stack : pre.stack = pointer :: offset :: value :: salt :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre))) (s1 cost pre) = .ok (s2 cost pre pointer offset value salt tail) := by
  have atPC : (s1 cost pre).pc = UInt256.ofNat 682 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre) = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre).pc).getD _ = _
    rw [code, atPC, decode682]
    rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost _ pointer _ stack

theorem decode683 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 683) = some (.SWAP1, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 683).toNat = some 144 := by
    have index : (UInt256.ofNat 683).toNat = 683 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 681)
    (_stack : pre.stack = pointer :: offset :: value :: salt :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre pointer offset value salt tail))) (s2 cost pre pointer offset value salt tail) = .ok (s3 cost pre pointer offset value salt tail) := by
  have atPC : (s2 cost pre pointer offset value salt tail).pc = UInt256.ofNat 683 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre pointer offset value salt tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre pointer offset value salt tail).pc).getD _ = _
    rw [code, atPC, decode683]
    rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre cost (s2 cost pre pointer offset value salt tail)) = _
  rfl

theorem decode684 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 684) = some (.DUP3, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 684).toNat = some 130 := by
    have index : (UInt256.ofNat 684).toNat = 684 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 681)
    (_stack : pre.stack = pointer :: offset :: value :: salt :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre pointer offset value salt tail))) (s3 cost pre pointer offset value salt tail) = .ok (s4 cost pre pointer offset value salt tail) := by
  have atPC : (s3 cost pre pointer offset value salt tail).pc = UInt256.ofNat 684 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre pointer offset value salt tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre pointer offset value salt tail).pc).getD _ = _
    rw [code, atPC, decode684]
    rfl
  rw [decoded]
  change EvmYul.dup 3 (stepPre cost (s3 cost pre pointer offset value salt tail)) = _
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 681)
    (stack : pre.stack = pointer :: offset :: value :: salt :: tail) :
    run fuel cost 4 pre = .ok (s4 cost pre pointer offset value salt tail) := by
  rw [run, transition1 fuel cost pre pointer offset value salt tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre pointer offset value salt tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre pointer offset value salt tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre pointer offset value salt tail code pc stack]
  rfl

theorem operands (cost : Nat) (pre : EVM.State) (pointer offset value salt : UInt256) (tail : Stack UInt256) :
    (s4 cost pre pointer offset value salt tail).stack.pop4 = some (salt :: tail, value, offset,
      (s1 cost pre).toMachineState.lookupMemory pointer, value) := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceCreateOperands
