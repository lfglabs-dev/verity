import Compiler.Proofs.IRGeneration.NativeSourceAllocatorJump

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorStart
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate : NativeSourceAbiWrite.code.extract' 913 914 = ⟨#[31]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[913]? = some 31 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (913 < 2^64 && 914 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 913 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)


theorem decode910 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 910) = some (.JUMPDEST, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 910).toNat = some 91 := by
    have index : (UInt256.ofNat 910).toNat = 910 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode911 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 911) = some (.SWAP1, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 911).toNat = some 144 := by
    have index : (UInt256.ofNat 911).toNat = 911 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode912 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 912) =
    some (.Push .PUSH1, some (UInt256.ofNat 31, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 912 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 912).toNat = 912 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 913 914), 1)) = _
  rw [immediate]
  decide

def s1 (cost : Nat) (pre : EVM.State) := (stepPre cost pre).incrPC
def s2 (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) := (stepPre cost (s1 cost pre)).replaceStackAndIncrPC (b :: a :: tail)
def s3 (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre a b tail)).replaceStackAndIncrPC (UInt256.ofNat 31 :: b :: a :: tail) 2

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (_stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre) := by
  have atPC : pre.pc = UInt256.ofNat 910 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode910]
    rfl
  rw [decoded]
  rfl

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre))) (s1 cost pre) = .ok (s2 cost pre a b tail) := by
  have atPC : (s1 cost pre).pc = UInt256.ofNat 911 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre).pc).getD _ = _
    rw [code, atPC, decode911]
    rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre cost (s1 cost pre)) = _
  unfold EvmYul.swap
  rw [show (stepPre cost (s1 cost pre)).stack = pre.stack from rfl, stack]
  rfl

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (_stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b tail))) (s2 cost pre a b tail) = .ok (s3 cost pre a b tail) := by
  have atPC : (s2 cost pre a b tail).pc = UInt256.ofNat 912 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b tail) = (.Push .PUSH1, some (UInt256.ofNat 31, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b tail).pc).getD _ = _
    rw [code, atPC, decode912]
    rfl
  rw [decoded]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = a :: b :: tail) :
    run fuel cost 3 pre = .ok (s3 cost pre a b tail) := by
  rw [run, transition1 fuel cost pre a b tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre a b tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre a b tail code pc stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorStart
