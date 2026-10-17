import Compiler.Proofs.IRGeneration.NativeSourceAllocatorOverflowEntry

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorLimit
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate : NativeSourceAbiWrite.code.extract' 925 933 = ⟨#[255,255,255,255,255,255,255,255]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  apply ByteArray.ext
  simp only [ByteArray.extract', show (925 < 2^64 && 933 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 8 := by simpa using right
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
    rcases cases with h | h | h | h | h | h | h | h <;> subst index <;>
      simp only [Array.getElem_extract] <;>
      apply Option.some.inj <;>
      rw [← Array.getElem?_eq_getElem] <;>
      simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append] <;>
      norm_num

theorem decode924 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 924) =
    some (.Push .PUSH8, some (UInt256.ofNat (2^64-1), 8)) := by
  have byte : NativeSourceAbiWrite.code.get? 924 = some 103 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 924).toNat = 924 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH8, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 925 933), 8)) = _
  rw [immediate]
  decide

def pushed (cost : Nat) (pre : EVM.State) :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat (2^64-1) :: pre.stack) 9

theorem push (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 924) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (pushed cost pre) := by
  have decoded : decodeAt pre = (.Push .PUSH8, some (UInt256.ofNat (2^64-1), 8)) := by
    unfold decodeAt
    rw [code, pc, decode924]
    rfl
  rw [decoded]
  rfl

def s1 (cost : Nat) (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (pointer :: limit :: overflow :: pointer :: tail)

theorem decode933 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 933) = some (.DUP3, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 933).toNat = some 130 := by
    have index : (UInt256.ofNat 933).toNat = 933 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (stack : pre.stack = limit :: overflow :: pointer :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre limit overflow pointer tail) := by
  have atPC : pre.pc = UInt256.ofNat 933 := by
    exact pc
  have decoded : decodeAt pre = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode933]
    rfl
  rw [decoded]
  have shape : pre.stack = limit :: overflow :: pointer :: tail := stack
  change EvmYul.dup 3 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, shape]
  rfl

def s2 (cost : Nat) (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre limit overflow pointer tail)).replaceStackAndIncrPC (UInt256.gt pointer limit :: overflow :: pointer :: tail)

theorem decode934 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 934) = some (.GT, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 934).toNat = some 17 := by
    have index : (UInt256.ofNat 934).toNat = 934 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (_stack : pre.stack = limit :: overflow :: pointer :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre limit overflow pointer tail))) (s1 cost pre limit overflow pointer tail) = .ok (s2 cost pre limit overflow pointer tail) := by
  have atPC : (s1 cost pre limit overflow pointer tail).pc = UInt256.ofNat 934 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre limit overflow pointer tail) = (.GT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre limit overflow pointer tail).pc).getD _ = _
    rw [code, atPC, decode934]
    rfl
  rw [decoded]
  have shape : (s1 cost pre limit overflow pointer tail).stack = pointer :: limit :: overflow :: pointer :: tail := rfl
  change EVM.execBinOp UInt256.gt (stepPre cost (s1 cost pre limit overflow pointer tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s1 cost pre limit overflow pointer tail)).stack = (s1 cost pre limit overflow pointer tail).stack from rfl, shape]
  rfl

def s3 (cost : Nat) (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre limit overflow pointer tail)).replaceStackAndIncrPC (UInt256.lor (UInt256.gt pointer limit) overflow :: pointer :: tail)

theorem decode935 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 935) = some (.OR, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 935).toNat = some 23 := by
    have index : (UInt256.ofNat 935).toNat = 935 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (_stack : pre.stack = limit :: overflow :: pointer :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre limit overflow pointer tail))) (s2 cost pre limit overflow pointer tail) = .ok (s3 cost pre limit overflow pointer tail) := by
  have atPC : (s2 cost pre limit overflow pointer tail).pc = UInt256.ofNat 935 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre limit overflow pointer tail) = (.OR, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre limit overflow pointer tail).pc).getD _ = _
    rw [code, atPC, decode935]
    rfl
  rw [decoded]
  have shape : (s2 cost pre limit overflow pointer tail).stack = UInt256.gt pointer limit :: overflow :: pointer :: tail := rfl
  change EVM.execBinOp UInt256.lor (stepPre cost (s2 cost pre limit overflow pointer tail)) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost (s2 cost pre limit overflow pointer tail)).stack = (s2 cost pre limit overflow pointer tail).stack from rfl, shape]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (limit overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 933)
    (stack : pre.stack = limit :: overflow :: pointer :: tail) :
    run fuel cost 3 pre = .ok (s3 cost pre limit overflow pointer tail) := by
  rw [run, transition1 fuel cost pre limit overflow pointer tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre limit overflow pointer tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre limit overflow pointer tail code pc stack]
  rfl

def guarded (cost : Nat) (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256) :=
  s3 cost (pushed cost pre) (UInt256.ofNat (2^64-1)) overflow pointer tail

theorem full (fuel cost : Nat) (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 924)
    (stack : pre.stack = overflow :: pointer :: tail) :
    run fuel cost 4 pre = .ok (guarded cost pre overflow pointer tail) := by
  have atPC : (pushed cost pre).pc = UInt256.ofNat 933 := by
    change pre.pc + UInt256.ofNat 9 = _
    rw [pc]; decide
  have shape : (pushed cost pre).stack = UInt256.ofNat (2^64-1) :: overflow :: pointer :: tail := by
    change UInt256.ofNat (2^64-1) :: pre.stack = _
    rw [stack]
  exact NativeSourceSizedPacking.compose fuel cost 1 3 pre _ _
    (by rw [run, push fuel cost pre code pc]; rfl)
    (execute fuel cost (pushed cost pre) (UInt256.ofNat (2^64-1)) overflow pointer tail code atPC shape)

theorem guarded_stack (cost : Nat) (pre : EVM.State) (overflow pointer : UInt256) (tail : Stack UInt256) :
    (guarded cost pre overflow pointer tail).stack =
      UInt256.lor (UInt256.gt pointer (UInt256.ofNat (2^64-1))) overflow :: pointer :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorLimit
