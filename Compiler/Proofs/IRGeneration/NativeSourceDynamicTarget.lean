import Compiler.Proofs.IRGeneration.NativeSourceDynamicInitialReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicTarget
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate499 : NativeSourceAbiWrite.code.extract' 500 502 = ⟨#[1, 64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[500]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[501]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (500 < 2^64 && 502 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 500 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 501 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode499 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 499) = some (.Push .PUSH2, some (UInt256.ofNat 320, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 499 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 499).toNat = 499 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 500 502), 2)) = _
  rw [immediate499]
  decide

theorem decode502 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 502) = some (.DUP13, none) := by
  have byte : NativeSourceAbiWrite.code.get? 502 = some 140 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 502).toNat = 502 by decide, byte]
  decide

theorem decode503 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 503) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 503 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 503).toNat = 503 by decide, byte]
  decide

theorem decode504 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 504) = some (.SWAP14, none) := by
  have byte : NativeSourceAbiWrite.code.get? 504 = some 157 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 504).toNat = 504 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 320 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) 3
def s2 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail)).replaceStackAndIncrPC (x11 :: UInt256.ofNat 320 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) 1
def s3 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail)).replaceStackAndIncrPC ((x11 + UInt256.ofNat 320) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) 1
def s4 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail)).replaceStackAndIncrPC (x13 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: (x11 + UInt256.ofNat 320) :: tail) 1

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  have atPC : pre.pc = UInt256.ofNat 499 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 320, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode499]; rfl
  rw [decoded]
  change Except.ok ((stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 320 :: pre.stack) 3) = _
  rw [stack]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail))) (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) = .ok (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  have atPC : (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).pc = UInt256.ofNat 502 := by
    change (pre.pc + UInt256.ofNat 3) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) = (.DUP13, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).pc).getD _ = _
    rw [code, atPC, decode502]; rfl
  rw [decoded]
  change EvmYul.dup 13 (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail))) (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) = .ok (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  have atPC : (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).pc = UInt256.ofNat 503 := by
    change ((pre.pc + UInt256.ofNat 3) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).pc).getD _ = _
    rw [code, atPC, decode503]; rfl
  rw [decoded]
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail))) (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) = .ok (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  have atPC : (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).pc = UInt256.ofNat 504 := by
    change (((pre.pc + UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) = (.SWAP14, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).pc).getD _ = _
    rw [code, atPC, decode504]; rfl
  rw [decoded]
  change EvmYul.swap 14 (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail)) = _
  unfold EvmYul.swap
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) :
    run fuel cost 4 pre = .ok (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  rw [run, transition1 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem target_register (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) :
    (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).stack[14]? = some (x11 + UInt256.ofNat 320) := by
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) : (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).memory = pre.memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicTarget
