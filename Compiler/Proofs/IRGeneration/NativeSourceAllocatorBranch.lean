import Compiler.Proofs.IRGeneration.NativeSourceAllocatorGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorBranch
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate : NativeSourceAbiWrite.code.extract' 937 939 = ⟨#[3, 18]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte1 : NativeSourceAbiWrite.code.data[937]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte2 : NativeSourceAbiWrite.code.data[938]? = some 18 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (937 < 2^64 && 939 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 937 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 938 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte2)

theorem decode936 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 936) =
    some (.Push .PUSH2, some (UInt256.ofNat 786, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 936 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 936).toNat = 936 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 937 939), 2)) = _
  rw [immediate]
  decide


theorem decode939 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 939) = some (.JUMPI, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 939).toNat = some 87 := by
    have index : (UInt256.ofNat 939).toNat = 939 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def pushed (cost : Nat) (pre : EVM.State) :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 786 :: pre.stack) 3

def branched (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256) : EVM.State :=
  { stepPre cost (pushed cost pre) with
    pc := if condition != ⟨0⟩ then UInt256.ofNat 786 else (pushed cost pre).pc + ⟨1⟩,
    stack := rest }

theorem push (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 936) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (pushed cost pre) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 786, 2)) := by
    unfold decodeAt
    rw [code, pc, decode936]
    rfl
  rw [decoded]
  rfl

theorem jump (fuel cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 936)
    (stack : pre.stack = condition :: rest) :
    EVM.step (fuel + 1) cost (some (decodeAt (pushed cost pre))) (pushed cost pre) =
      .ok (branched cost pre condition rest) := by
  have atPC : (pushed cost pre).pc = UInt256.ofNat 939 := by
    change pre.pc + UInt256.ofNat 3 = _
    rw [pc]; decide
  have decoded : decodeAt (pushed cost pre) = (.JUMPI, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (pushed cost pre).pc).getD _ = _
    rw [code, atPC, decode939]
    rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .JUMPI none (stepPre cost (pushed cost pre)) = _
  unfold EvmYul.step
  simp only [stepPre, pushed, EVM.State.replaceStackAndIncrPC, stack]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 936)
    (stack : pre.stack = condition :: rest) :
    run fuel cost 2 pre = .ok (branched cost pre condition rest) := by
  rw [run, push fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, jump fuel cost pre condition rest code pc stack]
  rfl

theorem destinations (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 936) :
    (branched cost pre condition rest).pc =
      if condition != ⟨0⟩ then UInt256.ofNat 786 else UInt256.ofNat 940 := by
  change (if condition != ⟨0⟩ then UInt256.ofNat 786 else
    (pre.pc + UInt256.ofNat 3) + ⟨1⟩) = _
  rw [pc]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorBranch
