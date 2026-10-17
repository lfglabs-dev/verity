import Compiler.Proofs.IRGeneration.NativeSourceAllocatorDecision

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorReturn
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate : NativeSourceAbiWrite.code.extract' 941 942 = ⟨#[64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[941]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (941 < 2^64 && 942 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 941 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)


theorem byte940 : NativeSourceAbiWrite.code.get? 940 = some 96 := by
  rw [NativeSourcePackingCopy.get_data]
  simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
  norm_num

theorem decode940 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 940) =
    some (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
  unfold EVM.decode
  rw [show (UInt256.ofNat 940).toNat = 940 by decide, byte940]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 941 942), 1)) = _
  rw [immediate]
  decide

theorem decode942 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 942) = some (.MSTORE, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 942).toNat = some 82 := by
    have index : (UInt256.ofNat 942).toNat = 942 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode943 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 943) = some (.JUMP, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 943).toNat = some 86 := by
    have index : (UInt256.ofNat 943).toNat = 943 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def pushed (cost : Nat) (pre : EVM.State) :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 64 :: pre.stack) 2

def stored (cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256) : EVM.State :=
  EVM.State.replaceStackAndIncrPC
    { stepPre cost (pushed cost pre) with
      toMachineState := (stepPre cost (pushed cost pre)).toMachineState.mstore (UInt256.ofNat 64) pointer }
    (target :: tail)

def returned (cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256) : EVM.State :=
  { stepPre cost (stored cost pre pointer target tail) with pc := target, stack := tail }

theorem push (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 940) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (pushed cost pre) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt
    rw [code, pc, decode940]
    rfl
  rw [decoded]
  rfl

theorem store (fuel cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 940)
    (stack : pre.stack = pointer :: target :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (pushed cost pre))) (pushed cost pre) =
      .ok (stored cost pre pointer target tail) := by
  have atPC : (pushed cost pre).pc = UInt256.ofNat 942 := by
    change pre.pc + UInt256.ofNat 2 = _
    rw [pc]; decide
  have decoded : decodeAt (pushed cost pre) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (pushed cost pre).pc).getD _ = _
    rw [code, atPC, decode942]
    rfl
  rw [decoded]
  apply step_MSTORE fuel cost _ (target :: tail) (UInt256.ofNat 64) pointer
  change Stack.pop2 (UInt256.ofNat 64 :: pre.stack) = _
  rw [stack]
  rfl

theorem jump (fuel cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 940) :
    EVM.step (fuel + 1) cost (some (decodeAt (stored cost pre pointer target tail)))
      (stored cost pre pointer target tail) = .ok (returned cost pre pointer target tail) := by
  have atPC : (stored cost pre pointer target tail).pc = UInt256.ofNat 943 := by
    change (pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (stored cost pre pointer target tail) = (.JUMP, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (stored cost pre pointer target tail).pc).getD _ = _
    rw [code, atPC, decode943]
    rfl
  rw [decoded]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 940)
    (stack : pre.stack = pointer :: target :: tail) :
    run fuel cost 3 pre = .ok (returned cost pre pointer target tail) := by
  rw [run, push fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, store fuel cost pre pointer target tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, jump fuel cost pre pointer target tail code pc]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorReturn
