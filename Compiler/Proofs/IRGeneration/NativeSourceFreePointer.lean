import Compiler.Proofs.IRGeneration.NativeSourceDecodedFirstCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceFreePointer
open EvmYul EVM.Proof

theorem byte632 : NativeSourceAbiWrite.code.get? 632 = some 91 := by
  rw [NativeSourcePackingCopy.get_data]
  simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
  norm_num

theorem byte633 : NativeSourceAbiWrite.code.get? 633 = some 96 := by
  rw [NativeSourcePackingCopy.get_data]
  simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
  norm_num

theorem byte635 : NativeSourceAbiWrite.code.get? 635 = some 81 := by
  rw [NativeSourcePackingCopy.get_data]
  simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
  norm_num

theorem immediate : NativeSourceAbiWrite.code.extract' 634 635 = ⟨#[64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[634]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (634 < 2^64 && 635 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 634 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode633 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 633) =
    some (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
  unfold EVM.decode
  rw [show (UInt256.ofNat 633).toNat = 633 by decide, byte633]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 634 635), 1)) = _
  rw [immediate]
  decide

theorem decode632 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 632) = some (.JUMPDEST, none) := by
  unfold EVM.decode
  rw [show (UInt256.ofNat 632).toNat = 632 by decide, byte632]
  decide

theorem decode635 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 635) = some (.MLOAD, none) := by
  unfold EVM.decode
  rw [show (UInt256.ofNat 635).toNat = 635 by decide, byte635]
  decide

def jumped (cost : Nat) (pre : EVM.State) := (stepPre cost pre).incrPC
def pushed (cost : Nat) (pre : EVM.State) :=
  (stepPre cost (jumped cost pre)).replaceStackAndIncrPC (UInt256.ofNat 64 :: pre.stack) 2
def loaded (cost : Nat) (pre : EVM.State) :=
  NativeSourceLoadStep.loaded cost (pushed cost pre) (UInt256.ofNat 64) pre.stack

theorem execute (fuel cost : Nat) (pre : EVM.State) :
    (do
      let one ← EVM.step (fuel + 1) cost (some (.JUMPDEST, none)) pre
      let two ← EVM.step (fuel + 1) cost (some (.Push .PUSH1, some (UInt256.ofNat 64, 1))) one
      EVM.step (fuel + 1) cost (some (.MLOAD, none)) two) = .ok (loaded cost pre) := by
  rw [step_JUMPDEST fuel cost pre]
  simp only [Bind.bind, Except.bind]
  rw [NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 64)]
  exact NativeSourceLoadStep.step fuel cost _ (UInt256.ofNat 64) pre.stack (by rfl)

theorem stack (cost : Nat) (pre : EVM.State) :
    (loaded cost pre).stack = (pushed cost pre).toMachineState.lookupMemory (UInt256.ofNat 64) :: pre.stack := by rfl

theorem memory (cost : Nat) (pre : EVM.State) : (loaded cost pre).memory = pre.memory := by rfl

theorem pc (cost : Nat) (pre : EVM.State) (initial : pre.pc = UInt256.ofNat 632) :
    (loaded cost pre).pc = UInt256.ofNat 636 := by
  change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1 = _
  rw [initial]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceFreePointer
