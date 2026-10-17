import Compiler.Proofs.IRGeneration.NativeSourceMcopyGrowth
import Compiler.Proofs.IRGeneration.NativeSourceAbiWrite

namespace Compiler.Proofs.IRGeneration.NativeSourcePackingCopy
open EvmYul EVM.Proof

theorem get_data (bytes : ByteArray) (index : Nat) : bytes.get? index = bytes.data[index]? := by
  by_cases inside : index < bytes.data.size
  · rw [Array.getElem?_eq_getElem inside]
    simp only [ByteArray.get?, ByteArray.size, ByteArray.get, inside, dif_pos]
    rfl
  · rw [Array.getElem?_eq_none (by omega)]
    simp only [ByteArray.get?, ByteArray.size, inside, dite_false]

theorem first_decode : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 647) = some (.MCOPY, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 647).toNat = some 0x5e := by
    have index : (UInt256.ofNat 647).toNat = 647 := by decide
    rw [index]
    rw [get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem second_decode : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 662) = some (.MCOPY, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 662).toNat = some 0x5e := by
    have index : (UInt256.ofNat 662).toNat = 662 := by decide
    rw [index]
    rw [get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode_at (pre : EVM.State) (same : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 647 ∨ pre.pc = UInt256.ofNat 662) :
    EVM.Proof.decodeAt pre = (.MCOPY, none) := by
  unfold EVM.Proof.decodeAt
  rw [same]
  rcases pc with first | second
  · rw [first, first_decode]; rfl
  · rw [second, second_decode]; rfl

theorem copied_bytes (fuel gasCost : Nat) (pre post : EVM.State)
    (same : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 647 ∨ pre.pc = UInt256.ofNat 662)
    (rest : Stack UInt256) (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size))
    (success : StepOk (fuel + 1) gasCost (EVM.Proof.decodeAt pre) pre post)
    (positive : 0 < size.toNat) (bounded : size.toNat < 2^64)
    (input : source.toNat + size.toNat ≤ pre.memory.size)
    (padding : dest.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    post.memory.readWithPadding dest.toNat size.toNat =
      pre.memory.extract source.toNat (source.toNat + size.toNat) := by
  rw [decode_at pre same pc] at success
  rw [NativeSourceMcopy.memory_step_MCOPY fuel gasCost pre post rest dest source size popped success]
  exact NativeSourceMcopyGrowth.readback pre.memory _ _ _ positive bounded input padding

end Compiler.Proofs.IRGeneration.NativeSourcePackingCopy
