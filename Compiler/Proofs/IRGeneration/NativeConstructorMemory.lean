import Compiler.Proofs.IRGeneration.NativeMidnightConstructor
import EvmYul.EVM.Proof.Memory

/-! Native CODECOPY source-offset bridge for the actual Midnight header.
This draft is separate from the frozen production validation inputs. -/
namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open Verity.Core.Model.MidnightInitcode

/-- Copying the appended payload at code offset 11 is exactly a whole-payload
write. Includes the empty payload, and arbitrary preexisting destination memory. -/
theorem write_payload (payload memory : ByteArray) (dest : Nat) :
    (initcode payload).write 11 memory dest payload.size =
      payload.write 0 memory dest payload.size := by
  by_cases empty : payload.size = 0
  · simp [ByteArray.write, empty]
  · have nonempty : 0 < payload.size := Nat.pos_of_ne_zero empty
    have sourceInside : ¬ 11 ≥ (initcode payload).size := by
      rw [initcode_size]; omega
    have payloadInside : ¬ 0 ≥ payload.size := by omega
    have practical : min payload.size ((initcode payload).size - 11) = payload.size := by
      rw [initcode_size]; omega
    have padding : min memory.size (dest + payload.size) - (dest + payload.size) = 0 := by
      omega
    simp only [ByteArray.write, empty, if_false, sourceInside, payloadInside, practical,
      Nat.sub_zero, Nat.min_self, padding]
    simp only [Nat.add_zero, ByteArray.copySlice, ByteArray.data_append, initcode]
    simp only [ffi.ByteArray.zeroes, USize.toNat, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
      Array.replicate_zero, Array.append_empty]
    have tail : (header.data ++ payload.data).extract 11 (11 + payload.size) = payload.data := by
      apply Array.extract_append_tail
      · rfl
      · rfl
    rw [tail]
    simp only [Array.size_append, show header.data.size = 11 from rfl,
      Nat.add_sub_cancel_left, Nat.sub_zero, Nat.zero_add]
    rw [show payload.data.extract 0 payload.size = payload.data from Array.extract_size]

/-- The native RETURN readback after the header's CODECOPY is the payload.
The native read API's explicit length limit remains part of the statement. -/
theorem read_copied_payload (payload memory : ByteArray)
    (bounded : payload.size < 2^64) :
    ((initcode payload).write 11 memory 0 payload.size).readWithPadding 0 payload.size =
      payload := by
  rw [write_payload]
  by_cases empty : payload.size = 0
  · have payloadEmpty : payload = ByteArray.empty := by
      apply ByteArray.ext
      exact Array.eq_empty_of_size_eq_zero empty
    subst payload
    simp only [ByteArray.write, ByteArray.size_empty, ↓reduceIte]
    unfold ByteArray.readWithPadding
    rw [if_neg (by decide : ¬ 0 ≥ 2^64)]
    have readZero : memory.readWithoutPadding 0 0 = ByteArray.empty := by
      unfold ByteArray.readWithoutPadding
      split
      · rfl
      · simp only [Nat.zero_min, Nat.zero_add, ByteArray.extract_same]
    rw [readZero]
    exact ByteArray.append_zeroes (by simp)
  · apply ByteArray.readWithPadding_write_self_of_pad
    · omega
    · exact bounded
    · rfl
    · simp

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
