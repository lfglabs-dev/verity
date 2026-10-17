import Compiler.Proofs.IRGeneration.NativeSourceSecondPayloadReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceEmptyPayload
open EvmYul

theorem read_zero (memory : ByteArray) (start : Nat) :
    memory.readWithPadding start 0 = ByteArray.empty := by
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding]
  rfl

theorem extract_zero (memory : ByteArray) (start : Nat) :
    memory.extract start (start + 0) = ByteArray.empty := by
  apply ByteArray.ext
  simp

theorem second_return (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (zero : (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat = 0) :
    (NativeSourcePackedAllocation.returned cost pre length b c d e f g dest x y tail).memory.readWithPadding
      (NativeSourceSecondPayload.output length d e).toNat
      (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat =
      pre.memory.extract c.toNat
        (c.toNat + (NativeSourceSecondPayload.amount cost pre length b c d e f g dest x y tail).toNat) := by
  rw [zero, read_zero, extract_zero]

end Compiler.Proofs.IRGeneration.NativeSourceEmptyPayload
