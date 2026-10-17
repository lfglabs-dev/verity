import Compiler.Proofs.IRGeneration.NativeSourceBoundedFirstPayload

namespace Compiler.Proofs.IRGeneration.NativeSourceDecodedCopyProvenance
open EvmYul

abbrev free := NativeSourceDecodedPackingStart.free
abbrev length (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :=
  NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre)
    (free cost pre) a b c d e f g h tail

theorem free_value (cost : Nat) (pre : EVM.State) :
    free cost pre = pre.toMachineState.lookupMemory (UInt256.ofNat 64) := by
  rfl

theorem length_value (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    length cost pre a b c d e f g h tail = (NativeSourceFreePointer.loaded cost pre).toMachineState.lookupMemory f := by
  rfl

theorem entry_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (NativeSourcePreludeCopy.entry cost cost (NativeSourceFreePointer.loaded cost pre)
      (free cost pre) a b c d e f g h tail).memory = pre.memory := by
  rfl

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (bounded : (length cost pre a b c d e f g h tail).toNat < 2 ^ 64)
    (sourceInside : c.toNat + (length cost pre a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (free cost pre + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail).memory.readWithPadding
      (free cost pre + b).toNat (length cost pre a b c d e f g h tail).toNat =
      pre.memory.extract c.toNat (c.toNat + (length cost pre a b c d e f g h tail).toNat) := by
  by_cases zero : (length cost pre a b c d e f g h tail).toNat = 0
  · rw [zero, NativeSourceEmptyPayload.read_zero, NativeSourceEmptyPayload.extract_zero]
  · exact NativeSourcePreludeCopy.bytes cost cost cost cost cost cost
      (NativeSourceFreePointer.loaded cost pre) (free cost pre) a b c d e f g h tail
      (show 0 < (length cost pre a b c d e f g h tail).toNat from Nat.pos_of_ne_zero zero)
      bounded sourceInside padding

end Compiler.Proofs.IRGeneration.NativeSourceDecodedCopyProvenance
