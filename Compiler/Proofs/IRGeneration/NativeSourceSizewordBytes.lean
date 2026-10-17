import Compiler.Proofs.IRGeneration.NativeSourceGuardedContextLookup

namespace Compiler.Proofs.IRGeneration.NativeSourceSizewordBytes
open EvmYul

theorem stored_bytes (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256)
    (tail : Stack UInt256)
    (padding : f.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFieldRoundingStore.s4 cost pre mask size a b c d e f g tail).memory.readWithPadding f.toNat 32 =
      (size + mask).toByteArray := by
  have bytes := NativeSourcePointerBytes.stored_word
    (EVM.Proof.stepPre cost (NativeSourceFieldRoundingStore.s3 cost pre mask size a b c d e f g tail)).toMachineState
    f (size + mask)
  apply bytes
  change f.toNat - (NativeSourceFieldRoundingStore.s3 cost pre mask size a b c d e f g tail).memory.size < _
  rw [NativeSourceSizeMemoryFrame.shuffle_memory]
  exact padding

theorem sized_bytes (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256)
    (padding : h.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).memory.readWithPadding h.toNat 32 =
      ((a - b) + UInt256.lnot (UInt256.ofNat 31)).toByteArray := by
  have bytes := stored_bytes cost (NativeSourceFieldSize.ready cost pre a b c d e f g h i tail)
    (UInt256.lnot (UInt256.ofNat 31)) (a - b) c d e f g h i tail
  apply bytes
  rw [NativeSourceSizeMemoryFrame.ready_memory]
  exact padding

theorem context_bytes (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding j.toNat 32 =
      ((b - c) + UInt256.lnot (UInt256.ofNat 31)).toByteArray := by
  exact sized_bytes cost _ b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0 :: tail) padding

end Compiler.Proofs.IRGeneration.NativeSourceSizewordBytes
