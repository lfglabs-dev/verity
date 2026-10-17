import Compiler.Proofs.IRGeneration.NativeSourceSizedPaddingCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceBoundedPadding
open EvmYul

theorem padding_of_address (address size : Nat)
    (bounded : address < 2 ^ System.Platform.numBits) :
    address - size < 2 ^ System.Platform.numBits := by
  exact lt_of_le_of_lt (Nat.sub_le _ _) bounded

theorem field_padding (base : UInt256) (memory : ByteArray)
    (bounded : base.toNat + 192 < 2 ^ System.Platform.numBits)
    (fits : base.toNat + 192 < 2 ^ 256) :
    (base + UInt256.ofNat 192).toNat - memory.size < 2 ^ System.Platform.numBits := by
  rw [NativeSourceFieldGeometry.offset_toNat base 192 (by decide) fits]
  exact padding_of_address _ _ bounded

theorem copy_padding (base : UInt256) (memory : ByteArray)
    (bounded : base.toNat + 32 < 2 ^ System.Platform.numBits)
    (fits : base.toNat + 32 < 2 ^ 256) :
    (base + UInt256.ofNat 32).toNat - memory.size < 2 ^ System.Platform.numBits := by
  rw [NativeSourceFieldGeometry.offset_toNat base 32 (by decide) fits]
  exact padding_of_address _ _ bounded

end Compiler.Proofs.IRGeneration.NativeSourceBoundedPadding
