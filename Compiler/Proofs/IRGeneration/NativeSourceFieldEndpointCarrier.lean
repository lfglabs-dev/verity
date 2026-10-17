import Compiler.Proofs.IRGeneration.NativeSourceEntryContainedReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldEndpointCarrier
open EvmYul

theorem returned_extent (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (platform : 64 ≤ System.Platform.numBits)
    (fields : c.toNat + 288 < 2 ^ 64)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32) :
    c.toNat + 320 ≤ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.size := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have firstPadding := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  have p1 := NativeSourceFieldPadding.second_padding cost pre a b c d e f g h i j k tail (by omega) firstPadding
  have p2 := NativeSourceFieldPadding.third_padding cost pre a b c d e f g h i j k tail (by omega) p1
  have p3 := NativeSourceFieldPadding.fourth_padding cost pre a b c d e f g h i j k tail (by omega) p2
  have p4 := NativeSourceSizePadding.size_padding_from_first cost pre a b c d e f g h i j k tail
    (by omega) firstPadding sizeBelow
  have extent := NativeSourceSizePadding.fourth_extent cost pre a b c d e f g h i j k tail p3
  have growth := NativeSourceSizeCarrier.context_monotone cost pre a b c d e f g h i j k tail p4
  have offset := NativeSourceFieldGeometry.offset_toNat c 288 (by decide) (by omega)
  rw [offset] at extent
  rw [NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k tail (by omega)]
  omega

theorem endpoint_inside (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (platform : 64 ≤ System.Platform.numBits)
    (fields : c.toNat + 288 < 2 ^ 64)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (endpoint : b.toNat ≤ c.toNat + 320) :
    b.toNat ≤ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.size := by
  exact endpoint.trans (returned_extent cost pre a b c d e f g h i j k tail platform fields sizeBelow)

end Compiler.Proofs.IRGeneration.NativeSourceFieldEndpointCarrier
