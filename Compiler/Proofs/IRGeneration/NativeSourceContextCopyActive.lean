import Compiler.Proofs.IRGeneration.NativeSourceDecodedCopyActive

namespace Compiler.Proofs.IRGeneration.NativeSourceContextCopyActive
open EvmYul NativeSourceContextCopy

theorem copied_bound (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64)
    (lengthAddress : k.toNat < 2 ^ 64)
    (destBound : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat < 2 ^ 64)
    (sourceBound : i.toNat < 2 ^ 64)
    (countBound : (length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64) :
    (copied cost pre a b c d e f g h i j k z tail).activeWords.toNat < 2 ^ 251 := by
  obtain ⟨d1, d2, d3, d4⟩ := NativeSourceFieldAddressBounds.field_bounds c fields
  have sized := NativeSourceSizeFieldExtent.all_fields_bound cost pre a b c d e f g h i j k
    (z :: tail) upper sd se sf sg d1 d2 d3 d4 sizeAddress
  have returned := NativeSourceAllocatorExtent.context_bound cost pre a b c d e f g h i j k
    (z :: tail) sized
  exact NativeSourceDecodedCopyActive.copied_bound cost _ h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0) z tail returned lengthAddress destBound sourceBound countBound

end Compiler.Proofs.IRGeneration.NativeSourceContextCopyActive
