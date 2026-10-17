import Compiler.Proofs.IRGeneration.NativeSourceDecodedActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceContextActiveGuard
open EvmYul NativeSourceContextCopy

theorem copied_guard (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64)
    (lengthAddress : k.toNat < 2 ^ 64)
    (destBound : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat < 2 ^ 64)
    (sourceBound : i.toNat < 2 ^ 64)
    (countBound : (length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64) :
    ¬j ≥ (copied cost pre a b c d e f g h i j k z tail).activeWords * ⟨32⟩ := by
  obtain ⟨d1, d2, d3, d4⟩ := NativeSourceFieldAddressBounds.field_bounds c fields
  have first := NativeSourceFirstFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) upper sd d1
  have second := NativeSourceSecondFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) first se d2
  have third := NativeSourceThirdFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) second sf d3
  have fourth := NativeSourceFourthFieldExtent.stored_bound cost pre a b c d e f g h i j k (z :: tail) third sg d4
  have active := NativeSourceAllocatorActiveGuard.sizeword_guard cost pre a b c d e f g h i j k
    (z :: tail) fourth sizeAddress
  have sized := NativeSourceSizeFieldExtent.all_fields_bound cost pre a b c d e f g h i j k
    (z :: tail) upper sd se sf sg d1 d2 d3 d4 sizeAddress
  have returned := NativeSourceAllocatorExtent.context_bound cost pre a b c d e f g h i j k
    (z :: tail) sized
  exact NativeSourceDecodedActiveGuard.copied_guard cost _ h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0) z j tail returned lengthAddress destBound sourceBound countBound active

end Compiler.Proofs.IRGeneration.NativeSourceContextActiveGuard
