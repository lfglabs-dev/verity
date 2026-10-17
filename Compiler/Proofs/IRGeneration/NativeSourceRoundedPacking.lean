import Compiler.Proofs.IRGeneration.NativeSourceRoundedSecondCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceRoundedPacking
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def rounded (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  NativeSourceRoundedSecondCopy.rounded cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632) :
    run fuel cost 27 (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) = .ok (rounded cost pre a b c d e f g h tail) := by
  exact NativeSourceRoundedSecondCopy.execute cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail fuel code
    (NativeSourcePackingCopies.entry_pc cost pre a b c d e f g h tail pc) (NativeSourcePackingCopies.entry_stack cost pre a b c d e f g h tail)

theorem execute (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 42 pre = .ok (rounded cost pre a b c d e f g h tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 15 27 pre _ _
    (NativeSourceDecodedPackingStart.execute fuel cost pre a b c d e f g h tail code pc stack)
    (second cost pre a b c d e f g h tail fuel code pc)

end Compiler.Proofs.IRGeneration.NativeSourceRoundedPacking
