import Compiler.Proofs.IRGeneration.NativeSourceSizedSecondCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceSizedPacking
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def sized (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  NativeSourceSizedSecondCopy.sized cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632) :
    run fuel cost 21 (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) = .ok (sized cost pre a b c d e f g h tail) := by
  exact NativeSourceSizedSecondCopy.execute cost (NativeSourceDecodedPackingStart.copied cost pre a b c d e f g h tail) (NativeSourcePreludeCopy.length cost (NativeSourceFreePointer.loaded cost pre) (NativeSourceDecodedPackingStart.free cost pre) a b c d e f g h tail) e a b (NativeSourceDecodedPackingStart.free cost pre) d (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail fuel code
    (NativeSourcePackingCopies.entry_pc cost pre a b c d e f g h tail pc) (NativeSourcePackingCopies.entry_stack cost pre a b c d e f g h tail)

theorem compose (fuel cost left right : Nat) (pre middle final : EVM.State)
    (first : run fuel cost left pre = .ok middle)
    (last : run fuel cost right middle = .ok final) :
    run fuel cost (left + right) pre = .ok final := by
  rw [run_add, first]
  exact last

theorem execute (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 36 pre = .ok (sized cost pre a b c d e f g h tail) := by
  exact compose fuel cost 15 21 pre _ _
    (NativeSourceDecodedPackingStart.execute fuel cost pre a b c d e f g h tail code pc stack)
    (second cost pre a b c d e f g h tail fuel code pc)

end Compiler.Proofs.IRGeneration.NativeSourceSizedPacking
