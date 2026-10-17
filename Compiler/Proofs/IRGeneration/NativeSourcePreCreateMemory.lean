import Compiler.Proofs.IRGeneration.NativeSourcePayloadReturn

namespace Compiler.Proofs.IRGeneration.NativeSourcePreCreateMemory
open EvmYul

theorem original (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (NativeSourcePreCreate.ready cost pre a b c d e f g h tail).memory =
      (NativeSourceOriginalAllocation.returned cost pre a b c d e f g h tail).memory := by
  unfold NativeSourcePreCreate.ready
  exact NativeSourcePackedReturnFrame.operands_memory cost _ _ _ g h tail

end Compiler.Proofs.IRGeneration.NativeSourcePreCreateMemory
