import Compiler.Proofs.IRGeneration.NativeSourcePointerActive

namespace Compiler.Proofs.IRGeneration.NativeSourceContextLength
open EvmYul

abbrev returned := NativeSourceFieldsAllocation.returned

theorem lookup (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (p q r s t u v w : UInt256) (rest : Stack UInt256)
    (carrier : u.toNat < (returned cost pre a b c d e f g h i j k tail).memory.size)
    (active : ¬u ≥ (returned cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩) :
    NativeSourceDecodedCopyProvenance.length cost (returned cost pre a b c d e f g h i j k tail)
      p q r s t u v w rest =
      (returned cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory u := by
  exact NativeSourceActiveLength.allocated_length cost _ p q r s t u v w rest carrier
    (NativeSourcePointerActive.context_allocated cost pre a b c d e f g h i j k tail) active

end Compiler.Proofs.IRGeneration.NativeSourceContextLength
