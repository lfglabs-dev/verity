import Compiler.Proofs.IRGeneration.NativeSourceSeparatedReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceCopyLookupFrame
open EvmYul

theorem lookup (machine : MachineState) (dest source count query : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251)
    (destBound : dest.toNat < 2 ^ 64) (sourceBound : source.toNat < 2 ^ 64)
    (countBound : count.toNat < 2 ^ 64)
    (sourceInside : source.toNat + count.toNat ≤ machine.memory.size)
    (padding : dest.toNat - machine.memory.size < 2 ^ System.Platform.numBits)
    (inside : query.toNat + 32 ≤ machine.memory.size)
    (below : query.toNat + 32 ≤ dest.toNat)
    (active : ¬query ≥ machine.activeWords * ⟨32⟩) :
    (machine.mcopy dest source count).lookupMemory query = machine.lookupMemory query := by
  apply NativeSourceLookupFrame.lookup_eq
  · omega
  · have growth := NativeSourceCopyCarrierMonotone.write_monotone machine.memory
      dest.toNat source.toNat count.toNat sourceInside padding
    change query.toNat < (machine.memory.write source.toNat machine.memory dest.toNat count.toNat).size
    omega
  · exact active
  · exact NativeSourceCopyActiveExtent.guard_preserved machine dest source count query
      upper destBound sourceBound countBound active
  · exact NativeSourceTotalCopyFrame.read_below machine.memory dest.toNat source.toNat count.toNat
      query.toNat 32 sourceInside padding (by decide) (by decide) inside below

end Compiler.Proofs.IRGeneration.NativeSourceCopyLookupFrame
