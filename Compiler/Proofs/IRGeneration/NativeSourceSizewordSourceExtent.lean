import Compiler.Proofs.IRGeneration.NativeSourceSizewordNatural

namespace Compiler.Proofs.IRGeneration.NativeSourceSizewordSourceExtent
open EvmYul

theorem source_extent (machine : MachineState) (finish base source : UInt256)
    (value : machine.lookupMemory base = (finish - base) + UInt256.lnot (UInt256.ofNat 31))
    (ordered : base.toNat + 32 ≤ finish.toNat)
    (sourceValue : source.toNat = base.toNat + 32)
    (inside : finish.toNat ≤ machine.memory.size) :
    source.toNat + (machine.lookupMemory base).toNat ≤ machine.memory.size := by
  rw [value, sourceValue]
  rw [NativeSourceSizewordNatural.source_end finish base ordered]
  exact inside

theorem length_bound (machine : MachineState) (finish base : UInt256)
    (value : machine.lookupMemory base = (finish - base) + UInt256.lnot (UInt256.ofNat 31))
    (ordered : base.toNat + 32 ≤ finish.toNat) (bounded : finish.toNat < 2 ^ 64) :
    (machine.lookupMemory base).toNat < 2 ^ 64 := by
  rw [value, NativeSourceSizewordNatural.length_value finish base ordered]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceSizewordSourceExtent
