import Compiler.Proofs.IRGeneration.NativeSourceAllocatedWindowFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceCopyProvenance
open EvmYul

theorem extract_of_read (before after : ByteArray) (source size : Nat)
    (positive : 0 < size) (bounded : size < 2 ^ 64)
    (beforeInside : source + size ≤ before.size) (afterInside : source + size ≤ after.size)
    (preserved : after.readWithPadding source size = before.readWithPadding source size) :
    after.extract source (source + size) = before.extract source (source + size) := by
  rw [ByteArray.readWithPadding_eq_extract after source size positive bounded afterInside,
    ByteArray.readWithPadding_eq_extract before source size positive bounded beforeInside] at preserved
  exact preserved

theorem readback_original (before after : ByteArray) (dest source size : Nat)
    (positive : 0 < size) (bounded : size < 2 ^ 64)
    (beforeInside : source + size ≤ before.size) (afterInside : source + size ≤ after.size)
    (padding : dest - after.size < 2 ^ System.Platform.numBits)
    (preserved : after.readWithPadding source size = before.readWithPadding source size) :
    (after.write source after dest size).readWithPadding dest size =
      before.extract source (source + size) := by
  rw [NativeSourceMcopyGrowth.readback after dest source size positive bounded afterInside padding]
  exact extract_of_read before after source size positive bounded beforeInside afterInside preserved

end Compiler.Proofs.IRGeneration.NativeSourceCopyProvenance
