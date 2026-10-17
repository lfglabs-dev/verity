import Verity.Core.Model.Create2Operation

namespace Compiler.Proofs.IRGeneration.CreationMemoryExpansion
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory

/-- Expanding caller memory retains every old readable byte and exposes zeroes.
The original total bytes function is never trusted beyond its active extent. -/
theorem expand_read (memory : Memory) (endOffset query : Nat) :
    (memory.expand endOffset).readByte query = memory.readByte query := by
  unfold Memory.expand Memory.readByte
  by_cases inside : query < memory.size
  · have expanded : query < max memory.size (expandedLength endOffset) :=
      Nat.lt_of_lt_of_le inside (Nat.le_max_left _ _)
    simp only [expanded, inside, if_true]
  · simp only [inside, if_false]
    split <;> rfl

/-- CREATE2 preparation expansion preserves the independently supplied slice. -/
theorem return_read (memory : Memory) (offset size query : Nat) :
    (MidnightInitcode.returnMemory memory offset size).readByte query =
      memory.readByte query := by
  unfold MidnightInitcode.returnMemory
  split
  · rfl
  · exact expand_read memory (offset + size) query

/-- No native postmemory is needed to derive bytes after caller expansion. -/
theorem return_code (world : Verity.ContractState) (offset size : Nat) :
    Create2.physicalInitcodeBytes
        (world.installPhysicalMemory (MidnightInitcode.returnMemory world.byteMemory offset size))
        offset size = Create2.physicalInitcodeBytes world offset size := by
  apply congrArg (fun values : List UInt8 => (⟨values.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro index _
  exact congrArg (fun byte : Byte => UInt8.ofNat byte.val)
    (return_read world.byteMemory offset size (offset + index))

end Compiler.Proofs.IRGeneration.CreationMemoryExpansion
