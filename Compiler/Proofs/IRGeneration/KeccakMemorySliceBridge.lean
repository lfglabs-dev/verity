import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Keccak.MemorySlice

/-! The proof IR's `keccak256` model and the EDSL's (`Compiler.Keccak.MemorySlice.keccak`)
are the same function. -/

namespace Compiler.Proofs.IRGeneration

theorem abstractKeccakMemorySlice_eq_memorySlice :
    abstractKeccakMemorySlice = Compiler.Keccak.MemorySlice.keccak := by
  rfl

end Compiler.Proofs.IRGeneration
