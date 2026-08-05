import Verity.Core.Model.DenoteMemory

/-! A minimal byte-precise `mstore`/`mload` proof. -/

namespace Contracts.Examples.DenoteMemory

open Compiler.CompilationModel.DenoteMemory

def exampleWord : Word := fun index => ⟨index + 1, by omega⟩

/-- After storing a word at zero, every byte read by the following `mload` is
the corresponding byte of the stored word. -/
theorem mstore_mload_postcondition (index : Fin 32) :
    (Memory.empty.writeWord 0 exampleWord).readWord 0 index = exampleWord index := by
  rw [Memory.readWord, Memory.readByte, if_pos]
  · exact Memory.writeWord_at Memory.empty 0 exampleWord index
  · simp [Memory.writeWord, Memory.expand, expandedLength, Memory.empty]

/-- The worked program also exposes the expected expanded memory extent. -/
theorem mstore_expands_one_word :
    (Memory.empty.writeWord 0 exampleWord).size = 32 := by
  decide

end Contracts.Examples.DenoteMemory
