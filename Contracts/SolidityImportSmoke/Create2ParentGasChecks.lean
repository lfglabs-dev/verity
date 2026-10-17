import Verity.Core.Model.Create2ParentGas

namespace SolidityImportSmoke.Create2ParentGasChecks
open Compiler.CompilationModel.Create2ParentGas

theorem zero_length_does_not_expand :
    resultingWords 10 (2^256 - 1) 0 = 10 := by decide

theorem insufficient_parent_gas :
    charge 32010 0 0 1 = .outOfGas := by decide

theorem exact_zero_length_cost :
    charge 32000 10 (2^256 - 1) 0 = .charged
      { memoryWords := 10, opcodeGas := 32000, childGas := 0, reservedGas := 0 } := by decide

theorem expanded_memory_and_eip150 :
    charge 100000 4 128 65 = .charged
      { memoryWords := 7, opcodeGas := 32033, childGas := 66906, reservedGas := 1061 } := by decide

theorem reject_excessive_child_refund :
    finish { memoryWords := 0, opcodeGas := 32000, childGas := 0, reservedGas := 0 } 1 =
      .error "CREATE2 child returned more gas than its allowance" := by simp [finish]

end SolidityImportSmoke.Create2ParentGasChecks
