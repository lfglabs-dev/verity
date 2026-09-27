import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.AbiRootLowering

namespace SolidityImportSmoke.AbiCoverageChecks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport

def schema : List AbiSchema.Member :=
  [.scalar ⟨"chainId", .uint ⟨31, by decide⟩⟩,
   .scalar ⟨"midnight", .address⟩,
   .scalar ⟨"loanToken", .address⟩,
   .structArray "collateralParams"
     [⟨"token", .address⟩, ⟨"lltv", .uint ⟨31, by decide⟩⟩,
      ⟨"liquidationCursor", .uint ⟨31, by decide⟩⟩, ⟨"oracle", .address⟩],
   .scalar ⟨"maturity", .uint ⟨31, by decide⟩⟩,
   .scalar ⟨"rcfThreshold", .uint ⟨31, by decide⟩⟩,
   .scalar ⟨"enterGate", .address⟩,
   .scalar ⟨"liquidatorGate", .address⟩]

theorem memory_root_is_executable :
    executableStmtListCovered (AbiRootLowering.root "source" 2 0 schema true).body = true := by
  decide +kernel

theorem calldata_root_is_executable :
    executableStmtListCovered (AbiRootLowering.root "source" 2 0 schema false).body = true := by
  decide +kernel

theorem memory_write_is_not_read_only :
    stmtCovered (.mstore (.literal 64) (.literal 128)) = false := by rfl

theorem loop_is_not_read_only :
    stmtCovered (.forEach "i" (.literal 1) [.mstore (.literal 0) (.literal 1)]) = false := by rfl

end SolidityImportSmoke.AbiCoverageChecks
