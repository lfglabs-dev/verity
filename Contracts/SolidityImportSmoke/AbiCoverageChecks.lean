import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.AbiRootLowering

namespace SolidityImportSmoke.AbiCoverageChecks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport

def schema : List AbiSchema.Member :=
  [.scalar ⟨"head", .uint ⟨31, by decide⟩⟩,
   .scalar ⟨"origin", .address⟩,
   .scalar ⟨"token", .address⟩,
   .structArray "items"
     [⟨"token", .address⟩, ⟨"weight", .uint ⟨31, by decide⟩⟩,
      ⟨"cursor", .uint ⟨31, by decide⟩⟩, ⟨"source", .address⟩],
   .scalar ⟨"deadline", .uint ⟨31, by decide⟩⟩,
   .scalar ⟨"threshold", .uint ⟨31, by decide⟩⟩,
   .scalar ⟨"firstGate", .address⟩,
   .scalar ⟨"secondGate", .address⟩]

theorem memory_root_is_executable :
    executableStmtListCovered (AbiRootLowering.root "source" 2 0 schema true).body = true := by
  decide +kernel

theorem calldata_root_is_executable :
    executableStmtListCovered (AbiRootLowering.root "source" 2 0 schema false).body = true := by
  decide +kernel

def envelopeSchema : List AbiSchema.Member :=
  [.nestedStruct "record" 0 "NestedRecord" [] schema,
   .scalar ⟨"flag", .bool⟩,
   .scalar ⟨"sender", .address⟩,
   .bytesField "payload",
   .scalar ⟨"maxUnits", .uint ⟨15, by decide⟩⟩]

theorem envelope_memory_root_is_executable :
    executableStmtListCovered
      (AbiRootLowering.root "envelope" 2 0 envelopeSchema true).body = true := by
  decide +kernel

theorem envelope_calldata_root_is_executable :
    executableStmtListCovered
      (AbiRootLowering.root "envelope" 2 0 envelopeSchema false).body = true := by
  decide +kernel

theorem memory_write_is_not_read_only :
    stmtCovered (.mstore (.literal 64) (.literal 128)) = false := by rfl

theorem loop_is_not_read_only :
    stmtCovered (.forEach "i" (.literal 1) [.mstore (.literal 0) (.literal 1)]) = false := by rfl

theorem early_exit_loop_is_not_read_only :
    stmtCovered
      (.forEachWhile "i" (.literal 1) (.literal 1) [.mstore (.literal 0) (.literal 1)]) = false := by
  rfl

theorem early_exit_loop_is_executable :
    executableStmtCovered
      (.forEachWhile "i" (.param "n") (.eq (.localVar "flag") (.literal 0))
        [.setStorage "hits" (.add (.storage "hits") (.literal 1))]) = true := by rfl

theorem early_exit_loop_preserves_abi_header :
    abiHeaderPreservingStmt
      (.forEachWhile "i" (.param "n") (.lt (.localVar "flag") (.literal 2))
        [.setStorage "hits" (.add (.storage "hits") (.literal 1))]) = true := by rfl

end SolidityImportSmoke.AbiCoverageChecks
