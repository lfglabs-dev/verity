import Compiler.SolidityImport.Import

/-!
Messages of `solcBinaryProblem?`, the importer's check of its pinned solc binary.
A missing binary (a worktree whose `.lake` was copied without `solidity-import/`)
must say so and name the setup command, not report a checksum mismatch.
-/

namespace Compiler.CompilationModel.SolidityImport.SolcBinaryCheckTest

open Compiler.CompilationModel.SolidityImport

private def pinned : Array String := #["aa", "bb"]

-- Missing binary: "not installed", the path, and the setup command; never "checksum mismatch".
#guard (solcBinaryProblem? "solc-0.8.34" "/w/.lake/solidity-import/solc-0.8.34" false 1 "" pinned).any
  fun m => (m.splitOn "is not installed at /w/.lake/solidity-import/solc-0.8.34").length > 1 &&
    (m.splitOn "scripts/setup_solc_import.py --all").length > 1 &&
    (m.splitOn "checksum mismatch").length == 1

-- Installed but not hashable.
#guard (solcBinaryProblem? "solc-0.8.34" "/p" true 2 "" pinned).any
  fun m => (m.splitOn "cannot compute the SHA-256 of /p").length > 1

-- Installed with a foreign digest: a real checksum mismatch, with the digest found.
#guard (solcBinaryProblem? "solc-0.8.34" "/p" true 0 "cc" pinned).any
  fun m => (m.splitOn "compiler checksum mismatch: /p has SHA-256 cc").length > 1

-- Installed with a pinned digest: no problem.
#guard (solcBinaryProblem? "solc-0.8.34" "/p" true 0 "bb" pinned).isNone

end Compiler.CompilationModel.SolidityImport.SolcBinaryCheckTest
