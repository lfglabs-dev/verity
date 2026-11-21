import Compiler.SolidityImport.Import

/-!
Imports through Foundry's inferred remappings (issue #2835).

* `inferred-remappings/`: `foundry.toml` sets `libs = ["deps"]` and writes no remapping for
  `deps/dep`. `src/Entry.sol` imports `dep/DepMath.sol` (inferred `dep/=deps/dep/src/`, as
  `forge remappings` prints), which imports `./Bounds.sol` relatively, and `local/Scale.sol`
  through the written `local/=src/local/`. solc receives both remappings, and the report
  lists the inferred one.
* `inferred-remappings-unknown/`: the same import while a library (`deps/bad`) has a
  `foundry.toml` line the importer cannot check. Foundry would skip that library's config,
  so its inferred set is unknown here, and the import fails.
-/
namespace SolidityImportSmoke.InferredRemappingsChecks
open Compiler.CompilationModel.SolidityImport

solidity_import inferred from "Contracts/SolidityImportSmoke/inferred-remappings"
  entry "src/Entry.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract Entry
  function combined(uint256)

private def has (text needle : String) : Bool := (text.splitOn needle).length > 1

#guard inferred.report.inferredRemappings == ["dep/=deps/dep/src/"]
#guard has inferred.report.settingsJson "\"remappings\":[\"local/=src/local/\",\"dep/=deps/dep/src/\"]"
#guard has inferred.report.toText "\ninferred remapping dep/=deps/dep/src/\n"

/--
error: src/Entry.sol: import dep/DepMath.sol needs Foundry's inferred remapping dep/=deps/dep/src/, but the inferred set is unknown here (deps/bad/foundry.toml line 2 is not TOML this reader checks); write the remapping in remappings.txt
-/
#guard_msgs in
solidity_import unknown from "Contracts/SolidityImportSmoke/inferred-remappings-unknown"
  entry "src/Entry.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract Entry
  function twice(uint256)

end SolidityImportSmoke.InferredRemappingsChecks
