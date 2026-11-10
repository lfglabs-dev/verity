import Compiler.SolidityImport.Import

/-!
`collectUnsupported` survey mode (issue #2621) on `CollectUnsupportedSurvey.sol`.

* With the flag, every construct `first` and `second` reach is recorded with its
  source position, AST node kind, reason and closure path (`first -> scaled`),
  the command succeeds, and only `report` is defined.
* Without it, the same import fails at the first construct, with the
  diagnostic of the first-failure importer.
* With the flag and no failure, model and report equal the flag-off import.
-/
namespace SolidityImportSmoke.CollectUnsupportedSurveyChecks
open Compiler.CompilationModel.SolidityImport

solidity_profile survey where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"
  collectUnsupported := true

solidity_profile strict where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

/--
warning: collectUnsupported: 2 of 3 roots unsupported; no model, theorem or accessor is emitted, and an unsupported root proves nothing
status first unsupported constructs 4 denoteCovered false compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)
  CollectUnsupportedSurvey.sol:12:26 Identifier: builtin call is outside this slice (closure CollectUnsupportedSurvey.first -> CollectUnsupportedSurvey.scaled)
  CollectUnsupportedSurvey.sol:13:20 Identifier: unresolved identifier 17 (closure CollectUnsupportedSurvey.first -> CollectUnsupportedSurvey.scaled) [possibly consequential: reads budget bound by a skipped statement]
  CollectUnsupportedSurvey.sol:17:9 DoWhileStatement: unsupported statement DoWhileStatement (closure CollectUnsupportedSurvey.first)
  CollectUnsupportedSurvey.sol:19:18 MemberAccess: unsupported block context member prevrandao (closure CollectUnsupportedSurvey.first)
status second unsupported constructs 2 denoteCovered false compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)
  CollectUnsupportedSurvey.sol:23:25 YulFunctionCall: unsupported Yul builtin gas (closure CollectUnsupportedSurvey.second)
  CollectUnsupportedSurvey.sol:24:9 TryStatement: unsupported statement TryStatement (closure CollectUnsupportedSurvey.second)
-/
#guard_msgs in
solidity_import collected from "Contracts/SolidityImportSmoke" entry "CollectUnsupportedSurvey.sol"
  using survey
  contract CollectUnsupportedSurvey
  function first(uint256)
  function second(uint256, address)
  function read()

/-- The `status` block of `report.toText` (the other lines carry digests). -/
def statusBlock (r : ImportReport) : String :=
  String.intercalate "\n" <| (r.toText.splitOn "\n").filter fun line =>
    line.startsWith "status " || line.startsWith "  "

/-- The exact `status` block of the survey report. -/
def expectedStatusBlock : String :=
  "status first unsupported constructs 4 denoteCovered false compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)\n" ++
  "  CollectUnsupportedSurvey.sol:12:26 Identifier: builtin call is outside this slice (closure CollectUnsupportedSurvey.first -> CollectUnsupportedSurvey.scaled)\n" ++
  "  CollectUnsupportedSurvey.sol:13:20 Identifier: unresolved identifier 17 (closure CollectUnsupportedSurvey.first -> CollectUnsupportedSurvey.scaled) [possibly consequential: reads budget bound by a skipped statement]\n" ++
  "  CollectUnsupportedSurvey.sol:17:9 DoWhileStatement: unsupported statement DoWhileStatement (closure CollectUnsupportedSurvey.first)\n" ++
  "  CollectUnsupportedSurvey.sol:19:18 MemberAccess: unsupported block context member prevrandao (closure CollectUnsupportedSurvey.first)\n" ++
  "status second unsupported constructs 2 denoteCovered false compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)\n" ++
  "  CollectUnsupportedSurvey.sol:23:25 YulFunctionCall: unsupported Yul builtin gas (closure CollectUnsupportedSurvey.second)\n" ++
  "  CollectUnsupportedSurvey.sol:24:9 TryStatement: unsupported statement TryStatement (closure CollectUnsupportedSurvey.second)\n" ++
  "status read importable denoteCovered true compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)"

#guard statusBlock collected.report == expectedStatusBlock

#guard collected.report.functions.map (·.denoteCovered) == [false, false, true]

-- Only `report` is defined: nothing downstream can use an unsupported import.
/-- error: Unknown identifier `collected.model` -/
#guard_msgs in
example : Compiler.CompilationModel.CompilationModel := collected.model

/-- error: Unknown identifier `collected.covered` -/
#guard_msgs in
example : Prop := collected.covered

/--
error: CollectUnsupportedSurvey.sol:17:9: DoWhileStatement: [solidity-import:unsupported] unsupported statement DoWhileStatement
closure: CollectUnsupportedSurvey.first
do { y += 1; } while (y < 10);
-/
#guard_msgs in
solidity_import firstFailure from "Contracts/SolidityImportSmoke" entry "CollectUnsupportedSurvey.sol"
  using strict
  contract CollectUnsupportedSurvey
  function first(uint256)
  function second(uint256, address)

solidity_import surveyedRead from "Contracts/SolidityImportSmoke" entry "CollectUnsupportedSurvey.sol"
  using survey
  contract CollectUnsupportedSurvey
  function read()

solidity_import strictRead from "Contracts/SolidityImportSmoke" entry "CollectUnsupportedSurvey.sol"
  using strict
  contract CollectUnsupportedSurvey
  function read()

#guard toString (repr surveyedRead.model) == toString (repr strictRead.model)
#guard surveyedRead.report == strictRead.report

end SolidityImportSmoke.CollectUnsupportedSurveyChecks
