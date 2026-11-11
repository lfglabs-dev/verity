import Compiler.SolidityImport.Import

/-!
`collectUnsupported` survey mode (issue #2621) on `CollectUnsupportedSurvey.sol`.

* With the flag, every construct `first` and `second` reach is recorded with its
  source position, AST node kind, reason and closure path (`first -> scaled`),
  the command succeeds, and only `report` is defined.
* Without it, the same import fails at the first construct, with the
  diagnostic of the first-failure importer.
* With the flag and no failure, model and report equal the flag-off import,
  on `read()` and on two richer existing fixtures.
* On `CollectUnsupportedRootBoundary.sol`: two roots with the same name are
  rejected as without the flag, in either order; an unsupported parameter or
  return type gives exactly one entry for its root.
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

/-- error: Unknown identifier `collected.sourceDigest` -/
#guard_msgs in
example : String := collected.sourceDigest

-- `read` is importable, but no accessor is emitted for it either (the
-- flag-off `strictRead` import below defines `strictRead.read`).
/-- error: Unknown identifier `collected.read` -/
#guard_msgs in
example := collected.read

-- Rollback isolation: the unsupported roots and their inlined helper `scaled`
-- are not in the closure; only the importable `read` is.
#guard collected.report.includedFunctions.map (·.name) == ["read"]

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

-- The flag-off import defines what the survey above withholds.
example : String := strictRead.sourceDigest
example := @strictRead.read

/-! With the flag and no failure, richer imports are unchanged too: locals,
storage effects, `emit`, `require`, nested loops in an inlined helper
(`HelperLoopSequence`), and modifiers with arguments, `unchecked` blocks,
struct and mapping writes and an internal call to a public function
(`ModifierUncheckedCompoundSequence`). -/

solidity_import surveyedLoop from "Contracts/SolidityImportSmoke" entry "HelperLoopSequence.sol"
  using survey
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()

solidity_import strictLoop from "Contracts/SolidityImportSmoke" entry "HelperLoopSequence.sol"
  using strict
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()

#guard toString (repr surveyedLoop.model) == toString (repr strictLoop.model)
#guard surveyedLoop.report == strictLoop.report

solidity_import surveyedModifier from "Contracts/SolidityImportSmoke"
  entry "ModifierUncheckedCompoundSequence.sol"
  using survey
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()

solidity_import strictModifier from "Contracts/SolidityImportSmoke"
  entry "ModifierUncheckedCompoundSequence.sol"
  using strict
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()

#guard toString (repr surveyedModifier.model) == toString (repr strictModifier.model)
#guard surveyedModifier.report == strictModifier.report

/-! Two roots with the same name (the overloads `pick(uint256)`, whose body is
unsupported, and `pick(address)`) are a root list error. The survey rejects
them as the flag-off import does, in either order: an unsupported earlier root
is rolled back, but its name still counts. -/

/--
error: CollectUnsupportedRootBoundary.sol:13:5: FunctionDefinition: [solidity-import:unsupported] root function name collision: CollectUnsupportedRootBoundary.pick; import overloaded roots in separate slices
closure:
function pick(address) external view returns (uint256) {
        return total;
    }
-/
-- `lax`: the closure line is empty here (the rolled-back `pick(uint256)` left
-- no call stack), and `#guard_msgs` would otherwise need a trailing space.
#guard_msgs (whitespace := lax) in
solidity_import pickedUnsupportedFirst from "Contracts/SolidityImportSmoke"
  entry "CollectUnsupportedRootBoundary.sol"
  using survey
  contract CollectUnsupportedRootBoundary
  function pick(uint256)
  function pick(address)

/--
error: CollectUnsupportedRootBoundary.sol:8:5: FunctionDefinition: [solidity-import:unsupported] root function name collision: CollectUnsupportedRootBoundary.pick; import overloaded roots in separate slices
closure: CollectUnsupportedRootBoundary.pick
function pick(uint256 x) external returns (uint256) {
        do { x += 1; } while (x < 10);
        total = x;
-/
#guard_msgs in
solidity_import pickedSupportedFirst from "Contracts/SolidityImportSmoke"
  entry "CollectUnsupportedRootBoundary.sol"
  using survey
  contract CollectUnsupportedRootBoundary
  function pick(address)
  function pick(uint256)

/--
error: CollectUnsupportedRootBoundary.sol:8:5: FunctionDefinition: [solidity-import:unsupported] root function name collision: CollectUnsupportedRootBoundary.pick; import overloaded roots in separate slices
closure: CollectUnsupportedRootBoundary.pick
function pick(uint256 x) external returns (uint256) {
        do { x += 1; } while (x < 10);
        total = x;
-/
#guard_msgs in
solidity_import pickedStrict from "Contracts/SolidityImportSmoke"
  entry "CollectUnsupportedRootBoundary.sol"
  using strict
  contract CollectUnsupportedRootBoundary
  function pick(address)
  function pick(uint256)

/-! A failure at the root boundary (an unsupported parameter or return type)
gives exactly one entry for the root: its body, which also has an unsupported
`do`-`while`, is not lowered. -/

/--
warning: collectUnsupported: 2 of 3 roots unsupported; no model, theorem or accessor is emitted, and an unsupported root proves nothing
status narrowKey unsupported constructs 1 denoteCovered false compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)
  CollectUnsupportedRootBoundary.sol:16:24 VariableDeclaration: unsupported parameter type bytes2 (closure CollectUnsupportedRootBoundary.narrowKey)
status narrowResult unsupported constructs 1 denoteCovered false compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)
  CollectUnsupportedRootBoundary.sol:20:56 VariableDeclaration: unsupported named root return type bytes2 (closure CollectUnsupportedRootBoundary.narrowResult)
-/
#guard_msgs in
solidity_import boundary from "Contracts/SolidityImportSmoke"
  entry "CollectUnsupportedRootBoundary.sol"
  using survey
  contract CollectUnsupportedRootBoundary
  function narrowKey(bytes2)
  function narrowResult(uint256)
  function read()

#guard boundary.report.functions.map (fun f => (f.function, f.unsupported.length)) ==
  [("narrowKey", 1), ("narrowResult", 1), ("read", 0)]

end SolidityImportSmoke.CollectUnsupportedSurveyChecks
