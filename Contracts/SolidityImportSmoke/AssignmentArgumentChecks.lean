import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
`x++`, `--m[k]` and `x = v` as internal call and `abi.encode` arguments
(`AssignmentArgumentSequence.sol`, `AssignmentArgumentRejections.sol`).

Both solc 0.8.34 pipelines evaluate these arguments left to right, each write at its own
position. Direct internal calls bind every scalar argument there (`lowerCallArgs`
`sequence`); an all-static `abi.encode` becomes ordered (`lowerAbiEncodeArgs`). The forms
below stay located rejections.
-/
namespace SolidityImportSmoke.AssignmentArgumentChecks

solidity_profile assignmentArguments where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile assignmentArgumentsLegacy where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

-- 0. The positive fixture also imports under the legacy pipeline (same left-to-right order).
solidity_import legacyForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentSequence.sol"
  using assignmentArgumentsLegacy
  contract SequenceFixture
  function change(uint256)
  function read()

-- 1. `x++` beside a dynamic (`bytes`) `abi.encode` argument: not ordered.
/--
error: AssignmentArgumentRejections.sol:11:43: UnaryOperation: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: DynamicC.digest
n++
-/
#guard_msgs in
solidity_import dynamicForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract DynamicC
  function digest(bytes)

-- 2. A hashed assignment encoding inside a non-ordered (dynamic) `abi.encode`, whose scalar
-- siblings are read while encoding (`assignmentAbiEncodeIn`).
/--
error: AssignmentArgumentRejections.sol:19:43: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: HashedDynamicC.digest
keccak256(abi.encode(n++))
-/
#guard_msgs in
solidity_import hashedDynamicForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract HashedDynamicC
  function digest(bytes)

-- 3. An assignment encoding as a `bytes.concat` argument (walked last to first).
/--
error: AssignmentArgumentRejections.sol:27:39: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: ConcatC.digest
abi.encode(n++)
-/
#guard_msgs in
solidity_import concatForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract ConcatC
  function digest(uint256)

-- 4. `x++` directly in `abi.encodePacked`.
/--
error: AssignmentArgumentRejections.sol:35:46: UnaryOperation: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: PackedC.digest
n++
-/
#guard_msgs in
solidity_import packedForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract PackedC
  function digest(uint256)

-- 5. `m[k] = v` as an `abi.encode` argument (only identifier targets are assignment expressions).
/--
error: AssignmentArgumentRejections.sol:43:43: Assignment: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: MappingAssignC.digest
m[x] = 9
-/
#guard_msgs in
solidity_import mappingAssignForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract MappingAssignC
  function digest(uint256)

-- 6. A compound assignment expression as an `abi.encode` argument.
/--
error: AssignmentArgumentRejections.sol:51:40: Assignment: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: CompoundC.digest
n += x
-/
#guard_msgs in
solidity_import compoundForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract CompoundC
  function digest(uint256)

-- 7. A struct beside `x++` in `abi.encode`: solc reads the struct only while encoding.
/--
error: AssignmentArgumentRejections.sol:61:37: Identifier: [solidity-import:unsupported] struct ABI encoding argument beside a state-changing argument is unsupported
closure: StructC.digest
pair
-/
#guard_msgs in
solidity_import structForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract StructC
  function digest(uint256)

-- 8. `m[k] = v` as an internal call argument.
/--
error: AssignmentArgumentRejections.sol:72:26: Assignment: [solidity-import:unsupported] assignment expression in multi-argument call requires explicit evaluation-order support
closure: CallMappingAssignC.digest
m[x] = 9
-/
#guard_msgs in
solidity_import callMappingAssignForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract CallMappingAssignC
  function digest(uint256)

-- 9. `m[x + 1]++` (a computed key) as an internal call argument.
/--
error: AssignmentArgumentRejections.sol:83:23: UnaryOperation: [solidity-import:unsupported] assignment expression in multi-argument call requires explicit evaluation-order support
closure: CallComputedKeyC.digest
m[x + 1]++
-/
#guard_msgs in
solidity_import callComputedKeyForm from "Contracts/SolidityImportSmoke"
  entry "AssignmentArgumentRejections.sol"
  using assignmentArguments
  contract CallComputedKeyC
  function digest(uint256)

end SolidityImportSmoke.AssignmentArgumentChecks
