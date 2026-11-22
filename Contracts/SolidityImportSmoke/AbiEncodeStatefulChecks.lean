import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
State-changing helper calls as `abi.encode*` arguments (`AbiEncodeStatefulSequence.sol`,
`AbiEncodeStatefulRejections.sol`).

Only plain `abi.encode` with an all-static argument list evaluates such arguments in
order (`lowerAbiEncodeArgs` with `orderedEffects`). The other encoding forms, dynamic and
struct arguments beside a helper, and external calls stay located rejections.
-/
namespace SolidityImportSmoke.AbiEncodeStatefulChecks

solidity_profile statefulEncoding where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile statefulEncodingLegacy where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

-- 0. The positive fixture also imports under the legacy pipeline (same left-to-right order).
solidity_import legacyForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulSequence.sol"
  using statefulEncodingLegacy
  contract SequenceFixture
  function change(uint256)
  function read()

-- 1. `abi.encodePacked` with a state-changing argument.
/--
error: AbiEncodeStatefulRejections.sol:28:46: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: PackedC.digest
_bump()
-/
#guard_msgs in
solidity_import packedForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract PackedC
  function digest(uint256)

-- 2. `abi.encodeWithSelector` with a state-changing argument.
/--
error: AbiEncodeStatefulRejections.sol:34:83: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: SelectorC.digest
_bump()
-/
#guard_msgs in
solidity_import selectorForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract SelectorC
  function digest(uint256)

-- 3. `abi.encode` with a dynamic (`bytes`) argument beside a state-changing one.
/--
error: AbiEncodeStatefulRejections.sol:40:46: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: DynamicC.digest
_bump()
-/
#guard_msgs in
solidity_import dynamicForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract DynamicC
  function digest(uint256)

-- 4. `abi.encode` with a struct argument beside a state-changing one: solc reads the struct
-- only while encoding, after the helper has run.
/--
error: AbiEncodeStatefulRejections.sol:46:49: Identifier: [solidity-import:unsupported] struct ABI encoding argument beside a state-changing argument is unsupported
closure: StructC.digest
pair
-/
#guard_msgs in
solidity_import structForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract StructC
  function digest(uint256)

-- 5. An external call among the arguments of an ordered `abi.encode`.
/--
error: AbiEncodeStatefulRejections.sol:54:46: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: ExternalC.digest
target.poke(x)
-/
#guard_msgs in
solidity_import externalForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract ExternalC
  function digest(uint256)

-- 6. An ordered `abi.encode` hashed inside `abi.encodePacked`.
/--
error: AbiEncodeStatefulRejections.sol:60:43: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: NestedPackedC.digest
keccak256(abi.encode(_bump()))
-/
#guard_msgs in
solidity_import nestedPackedForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract NestedPackedC
  function digest(uint256)

-- 7. An ordered `abi.encode` as an unhashed `bytes.concat` argument (walked last to first).
/--
error: AbiEncodeStatefulRejections.sol:66:39: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: ConcatC.digest
abi.encode(_bump())
-/
#guard_msgs in
solidity_import concatForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract ConcatC
  function digest(uint256)

-- 8. An ordered `abi.encode` as an unhashed `abi.encodePacked` argument beside another one.
/--
error: AbiEncodeStatefulRejections.sol:72:43: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: PackedEncodeC.digest
abi.encode(_bump())
-/
#guard_msgs in
solidity_import packedEncodeForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStatefulRejections.sol"
  using statefulEncoding
  contract PackedEncodeC
  function digest(uint256)

end SolidityImportSmoke.AbiEncodeStatefulChecks
