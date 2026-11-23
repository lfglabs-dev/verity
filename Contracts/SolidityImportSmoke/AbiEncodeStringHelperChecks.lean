import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
Pure or view helpers returning `string` / `bytes` as `abi.encode` arguments and root return
tuple components (`AbiEncodeStringHelperSequence.sol`, `AbiEncodeStringHelperRejections.sol`).

Such a helper may revert with a custom error: it runs at its own argument position, as both
solc pipelines evaluate the arguments left to right. A state-changing helper, a calldata
sibling, a storage sibling, a reverting scalar helper and a reverting multi-argument concat beside
it stay located rejections, as does a string literal as event data for a `bytesN` parameter.
-/
namespace SolidityImportSmoke.AbiEncodeStringHelperChecks

solidity_profile stringHelperEncoding where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile stringHelperEncodingLegacy where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

-- 0. The positive fixture also imports under the legacy pipeline (same left-to-right order).
solidity_import legacyForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperSequence.sol"
  using stringHelperEncodingLegacy
  contract SequenceFixture
  function change(uint256)
  function read()

-- 1. A state-changing `string` helper beside another argument.
/--
error: AbiEncodeStringHelperRejections.sol:34:37: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: StatefulStringC.digest
_countedName()
-/
#guard_msgs in
solidity_import statefulStringForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract StatefulStringC
  function digest(uint256)

-- 2. A reverting `string` helper beside a state-changing scalar helper.
/--
error: AbiEncodeStringHelperRejections.sol:40:49: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: StringBesideStatefulC.digest
_bump()
-/
#guard_msgs in
solidity_import besideStatefulForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract StringBesideStatefulC
  function digest(uint256)

-- 3. A reverting `string` helper beside a calldata argument, validated only while encoding.
/--
error: AbiEncodeStringHelperRejections.sol:46:37: Identifier: [solidity-import:unsupported] calldata ABI encoding argument beside a reverting helper is unsupported
closure: StringBesideCalldataC.digest
data
-/
#guard_msgs in
solidity_import besideCalldataForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract StringBesideCalldataC
  function digest(bytes)

-- 4. A reverting scalar helper beside a `string` helper.
/--
error: AbiEncodeStringHelperRejections.sol:52:49: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: StringBesideRevertingScalarC.digest
_checkedCount()
-/
#guard_msgs in
solidity_import besideRevertingScalarForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract StringBesideRevertingScalarC
  function digest(uint256)

-- 5. A multi-argument `string.concat` with a reverting argument beside other arguments: the
-- concat arguments are lowered last to first, solc evaluates them left to right.
/--
error: AbiEncodeStringHelperRejections.sol:58:40: FunctionCall: [solidity-import:unsupported] reverting concat ABI encoding argument beside other arguments is unsupported
closure: ConcatBesideC.digest
string.concat(_name(), _name())
-/
#guard_msgs in
solidity_import besideConcatForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract ConcatBesideC
  function digest(uint256)

-- 6. A storage `string` argument beside a reverting helper: solc reads it only while encoding.
/--
error: AbiEncodeStringHelperRejections.sol:64:37: Identifier: [solidity-import:unsupported] storage ABI encoding argument beside a reverting helper is unsupported
closure: StorageBesideC.digest
label
-/
#guard_msgs in
solidity_import besideStorageForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract StorageBesideC
  function digest(uint256)

-- 7. A string literal as event data for a `bytesN` parameter: the data is encoded by the
-- arguments' own types, where the literal is a dynamic `string`; solc encodes a static word.
/--
error: AbiEncodeStringHelperRejections.sol:74:21: Literal: [solidity-import:unsupported] string literal event data argument for a bytes1 parameter is unsupported
closure: EventLiteralFixedBytesC.tag
hex"0f"
-/
#guard_msgs in
solidity_import eventLiteralForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract EventLiteralFixedBytesC
  function tag(string)

-- 8. A string literal for a `bytesN` parameter of an all-static typed interface call (the
-- static encoder lowers its arguments with `lowerExpr`).
/--
error: AbiEncodeStringHelperRejections.sol:85:39: Literal: [solidity-import:unsupported] unsupported non-numeric literal
closure: InterfaceLiteralFixedBytesC.probe
hex"0f"
-/
#guard_msgs in
solidity_import interfaceLiteralForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeStringHelperRejections.sol"
  using stringHelperEncoding
  contract InterfaceLiteralFixedBytesC
  function probe(address)

end SolidityImportSmoke.AbiEncodeStringHelperChecks
