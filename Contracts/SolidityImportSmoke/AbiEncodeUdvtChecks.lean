import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
User-defined value type `T.wrap(x)` / `T.unwrap(x)` inside `abi.encode*` arguments
(`AbiEncodeUdvtSequence.sol`, `AbiEncodeUdvtRejections.sol`).

`checkEncodingScalar` admits the conversion as the identity on the underlying word and
inspects only its argument, so an effect beneath the conversion is still rejected at the
inner call.
-/
namespace SolidityImportSmoke.AbiEncodeUdvtChecks

solidity_profile udvtEncoding where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- 1. A custom revert beneath `unwrap` is rejected at the inner call.
/--
error: AbiEncodeUdvtRejections.sol:17:57: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: UnwrapRevertC.digest
_mayRevert(x)
-/
#guard_msgs in
solidity_import unwrapRevertForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeUdvtRejections.sol"
  using udvtEncoding
  contract UnwrapRevertC
  function digest(uint256)

-- 2. A state-changing helper beneath `unwrap` is rejected at the inner call.
/--
error: AbiEncodeUdvtRejections.sol:29:54: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: UnwrapStatefulC.digest
_useWord()
-/
#guard_msgs in
solidity_import unwrapStatefulForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeUdvtRejections.sol"
  using udvtEncoding
  contract UnwrapStatefulC
  function digest(uint256)

-- 3. A state-changing helper beneath `wrap` is rejected at the inner call.
/--
error: AbiEncodeUdvtRejections.sol:41:61: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: WrapStatefulC.digest
_useCount()
-/
#guard_msgs in
solidity_import wrapStatefulForm from "Contracts/SolidityImportSmoke"
  entry "AbiEncodeUdvtRejections.sol"
  using udvtEncoding
  contract WrapStatefulC
  function digest(uint256)

end SolidityImportSmoke.AbiEncodeUdvtChecks
