import Compiler.SolidityImport.Import

/-!
`super.f(...)` and `Base.f(...)` inside `abi.encode*` arguments
(`EncodingArgSuperOverrideRejections.sol`).

Effect checks (`fnHasCustomRevert`, `checkEncodingScalar`, `statefulCallIn`, `memoryWriteIn`)
must follow the same C3 / qualified dispatch as call lowering rather than resolving every
declaration reference to the target contract's most-derived override.
-/
namespace SolidityImportSmoke.EncodingArgSuperOverrideChecks

solidity_profile superEncoding where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- 3-level C3 `super.sep()` chain lowers to the exact same model functions as the flat
-- helper chain without `super` (and with zero state variables in the contract).
solidity_import chainSuper from "Contracts/SolidityImportSmoke"
  entry "EncodingArgSuperOverrideRejections.sol"
  using superEncoding
  contract ChainSuperC
  function digest(bytes32)

solidity_import chainPlain from "Contracts/SolidityImportSmoke"
  entry "EncodingArgSuperOverrideRejections.sol"
  using superEncoding
  contract ChainPlainC
  function digest(bytes32)

#guard toString (repr chainSuper.model.functions) == toString (repr chainPlain.model.functions)

-- 1. Multi-level `super` chain whose base uses `require(...)` is still rejected.
/--
error: EncodingArgSuperOverrideRejections.sol:65:55: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: RevertChainC.digest
sep(x)
-/
#guard_msgs in
solidity_import revertChainForm from "Contracts/SolidityImportSmoke"
  entry "EncodingArgSuperOverrideRejections.sol"
  using superEncoding
  contract RevertChainC
  function digest(uint256, bytes32)

-- 2. C3 diamond where `DiamondRight`'s `super.sep` AST `referencedDeclaration` points to pure
-- `DiamondRoot.sep`, but C3 linearisation routes through reverting `DiamondLeft.sep`.
/--
error: EncodingArgSuperOverrideRejections.sol:101:55: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: DiamondLeaf.digest
sep(x)
-/
#guard_msgs in
solidity_import diamondRevertForm from "Contracts/SolidityImportSmoke"
  entry "EncodingArgSuperOverrideRejections.sol"
  using superEncoding
  contract DiamondLeaf
  function digest(uint256, bytes32)

-- 3. Direct `super.sep(x)` to a reverting base when the derived override is pure.
/--
error: EncodingArgSuperOverrideRejections.sol:122:37: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: DirectRevertDerived.viaSuper
super.sep(x)
-/
#guard_msgs in
solidity_import directSuperRevertForm from "Contracts/SolidityImportSmoke"
  entry "EncodingArgSuperOverrideRejections.sol"
  using superEncoding
  contract DirectRevertDerived
  function viaSuper(uint256)

-- 4. Qualified `DirectRevertBase.sep(x)` to a reverting base when the derived override is pure.
/--
error: EncodingArgSuperOverrideRejections.sol:126:37: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: DirectRevertDerived.viaQualified
DirectRevertBase.sep(x)
-/
#guard_msgs in
solidity_import qualifiedBaseRevertForm from "Contracts/SolidityImportSmoke"
  entry "EncodingArgSuperOverrideRejections.sol"
  using superEncoding
  contract DirectRevertDerived
  function viaQualified(uint256)

-- 5. `super.bump()` to a stateful base when the derived override is `pure`.
/--
error: EncodingArgSuperOverrideRejections.sol:146:46: FunctionCall: [solidity-import:unsupported] effectful ABI encoding argument is unsupported
closure: StatefulSuperDerived.encodeDynamic
super.bump()
-/
#guard_msgs in
solidity_import statefulSuperForm from "Contracts/SolidityImportSmoke"
  entry "EncodingArgSuperOverrideRejections.sol"
  using superEncoding
  contract StatefulSuperDerived
  function encodeDynamic(bytes)

end SolidityImportSmoke.EncodingArgSuperOverrideChecks
