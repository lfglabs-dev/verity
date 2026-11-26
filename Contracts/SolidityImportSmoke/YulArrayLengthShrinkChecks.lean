import Compiler.SolidityImport.Import
import Compiler.Codegen

/-!
Smoke checks and located rejections for inline-assembly dynamic memory-array length shrinks
(`assembly { mstore(x, n) }`, Refs #2620).
-/
namespace SolidityImportSmoke.YulArrayLengthShrinkChecks

solidity_profile shrinkCancunViaIR where
  solc := "0.8.38+commit.1835d247"
  evmVersion := "cancun"
  viaIR := true
  optimizerRuns := some 10
  bytecodeHash := "ipfs"

solidity_profile shrinkCancunLegacy where
  solc := "0.8.38+commit.1835d247"
  evmVersion := "cancun"
  viaIR := false
  optimizerRuns := some 10
  bytecodeHash := "ipfs"

solidity_profile shrinkOsakaViaIR where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- Strict positive smoke imports: paginated sentinel linked-list walk with shrink (`mstore(page, count)`).
solidity_import paginatedViaIR from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkCancunViaIR
  contract YulArrayLengthShrink
  function paginate(address,uint256)

#guard paginatedViaIR.report.functions.all (·.denoteCovered)
#guard (Compiler.CompilationModel.compile paginatedViaIR.model [0x1] .cancun).isOk

solidity_import paginatedLegacy from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkCancunLegacy
  contract YulArrayLengthShrink
  function paginate(address,uint256)

#guard paginatedLegacy.report.functions.all (·.denoteCovered)
#guard (Compiler.CompilationModel.compile paginatedLegacy.model [0x1] .cancun).isOk

solidity_import paginatedOsaka from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function paginate(address,uint256)

#guard paginatedOsaka.report.functions.all (·.denoteCovered)
#guard (Compiler.CompilationModel.compile paginatedOsaka.model [0x1] .osaka).isOk

-- 1. Grow rejections (literal `5 > 3` and inclusive `<=` loop bound).
/--
error: YulArrayLengthShrink.sol:34:24: YulLiteral: [solidity-import:unsupported] Yul memory array length mstore requires a length provably at most the allocated array length
closure: YulArrayLengthShrink.growLiteral
5
-/
#guard_msgs in
solidity_import rejGrowLiteral from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function growLiteral()

/--
error: YulArrayLengthShrink.sol:45:24: YulIdentifier: [solidity-import:unsupported] Yul memory array length mstore requires a length provably at most the allocated array length
closure: YulArrayLengthShrink.growInclusiveLoop
count
-/
#guard_msgs in
solidity_import rejGrowLoop from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function growInclusiveLoop(uint256)

-- 2. Non-array target rejections (scalar, `bytes memory`, fixed-size memory array).
/--
error: YulArrayLengthShrink.sol:52:13: YulFunctionCall: [solidity-import:unsupported] Yul mstore requires a fixed address below 0x80
closure: YulArrayLengthShrink.nonArrayScalar
mstore(p, 0)
-/
#guard_msgs in
solidity_import rejNonArrayScalar from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function nonArrayScalar()

/--
error: YulArrayLengthShrink.sol:59:20: YulIdentifier: [solidity-import:unsupported] unbound Yul identifier b
closure: YulArrayLengthShrink.nonArrayBytes
b
-/
#guard_msgs in
solidity_import rejNonArrayBytes from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function nonArrayBytes()

/--
error: YulArrayLengthShrink.sol:66:20: YulIdentifier: [solidity-import:unsupported] unbound Yul identifier fixedArr
closure: YulArrayLengthShrink.nonArrayFixed
fixedArr
-/
#guard_msgs in
solidity_import rejNonArrayFixed from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function nonArrayFixed()

-- 3. Offset target rejection (`mstore(add(xs, 0x20), 0)`).
/--
error: YulArrayLengthShrink.sol:74:24: YulIdentifier: [solidity-import:unsupported] unbound Yul identifier xs
closure: YulArrayLengthShrink.offsetTarget
xs
-/
#guard_msgs in
solidity_import rejOffsetTarget from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function offsetTarget()

-- 4. Unproved `n` and aliasing / parameter rejections.
/--
error: YulArrayLengthShrink.sol:81:24: YulIdentifier: [solidity-import:unsupported] Yul memory array length mstore requires a length provably at most the allocated array length
closure: YulArrayLengthShrink.unprovedLenParam
n
-/
#guard_msgs in
solidity_import rejUnprovedParam from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function unprovedLenParam(uint256,uint256)

/--
error: YulArrayLengthShrink.sol:96:24: YulIdentifier: [solidity-import:unsupported] Yul memory array length mstore requires a length provably at most the allocated array length
closure: YulArrayLengthShrink.unprovedShortCircuitInit
count
-/
#guard_msgs in
solidity_import rejShortCircuitInit from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function unprovedShortCircuitInit(bool,uint256)

/--
error: YulArrayLengthShrink.sol:102:20: YulIdentifier: [solidity-import:unsupported] Yul memory array length mstore requires a local memory array variable, not a parameter
closure: YulArrayLengthShrink.parameterArrayTarget
xs
-/
#guard_msgs in
solidity_import rejParamArray from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function parameterArrayTarget(«uint256[]»)

/--
error: YulArrayLengthShrink.sol:112:20: YulIdentifier: [solidity-import:unsupported] Yul memory array length mstore requires an unaliased local new-array allocation
closure: YulArrayLengthShrink.aliasedArrayTarget
xs
-/
#guard_msgs in
solidity_import rejAliasedArray from "Contracts/SolidityImportSmoke" entry "YulArrayLengthShrink.sol"
  using shrinkOsakaViaIR
  contract YulArrayLengthShrink
  function aliasedArrayTarget()

end SolidityImportSmoke.YulArrayLengthShrinkChecks
