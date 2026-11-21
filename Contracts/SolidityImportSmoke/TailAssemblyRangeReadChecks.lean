import Compiler.SolidityImport.Import

/-!
Tail `assembly` of a `bytes32[]`-returning function over a (start slot, count) pair
(`TailAssemblyRangeRead.sol`).

The importer replaces such a block with a fixed lowering (`lowerBatchRangeSloadShim`: `count`
consecutive `sload`s from the start slot, ABI-encoded) only when the block is the exact range read
it models (`extsloadRangeYulFingerprint`) and its Yul identifiers resolve to one `bytes32` and one
`uint256` variable (`rangeReadBindings?`). It used to apply whenever Yul names `startSlot` and
`nSlots` were in scope, whatever the block did: `echoRange` returns the keys (solc: `[0, 1]` for
`(0, 2)`) and imported silently as the storage read (`[7, 9]`). Blocks the shortcut does not take
go through the ordinary assembly lowering, which rejects these.
-/
namespace SolidityImportSmoke.TailAssemblyRangeReadChecks

solidity_profile tailAssemblyRangeRead where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- The exact range read keeps its lowering, over parameters in either order or over locals.
solidity_import rangeReads from "Contracts/SolidityImportSmoke" entry "TailAssemblyRangeRead.sol"
  using tailAssemblyRangeRead
  contract TailAssemblyRangeRead
  function loadRange(bytes32, uint256)
  function loadRangeSwapped(uint256, bytes32)
  function loadRangeFromLocals(uint256, uint256)

-- Same shape and Yul names, different code.
/--
error: TailAssemblyRangeRead.sol:77:27: YulFunctionCall: [solidity-import:unsupported] Yul reads of the free-memory pointer may only restore it or place a bubbled revert
closure: TailAssemblyRangeRead.echoRange
mload(0x40)
-/
#guard_msgs in
solidity_import echoForm from "Contracts/SolidityImportSmoke" entry "TailAssemblyRangeRead.sol"
  using tailAssemblyRangeRead
  contract TailAssemblyRangeRead
  function echoRange(bytes32, uint256)

-- The exact block over a count type the lowering does not model.
/--
error: TailAssemblyRangeRead.sol:98:27: YulFunctionCall: [solidity-import:unsupported] Yul reads of the free-memory pointer may only restore it or place a bubbled revert
closure: TailAssemblyRangeRead.loadRangeNarrow
mload(0x40)
-/
#guard_msgs in
solidity_import narrowForm from "Contracts/SolidityImportSmoke" entry "TailAssemblyRangeRead.sol"
  using tailAssemblyRangeRead
  contract TailAssemblyRangeRead
  function loadRangeNarrow(bytes32, uint8)

end SolidityImportSmoke.TailAssemblyRangeReadChecks
