import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
Tail `assembly` of a `bytes32[]`-returning function over a (start slot, count) pair
(`TailAssemblyRangeRead.sol`).

The importer replaces such a block with a fixed lowering (`lowerBatchRangeSloadShim`: consecutive
`sload`s from the start slot, ABI-encoded, over the block's wrapping length) only when the block is the exact range read
it models (`extsloadRangeYulFingerprint`) and its Yul identifiers resolve to one `bytes32` and one
`uint256` variable (`rangeReadBindings?`). It used to apply whenever Yul names `startSlot` and
`nSlots` were in scope, whatever the block did: `echoRange` returns the keys (solc: `[0, 1]` for
`(0, 2)`) and imported silently as the storage read (`[7, 9]`). Blocks the shortcut does not take
go through the ordinary assembly lowering, which rejects these.
-/
namespace SolidityImportSmoke.TailAssemblyRangeReadChecks
open Compiler.CompilationModel Denote Verity.Core

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

/-- Status and returned words of `name(args)` in the imported model, with storage slots 0 and 1
holding 7 and 9 as the source's initializers leave them. -/
private def observe (name : String) (args : List Nat) : Option (Bool × List Nat) := do
  let fn ← rangeReads.model.functions.find? (·.name == name)
  let initial := (Verity.defaultState.writePhysicalSlot 0 (Uint256.ofNat 7)).writePhysicalSlot 1
    (Uint256.ofNat 9)
  let r := denoteFunction SolidityImport.Differential.oracle rangeReads.model fn
    {sender := 0, functionSelector := 0, args} initial
  return (r.success, if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords)

-- Return words observed from solc 0.8.26 and 0.8.34 (via-IR) on the same storage. `nSlots` wraps
-- through `shl(5, nSlots)`: the block reads `nSlots mod 2^251` words and returns 0 or 32 bytes
-- for the two largest residues.
#guard observe "loadRange" [0, 2] == some (true, [32, 2, 7, 9])
#guard observe "loadRange" [0, 0] == some (true, [32, 0])
#guard observe "loadRange" [1, 3] == some (true, [32, 3, 9, 0, 0])
#guard observe "loadRange" [2^256 - 1, 2] == some (true, [32, 2, 0, 7])
#guard observe "loadRange" [0, 2^251] == some (true, [32, 2^251])
#guard observe "loadRange" [0, 2^251 + 1] == some (true, [32, 2^251 + 1, 7])
#guard observe "loadRange" [0, 2^252 - 2] == some (true, [])
#guard observe "loadRange" [0, 2^256 - 1] == some (true, [32])
#guard observe "loadRangeSwapped" [2, 0] == some (true, [32, 2, 7, 9])
#guard observe "loadRangeSwapped" [1, 1] == some (true, [32, 1, 9])
#guard observe "loadRangeFromLocals" [0, 1] == some (true, [32, 1, 9])
#guard observe "loadRangeFromLocals" [2^256 - 3, 3] == some (true, [32, 3, 0, 0, 7])
#guard (observe "loadRangeFromLocals" [2^256 - 1, 1]).map Prod.fst == some false

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
