import Compiler.SolidityImport.Import

/-!
Tail `assembly` of a `bytes32[]`-returning function (`TailAssemblyArrayRead.sol`).

The importer replaces such a block with a fixed lowering (`lowerBatchArrayLoadShim`: one
`sload` or `tload` per calldata key, ABI-encoded) only when the block is the exact batch read
it models, checked by `yulBlockFingerprint`. `echoSlots` has the same shape but returns the
keys: solc returns `[0, 1]` for `[0, 1]` where the fixed lowering would return the stored
`[7, 9]`. It used to import silently with that lowering; it is now a located rejection.
-/
namespace SolidityImportSmoke.TailAssemblyArrayReadChecks

solidity_profile tailAssemblyArrayRead where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- The exact storage and transient batch reads keep their lowering.
solidity_import batchReads from "Contracts/SolidityImportSmoke" entry "TailAssemblyArrayRead.sol"
  using tailAssemblyArrayRead
  contract TailAssemblyArrayRead
  function loadSlots(«bytes32[]»)
  function loadTransientSlots(«bytes32[]»)

-- Same shape, different code.
/--
error: TailAssemblyArrayRead.sol:51:9: InlineAssembly: [solidity-import:unsupported] shortcut fingerprint mismatch: tail assembly of a bytes32[]-returning function is not a registered calldata-keyed batch slot read (fingerprint 7c0f2f1598a9)
closure: TailAssemblyArrayRead.echoSlots
assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            mstore(memp
-/
#guard_msgs in
solidity_import echoForm from "Contracts/SolidityImportSmoke" entry "TailAssemblyArrayRead.sol"
  using tailAssemblyArrayRead
  contract TailAssemblyArrayRead
  function echoSlots(«bytes32[]»)

end SolidityImportSmoke.TailAssemblyArrayReadChecks
