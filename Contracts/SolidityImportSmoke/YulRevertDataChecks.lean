import Compiler.SolidityImport.Import

/-!
Yul `revert(offset, size)` with a nonzero size outside the modeled shape (`YulRevertData.sol`).

The revert returns `size` memory bytes. The model's memory agrees with the EVM's only on the
scratch bytes below 0x40 that the same Yul block wrote on every path, so only a literal range of
such bytes lowers to `Stmt.revertMemory` (`YulRevertMemorySequence`). A restored free-memory
pointer at 0x40 holds solc's pointer, which the model's differs from, so it never counts.
Every other shape is a located rejection, whatever the number of state variables. A zero-size
revert is modeled as `revertEmpty` (`YulEmptyRevertSequence`).
-/
namespace SolidityImportSmoke.YulRevertDataChecks

solidity_profile yulRevert where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- No `mstore` in the block: the scratch words hold whatever the Solidity code left there.
/--
error: YulRevertData.sol:15:17: YulFunctionCall: [solidity-import:unsupported] Yul revert with revert data is supported only for a literal range below 0x40 that this Yul block wrote on every path
closure: YulRevertData.unwrittenRevert
revert(0, 4)
-/
#guard_msgs in
solidity_import unwrittenForm from "Contracts/SolidityImportSmoke" entry "YulRevertData.sol"
  using yulRevert
  contract YulRevertData
  function unwrittenRevert(uint256)

-- A size only known at run time.
/--
error: YulRevertData.sol:23:13: YulFunctionCall: [solidity-import:unsupported] Yul revert with revert data is supported only for a literal range below 0x40 that this Yul block wrote on every path
closure: YulRevertData.sizedRevert
revert(0, n)
-/
#guard_msgs in
solidity_import sizedForm from "Contracts/SolidityImportSmoke" entry "YulRevertData.sol"
  using yulRevert
  contract YulRevertData
  function sizedRevert(uint256)

-- The scratch word is written only when the Yul `if` is taken.
/--
error: YulRevertData.sol:31:13: YulFunctionCall: [solidity-import:unsupported] Yul revert with revert data is supported only for a literal range below 0x40 that this Yul block wrote on every path
closure: YulRevertData.conditionalWriteRevert
revert(0, 4)
-/
#guard_msgs in
solidity_import conditionalForm from "Contracts/SolidityImportSmoke" entry "YulRevertData.sol"
  using yulRevert
  contract YulRevertData
  function conditionalWriteRevert(uint256)

-- The range runs past the written scratch words into the unwritten free-memory pointer slot.
/--
error: YulRevertData.sol:38:13: YulFunctionCall: [solidity-import:unsupported] Yul revert with revert data is supported only for a literal range below 0x40 that this Yul block wrote on every path
closure: YulRevertData.beyondScratchRevert
revert(0, 0x60)
-/
#guard_msgs in
solidity_import beyondScratchForm from "Contracts/SolidityImportSmoke" entry "YulRevertData.sol"
  using yulRevert
  contract YulRevertData
  function beyondScratchRevert(uint256)

-- The free-memory pointer word, written back from `mload(0x40)`: solc's pointer, not the model's.
/--
error: YulRevertData.sol:45:13: YulFunctionCall: [solidity-import:unsupported] Yul revert with revert data is supported only for a literal range below 0x40 that this Yul block wrote on every path
closure: YulRevertData.freePointerRevert
revert(0x40, 0x20)
-/
#guard_msgs in
solidity_import freePointerForm from "Contracts/SolidityImportSmoke" entry "YulRevertData.sol"
  using yulRevert
  contract YulRevertData
  function freePointerRevert(uint256)

end SolidityImportSmoke.YulRevertDataChecks
