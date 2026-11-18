import Compiler.SolidityImport.Import

/-!
Yul `revert(offset, size)` with a nonzero or non-constant size (`YulRevertData.sol`).

The revert returns `size` memory bytes as revert data. There is no lowering for that, so the
importer rejects it with a located error, whatever the number of state variables. It used to
import as a revert with no data (`revertEmpty`) when the compiled sources declared more than
one state variable. A zero-size revert is modeled (`YulEmptyRevertSequence`).
-/
namespace SolidityImportSmoke.YulRevertDataChecks

solidity_profile yulRevert where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- A constant nonzero size: a 4-byte custom-error selector.
/--
error: YulRevertData.sol:14:17: YulFunctionCall: [solidity-import:unsupported] Yul revert with revert data (nonzero size) is unsupported
closure: YulRevertData.selectorRevert
revert(0, 4)
-/
#guard_msgs in
solidity_import selectorForm from "Contracts/SolidityImportSmoke" entry "YulRevertData.sol"
  using yulRevert
  contract YulRevertData
  function selectorRevert(uint256)

-- A size only known at run time.
/--
error: YulRevertData.sol:21:13: YulFunctionCall: [solidity-import:unsupported] Yul revert with revert data (nonzero size) is unsupported
closure: YulRevertData.sizedRevert
revert(0, n)
-/
#guard_msgs in
solidity_import sizedForm from "Contracts/SolidityImportSmoke" entry "YulRevertData.sol"
  using yulRevert
  contract YulRevertData
  function sizedRevert(uint256)

end SolidityImportSmoke.YulRevertDataChecks
