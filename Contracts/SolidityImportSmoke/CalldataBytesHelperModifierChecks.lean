import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.CalldataBytesHelperModifierChecks
open Compiler.CompilationModel Denote

solidity_import imported from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifier
  function inspect(uint256,bytes,uint256,uint256,uint256)
  function subSliceInfo(bytes,uint256,uint256,uint256)
  function sliceModifierArg(bytes,uint256,uint256)

private def observe (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle imported.model fn
    {sender := 0, functionSelector := 0, args} Verity.defaultState
  return (r.success, r.revertData, r.returnWords, r.finalStorage 0)

-- Exact return bytes and final storage observed under both solc 0.8.34 pipelines.
#guard observe "inspect" [3, 160, 1, 3, 2, 4, 0x02030405 * 2^224] == some (true, none,
  [0x589e0c4e37aeb811926597061255abf8372d01ad2dc26bd3011b684233a38772], 7040402030205)
#guard observe "inspect" [3, 160, 0, 1, 1, 1, 2 * 2^248] ==
  some (false, some (errorStringBytes "short"), [], 0)
#guard observe "inspect" [3, 160, 0, 2, 1, 2, 0xff03 * 2^240] ==
  some (false, some (errorStringBytes "post"), [], 0)
#guard observe "subSliceInfo" [128, 1, 4, 2, 4, 0x11223344 * 2^224] == some (true, none,
  [2, 0x44 * 2^248, 0x223344 * 2^232,
   0x3e065884a62abfbb4d6dfe8f8fddce4d1d446b6af51bc55cd64064a83b78d94b], 0)
#guard observe "subSliceInfo" [128, 1, 3, 2, 4, 0x11223344 * 2^224] ==
  some (false, some (panicBytes 0x32), [], 0)
#guard observe "subSliceInfo" [128, 1, 5, 0, 4, 0x11223344 * 2^224] == some (false, some [], [], 0)
#guard observe "sliceModifierArg" [96, 1, 3, 3, 0x050607 * 2^232] == some (true, none, [707], 70706)

#guard (Compiler.CompilationModel.compile imported.model
  (List.range imported.model.functions.length) .cancun).isOk

/--
error: CalldataBytesHelperModifier.sol:75:66: VariableDeclaration: [solidity-import:unsupported] named bytes calldata helper return is unsupported
closure: CalldataBytesHelperModifierUnsupported.useNamedHelper -> CalldataBytesHelperModifierUnsupported.namedHelper
bytes calldata out
-/
#guard_msgs in
solidity_import named from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useNamedHelper(bytes)

/--
error: CalldataBytesHelperModifier.sol:83:86: Block: [solidity-import:unsupported] calldata helper must directly return a parameter or slice
closure: CalldataBytesHelperModifierUnsupported.useMultiStmtHelper -> CalldataBytesHelperModifierUnsupported.multiStmtHelper
{
        uint256 n = x.length;
        n;
        return x;
    }
-/
#guard_msgs in
solidity_import multiStmt from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useMultiStmtHelper(bytes)

/--
error: CalldataBytesHelperModifier.sol:94:16: IndexRangeAccess: [solidity-import:unsupported] expected a slice of a calldata parameter
closure: CalldataBytesHelperModifierUnsupported.useMsgDataSliceHelper -> CalldataBytesHelperModifierUnsupported.msgDataSliceHelper
msg.data[start:]
-/
#guard_msgs in
solidity_import msgDataSlice from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useMsgDataSliceHelper(uint256)

/--
error: CalldataBytesHelperModifier.sol:101:34: VariableDeclaration: [solidity-import:unsupported] reassigned calldata parameter is outside this slice
closure: CalldataBytesHelperModifierUnsupported.useReassignHelperParam -> CalldataBytesHelperModifierUnsupported.reassignHelperParam
bytes calldata x
-/
#guard_msgs in
solidity_import reassignHelper from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useReassignHelperParam(bytes)

/--
error: CalldataBytesHelperModifier.sol:110:26: VariableDeclaration: [solidity-import:unsupported] reassigned calldata modifier parameter is outside this slice
closure: CalldataBytesHelperModifierUnsupported.useReassignMod -> CalldataBytesHelperModifierUnsupported.reassignMod
bytes calldata x
-/
#guard_msgs in
solidity_import mutated from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := false, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useReassignMod(bytes)

/--
error: CalldataBytesHelperModifier.sol:119:24: VariableDeclaration: [solidity-import:unsupported] unsupported modifier parameter type bytes
closure: CalldataBytesHelperModifierUnsupported.useMemoryMod
bytes memory x
-/
#guard_msgs in
solidity_import memoryMod from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useMemoryMod(bytes)

/--
error: CalldataBytesHelperModifier.sol:133:67: MemberAccess: [solidity-import:unsupported] expected a calldata bytes parameter or slice
closure: CalldataBytesHelperModifierUnsupported.useMsgDataInMod
msg.data
-/
#guard_msgs in
solidity_import msgDataMod from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useMsgDataInMod(uint256)

/--
error: CalldataBytesHelperModifier.sol:137:72: IndexRangeAccess: [solidity-import:unsupported] expected a slice of a calldata parameter
closure: CalldataBytesHelperModifierUnsupported.useMsgDataSliceInMod
msg.data[4:]
-/
#guard_msgs in
solidity_import msgDataSliceMod from "Contracts/SolidityImportSmoke" entry "CalldataBytesHelperModifier.sol"
  using { evmVersion := "cancun", viaIR := true, optimizerRuns := some 200, bytecodeHash := "none" }
  contract CalldataBytesHelperModifierUnsupported
  function useMsgDataSliceInMod(uint256)

end SolidityImportSmoke.CalldataBytesHelperModifierChecks
