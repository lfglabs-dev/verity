import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
A two-parameter `bytes memory` helper is modeled by its own body, whatever its name
(`BytesHelperNameIndependence.sol`).

In a contract with more than one state variable, a string/bytes helper named `callHook` with
two arguments used to be replaced by a fixed low-level CALL to its first argument, whatever the
body did. `viaHookName` below, whose helper only packs its arguments, was then rejected as an
external CALL while the same body under another name (`viaOtherName`) imported. Both now take
the ordinary helper lowering and return what solc returns. A helper of that name that does
perform a CALL and copies the return data from the free-memory pointer (the structure of
Uniswap v4's `Hooks.callHook`) is a located rejection of the ordinary lowering.
-/
namespace SolidityImportSmoke.BytesHelperNameIndependenceChecks
open Compiler.CompilationModel Denote Verity.Core

solidity_profile bytesHelperName where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import named from "Contracts/SolidityImportSmoke" entry "BytesHelperNameIndependence.sol"
  using bytesHelperName
  contract BytesHelperNameIndependence
  function viaHookName(uint256)
  function viaOtherName(uint256)

/-- Status and returned words of `name(args)` in the imported model. -/
private def observe (name : String) (args : List Nat) : Option (Bool × List Nat) := do
  let fn ← named.model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle named.model fn
    {sender := 0, functionSelector := 0, args} Verity.defaultState
  return (r.success, if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords)

/-- The words solc 0.8.26 (cancun) and 0.8.34 (osaka) via-IR return for both functions:
`abi.encode(abi.encodePacked(abi.encode(x), address(uint160(x))))`. -/
private def expected (x : Nat) : List Nat :=
  [0x20, 0x34, x, (x % 2 ^ 160) * 2 ^ 96]

#guard observe "viaHookName" [0] == some (true, expected 0)
#guard observe "viaHookName" [1] == some (true, expected 1)
#guard observe "viaHookName" [2 ^ 160 + 5] == some (true, expected (2 ^ 160 + 5))
#guard observe "viaHookName" [2 ^ 256 - 1] == some (true, expected (2 ^ 256 - 1))
#guard observe "viaOtherName" [0] == some (true, expected 0)
#guard observe "viaOtherName" [1] == some (true, expected 1)
#guard observe "viaOtherName" [2 ^ 160 + 5] == some (true, expected (2 ^ 160 + 5))
#guard observe "viaOtherName" [2 ^ 256 - 1] == some (true, expected (2 ^ 256 - 1))

-- A helper named `callHook` that performs the CALL itself is lowered through its body.
/--
error: BytesHelperNameIndependence.sol:39:9: InlineAssembly: [solidity-import:unsupported] inline assembly in a helper with a bytes memory or bytes-member struct result is unsupported
closure: LowLevelCallBytesHelper.ping -> LowLevelCallBytesHelper.callHook
assembly ("memory-safe") {
            success := call(gas(), self, 0, add(data, 0x20), mload(data), 0, 0)
        }
-/
#guard_msgs in
solidity_import lowLevel from "Contracts/SolidityImportSmoke" entry "BytesHelperNameIndependence.sol"
  using bytesHelperName
  contract LowLevelCallBytesHelper
  function ping(address)

end SolidityImportSmoke.BytesHelperNameIndependenceChecks
