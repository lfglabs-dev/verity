import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
An internal library function is modeled by its own body, whatever the library and function are
called (`LibraryHelperNameIndependence.sol`, `LibraryLowLevelTransfer.sol`).

In a contract with more than one state variable, a three-argument void function `transfer` of a
library named `CurrencyLibrary` used to be replaced by a fixed native-value or ERC-20 `transfer`
CALL, whatever its body did. `viaCurrencyName` below, whose `transfer` only checks its
arguments, then imported silently as a CALL. The same body in another library (`viaOtherName`)
imported as the checks. Both now take the ordinary helper lowering and agree with solc.
-/
namespace SolidityImportSmoke.LibraryHelperNameIndependenceChecks
open Compiler.CompilationModel Denote Verity.Core

solidity_profile libraryHelperName where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import named from "Contracts/SolidityImportSmoke" entry "LibraryHelperNameIndependence.sol"
  using libraryHelperName
  contract LibraryHelperNameIndependence
  function viaCurrencyName(address, address, uint256)
  function viaOtherName(address, address, uint256)

/-- Status and returned words of `name(args)` in the imported model. -/
private def observe (name : String) (args : List Nat) : Option (Bool × List Nat) := do
  let fn ← named.model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle named.model fn
    {sender := 0, functionSelector := 0, args} Verity.defaultState
  return (r.success, if r.success then
    (if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords) else [])

-- Status and return words observed from solc 0.8.26 (cancun) and 0.8.34 (osaka) via-IR, which
-- agree: the checks pass and `amount * 2` is returned, or the call reverts (empty revert data for
-- a failed `require`, Panic(0x11) for the overflow).
#guard observe "viaCurrencyName" [0, 2, 5] == some (true, [10])
#guard observe "viaCurrencyName" [0, 0, 5] == some (false, [])
#guard observe "viaCurrencyName" [1, 2, 1000] == some (true, [2000])
#guard observe "viaCurrencyName" [1, 2, 1001] == some (false, [])
#guard observe "viaCurrencyName" [0, 2, 2 ^ 255] == some (false, [])
#guard observe "viaOtherName" [0, 2, 5] == some (true, [10])
#guard observe "viaOtherName" [0, 0, 5] == some (false, [])
#guard observe "viaOtherName" [1, 2, 1000] == some (true, [2000])
#guard observe "viaOtherName" [1, 2, 1001] == some (false, [])
#guard observe "viaOtherName" [0, 2, 2 ^ 255] == some (false, [])

-- A `CurrencyLibrary.transfer` that performs the native or ERC-20 CALL in inline assembly (the
-- structure of Uniswap v4's) is lowered through its body: a located rejection at the value
-- argument of the native-value CALL, which the ordinary Yul lowering does not admit.
/--
error: LibraryLowLevelTransfer.sol:14:44: YulIdentifier: [solidity-import:unsupported] Yul call with a nonzero value is outside this slice
closure: LibraryLowLevelTransfer.pay -> CurrencyLibrary.transfer
amount
-/
#guard_msgs in
solidity_import lowLevel from "Contracts/SolidityImportSmoke" entry "LibraryLowLevelTransfer.sol"
  using libraryHelperName
  contract LibraryLowLevelTransfer
  function pay(address, address, uint256)

end SolidityImportSmoke.LibraryHelperNameIndependenceChecks
