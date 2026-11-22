import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
A private helper called with an address and an `abi.encodeWithSelector(I.f.selector, ...)`
payload is modeled by its own body, whatever it is called
(`SelectorPayloadHelperNameIndependence.sol`, `SelectorPayloadLowLevelCall.sol`).

A statement call to a helper named `_callOptionalReturn` with that argument shape used to be
replaced by a fixed optional-bool CALL to the address (empty return data accepted as success,
the callee's revert data re-raised) followed by
`require(ok, "SafeERC20: ERC20 operation did not succeed")`, whatever the body did.
`viaOptionalName` below, whose helper only checks its arguments, then imported silently as that
CALL. The same body under another name (`viaOtherName`) imported as the checks. Both now take the
ordinary helper lowering and agree with solc.
-/
namespace SolidityImportSmoke.SelectorPayloadHelperNameIndependenceChecks
open Compiler.CompilationModel Denote Verity.Core

solidity_profile selectorPayloadHelperName where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import named from "Contracts/SolidityImportSmoke" entry "SelectorPayloadHelperNameIndependence.sol"
  using selectorPayloadHelperName
  contract SelectorPayloadHelperNameIndependence
  function viaOptionalName(address, uint256)
  function viaOtherName(address, uint256)

/-- Status and returned words of `name(args)` in the imported model. -/
private def observe (name : String) (args : List Nat) : Option (Bool × List Nat) := do
  let fn ← named.model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle named.model fn
    {sender := 0, functionSelector := 0, args} Verity.defaultState
  return (r.success, if r.success then
    (if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords) else [])

-- Status and returned word observed from solc 0.8.26 (cancun) and 0.8.34 (osaka) via-IR, which
-- agree. Revert data (empty for a failed `require`, Panic(0x11) for the overflow) is not
-- compared here.
#guard observe "viaOptionalName" [0xBEEF, 5] == some (true, [6])
#guard observe "viaOptionalName" [0, 5] == some (false, [])
#guard observe "viaOptionalName" [1, 0] == some (true, [1])
#guard observe "viaOptionalName" [0xBEEF, 2 ^ 256 - 1] == some (false, [])
#guard observe "viaOtherName" [0xBEEF, 5] == some (true, [6])
#guard observe "viaOtherName" [0, 5] == some (false, [])
#guard observe "viaOtherName" [1, 0] == some (true, [1])
#guard observe "viaOtherName" [0xBEEF, 2 ^ 256 - 1] == some (false, [])

-- A `_callOptionalReturn` that performs the CALL itself (the structure of OpenZeppelin 4.x) is
-- lowered through its body: a located rejection at the low-level call, whose data is a `bytes`
-- parameter rather than an `abi.encodeCall` the ordinary lowering admits.
/--
error: SelectorPayloadLowLevelCall.sol:17:62: Identifier: [solidity-import:unsupported] low-level call data must be abi.encodeCall of an external function with address, bool, bytes32 or uint256 parameters
closure: SelectorPayloadLowLevelCall.send -> SelectorPayloadLowLevelCall._callOptionalReturn
data
-/
#guard_msgs in
solidity_import lowLevel from "Contracts/SolidityImportSmoke" entry "SelectorPayloadLowLevelCall.sol"
  using selectorPayloadHelperName
  contract SelectorPayloadLowLevelCall
  function send(address, uint256)

end SolidityImportSmoke.SelectorPayloadHelperNameIndependenceChecks
