import Contracts.SolidityImportSmoke.InterfaceVoidCallSequenceModel

/-!
Trust flags of the imported `InterfaceVoidCallSequence` roots. A closed low-level `CALL`
hands control to an arbitrary account, so it is a reentrancy window: every root that
makes one is trailing (nothing after the call reads or writes storage or logs) and
carries `solidity_trailing_low_level_call_reentrancy`, never the CREATE2-only
`solidity_create2_initcode_reentrancy`. `solidity_closed_transport_cei` covers only the
call's own effect following the closed code-size check. Roots that read or write
storage or log after the call carry `solidity_post_call_state_access` instead
(`PostCallStateAccessChecks`).
-/
namespace SolidityImportSmoke.InterfaceVoidCallTrustChecks
open Compiler.CompilationModel

private def flags (name : String) : Option (Bool × Bool × List String) :=
  (SolidityImportSmoke.InterfaceVoidCallSequenceModel.model.functions.find? (·.name == name)).map
    fun f => (f.allowPostInteractionWrites, f.reentrancyTrusted, f.localObligations.map (·.name))

private def trailingCall (abi : String) : Option (Bool × Bool × List String) :=
  some (true, true, [abi, "solidity_closed_transport_cei",
    "solidity_trailing_low_level_call_reentrancy"])

#guard flags "ping" == trailingCall "solidity_scalar_abi_entry"
#guard flags "relayData" == trailingCall "solidity_explicit_abi"
#guard flags "tryPing" == trailingCall "solidity_scalar_abi_entry"
#guard flags "tryRelay" == trailingCall "solidity_explicit_abi"
#guard flags "tryPoke" == trailingCall "solidity_scalar_abi_entry"
#guard flags "signalWord" ==
  some (false, true, ["solidity_scalar_abi_entry", "solidity_trailing_low_level_call_reentrancy"])
#guard flags "read" == some (false, false, [])
#guard SolidityImportSmoke.InterfaceVoidCallSequenceModel.model.functions.all fun f =>
  !(f.localObligations.map (·.name)).contains "solidity_create2_initcode_reentrancy"

end SolidityImportSmoke.InterfaceVoidCallTrustChecks
