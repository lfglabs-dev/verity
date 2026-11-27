import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- A failed ECM call reverts with what the module's compiled Yul reverts with:
-- `callWithValue` bubbles the callee's returndata (an unfunded call bubbles none),
-- and the ecrecover precompile module reverts with no data (`failurePayload`).
-- `test/EcmFailurePayloadSmoke.t.sol` checks the compiled side of `forward`.
verity_contract EcmFailurePayloadSmoke where
  storage
    last : Uint256 := slot 0

  function payable allow_post_interaction_writes reentrancy_trusted forward
      (target : Address, value : Uint256) : Unit := do
    ecmDo Compiler.Modules.Calls.callWithValueModule [addressToWord target, value, 0, 0]

  function recover (h : Uint256, v : Uint256, r : Uint256, s : Uint256) : Uint256 := do
    let signer ← ecmCall Compiler.Modules.Precompiles.ecrecoverModule [h, v, r, s]
    return signer

end Contracts.Smoke

namespace Contracts.Smoke.EcmFailurePayloadSmokeProofs

open Verity Contracts Contracts.Smoke

/-- Every call fails, answering the word `5`. -/
def failingAdversary : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ s => s
  result := fun _ _ => .revert [5]
  gasUsed := fun _ _ => 0

def ctx : ExecutableCallContext := .ofAdversary failingAdversary

/-- The contract holds 1 wei. -/
def s0 : ContractState := { Verity.defaultState with selfBalance := 1 }

/-- `callWithValue` re-raises the callee's answer: the 32 bytes of the word `5`. -/
example :
    EcmFailurePayloadSmoke.forward ctx (Verity.Core.Address.ofNat 0xB0B) 1 s0 =
      .revert (.raw (List.replicate 31 0 ++ [5])) s0 := by
  rfl

/-- An unfunded `callWithValue` reverts with no bytes: the EVM call fails with empty
returndata, which the module bubbles. -/
example :
    EcmFailurePayloadSmoke.forward ctx (Verity.Core.Address.ofNat 0xB0B) 2 s0 =
      .revert (.raw []) s0 := by
  rfl

/-- The ecrecover module reverts with no data (`revert(0, 0)`), whatever the failed
precompile answered. -/
example :
    EcmFailurePayloadSmoke.recover ctx 1 27 2 3 s0 = .revert .empty s0 := by
  rfl

end Contracts.Smoke.EcmFailurePayloadSmokeProofs
