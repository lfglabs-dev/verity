import Contracts.Common
import Verity.Core.Model.CallbackBridge
import Verity.Core.Model.NonReentrantGuard

namespace Contracts.ReentrancyRelyGuarantee

open Contracts
open Verity hiding pure bind
open Compiler.CompilationModel.DenoteExternalCalls

/-! Focused generated consumer for the registry/guard boundary.  It contains
an actual mutable external-call window, so the executable entrypoint must take
an explicit adversary and the nonreentrant annotation must guard that same
generated function. -/
verity_contract GeneratedRegistry where
  storage
    lock : Uint256 := slot 0
  linked_externals
    external ping(Uint256) -> (Uint256)

  function nonreentrant(lock) guardedPing (value : Uint256) : Unit := do
    let _response := externalCall "ping" [value]
    return ()

  function noop (value : Uint256) : Uint256 := do
    return value

namespace GeneratedRegistry

/-- The generated registry uses its explicit adversary at the external-call
entrypoint; there is no `.stub` compatibility path in this theorem surface. -/
theorem guardedPing_registered (adv : AdversaryModel) (ctx : CallbackContext)
    (value : Uint256) (hvalue : ctx.msgValue = 0) :
    entrypointRegistry adv
      (callbackContractTransition ctx
        (guardedPing_registry (Contracts.ExecutableCallContext.ofAdversary adv) value)) := by
  left
  exact ⟨ctx, value, hvalue, rfl⟩

/-- The executable generated entrypoint is definitionally protected by the
canonical source guard at the same slot used by the compiled dispatch guard. -/
theorem guardedPing_reentry_blocked (adv : AdversaryModel) (value : Uint256)
    (state : ContractState) (hlock : state.transientStorage 0 ≠ 0) :
    (guardedPing (Contracts.ExecutableCallContext.ofAdversary adv) value).runState state = state := by
  apply Verity.Core.NonReentrantGuard.guarded_reentry_blocked
  exact hlock

end GeneratedRegistry

/-! Regression for registry window-helper routing: `readBal` is adversarial
(view/staticcall ECM) but does not open a reentrancy window, while `hop`
opens a window and then calls `readBal`. `entry_registry` must call
`hop_registry` (which calls `readBal_registry`) rather than public `hop`
(which uses stub-only `readBal` and under-approximates a callee-controlled
view ECM). -/
verity_contract RegistryWindowHelperRouting where
  storage
    last : Uint256 := slot 0
  interfaces
    interface IToken where
      function balanceOf(Address) view returns (Uint256)
    end
  linked_externals
    external ping(Uint256) -> (Uint256)

  function view readBal (token : IToken, who : Address) : Uint256 := do
    let observed ← token.balanceOf who
    return observed

  function reentrancy_trusted hop (token : IToken, who : Address) : Uint256 := do
    let _ack := externalCall "ping" [0]
    let observed ← readBal token who
    return observed

  function allow_post_interaction_writes reentrancy_trusted entry
      (token : IToken, who : Address) : Uint256 := do
    let observed ← hop token who
    setStorage last observed
    return observed

namespace RegistryWindowHelperRouting

/-- Distinctive view-call adversary: staticcall sites return 42 instead of the
deterministic stub word. Public `hop` ignores this because it calls stub-only
`readBal`; `hop_registry` / `entry_registry` must observe 42. -/
def distinctiveViewAdv : AdversaryModel where
  stateTransition := fun _ state => state
  result := fun site world =>
    if site.kind = .staticcall then .success [42]
    else AdversaryModel.stub.result site world
  gasUsed := fun _ _ => 0

def distinctiveCtx : Contracts.ExecutableCallContext :=
  Contracts.ExecutableCallContext.ofAdversary distinctiveViewAdv

/-- Public `hop` still uses stub-only `readBal` (no adversary). -/
def hopPublicSeesStub : Bool :=
  match (hop distinctiveCtx 0 0).run Verity.defaultState with
  | .success value _ => !(value == 42)
  | _ => false

example : hopPublicSeesStub = true := by decide

/-- `hop_registry` routes the nested view helper through `readBal_registry`. -/
def hopRegistrySeesAdversary : Bool :=
  match (hop_registry distinctiveCtx 0 0).run Verity.defaultState with
  | .success value _ => value == 42
  | _ => false

example : hopRegistrySeesAdversary = true := by decide

/-- `entry_registry` must call `hop_registry`, not public `hop`. -/
def entryRegistrySeesAdversary : Bool :=
  match (entry_registry distinctiveCtx 0 0).run Verity.defaultState with
  | .success value _ => value == 42
  | _ => false

example : entryRegistrySeesAdversary = true := by decide

end RegistryWindowHelperRouting

/-- `ReentrancyRelyGuarantee` consumes the emitted registry at the restricted
callback boundary.  Contract-specific preservation obligations remain with
authors; this PR establishes only the generated registry/guard connection. -/
theorem generated_registry_callback_preserves
    {adversary : AdversaryModel}
    (hbound : CallbackBounded GeneratedRegistry.entrypointRegistry adversary)
    (hregistry : RegistryPreserves (fun _ => True)
      GeneratedRegistry.entrypointRegistry adversary)
    (site : CallSite) (state : CallState) :
    (fun _ : ContractState => True)
      (denoteCall adversary site state).state.world :=
  hbound.denoteCall_preserves_registry (fun _ => True)
    GeneratedRegistry.entrypointRegistry hregistry site state trivial

end Contracts.ReentrancyRelyGuarantee
