import Contracts.Common
import Verity.Core.Model.CallbackBridge
import Verity.Core.Model.NonReentrantGuard

namespace Contracts.ReentrancyRelyGuarantee

open Contracts
open Verity hiding pure bind

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

open Compiler.CompilationModel.DenoteExternalCalls

/-- The generated registry uses its explicit adversary at the external-call
entrypoint; there is no `.stub` compatibility path in this theorem surface. -/
theorem guardedPing_registered (adv : AdversaryModel) (ctx : CallbackContext)
    (value : Uint256) :
    entrypointRegistry adv
      (callbackTransition ctx
        (guardedPing_registry (ExecutableCallContext.ofAdversary adv) value).runState) := by
  left
  exact ⟨ctx, value, rfl⟩

/-- The executable generated entrypoint is definitionally protected by the
canonical source guard at the same slot used by the compiled dispatch guard. -/
theorem guardedPing_reentry_blocked (adv : AdversaryModel) (value : Uint256)
    (state : ContractState) (hlock : state.transientStorage 0 ≠ 0) :
    (guardedPing (ExecutableCallContext.ofAdversary adv) value).runState state = state := by
  apply Verity.Core.NonReentrantGuard.guarded_reentry_blocked
  exact hlock

end GeneratedRegistry

open Compiler.CompilationModel.DenoteExternalCalls

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
