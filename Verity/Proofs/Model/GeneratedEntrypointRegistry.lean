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
entrypoint; there is no `.stub` compatibility path in this theorem surface.
The registry quantifies over the executable resolver, so any
`ExecutableCallContext` carrying the adversary is covered, not only
`ofAdversary` (whose resolver fixes target/value to 0). -/
theorem guardedPing_registered (ectx : Contracts.ExecutableCallContext) (ctx : CallbackContext)
    (value : Uint256) (hvalue : ctx.msgValue = 0) :
    entrypointRegistry ectx.adversary
      (callbackContractTransition ctx (guardedPing_registry ectx value)) := by
  left
  exact ⟨ctx, ectx.resolve, value, hvalue, rfl⟩

/-- The `ofAdversary` instance of the general registration theorem. -/
theorem guardedPing_registered_ofAdversary (adv : AdversaryModel) (ctx : CallbackContext)
    (value : Uint256) (hvalue : ctx.msgValue = 0) :
    entrypointRegistry adv
      (callbackContractTransition ctx
        (guardedPing_registry (Contracts.ExecutableCallContext.ofAdversary adv) value)) :=
  guardedPing_registered (Contracts.ExecutableCallContext.ofAdversary adv) ctx value hvalue

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

/-! Regression: parenthesized overloaded helper + nested `externalCall`.
Second-pass `threadHelperApp?` must resolve the overload from the original
source arguments (`originalArgsForOverload`), not the hoisted temps. Otherwise
the registry body falls through to the public helper and observes stub
returndata. The parenthesized `let observed ← overloadedHop(externalCall ...)`
form is the let-bind second-pass site; `hoistNested` rewrites the nested
`externalCall` argument of that same application. -/
verity_contract RegistryOverloadedNestedExternal where
  storage
    last : Uint256 := slot 0
  linked_externals
    external ping(Uint256) -> (Uint256)

  function overloadedHop (_who : Address) : Uint256 := do
    return 0

  function reentrancy_trusted overloadedHop (x : Uint256) : Uint256 := do
    let observed := externalCall "ping" [x]
    return observed

  function allow_post_interaction_writes reentrancy_trusted entryLet (x : Uint256) : Uint256 := do
    let observed ← overloadedHop(externalCall "ping" [x])
    setStorage last observed
    return observed

namespace RegistryOverloadedNestedExternal

def distinctivePingAdv : AdversaryModel where
  stateTransition := fun _ state => state
  result := fun site world =>
    if site.name = "ping" then .success [42]
    else AdversaryModel.stub.result site world
  gasUsed := fun _ _ => 0

def distinctivePingCtx : Contracts.ExecutableCallContext :=
  Contracts.ExecutableCallContext.ofAdversary distinctivePingAdv

/-- `entryLet_registry` must call `overloadedHop_registry`, not public `overloadedHop`. -/
def entryLetRegistrySeesAdversary : Bool :=
  match (entryLet_registry distinctivePingCtx 0).run Verity.defaultState with
  | .success value _ => value == 42
  | _ => false

example : entryLetRegistrySeesAdversary = true := by decide

end RegistryOverloadedNestedExternal

/-! Regression: `linked_contracts` hop to a view/static-only bound callee.
Public `helper.get` uses `.stub`; `entry_registry` must hop through
`BoundViewCallee.get_registry` so a distinctive staticcall adversary is
observed (Codex P1 on #2406). -/
verity_contract BoundViewCallee where
  storage
    unused : Uint256 := slot 0
  interfaces
    interface IToken where
      function balanceOf(Address) view returns (Uint256)
    end

  function view get (token : IToken, who : Address) : Uint256 := do
    let observed ← token.balanceOf who
    return observed

verity_contract BoundViewCaller where
  storage
    last : Uint256 := slot 0
  interfaces
    interface IViewCallee where
      function get(Address, Address) view returns (Uint256)
    end
  linked_contracts
    helper : IViewCallee := BoundViewCallee

  function allow_post_interaction_writes reentrancy_trusted entry
      (helper : IViewCallee, token : Address, who : Address) : Uint256 := do
    let observed ← helper.get token who
    setStorage last observed
    return observed

namespace BoundViewCaller

def distinctiveViewAdv : AdversaryModel where
  stateTransition := fun _ state => state
  result := fun site world =>
    if site.kind = .staticcall then .success [42]
    else AdversaryModel.stub.result site world
  gasUsed := fun _ _ => 0

def distinctiveCtx : Contracts.ExecutableCallContext :=
  Contracts.ExecutableCallContext.ofAdversary distinctiveViewAdv

/-- Public `entry` is ctx-free and hops to stub-backed `BoundViewCallee.get`. -/
def entryPublicSeesStub : Bool :=
  match (entry 0 0 0).run Verity.defaultState with
  | .success value _ => !(value == 42)
  | _ => false

example : entryPublicSeesStub = true := by decide

/-- `entry_registry` hops through `BoundViewCallee.get_registry`. -/
def entryRegistrySeesAdversary : Bool :=
  match (entry_registry distinctiveCtx 0 0 0).run Verity.defaultState with
  | .success value _ => value == 42
  | _ => false

example : entryRegistrySeesAdversary = true := by decide

end BoundViewCaller

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
