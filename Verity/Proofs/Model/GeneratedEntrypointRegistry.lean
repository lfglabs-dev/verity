import Contracts.Common
import Verity.Core.Model.CallbackBridge
import Verity.Core.Model.NonReentrantGuard
import Compiler.CompilationModel.TrustSurface

namespace Contracts.ReentrancyRelyGuarantee

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
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
    (value : Uint256) (hvalue : ctx.msgValue = 0)
    (hcalldata : dispatchCalldataMatches ctx
      (abiEncodeDispatchArgs [ToDispatchVal.toDispatchVal value])) :
    entrypointRegistry ectx.adversary
      (callbackContractTransition ctx (guardedPing_registry ectx value)) := by
  left
  exact ⟨ctx, ectx.resolve, value, hcalldata, hvalue, rfl⟩

/-- The `ofAdversary` instance of the general registration theorem. -/
theorem guardedPing_registered_ofAdversary (adv : AdversaryModel) (ctx : CallbackContext)
    (value : Uint256) (hvalue : ctx.msgValue = 0)
    (hcalldata : dispatchCalldataMatches ctx
      (abiEncodeDispatchArgs [ToDispatchVal.toDispatchVal value])) :
    entrypointRegistry adv
      (callbackContractTransition ctx
        (guardedPing_registry (Contracts.ExecutableCallContext.ofAdversary adv) value)) :=
  guardedPing_registered (Contracts.ExecutableCallContext.ofAdversary adv) ctx value hvalue
    hcalldata

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

/-! Regression: registered transitions cannot pair Lean arguments with
unrelated calldata, and `receive` is only registered for empty calldata. -/
verity_contract RegistryDispatchCalldata where
  storage
    last : Uint256 := slot 0

  receive := do
    setStorage last 7

  function setLast (value : Uint256) : Unit := do
    setStorage last value
    return ()

namespace RegistryDispatchCalldata

def matchingCtx (value : Uint256) : CallbackContext where
  sender := 0
  msgValue := 0
  calldataSize := Verity.Core.Uint256.ofNat 36
  calldata := [value.val]

def mismatchedCtx : CallbackContext where
  sender := 0
  msgValue := 0
  calldataSize := Verity.Core.Uint256.ofNat 36
  calldata := [99]

def emptyReceiveCtx : CallbackContext where
  sender := 0
  msgValue := 0
  calldataSize := 0
  calldata := []

def nonemptyReceiveCtx : CallbackContext where
  sender := 0
  msgValue := 0
  calldataSize := Verity.Core.Uint256.ofNat 4
  calldata := [1]

def argWords (value : Uint256) : List Nat :=
  abiEncodeDispatchArgs [ToDispatchVal.toDispatchVal value]

example : dispatchCalldataMatches (matchingCtx 7) (argWords 7) := by decide

example : ¬ dispatchCalldataMatches mismatchedCtx (argWords 7) := by decide

example : receiveCalldataMatches emptyReceiveCtx := by decide

example : ¬ receiveCalldataMatches nonemptyReceiveCtx := by decide

theorem setLast_registered_matching (value : Uint256)
    (h : dispatchCalldataMatches (matchingCtx value) (argWords value)) :
    setLast_entrypoint AdversaryModel.stub
      (callbackContractTransition (matchingCtx value)
        (setLast_registry (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) value)) :=
  ⟨matchingCtx value, (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub).resolve,
    value, h, rfl, rfl⟩

theorem setLast_entrypoint_requires_dispatch
    {adv : AdversaryModel} {transition : ContractState → ContractState}
    (h : setLast_entrypoint adv transition) :
    ∃ ctx resolve value,
      dispatchCalldataMatches ctx (argWords value) ∧
        ctx.msgValue = 0 ∧
        transition =
          callbackContractTransition ctx
            (setLast_registry { adversary := adv, resolve := resolve } value) :=
  h

theorem receive_registered_empty :
    __verity_receive_entrypoint AdversaryModel.stub
      (callbackContractTransition emptyReceiveCtx
        (__verity_receive_registry
          (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub))) :=
  ⟨emptyReceiveCtx, (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub).resolve,
    by decide, rfl⟩

theorem receive_entrypoint_requires_empty
    {adv : AdversaryModel} {transition : ContractState → ContractState}
    (h : __verity_receive_entrypoint adv transition) :
    ∃ ctx resolve,
      receiveCalldataMatches ctx ∧
        transition =
          callbackContractTransition ctx
            (__verity_receive_registry { adversary := adv, resolve := resolve }) :=
  h

/-- Journal encoding of `Bytes` is one word per byte (`[len, b0, b1, …]`).
Compiled dispatch marks bytes as dynamic (`DispatchVal.bytes`) and packs
them as `[length, packed data…]` via `abiEncodeDispatchArgs`. -/
example : dispatchArgsAllWords
    [ToDispatchVal.toDispatchVal (ByteArray.mk #[0x61, 0x62])] = false :=
  rfl

example :
    List.map (fun w => (w : Nat))
        (Contracts.ExternalArg.toWords (ByteArray.mk #[0x61, 0x62])) =
      [2, 0x61, 0x62] := by
  decide

end RegistryDispatchCalldata

/-! Regression: registry executables observe live callback calldata, not the
public `calldatasize = 0` / `calldataload offset = offset` stubs. -/
verity_contract RegistryLiveCalldata where
  storage
    last : Uint256 := slot 0

  function setFromCalldata (_value : Uint256)
      local_obligations [manual_low_level_refinement := assumed
        "Fixture reads compiled-dispatch calldata via calldataload 4."]
      : Unit := do
    let cds := calldatasize
    let loaded := calldataload 4
    if cds == 36 then
      setStorage last loaded
    else
      setStorage last 0
    return ()

namespace RegistryLiveCalldata

def liveCtx (value : Uint256) : CallbackContext where
  sender := 0
  msgValue := 0
  calldataSize := Verity.Core.Uint256.ofNat 36
  calldata := [value.val]

def publicWritesStub : Bool :=
  match (setFromCalldata (7 : Uint256)).run Verity.defaultState with
  | .success _ s => s.storage 0 == 0
  | _ => false

example : publicWritesStub = true := by decide

def liveWritesLoaded : Bool :=
  let s := callbackContractTransition (liveCtx 7)
    (setFromCalldata_registry
      (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) 7)
    Verity.defaultState
  s.storage 0 == 7

example : liveWritesLoaded = true := by decide

def liveArgWords (value : Uint256) : List Nat :=
  abiEncodeDispatchArgs [ToDispatchVal.toDispatchVal value]

theorem setFromCalldata_registered_live
    (h : dispatchCalldataMatches (liveCtx 7) (liveArgWords 7)) :
    setFromCalldata_entrypoint AdversaryModel.stub
      (callbackContractTransition (liveCtx 7)
        (setFromCalldata_registry
          (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) 7)) :=
  ⟨liveCtx 7, (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub).resolve,
    7, h, rfl, rfl⟩

end RegistryLiveCalldata

verity_contract RegistryLiveSelector where
  storage
    last : Uint256 := slot 0

  function setFromSelector (_unused : Uint256)
      local_obligations [manual_low_level_refinement := assumed
        "Fixture reads compiled-dispatch selector via calldataload 0."]
      : Unit := do
    let loaded := calldataload 0
    setStorage last loaded
    return ()

namespace RegistryLiveSelector

def selCtx : CallbackContext where
  sender := 0
  msgValue := 0
  calldataSize := Verity.Core.Uint256.ofNat 4
  calldata := []
  selector := 0xa9059cbb

def publicWritesOffset : Bool :=
  match (setFromSelector (0 : Uint256)).run Verity.defaultState with
  | .success _ s => s.storage 0 == 0
  | _ => false

example : publicWritesOffset = true := by decide

def liveWritesSelectorWord : Bool :=
  let s := callbackContractTransition selCtx
    (setFromSelector_registry
      (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) 0)
    Verity.defaultState
  s.storage 0 == Compiler.CompilationModel.Denote.selectorWord 0xa9059cbb

example : liveWritesSelectorWord = true := by decide

end RegistryLiveSelector

/-! P1: FixedArray vs Array encoding; flattened 3-member tuples. -/
example :
    DispatchVal.isDynamic
      (dispatchFixedArray
        [ToDispatchVal.toDispatchVal (1 : Uint256),
         ToDispatchVal.toDispatchVal (2 : Uint256)]) = false :=
  rfl

example :
    (dispatchFixedArray
      [ToDispatchVal.toDispatchVal (1 : Uint256),
       ToDispatchVal.toDispatchVal (2 : Uint256)]).payloadWords = [1, 2] :=
  rfl

example :
    dispatchArgsAllWords
      [ToDispatchVal.toDispatchVal (#[(1 : Uint256), (2 : Uint256)] : Array Uint256)] = false :=
  rfl

example :
    (abiEncodeDispatchArgs
      [ToDispatchVal.toDispatchVal (#[(1 : Uint256), (2 : Uint256)] : Array Uint256)]).head? =
      some 32 :=
  rfl

example :
    dispatchArgsAllWords
      [ToDispatchVal.toDispatchVal
        ((1 : Uint256), ("ab", (3 : Uint256)))] = false :=
  rfl

example :
    dispatchArgsAllWords
      [dispatchFlatTuple
        (DispatchVal.tuple
          [ToDispatchVal.toDispatchVal (1 : Uint256),
           ToDispatchVal.toDispatchVal ("ab" : String),
           ToDispatchVal.toDispatchVal (3 : Uint256)])] = false :=
  rfl

/-! P1: genScalarLoad-normalized noncanonical scalar words still match. -/
example : dispatchCalldataMatchesKinds
    { sender := 0, msgValue := 0,
      calldataSize := Verity.Core.Uint256.ofNat 36, calldata := [2] }
    [.bool]
    (abiEncodeDispatchArgs [ToDispatchVal.toDispatchVal true]) := by decide

example : dispatchCalldataMatchesKinds
    { sender := 0, msgValue := 0,
      calldataSize := Verity.Core.Uint256.ofNat 36, calldata := [256] }
    [.uint8]
    (abiEncodeDispatchArgs [ToDispatchVal.toDispatchVal (0 : Verity.Core.UIntN 8)]) := by decide

example : dispatchCalldataMatchesKinds
    { sender := 0, msgValue := 0,
      calldataSize := Verity.Core.Uint256.ofNat 36,
      calldata := [Compiler.Constants.addressMask + 1 + 7] }
    [.address]
    (abiEncodeDispatchArgs [ToDispatchVal.toDispatchVal (7 : Address)]) := by decide

/-! P1: calldata-reading helpers are routed through *_registry. -/
verity_contract RegistryCalldataHelperRouting where
  storage
    last : Uint256 := slot 0

  function loadArg (_unused : Uint256)
      local_obligations [manual_low_level_refinement := assumed
        "Helper reads compiled-dispatch calldata via calldataload 4."]
      : Uint256 := do
    return calldataload 4

  function setFromHelper (_value : Uint256)
      local_obligations [manual_low_level_refinement := assumed
        "Entrypoint delegates calldata load to an internal helper."]
      : Unit := do
    let loaded ← loadArg 0
    setStorage last loaded
    return ()

namespace RegistryCalldataHelperRouting

def helperCtx (value : Uint256) : CallbackContext where
  sender := 0
  msgValue := 0
  calldataSize := Verity.Core.Uint256.ofNat 36
  calldata := [value.val]

def publicHelperWritesStub : Bool :=
  match (setFromHelper (7 : Uint256)).run Verity.defaultState with
  | .success _ s => s.storage 0 == 4
  | _ => false

example : publicHelperWritesStub = true := by decide

def registryHelperWritesLive : Bool :=
  let s := callbackContractTransition (helperCtx 7)
    (setFromHelper_registry
      (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) 7)
    Verity.defaultState
  s.storage 0 == 7

example : registryHelperWritesLive = true := by decide

end RegistryCalldataHelperRouting

/-! Regression: public Solidity self-calls still hit the nonReentrant tload
prologue. Bound hops must keep the guarded registry path, not `*_unguarded`. -/
verity_contract RegistrySelfCallGuard where
  storage
    lock : Uint256 := slot 0
    last : Uint256 := slot 1
  linked_externals
    external ping(Uint256) -> (Uint256)

  function nonreentrant(lock) reentrancy_trusted hop (value : Uint256) : Unit := do
    let _ack := externalCall "ping" [value]
    setStorage last value
    return ()

  function reentrancy_trusted allow_post_interaction_writes entry
      (value : Uint256)
      local_obligations [manual_low_level_refinement := assumed
        "tryCall/selfCall compilation model is CALL-with-status to this; selector and argument encoding are a documented gap."]
      : Unit := do
    tryCall (selfCall hop(value)) then
      (do setStorage last value)
    catch
      (do setStorage last 99)
    return ()

namespace RegistrySelfCallGuard

def lockedState : ContractState :=
  Verity.defaultState.writeTransient 0 1

def hopBlockedWhenLocked : Bool :=
  match (hop (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) (7 : Uint256)).run lockedState with
  | .revert _ s => s.storage 1 == 0
  | _ => false

example : hopBlockedWhenLocked = true := by decide

def selfCallHopBlockedWhenLocked : Bool :=
  match (entry (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) (7 : Uint256)).run lockedState with
  | .success _ s => s.storage 1 == 99
  | _ => false

example : selfCallHopBlockedWhenLocked = true := by decide

def selfCallHopRegistryBlockedWhenLocked : Bool :=
  match (entry_registry (Contracts.ExecutableCallContext.ofAdversary AdversaryModel.stub) (7 : Uint256)).run lockedState with
  | .success _ s => s.storage 1 == 99
  | _ => false

example : selfCallHopRegistryBlockedWhenLocked = true := by decide

end RegistrySelfCallGuard

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

/-! ### Generated `<fn>_registry_eq`, `entrypointRegistry_cases`, and worked `Vault.withdraw` example (#2564)

This section machine-checks all four deliverables of issue #2564:
1. Per-function `@[simp] theorem <fn>_registry_eq` and per-contract
   `entrypointRegistry_cases` / `entrypointRegistry_preserves` generated by
   `verity_contract`.
2. `CallbackBridge` combinators (`registry_of_preserves`,
   `guarded_callback_preserves_locked`, `preserves_under_lock`,
   `guarded_preserves_of_locked_body`).
3. Packaged `Verity.EVMHyp` (`s.EVMHyp` / `s.msgSender_ne_zero : s.sender ≠ 0`)
   as a theorem hypothesis rather than a custom axiom.
4. End-to-end worked `Vault.withdraw` example (`nonreentrant(lock)` +
   `callWithValue` + post-interaction storage write using `msg.sender`), with a
   clean `#print axioms` footprint and assumption-report verification for both
   `CallbackBounded` and `EVMHyp` ("EVM facts assumed"). -/

example (ectx : Contracts.ExecutableCallContext) (v : Uint256) :
    GeneratedRegistry.guardedPing_registry ectx v =
      GeneratedRegistry.guardedPing ectx v :=
  GeneratedRegistry.guardedPing_registry_eq ectx v

example (ectx : Contracts.ExecutableCallContext) (v : Uint256) :
    GeneratedRegistry.noop_registry ectx v =
      GeneratedRegistry.noop v :=
  GeneratedRegistry.noop_registry_eq ectx v

example (adv : AdversaryModel) (g : ContractState → ContractState) :
    GeneratedRegistry.entrypointRegistry adv g ↔
      (GeneratedRegistry.guardedPing_entrypoint adv g ∨
        GeneratedRegistry.noop_entrypoint adv g) :=
  GeneratedRegistry.entrypointRegistry_cases adv g

verity_contract Vault where
  storage
    lock : Uint256 := slot 0
    totalTracked : Uint256 := slot 1
    lastActor : Address := slot 2

  function payable nonreentrant(lock) deposit () : Unit := do
    let sender ← msgSender
    require (sender != zeroAddress) "zero sender"
    let amount ← msgValue
    let current ← getStorage totalTracked
    let bal ← selfBalance
    require (current + amount <= bal) "accounting overflow"
    setStorage totalTracked (current + amount)
    setStorageAddr lastActor sender
    return ()

  function nonreentrant(lock) withdraw
      (recipient : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let current ← getStorage totalTracked
    require (amount <= current) "insufficient tracked"
    setStorage totalTracked (current - amount)
    ecmDo Compiler.Modules.Calls.callWithValueModule [addressToWord recipient, amount, 0, 0]
    setStorageAddr lastActor sender
    return ()

  function view peekTracked () : Uint256 := do
    let current ← getStorage totalTracked
    return current

namespace Vault

/-- Core Vault invariant:
1. Tracked liabilities (`slot 1`) never exceed `selfBalance`.
2. The recorded `lastActor` (`slot 2`) is never the zero address (`0`). -/
@[reducible] def VaultInv (s : ContractState) : Prop :=
  (s.storage 1).val ≤ s.selfBalance.val ∧ s.storageAddr 2 ≠ 0

theorem vaultInv_frame_calls_returndata
    (w : ContractState) (c : List ExternalCall) (r : List Nat)
    (h : LockedInv VaultInv 0 w) :
    LockedInv VaultInv 0 { w with calls := c, returndata := r } :=
  h

theorem vaultInv_setLock (s : ContractState) (v : Uint256) (h : VaultInv s) :
    VaultInv (Verity.Core.NonReentrantGuard.setLock 0 v s) := by
  refine ⟨?_, ?_⟩
  · simpa [Verity.Core.NonReentrantGuard.setLock, ContractState.storage,
      ContractState.writeTransient] using h.1
  · simpa [Verity.Core.NonReentrantGuard.setLock, ContractState.storageAddr,
      ContractState.writeTransient] using h.2

/-- 1a. `deposit_entrypoint` preserves `LockedInv VaultInv 0` because `deposit`
is `guarded 0 ...` and reverts immediately when lock slot `0` is nonzero. -/
theorem deposit_entrypoint_preserves_locked (adv : AdversaryModel) :
    RegistryPreserves (LockedInv VaultInv 0) deposit_entrypoint adv := by
  rintro g ⟨ctx, resolve, _hcalldata, rfl⟩
  rw [deposit_registry_eq]
  exact guarded_callback_preserves_locked VaultInv 0 ctx _

/-- 1b. `withdraw_entrypoint` preserves `LockedInv VaultInv 0` because `withdraw`
is `guarded 0 ...` and reverts immediately when lock slot `0` is nonzero. -/
theorem withdraw_entrypoint_preserves_locked (adv : AdversaryModel) :
    RegistryPreserves (LockedInv VaultInv 0) withdraw_entrypoint adv := by
  rintro g ⟨ctx, resolve, recipient, amount, _hcalldata, _hval, rfl⟩
  rw [withdraw_registry_eq]
  exact guarded_callback_preserves_locked VaultInv 0 ctx _

/-- 1c. `peekTracked_entrypoint` is an unguarded `view` entrypoint; we discharge
it via `callbackContractTransition_preserves` because it neither modifies
storage/transientStorage nor credits `msgValue` (it is non-payable, so
`ctx.msgValue = 0`). -/
theorem peekTracked_entrypoint_preserves_locked (adv : AdversaryModel) :
    RegistryPreserves (LockedInv VaultInv 0) peekTracked_entrypoint adv := by
  rintro g ⟨ctx, resolve, _hcalldata, hval, rfl⟩
  rw [peekTracked_registry_eq]
  apply callbackContractTransition_preserves
  intro s a s' ⟨⟨hbal, hactor⟩, hlock⟩ hrun
  have hEq : s' = withCallbackContext ctx s := by
    simp [peekTracked, Contract.run, getStorage, ContractState.readSlot,
      Verity.pure, Pure.pure, Bind.bind, Verity.bind] at hrun
    exact hrun.2.symm
  subst hEq
  refine ⟨⟨?_, by simpa using hactor⟩, by simpa using hlock⟩
  rw [restoreCallbackContext_selfBalance, withCallbackContext_selfBalance_of_msgValue_zero ctx s hval]
  simpa using hbal

/-- 2. Compose the per-entrypoint proofs into `RegistryPreserves` for the whole
generated `Vault.entrypointRegistry` via the macro-generated
`Vault.entrypointRegistry_preserves` theorem. -/
theorem registry_preserves_locked (adv : AdversaryModel) :
    RegistryPreserves (LockedInv VaultInv 0) entrypointRegistry adv :=
  entrypointRegistry_preserves (LockedInv VaultInv 0) adv
    (deposit_entrypoint_preserves_locked adv)
    (withdraw_entrypoint_preserves_locked adv)
    (peekTracked_entrypoint_preserves_locked adv)

private theorem locked_after_tracked_sub
    (s₁ : ContractState) (amount : Uint256)
    (hlocked : LockedInv VaultInv 0 s₁)
    (hamt : amount.val ≤ (s₁.storage 1).val) :
    LockedInv VaultInv 0 (s₁.writeSlot 1 (s₁.storage 1 - amount)) := by
  obtain ⟨⟨hbal, hactor⟩, hlock⟩ := hlocked
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [ContractState.storage_writeSlot_same, ContractState.selfBalance_writeSlot]
    have hsub : (s₁.storage 1 - amount).val = (s₁.storage 1).val - amount.val :=
      Core.Uint256.subNoWrap hamt
    omega
  · simpa [ContractState.storageAddr_writeSlot] using hactor
  · simpa [ContractState.transientStorage, ContractState.writeSlot] using hlock

private theorem locked_after_tracked_sub_and_debit
    (s₁ : ContractState) (amount : Uint256)
    (hlocked : LockedInv VaultInv 0 s₁)
    (hamt : amount.val ≤ (s₁.storage 1).val)
    (hbal_deb : amount.val ≤ (s₁.writeSlot 1 (s₁.storage 1 - amount)).selfBalance.val) :
    LockedInv VaultInv 0
      { s₁.writeSlot 1 (s₁.storage 1 - amount) with
        selfBalance := (s₁.writeSlot 1 (s₁.storage 1 - amount)).selfBalance -
          Core.Uint256.ofNat amount.val } := by
  obtain ⟨⟨hbal, hactor⟩, hlock⟩ := hlocked
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change ((s₁.writeSlot 1 (s₁.storage 1 - amount)).storage 1).val ≤
      (s₁.selfBalance - Core.Uint256.ofNat amount.val).val
    simp only [ContractState.storage_writeSlot_same]
    have hofNat : Core.Uint256.ofNat amount.val = amount := by
      apply Core.Uint256.ext
      exact Nat.mod_eq_of_lt amount.isLt
    rw [hofNat]
    have hsub₁ : (s₁.storage 1 - amount).val = (s₁.storage 1).val - amount.val :=
      Core.Uint256.subNoWrap hamt
    have hbal_deb' : amount.val ≤ s₁.selfBalance.val := hbal_deb
    have hsub₂ : (s₁.selfBalance - amount).val = s₁.selfBalance.val - amount.val :=
      Core.Uint256.subNoWrap hbal_deb'
    omega
  · change (s₁.writeSlot 1 (s₁.storage 1 - amount)).storageAddr 2 ≠ 0
    simpa [ContractState.storageAddr_writeSlot] using hactor
  · change (s₁.writeSlot 1 (s₁.storage 1 - amount)).transientStorage 0 ≠ 0
    simpa [ContractState.transientStorage, ContractState.writeSlot] using hlock

private theorem ecmDoWords_raw_of_run_success
    (mod : Compiler.ECM.ExternalCallModule) (adv : AdversaryModel)
    (args : List Uint256) (ret : Nat) (s s' : ContractState) (u : Unit)
    (hecm : (Contracts.ecmDoWords mod adv args ret).run s = .success u s') :
    Contracts.ecmDoWords mod adv args ret s = .success () s' := by
  simp only [Contract.run] at hecm
  revert hecm
  cases Contracts.ecmDoWords mod adv args ret s with
  | success a _ => cases a; exact id
  | «revert» _ _ => intro hEq; cases hEq

private theorem ecmDoWords_raw_of_run_revert
    (mod : Compiler.ECM.ExternalCallModule) (adv : AdversaryModel)
    (args : List Uint256) (ret : Nat) (s s' : ContractState) (msg : String)
    (hecm : (Contracts.ecmDoWords mod adv args ret).run s = .revert msg s') :
    ∃ s_rev, Contracts.ecmDoWords mod adv args ret s = .revert msg s_rev := by
  simp only [Contract.run] at hecm
  revert hecm
  cases Contracts.ecmDoWords mod adv args ret s with
  | success _ _ => intro hEq; cases hEq
  | «revert» msg' s_rev => intro hEq; cases hEq; exact ⟨s_rev, rfl⟩

private theorem locked_after_withdraw_ecm
    (adv : AdversaryModel) (hbound : CallbackBounded entrypointRegistry adv)
    (recipient : Address) (amount : Uint256) (s₁ s₃ : ContractState) (unitVal : Unit)
    (hlocked₁ : LockedInv VaultInv 0 s₁) (hamt : amount.val ≤ (s₁.storage 1).val)
    (hecm : (Contracts.ecmDoWords Compiler.Modules.Calls.callWithValueModule adv
      [Verity.addressToWord recipient, amount, Core.Uint256.ofNat 0, Core.Uint256.ofNat 0] 0).run
      (s₁.writeSlot 1 (s₁.storage 1 - amount)) = .success unitVal s₃) :
    LockedInv VaultInv 0 s₃ := by
  set s₂ := s₁.writeSlot 1 (s₁.storage 1 - amount)
  set args := [Verity.addressToWord recipient, amount, Core.Uint256.ofNat 0, Core.Uint256.ofNat 0]
  have hlocked₂ : LockedInv VaultInv 0 s₂ := locked_after_tracked_sub s₁ amount hlocked₁ hamt
  have hdeb₂ : Contracts.ecmValueWord Compiler.Modules.Calls.callWithValueModule args ≤ s₂.selfBalance.val →
      LockedInv VaultInv 0 { s₂ with selfBalance := s₂.selfBalance -
        (Contracts.ecmValueWord Compiler.Modules.Calls.callWithValueModule args : Core.Uint256) } := by
    intro hbal_deb
    simp only [args, Contracts.ecmValueWord_callWithValueModule] at hbal_deb ⊢
    exact locked_after_tracked_sub_and_debit s₁ amount hlocked₁ hamt hbal_deb
  exact Contracts.ecmDoWords_callbackBounded_preserves_registry_of_success
    (LockedInv VaultInv 0) entrypointRegistry
    Compiler.Modules.Calls.callWithValueModule adv args 0 s₂ s₃
    hbound (registry_preserves_locked adv) vaultInv_frame_calls_returndata
    hlocked₂ hdeb₂ hecm

/-- 3. Worked end-to-end reentrancy theorem (`Vault.keeps_withdraw`):
Under `CallbackBounded Vault.entrypointRegistry adv` and the packaged EVM
environment hypothesis `s.EVMHyp` (`s.sender ≠ 0`), `Vault.withdraw` preserves
`VaultInv` across its `callWithValue` interaction and subsequent post-interaction
write `setStorageAddr lastActor sender`. -/
theorem keeps_withdraw
    (adv : AdversaryModel) (hbound : CallbackBounded entrypointRegistry adv)
    (recipient : Address) (amount : Uint256)
    (s : ContractState) (hevm : s.EVMHyp) (hInv : VaultInv s) :
    VaultInv ((withdraw (Contracts.ExecutableCallContext.ofAdversary adv) recipient amount).run s).snd := by
  refine guarded_preserves_of_locked_body VaultInv 0 _ vaultInv_setLock s ?_ hInv
  intro u s_final hlocked₁ hbody
  set s₁ := Verity.Core.NonReentrantGuard.setLock 0 1 s
  simp only [Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    msgSender, getStorage, totalTracked, setStorage, setStorageAddr, lastActor,
    ContractState.readSlot, Verity.require,
    Contracts.ExecutableCallContext.ofAdversary,
    Contracts.ExternalArg.toWords, List.flatten] at hbody
  by_cases hreq : decide (amount ≤ s₁.storage 1) = true
  · rw [if_pos hreq] at hbody
    dsimp only [List.append] at hbody
    cases hecm : (Contracts.ecmDoWords Compiler.Modules.Calls.callWithValueModule adv
        [Verity.addressToWord recipient, amount, Core.Uint256.ofNat 0, Core.Uint256.ofNat 0] 0).run
        (s₁.writeSlot 1 (s₁.storage 1 - amount)) with
    | «revert» msg s_rev =>
        obtain ⟨s_rev', hraw⟩ := ecmDoWords_raw_of_run_revert _ adv _ 0 _ s_rev msg hecm
        rw [hraw] at hbody; cases hbody
    | success unitVal s₃ =>
        rw [ecmDoWords_raw_of_run_success _ adv _ 0 _ s₃ unitVal hecm] at hbody
        simp only [ContractResult.success.injEq, true_and] at hbody; subst hbody
        have hlocked₃ := locked_after_withdraw_ecm adv hbound recipient amount s₁ s₃ unitVal
          hlocked₁ (of_decide_eq_true hreq) hecm
        exact ⟨by simpa [ContractState.storage_writeAddrSlot] using hlocked₃.1.1,
          by rw [ContractState.storageAddr_writeAddrSlot_same]; exact hevm.msgSender_ne_zero⟩
  · rw [if_neg hreq] at hbody; cases hbody

/-- Assumption-report check (#2564): when `Vault.keeps_withdraw`'s hypotheses
(`CallbackBounded` and `EVMHyp` / `msgSender_ne_zero`) are attached to
`Vault.spec`, `theoremAssumptionsFromUsedConstants` and `withTheoremAssumptions`
surface both `"CallbackBounded"` (`boundaryClass: "callback"`) and
`"EVM facts assumed"` (`boundaryClass: "compilerIntrinsic"`). -/
def keepsWithdrawAssumptions : List Compiler.CompilationModel.LocalObligation :=
  Compiler.CompilationModel.theoremAssumptionsFromUsedConstants
    ["Compiler.CompilationModel.DenoteExternalCalls.CallbackBounded",
     "Verity.ContractState.EVMHyp",
     "Verity.EVMHyp.msgSender_ne_zero"]
    "Vault"

theorem callbackBounded_assumption_fields :
    (Compiler.CompilationModel.LocalObligation.callbackBounded "Vault").name = "CallbackBounded" ∧
    (Compiler.CompilationModel.LocalObligation.callbackBounded "Vault").proofStatus = .assumed ∧
    (Compiler.CompilationModel.LocalObligation.callbackBounded "Vault").obligation =
      "Adversary callbacks restricted to Vault.entrypointRegistry (CallbackBounded)" :=
  ⟨rfl, rfl, rfl⟩

theorem evmHyp_assumption_fields :
    Compiler.CompilationModel.LocalObligation.evmHyp.name = "EVMHyp" ∧
    Compiler.CompilationModel.LocalObligation.evmHyp.obligation =
      "EVM facts assumed: s.sender ≠ 0, s.thisAddress ≠ 0, s.chainId ≠ 0" ∧
    Compiler.CompilationModel.LocalObligation.msgSenderNeZero.name = "msgSender_ne_zero" ∧
    Compiler.CompilationModel.LocalObligation.msgSenderNeZero.obligation =
      "EVM facts assumed: s.sender ≠ 0" :=
  ⟨rfl, rfl, rfl, rfl⟩

end Vault

end Contracts.ReentrancyRelyGuarantee
