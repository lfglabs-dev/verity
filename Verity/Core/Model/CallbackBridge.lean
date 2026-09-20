import Verity.Core.Model.SummaryBridge
import Verity.Core.Reentrancy

/-!
# Callback-bounded adversaries

Connects the external-call boundary (`AdversaryModel`) to the reentrancy
rely-guarantee framework (`ReentrancySpec`): instead of treating the callee as
an arbitrary world transformer, a *callback-bounded* adversary's committed
transitions are exactly finite reentry schedules drawn from the caller's
registered entrypoints — the callee may call back into the caller, choose any
entrypoints in any order, observe intermediate state, and reenter before the
first call's continuation runs, but it cannot perform caller-state magic that
no entrypoint could.

The payoff mirrors `ReentrancySpec.schedule_preserves`: one invariant proof
per entrypoint extends to every call site of every `CallProgram`, at every
externally opened window, and through the transaction commit/revert boundary.
-/
namespace Compiler.CompilationModel.DenoteExternalCalls

open Verity.Core.Invariant (Preserves runSeq)
open Verity.Core.Reentrancy (ReentrancySpec)

/-- The macro-emitted registry is a predicate rather than a list of already
applied functions.  Entrypoint arguments stay existential, but they are
tied to the same calldata the compiled dispatcher ABI-decodes, and every
transition is indexed by the explicit adversary used at the call boundary. -/
abbrev EntrypointRegistry :=
  AdversaryModel → (Verity.ContractState → Verity.ContractState) → Prop

namespace EntrypointRegistry

/-- Compatibility adapter for the original, argument-free worked examples. -/
def ofList (entrypoints : List (Verity.ContractState → Verity.ContractState)) :
    EntrypointRegistry :=
  fun _ entrypoint => entrypoint ∈ entrypoints

instance : Coe (List (Verity.ContractState → Verity.ContractState))
    EntrypointRegistry where
  coe := ofList

end EntrypointRegistry

/-- EVM frame data chosen by a callee when it calls back into the current
contract.  Entrypoint arguments remain existential in the generated
registry; this record covers the ambient values observable through
`msg.sender`, `msg.value`, and raw calldata intrinsics. -/
structure CallbackContext where
  sender : Verity.Address
  msgValue : Verity.Uint256
  calldataSize : Verity.Uint256
  calldata : List Nat

/-- Packed ABI bytes/string data: 32-byte big-endian words, right-zero-padded.
Not `ExternalArg.toWords`, which journals one word per byte. Fuel is
`bytes.length`, so this is structurally recursive on `Nat` and reduces
under `decide`. -/
def packAbiBytes (bytes : List Nat) : List Nat :=
  packAbiBytesFuel bytes.length bytes
where
  packAbiBytesFuel : Nat → List Nat → List Nat
    | 0, _ => []
    | _n+1, [] => []
    | n+1, x :: xs =>
        let rest := x :: xs
        let chunk := rest.take 32
        let padded := chunk ++ List.replicate (32 - chunk.length) 0
        let word := padded.foldl (fun acc b => acc * 256 + b % 256) 0
        word :: packAbiBytesFuel n (rest.drop 32)

/-- One ABI argument as consumed by `genParamLoads` / compiled dispatch. -/
inductive DispatchVal where
  | word : Nat → DispatchVal
  | bytes : List Nat → DispatchVal
  | array : List DispatchVal → DispatchVal
  | tuple : List DispatchVal → DispatchVal

mutual
  def DispatchVal.isDynamic : DispatchVal → Bool
    | .word _ => false
    | .bytes _ => true
    | .array _ => true
    | .tuple vs => dispatchValAnyDynamic vs

  def dispatchValAnyDynamic : List DispatchVal → Bool
    | [] => false
    | v :: vs => v.isDynamic || dispatchValAnyDynamic vs

  def DispatchVal.headBytes : DispatchVal → Nat
    | .word _ => 32
    | .bytes _ => 32
    | .array _ => 32
    | .tuple vs =>
        if dispatchValAnyDynamic vs then 32
        else dispatchValHeadBytesList vs

  def dispatchValHeadBytesList : List DispatchVal → Nat
    | [] => 0
    | v :: vs => v.headBytes + dispatchValHeadBytesList vs

  /-- Payload words of a value (no parent offset). Dynamic arrays of dynamic
  elements use offsets relative to the start of the post-length head. -/
  def DispatchVal.payloadWords : DispatchVal → List Nat
    | .word w => [w]
    | .bytes bs => bs.length :: packAbiBytes bs
    | .array vs =>
        if dispatchValAnyDynamic vs then
          let (offs, tails) := encodeDynamicList vs (32 * vs.length)
          vs.length :: offs ++ tails
        else
          vs.length :: dispatchValFlatPayload vs
    | .tuple vs =>
        if dispatchValAnyDynamic vs then
          let (heads, tails) := encodeArgBlock vs (dispatchValHeadBytesList vs)
          heads ++ tails
        else
          dispatchValFlatPayload vs

  def dispatchValFlatPayload : List DispatchVal → List Nat
    | [] => []
    | v :: vs => v.payloadWords ++ dispatchValFlatPayload vs

  def encodeDynamicList : List DispatchVal → Nat → List Nat × List Nat
    | [], _ => ([], [])
    | v :: vs, tailOff =>
        let pay := v.payloadWords
        let (offs, tails) := encodeDynamicList vs (tailOff + pay.length * 32)
        (tailOff :: offs, pay ++ tails)

  def encodeArgBlock : List DispatchVal → Nat → List Nat × List Nat
    | [], _ => ([], [])
    | v :: vs, tailOff =>
        if v.isDynamic then
          let pay := v.payloadWords
          let (heads, tails) := encodeArgBlock vs (tailOff + pay.length * 32)
          (tailOff :: heads, pay ++ tails)
        else
          let (heads, tails) := encodeArgBlock vs tailOff
          (v.payloadWords ++ heads, tails)
end

/-- True when every argument is a static ABI word. Kept outside the mutual
block so `decide` unfolds it. -/
def dispatchArgsAllWords : List DispatchVal → Bool
  | [] => true
  | .word _ :: rest => dispatchArgsAllWords rest
  | _ => false

def dispatchArgWordVals : List DispatchVal → List Nat
  | [] => []
  | .word w :: rest => w :: dispatchArgWordVals rest
  | _ :: rest => 0 :: dispatchArgWordVals rest

/-- ABI argument-block encoding matching `genParamLoads`: static values occupy
head words; dynamic values contribute a head offset then a tail of
`[length, packed data…]` (bytes/string) or `[length, elements…]` (arrays).
All-static-word argument lists skip the mutual encoder so kernel `decide`
reduces generated scalar `*_entrypoint` tests. -/
def abiEncodeDispatchArgs (args : List DispatchVal) : List Nat :=
  if dispatchArgsAllWords args then
    dispatchArgWordVals args
  else
    let (heads, tails) := encodeArgBlock args (dispatchValHeadBytesList args)
    heads ++ tails

@[simp] theorem abiEncodeDispatchArgs_nil :
    abiEncodeDispatchArgs [] = [] := rfl

@[simp] theorem abiEncodeDispatchArgs_singleton_word (w : Nat) :
    abiEncodeDispatchArgs [.word w] = [w] := rfl

class ToDispatchVal (α : Type) where
  toDispatchVal : α → DispatchVal

instance : ToDispatchVal Verity.Uint256 where
  toDispatchVal v := .word v.val

instance : ToDispatchVal Verity.Uint16 where
  toDispatchVal v := .word v.toUint256.val

instance : ToDispatchVal (Verity.UIntN bits) where
  toDispatchVal v := .word v.toUint256.val

instance : ToDispatchVal (Verity.IntN bits) where
  toDispatchVal v := .word v.toUint256.val

instance : ToDispatchVal (Verity.BytesN bytes) where
  toDispatchVal v := .word v.toUint256.val

instance : ToDispatchVal Verity.Int256 where
  toDispatchVal v := .word v.word.val

instance : ToDispatchVal Verity.Address where
  toDispatchVal v := .word v.val

instance : ToDispatchVal Bool where
  toDispatchVal v := .word (if v then 1 else 0)

instance : ToDispatchVal Nat where
  toDispatchVal v := .word v

instance : ToDispatchVal ByteArray where
  toDispatchVal b := .bytes (b.data.toList.map (fun x => x.toNat))

instance : ToDispatchVal String where
  toDispatchVal s := ToDispatchVal.toDispatchVal s.toUTF8

instance [ToDispatchVal α] : ToDispatchVal (Array α) where
  toDispatchVal vs := .array (vs.toList.map ToDispatchVal.toDispatchVal)

instance [ToDispatchVal α] [ToDispatchVal β] : ToDispatchVal (α × β) where
  toDispatchVal p := .tuple [ToDispatchVal.toDispatchVal p.1, ToDispatchVal.toDispatchVal p.2]

/-- Compiled dispatch ABI-decodes arguments from the same calldata that
selected the function (`calldataload` at 4 + 32*i, `calldatasize` at
least 4 + 32 * n). Extra trailing words are allowed, matching Yul
`calldatasizeGuard`. `argWords` is the ABI data region (no 4-byte selector),
from `abiEncodeDispatchArgs`, not `ExternalArg.toWords`. -/
def dispatchCalldataMatches (ctx : CallbackContext) (argWords : List Nat) : Prop :=
  ctx.calldata.take argWords.length = argWords ∧
    Verity.Core.Uint256.ofNat (4 + 32 * argWords.length) ≤ ctx.calldataSize

instance (ctx : CallbackContext) (argWords : List Nat) :
    Decidable (dispatchCalldataMatches ctx argWords) := by
  dsimp [dispatchCalldataMatches]
  infer_instance

/-- Compiled `receive()` runs only when `calldatasize == 0`. -/
def receiveCalldataMatches (ctx : CallbackContext) : Prop :=
  ctx.calldata = [] ∧ ctx.calldataSize = 0

instance (ctx : CallbackContext) :
    Decidable (receiveCalldataMatches ctx) := by
  dsimp [receiveCalldataMatches]
  infer_instance

/-- Execute a registered callback in its own call frame, then restore the
outer frame's ambient context while retaining the callback's contract-state
effects. -/
def withCallbackContext (ctx : CallbackContext) (world : Verity.ContractState) :
    Verity.ContractState :=
  { world with
    sender := ctx.sender
    msgValue := ctx.msgValue
    selfBalance := world.selfBalance + ctx.msgValue
    calldataSize := ctx.calldataSize
    calldata := ctx.calldata
    memory := fun _ => 0
    returndata := [] }

def restoreCallbackContext (outer callbackResult : Verity.ContractState) :
    Verity.ContractState :=
  { callbackResult with
    sender := outer.sender
    msgValue := outer.msgValue
    calldataSize := outer.calldataSize
    calldata := outer.calldata
    memory := outer.memory
    returndata := outer.returndata }

def callbackTransition (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState) :
    Verity.ContractState → Verity.ContractState :=
  fun outer => restoreCallbackContext outer (entrypoint (withCallbackContext ctx outer))

/-- Run an executable callback while retaining its success/revert outcome.
Successful callbacks commit their state after restoring the caller's ambient
frame; reverting callbacks roll back the entire callback, including the value
credit installed on entry. -/
def callbackContractTransition (ctx : CallbackContext)
    (entrypoint : Verity.Contract α) :
    Verity.ContractState → Verity.ContractState :=
  fun outer =>
    match entrypoint.run (withCallbackContext ctx outer) with
    | .success _ callbackResult => restoreCallbackContext outer callbackResult
    | .revert _ _ => outer

@[simp] theorem callbackContractTransition_success (ctx : CallbackContext)
    (entrypoint : Verity.Contract α) (outer callbackResult : Verity.ContractState)
    (value : α)
    (hrun : entrypoint.run (withCallbackContext ctx outer) =
      Verity.ContractResult.success value callbackResult) :
    callbackContractTransition ctx entrypoint outer =
      restoreCallbackContext outer callbackResult := by
  simp [callbackContractTransition, hrun]

@[simp] theorem callbackContractTransition_revert (ctx : CallbackContext)
    (entrypoint : Verity.Contract α) (outer : Verity.ContractState) (message : String)
    (hrun : entrypoint.run (withCallbackContext ctx outer) =
      Verity.ContractResult.revert message (withCallbackContext ctx outer)) :
    callbackContractTransition ctx entrypoint outer = outer := by
  simp [callbackContractTransition, hrun]

@[simp] theorem withCallbackContext_sender (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).sender = ctx.sender := rfl

@[simp] theorem withCallbackContext_msgValue (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).msgValue = ctx.msgValue := rfl

@[simp] theorem withCallbackContext_calldata (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).calldata = ctx.calldata := rfl

@[simp] theorem withCallbackContext_calldataSize (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).calldataSize = ctx.calldataSize := rfl

@[simp] theorem withCallbackContext_selfBalance (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).selfBalance = world.selfBalance + ctx.msgValue := rfl

@[simp] theorem withCallbackContext_returndata (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).returndata = [] := rfl

@[simp] theorem withCallbackContext_memory (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).memory = (fun _ => 0) := rfl

@[simp] theorem callbackTransition_restores_sender (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).sender = outer.sender := rfl

@[simp] theorem callbackTransition_restores_msgValue (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).msgValue = outer.msgValue := rfl

@[simp] theorem callbackTransition_restores_calldata (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).calldata = outer.calldata := rfl

@[simp] theorem callbackTransition_restores_calldataSize (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).calldataSize = outer.calldataSize := rfl

@[simp] theorem callbackTransition_restores_memory (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).memory = outer.memory := rfl

@[simp] theorem callbackTransition_restores_returndata (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).returndata = outer.returndata := rfl

/-- Each mutable transition is some finite reentry schedule drawn from the
registry.  Static sites are unrestricted: `denoteCall` never commits their
transitions, and `Conforms` separately pins them externally. -/
def CallbackBounded
    (entrypoints : EntrypointRegistry)
    (adversary : AdversaryModel) : Prop :=
  ∀ site world, site.kind ≠ .staticcall →
    ∃ sched : List (Verity.ContractState → Verity.ContractState),
      (∀ f ∈ sched, entrypoints adversary f) ∧
        adversary.stateTransition site world = runSeq sched world

/-- The sole proof obligation at the generated-registry boundary: every
transition admitted by the registry for this adversary preserves the caller's
invariant. -/
def RegistryPreserves (Inv : Verity.ContractState → Prop)
    (entrypoints : EntrypointRegistry) (adversary : AdversaryModel) : Prop :=
  ∀ f, entrypoints adversary f → Preserves Inv f

/-- A call through the restricted generated-registry boundary preserves any
invariant discharged for every registered, fully-applied entrypoint. -/
theorem CallbackBounded.denoteCall_preserves_registry
    (Inv : Verity.ContractState → Prop) (entrypoints : EntrypointRegistry)
    {adversary : AdversaryModel}
    (hbound : CallbackBounded entrypoints adversary)
    (hregistry : RegistryPreserves Inv entrypoints adversary)
    (site : CallSite) (state : CallState) (hInv : Inv state.world) :
    Inv (denoteCall adversary site state).state.world := by
  cases hkind : site.kind with
  | staticcall =>
      rw [denoteCall_staticcall_world adversary site state hkind]
      exact hInv
  | call =>
      cases hres : adversary.result site state.world with
      | success data =>
          rw [denoteCall_call_success_world adversary site state data hkind hres]
          obtain ⟨sched, hmem, htrans⟩ := hbound site state.world (by simp [hkind])
          rw [htrans]
          exact Verity.Core.Invariant.runSeq_preserves sched
            (fun f hf => hregistry f (hmem f hf)) state.world hInv
      | failure data =>
          rw [denoteCall_failure_world adversary site state data (Or.inl hkind) hres]
          exact hInv
      | revert data =>
          rw [denoteCall_revert_world adversary site state data (Or.inl hkind) hres]
          exact hInv
  | delegatecall =>
      cases hres : adversary.result site state.world with
      | success data =>
          rw [denoteCall_delegatecall_success_world adversary site state data hkind hres]
          obtain ⟨sched, hmem, htrans⟩ := hbound site state.world (by simp [hkind])
          rw [htrans]
          exact Verity.Core.Invariant.runSeq_preserves sched
            (fun f hf => hregistry f (hmem f hf)) state.world hInv
      | failure data =>
          rw [denoteCall_failure_world adversary site state data (Or.inr hkind) hres]
          exact hInv
      | revert data =>
          rw [denoteCall_revert_world adversary site state data (Or.inr hkind) hres]
          exact hInv

/-- One external call under a callback-bounded adversary preserves the spec
invariant: rollback outcomes keep the pre-call world, and committed outcomes
are reentry schedules, covered by the per-entrypoint obligations. -/
theorem CallbackBounded.denoteCall_preserves (spec : ReentrancySpec)
    {adversary : AdversaryModel}
    (h : CallbackBounded (EntrypointRegistry.ofList spec.entrypoints) adversary)
    (site : CallSite) (state : CallState)
    (hInv : spec.Inv state.world) :
    spec.Inv (denoteCall adversary site state).state.world := by
  cases hkind : site.kind with
  | staticcall =>
      rw [denoteCall_staticcall_world adversary site state hkind]
      exact hInv
  | call =>
      cases hres : adversary.result site state.world with
      | success data =>
          rw [denoteCall_call_success_world adversary site state data hkind hres]
          obtain ⟨sched, hmem, htrans⟩ := h site state.world (by simp [hkind])
          rw [htrans]
          exact spec.schedule_preserves sched hmem state.world hInv
      | failure data =>
          rw [denoteCall_failure_world adversary site state data (Or.inl hkind) hres]
          exact hInv
      | revert data =>
          rw [denoteCall_revert_world adversary site state data (Or.inl hkind) hres]
          exact hInv
  | delegatecall =>
      cases hres : adversary.result site state.world with
      | success data =>
          rw [denoteCall_delegatecall_success_world adversary site state data hkind hres]
          obtain ⟨sched, hmem, htrans⟩ := h site state.world (by simp [hkind])
          rw [htrans]
          exact spec.schedule_preserves sched hmem state.world hInv
      | failure data =>
          rw [denoteCall_failure_world adversary site state data (Or.inr hkind) hres]
          exact hInv
      | revert data =>
          rw [denoteCall_revert_world adversary site state data (Or.inr hkind) hres]
          exact hInv

/-- The invariant threads through every call of any program: no finite
sequence of externally opened windows — each free to reenter through any
registered schedule — can break it. -/
theorem CallbackBounded.denote_preserves (spec : ReentrancySpec)
    {adversary : AdversaryModel}
    (h : CallbackBounded (EntrypointRegistry.ofList spec.entrypoints) adversary)
    (prog : CallProgram α) (state : CallState)
    (hInv : spec.Inv state.world) :
    spec.Inv (denote prog adversary state).2.world := by
  induction prog generalizing state with
  | pure value => exact hInv
  | bind site next ih =>
      exact ih (denoteCall adversary site state)
        (denoteCall adversary site state).state
        (h.denoteCall_preserves spec site state hInv)

/-- Through the transaction boundary: a committed transaction ends in an
invariant state by the program law, and a reverted one by rollback to the
initial state. -/
theorem CallbackBounded.transaction_preserves (spec : ReentrancySpec)
    {adversary : AdversaryModel}
    (h : CallbackBounded (EntrypointRegistry.ofList spec.entrypoints) adversary)
    (prog : CallProgram (TransactionResult α)) (state : CallState)
    (hInv : spec.Inv state.world) :
    spec.Inv (denoteTransaction prog adversary state).state.world := by
  cases hres : (denote prog adversary state).1 with
  | commit value =>
      rw [denoteTransaction_commit_eq prog adversary state value hres]
      exact h.denote_preserves spec prog state hInv
  | revert data =>
      rw [denoteTransaction_revert_world prog adversary state data hres]
      exact hInv

end Compiler.CompilationModel.DenoteExternalCalls
