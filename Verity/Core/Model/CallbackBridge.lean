import Verity.Core.Model.SummaryBridge
import Verity.Core.Model.NonReentrantGuard
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
  /-- 4-byte selector of the selected entrypoint. Live `calldataload 0`
  observes this via `ContractState.selector`. Defaults to 0 so existing
  fixtures that omit it stay well-typed. -/
  selector : Nat := 0

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
block so `decide` unfolds it. Static tuples/fixed arrays use `payloadWords`
via the mutual encoder (not this fast path). -/
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

/-- Right-nested Lean products (`α × (β × γ)`) encode as a nested ABI tuple
unless flattened. Compiled `Tuple [α, β, γ]` is a single flat tuple. -/
def flattenDispatchTuple : DispatchVal → List DispatchVal
  | .tuple vs => vs.flatMap flattenDispatchTuple
  | v => [v]

/-- Compiled `T[n]` is a static/dynamic composite with no `T[]` length word.
Encode as a tuple of n members (inlined if static; offset-only if dynamic). -/
def dispatchFixedArray (elems : List DispatchVal) : DispatchVal :=
  .tuple elems

/-- Flatten a right-nested product encoding into one ABI tuple. -/
def dispatchFlatTuple (v : DispatchVal) : DispatchVal :=
  .tuple (flattenDispatchTuple v)

instance [ToDispatchVal α] [ToDispatchVal β] : ToDispatchVal (α × β) where
  toDispatchVal p :=
    .tuple (flattenDispatchTuple (ToDispatchVal.toDispatchVal p.1) ++
      flattenDispatchTuple (ToDispatchVal.toDispatchVal p.2))

/-- How `genScalarLoad` normalizes a loaded word before the body sees it. -/
inductive ScalarLoadKind where
  | identity
  | bool
  | uint8
  | uint16
  | uintN (bits : Nat)
  | address
  | bytesN (bytes : Nat)
  deriving Repr, DecidableEq

def normalizeLoadedWord (kind : ScalarLoadKind) (loaded : Nat) : Nat :=
  let w := loaded % Compiler.Constants.evmModulus
  match kind with
  | .identity => w
  | .bool => if w == 0 then 0 else 1
  | .uint8 => w % 256
  | .uint16 => w % 65536
  | .uintN bits => w % (2 ^ bits)
  | .address => w &&& Compiler.Constants.addressMask
  | .bytesN bytes =>
      w &&& ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))

def scalarWordMatches (kind : ScalarLoadKind) (canonical loaded : Nat) : Bool :=
  normalizeLoadedWord kind loaded == canonical % Compiler.Constants.evmModulus

def dispatchWordsMatch : List ScalarLoadKind → List Nat → List Nat → Bool
  | [], _, _ => true
  | _ :: _, [], _ => false
  | _ :: _, _ :: _, [] => false
  | k :: ks, c :: cs, l :: ls =>
      scalarWordMatches k c l && dispatchWordsMatch ks cs ls

/-- Compiled dispatch ABI-decodes arguments from the same calldata that
selected the function (`calldataload` at 4 + 32*i, `calldatasize` at
least 4 + 32 * n). Extra trailing words are allowed, matching Yul
`calldatasizeGuard`. `argWords` is the ABI data region (no 4-byte selector),
from `abiEncodeDispatchArgs`, not `ExternalArg.toWords`. Scalar prefixes
compare after `genScalarLoad` normalization so noncanonical Bool/uintN/
address words still register. -/
def dispatchCalldataMatches (ctx : CallbackContext) (argWords : List Nat) : Prop :=
  dispatchWordsMatch
      (List.replicate argWords.length ScalarLoadKind.identity)
      argWords (ctx.calldata.take argWords.length) = true ∧
    Verity.Core.Uint256.ofNat (4 + 32 * argWords.length) ≤ ctx.calldataSize

/-- Like `dispatchCalldataMatches`, but scalar words compare after the compiled
`genScalarLoad` normalization for each argument. -/
def dispatchCalldataMatchesKinds (ctx : CallbackContext)
    (kinds : List ScalarLoadKind) (argWords : List Nat) : Prop :=
  dispatchWordsMatch kinds argWords (ctx.calldata.take argWords.length) = true ∧
    Verity.Core.Uint256.ofNat (4 + 32 * argWords.length) ≤ ctx.calldataSize

instance (ctx : CallbackContext) (kinds : List ScalarLoadKind) (argWords : List Nat) :
    Decidable (dispatchCalldataMatchesKinds ctx kinds argWords) := by
  dsimp [dispatchCalldataMatchesKinds]
  infer_instance

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
    selector := ctx.selector
    memory := fun _ => 0
    returndata := [] }

def restoreCallbackContext (outer callbackResult : Verity.ContractState) :
    Verity.ContractState :=
  { callbackResult with
    sender := outer.sender
    msgValue := outer.msgValue
    calldataSize := outer.calldataSize
    calldata := outer.calldata
    selector := outer.selector
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

@[simp] theorem withCallbackContext_selector (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).selector = ctx.selector := rfl

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

@[simp] theorem callbackTransition_restores_selector (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).selector = outer.selector := rfl

@[simp] theorem callbackTransition_restores_memory (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).memory = outer.memory := rfl

@[simp] theorem callbackTransition_restores_returndata (ctx : CallbackContext)
    (entrypoint : Verity.ContractState → Verity.ContractState)
    (outer : Verity.ContractState) :
    (callbackTransition ctx entrypoint outer).returndata = outer.returndata := rfl

@[simp] theorem withCallbackContext_storageWords (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).storageWords = world.storageWords := rfl

@[simp] theorem withCallbackContext_storage (ctx : CallbackContext)
    (world : Verity.ContractState) (slot : Nat) :
    (withCallbackContext ctx world).storage slot = world.storage slot := rfl

@[simp] theorem withCallbackContext_storageAddr (ctx : CallbackContext)
    (world : Verity.ContractState) (slot : Nat) :
    (withCallbackContext ctx world).storageAddr slot = world.storageAddr slot := rfl

@[simp] theorem withCallbackContext_storageMap (ctx : CallbackContext)
    (world : Verity.ContractState) (slot : Nat) (key : Verity.Address) :
    (withCallbackContext ctx world).storageMap slot key = world.storageMap slot key := rfl

@[simp] theorem withCallbackContext_storageMapUint (ctx : CallbackContext)
    (world : Verity.ContractState) (slot : Nat) (key : Verity.Uint256) :
    (withCallbackContext ctx world).storageMapUint slot key = world.storageMapUint slot key := rfl

@[simp] theorem withCallbackContext_storageMap2 (ctx : CallbackContext)
    (world : Verity.ContractState) (slot : Nat) (k1 k2 : Verity.Address) :
    (withCallbackContext ctx world).storageMap2 slot k1 k2 = world.storageMap2 slot k1 k2 := rfl

@[simp] theorem withCallbackContext_storageArray (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).storageArray = world.storageArray := rfl

@[simp] theorem withCallbackContext_transientStorage (ctx : CallbackContext)
    (world : Verity.ContractState) (slot : Nat) :
    (withCallbackContext ctx world).transientStorage slot = world.transientStorage slot := rfl

@[simp] theorem withCallbackContext_thisAddress (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).thisAddress = world.thisAddress := rfl

@[simp] theorem withCallbackContext_chainId (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).chainId = world.chainId := rfl

@[simp] theorem withCallbackContext_blockTimestamp (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).blockTimestamp = world.blockTimestamp := rfl

@[simp] theorem withCallbackContext_blockNumber (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).blockNumber = world.blockNumber := rfl

@[simp] theorem withCallbackContext_blobBaseFee (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).blobBaseFee = world.blobBaseFee := rfl

@[simp] theorem withCallbackContext_baseFee (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).baseFee = world.baseFee := rfl

@[simp] theorem withCallbackContext_gasPrice (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).gasPrice = world.gasPrice := rfl

@[simp] theorem withCallbackContext_txOrigin (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).txOrigin = world.txOrigin := rfl

@[simp] theorem withCallbackContext_knownAddresses (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).knownAddresses = world.knownAddresses := rfl

@[simp] theorem withCallbackContext_events (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).events = world.events := rfl

@[simp] theorem withCallbackContext_calls (ctx : CallbackContext)
    (world : Verity.ContractState) :
    (withCallbackContext ctx world).calls = world.calls := rfl

theorem withCallbackContext_selfBalance_of_msgValue_zero (ctx : CallbackContext)
    (world : Verity.ContractState) (h : ctx.msgValue = 0) :
    (withCallbackContext ctx world).selfBalance = world.selfBalance := by
  simp [withCallbackContext, h, Verity.Core.Uint256.add_zero]

@[simp] theorem restoreCallbackContext_storageWords
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).storageWords = callbackResult.storageWords := rfl

@[simp] theorem restoreCallbackContext_storage
    (outer callbackResult : Verity.ContractState) (slot : Nat) :
    (restoreCallbackContext outer callbackResult).storage slot = callbackResult.storage slot := rfl

@[simp] theorem restoreCallbackContext_storageAddr
    (outer callbackResult : Verity.ContractState) (slot : Nat) :
    (restoreCallbackContext outer callbackResult).storageAddr slot = callbackResult.storageAddr slot := rfl

@[simp] theorem restoreCallbackContext_storageMap
    (outer callbackResult : Verity.ContractState) (slot : Nat) (key : Verity.Address) :
    (restoreCallbackContext outer callbackResult).storageMap slot key = callbackResult.storageMap slot key := rfl

@[simp] theorem restoreCallbackContext_storageMapUint
    (outer callbackResult : Verity.ContractState) (slot : Nat) (key : Verity.Uint256) :
    (restoreCallbackContext outer callbackResult).storageMapUint slot key = callbackResult.storageMapUint slot key := rfl

@[simp] theorem restoreCallbackContext_storageMap2
    (outer callbackResult : Verity.ContractState) (slot : Nat) (k1 k2 : Verity.Address) :
    (restoreCallbackContext outer callbackResult).storageMap2 slot k1 k2 = callbackResult.storageMap2 slot k1 k2 := rfl

@[simp] theorem restoreCallbackContext_storageArray
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).storageArray = callbackResult.storageArray := rfl

@[simp] theorem restoreCallbackContext_transientStorage
    (outer callbackResult : Verity.ContractState) (slot : Nat) :
    (restoreCallbackContext outer callbackResult).transientStorage slot =
      callbackResult.transientStorage slot := rfl

@[simp] theorem restoreCallbackContext_selfBalance
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).selfBalance = callbackResult.selfBalance := rfl

@[simp] theorem restoreCallbackContext_thisAddress
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).thisAddress = callbackResult.thisAddress := rfl

@[simp] theorem restoreCallbackContext_chainId
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).chainId = callbackResult.chainId := rfl

@[simp] theorem restoreCallbackContext_blockTimestamp
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).blockTimestamp = callbackResult.blockTimestamp := rfl

@[simp] theorem restoreCallbackContext_blockNumber
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).blockNumber = callbackResult.blockNumber := rfl

@[simp] theorem restoreCallbackContext_blobBaseFee
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).blobBaseFee = callbackResult.blobBaseFee := rfl

@[simp] theorem restoreCallbackContext_baseFee
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).baseFee = callbackResult.baseFee := rfl

@[simp] theorem restoreCallbackContext_gasPrice
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).gasPrice = callbackResult.gasPrice := rfl

@[simp] theorem restoreCallbackContext_txOrigin
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).txOrigin = callbackResult.txOrigin := rfl

@[simp] theorem restoreCallbackContext_knownAddresses
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).knownAddresses = callbackResult.knownAddresses := rfl

@[simp] theorem restoreCallbackContext_events
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).events = callbackResult.events := rfl

@[simp] theorem restoreCallbackContext_calls
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).calls = callbackResult.calls := rfl

@[simp] theorem restoreCallbackContext_sender
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).sender = outer.sender := rfl

@[simp] theorem restoreCallbackContext_msgValue
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).msgValue = outer.msgValue := rfl

@[simp] theorem restoreCallbackContext_calldata
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).calldata = outer.calldata := rfl

@[simp] theorem restoreCallbackContext_calldataSize
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).calldataSize = outer.calldataSize := rfl

@[simp] theorem restoreCallbackContext_selector
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).selector = outer.selector := rfl

@[simp] theorem restoreCallbackContext_memory
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).memory = outer.memory := rfl

@[simp] theorem restoreCallbackContext_returndata
    (outer callbackResult : Verity.ContractState) :
    (restoreCallbackContext outer callbackResult).returndata = outer.returndata := rfl

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

/-- Registry built from a list of parameterized `Contract` entrypoints under
arbitrary `CallbackContext` frames. -/
def EntrypointRegistry.ofContracts {Args : Type} {α : Type}
    (entrypoints : List (Args → Verity.Contract α)) : EntrypointRegistry :=
  fun _ g => ∃ ctx : CallbackContext, ∃ args : Args, ∃ f,
    f ∈ entrypoints ∧ g = callbackContractTransition ctx (f args)

/-- Compositor lifting per-entrypoint preservation across
`callbackContractTransition` to `RegistryPreserves` for a parameterized
entrypoint list (#2564). -/
theorem registry_of_preserves {Args : Type} {α : Type}
    (Inv : Verity.ContractState → Prop)
    {entrypoints : List (Args → Verity.Contract α)}
    {adv : AdversaryModel}
    (h : ∀ (ctx : CallbackContext) (args : Args) (f : Args → Verity.Contract α),
      f ∈ entrypoints → Preserves Inv (callbackContractTransition ctx (f args))) :
    RegistryPreserves Inv (EntrypointRegistry.ofContracts entrypoints) adv := by
  rintro g ⟨ctx, args, f, hf, rfl⟩
  exact h ctx args f hf

/-- Discharge `Preserves Inv (callbackContractTransition ctx c)` from successful
runs of `c`; reverted callback executions roll back to `outer` automatically. -/
theorem callbackContractTransition_preserves {α : Type}
    (Inv : Verity.ContractState → Prop)
    (ctx : CallbackContext) (c : Verity.Contract α)
    (hstep : ∀ s a s', Inv s →
      c.run (withCallbackContext ctx s) = .success a s' →
      Inv (restoreCallbackContext s s')) :
    Preserves Inv (callbackContractTransition ctx c) := by
  intro s hInv
  unfold callbackContractTransition
  cases hrun : c.run (withCallbackContext ctx s) with
  | success a s' => exact hstep s a s' hInv hrun
  | revert _ _ => exact hInv

namespace RegistryPreserves

theorem of_false (Inv : Verity.ContractState → Prop) (adv : AdversaryModel) :
    RegistryPreserves Inv (fun _ _ => False) adv :=
  fun _ h => False.elim h

theorem of_or {Inv : Verity.ContractState → Prop}
    {E₁ E₂ : EntrypointRegistry} {adv : AdversaryModel}
    (h₁ : RegistryPreserves Inv E₁ adv)
    (h₂ : RegistryPreserves Inv E₂ adv) :
    RegistryPreserves Inv (fun a g => E₁ a g ∨ E₂ a g) adv := by
  intro g hg
  rcases hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

theorem of_iff {Inv : Verity.ContractState → Prop}
    {E₁ E₂ : EntrypointRegistry} {adv : AdversaryModel}
    (hiff : ∀ g, E₁ adv g ↔ E₂ adv g)
    (h₂ : RegistryPreserves Inv E₂ adv) :
    RegistryPreserves Inv E₁ adv :=
  fun g hg => h₂ g ((hiff g).mp hg)

end RegistryPreserves

/-! ## Breaking reentrancy circularity under a transient lock (#2564)

When a `nonreentrant(lockSlot)` entrypoint `withdraw` makes an external call,
`withdraw` preserves the contract invariant `Inv` only if every registered
callback preserves `Inv` — and `withdraw` is itself in the registry.

While the transient lock at `lockSlot` is held (`s.transientStorage lockSlot ≠ 0`),
any reentrant callback to a `guarded lockSlot` entrypoint reverts immediately at
the `tload` check (`guarded_locked_reverts`), acting as the identity on state.
Strengthening `Inv` to `LockedInv Inv lockSlot` (`Inv s ∧ s.transientStorage lockSlot ≠ 0`)
or `InvT Inv T` (`Inv s ∧ s.transientStorage = T`) breaks the circularity:
1. Every `guarded lockSlot` entrypoint preserves `LockedInv Inv lockSlot` unconditionally (`guarded_callback_preserves_locked`).
2. Every other entrypoint that preserves `Inv` and does not clear `transientStorage lockSlot` also preserves `LockedInv Inv lockSlot` (`preserves_under_lock`).
3. Once `RegistryPreserves (LockedInv Inv lockSlot) registry adv` is established, the external call inside `withdraw` preserves `LockedInv Inv lockSlot`, so `withdraw` preserves `Inv` (and leaves `transientStorage lockSlot = 0`) on all states (`guarded_preserves_of_locked_body`). -/

/-- Strengthen `Inv` with the fact that transient lock `lockSlot` is currently held. -/
def LockedInv (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    (s : Verity.ContractState) : Prop :=
  Inv s ∧ s.transientStorage lockSlot ≠ 0

/-- Strengthen `Inv` with the fact that transient lock `lockSlot` is clear. -/
def UnlockedInv (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    (s : Verity.ContractState) : Prop :=
  Inv s ∧ s.transientStorage lockSlot = 0

/-- Strengthen `Inv` by pinning the entire `transientStorage` map to `T`. -/
def InvT (Inv : Verity.ContractState → Prop) (T : Nat → Verity.Uint256)
    (s : Verity.ContractState) : Prop :=
  Inv s ∧ s.transientStorage = T

/-- Any `nonreentrant(lockSlot)` entrypoint reverts when called while `lockSlot`
is held, and therefore trivially preserves `LockedInv Inv lockSlot` across
`callbackContractTransition` without inspecting `body`. -/
theorem guarded_callback_preserves_locked {α : Type}
    (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    (ctx : CallbackContext) (body : Verity.Contract α) :
    Preserves (LockedInv Inv lockSlot)
      (callbackContractTransition ctx
        (Verity.Core.NonReentrantGuard.guarded lockSlot body)) := by
  intro s ⟨hInv, hlock⟩
  have hrev := Verity.Core.NonReentrantGuard.guarded_locked_reverts lockSlot body
    (withCallbackContext ctx s) hlock
  unfold callbackContractTransition
  simp only [Verity.Contract.run, hrev]
  exact ⟨hInv, hlock⟩

/-- Any `nonreentrant(lockSlot)` entrypoint also preserves `InvT Inv T` whenever
`T lockSlot ≠ 0`. -/
theorem guarded_callback_preserves_invT {α : Type}
    (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    (T : Nat → Verity.Uint256) (hT : T lockSlot ≠ 0)
    (ctx : CallbackContext) (body : Verity.Contract α) :
    Preserves (InvT Inv T)
      (callbackContractTransition ctx
        (Verity.Core.NonReentrantGuard.guarded lockSlot body)) := by
  intro s ⟨hInv, hts⟩
  have hlock' : (withCallbackContext ctx s).transientStorage lockSlot ≠ 0 := by
    change s.transientStorage lockSlot ≠ 0
    rw [hts]
    exact hT
  have hrev := Verity.Core.NonReentrantGuard.guarded_locked_reverts lockSlot body
    (withCallbackContext ctx s) hlock'
  unfold callbackContractTransition
  simp only [Verity.Contract.run, hrev]
  exact ⟨hInv, hts⟩

/-- Break reentrancy circularity under `lockSlot` (#2564): if every registered
transition either reverts (or acts as the identity) when `lockSlot` is held, or
preserves `Inv` while keeping `lockSlot` nonzero, then the entire registry
preserves `LockedInv Inv lockSlot`. -/
theorem preserves_under_lock
    (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    {registry : EntrypointRegistry} {adv : AdversaryModel}
    (h : ∀ g, registry adv g → ∀ s, LockedInv Inv lockSlot s →
      g s = s ∨ LockedInv Inv lockSlot (g s)) :
    RegistryPreserves (LockedInv Inv lockSlot) registry adv := by
  intro g hg s hs
  rcases h g hg s hs with heq | hlocked
  · rw [heq]; exact hs
  · exact hlocked

/-- Single-entrypoint helper for `preserves_under_lock`: an unguarded entrypoint
`c` that preserves `Inv` on locked states and does not clear `transientStorage lockSlot`
preserves `LockedInv Inv lockSlot` across `callbackContractTransition`. -/
theorem callback_preserves_under_lock {α : Type}
    (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    (ctx : CallbackContext) (c : Verity.Contract α)
    (hstep : ∀ s a s', LockedInv Inv lockSlot s →
      c.run (withCallbackContext ctx s) = .success a s' →
      Inv (restoreCallbackContext s s') ∧ s'.transientStorage lockSlot ≠ 0) :
    Preserves (LockedInv Inv lockSlot) (callbackContractTransition ctx c) := by
  apply callbackContractTransition_preserves
  intro s a s' hs hrun
  obtain ⟨hInv', hlock'⟩ := hstep s a s' hs hrun
  exact ⟨hInv', hlock'⟩

/-- Close the outer `guarded lockSlot body` proof once `body` is known to
preserve `Inv` from the locked entry state `setLock lockSlot 1 s`:
`guarded lockSlot body` preserves `Inv` on *all* states (both unlocked and
already-locked). -/
theorem guarded_preserves_of_locked_body {α : Type}
    (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    (body : Verity.Contract α)
    (hset : ∀ s v, Inv s → Inv (Verity.Core.NonReentrantGuard.setLock lockSlot v s))
    (s : Verity.ContractState)
    (hbody : ∀ a s₂,
      LockedInv Inv lockSlot (Verity.Core.NonReentrantGuard.setLock lockSlot 1 s) →
      body.run (Verity.Core.NonReentrantGuard.setLock lockSlot 1 s) = .success a s₂ →
      Inv s₂)
    (hInv : Inv s) :
    Inv ((Verity.Core.NonReentrantGuard.guarded lockSlot body).run s).snd := by
  by_cases hfree : s.transientStorage lockSlot = 0
  · have hrun := Verity.Core.NonReentrantGuard.guarded_free_runs_body lockSlot body s hfree
    have hlocked₁ : LockedInv Inv lockSlot (Verity.Core.NonReentrantGuard.setLock lockSlot 1 s) := by
      refine ⟨hset s 1 hInv, ?_⟩
      rw [Verity.Core.NonReentrantGuard.setLock_reads]
      decide
    cases hb : body.run (Verity.Core.NonReentrantGuard.setLock lockSlot 1 s) with
    | success a s₂ =>
        rw [hb] at hrun
        simpa [Verity.Contract.run, hrun, Verity.ContractResult.snd] using
          hset s₂ 0 (hbody a s₂ hlocked₁ hb)
    | revert msg s₂ =>
        rw [hb] at hrun
        simpa [Verity.Contract.run, hrun, Verity.ContractResult.snd] using hInv
  · have hrun := Verity.Core.NonReentrantGuard.guarded_locked_reverts lockSlot body s hfree
    simpa [Verity.Contract.run, hrun, Verity.ContractResult.snd] using hInv

/-- Moreover, from any unlocked state (`UnlockedInv Inv lockSlot`), a `guarded`
entrypoint preserves `Inv` AND leaves the lock clear (`transientStorage lockSlot = 0`)
whether it succeeds or reverts. -/
theorem guarded_preserves_unlocked {α : Type}
    (Inv : Verity.ContractState → Prop) (lockSlot : Nat)
    (body : Verity.Contract α)
    (hset : ∀ s v, Inv s → Inv (Verity.Core.NonReentrantGuard.setLock lockSlot v s))
    (s : Verity.ContractState)
    (hbody : ∀ a s₂,
      LockedInv Inv lockSlot (Verity.Core.NonReentrantGuard.setLock lockSlot 1 s) →
      body.run (Verity.Core.NonReentrantGuard.setLock lockSlot 1 s) = .success a s₂ →
      Inv s₂)
    (hUnlocked : UnlockedInv Inv lockSlot s) :
    UnlockedInv Inv lockSlot
      ((Verity.Core.NonReentrantGuard.guarded lockSlot body).run s).snd := by
  obtain ⟨hInv, hfree⟩ := hUnlocked
  refine ⟨guarded_preserves_of_locked_body Inv lockSlot body hset s hbody hInv, ?_⟩
  have hrun := Verity.Core.NonReentrantGuard.guarded_free_runs_body lockSlot body s hfree
  cases hb : body.run (Verity.Core.NonReentrantGuard.setLock lockSlot 1 s) with
  | success a s₂ =>
      rw [hb] at hrun
      simp [Verity.Contract.run, hrun, Verity.ContractResult.snd]
  | revert msg s₂ =>
      rw [hb] at hrun
      simpa [Verity.Contract.run, hrun, Verity.ContractResult.snd] using hfree

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

/-- Program-level preservation for a general `EntrypointRegistry`. -/
theorem CallbackBounded.denote_preserves_registry
    (Inv : Verity.ContractState → Prop) (entrypoints : EntrypointRegistry)
    {adversary : AdversaryModel}
    (hbound : CallbackBounded entrypoints adversary)
    (hregistry : RegistryPreserves Inv entrypoints adversary)
    (prog : CallProgram α) (state : CallState) (hInv : Inv state.world) :
    Inv (denote prog adversary state).2.world := by
  induction prog generalizing state with
  | pure value => exact hInv
  | bind site next ih =>
      exact ih (denoteCall adversary site state)
        (denoteCall adversary site state).state
        (hbound.denoteCall_preserves_registry Inv entrypoints hregistry site state hInv)

/-- Transaction-level preservation for a general `EntrypointRegistry`. -/
theorem CallbackBounded.transaction_preserves_registry
    (Inv : Verity.ContractState → Prop) (entrypoints : EntrypointRegistry)
    {adversary : AdversaryModel}
    (hbound : CallbackBounded entrypoints adversary)
    (hregistry : RegistryPreserves Inv entrypoints adversary)
    (prog : CallProgram (TransactionResult α)) (state : CallState)
    (hInv : Inv state.world) :
    Inv (denoteTransaction prog adversary state).state.world := by
  cases hres : (denote prog adversary state).1 with
  | commit value =>
      rw [denoteTransaction_commit_eq prog adversary state value hres]
      exact hbound.denote_preserves_registry Inv entrypoints hregistry prog state hInv
  | revert data =>
      rw [denoteTransaction_revert_world prog adversary state data hres]
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

namespace Verity

/-- Standard EVM environment hypotheses (#2564) that hold for every real
transaction and external call frame on the EVM, but are left unconstrained by
default in `ContractState` so unit tests can use `defaultState`:
- `msgSender_ne_zero`: `msg.sender ≠ 0` (an uninitialized address slot `0`
  cannot match `addressToWord s.sender`).
- `thisAddress_ne_zero`: `address(this) ≠ 0` (a deployed contract does not
  reside at the zero address).
- `chainId_ne_zero`: `block.chainid ≠ 0` (EIP-155 chain IDs are positive). -/
structure EVMHyp (s : ContractState) : Prop where
  msgSender_ne_zero : s.sender ≠ 0
  thisAddress_ne_zero : s.thisAddress ≠ 0
  chainId_ne_zero : s.chainId ≠ 0

namespace ContractState

abbrev EVMHyp (s : ContractState) : Prop := Verity.EVMHyp s
abbrev msgSender_ne_zero (s : ContractState) : Prop := s.sender ≠ 0
abbrev thisAddress_ne_zero (s : ContractState) : Prop := s.thisAddress ≠ 0
abbrev chainId_ne_zero (s : ContractState) : Prop := s.chainId ≠ 0

end ContractState

@[simp] theorem addressToWord_eq_zero_iff (a : Address) :
    addressToWord a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply Verity.Core.Address.ext
    have hval : (addressToWord a).val = 0 := congrArg Verity.Core.Uint256.val h
    have hlt : a.val < Verity.Core.Uint256.modulus :=
      Nat.lt_trans a.isLt (by
        change 2 ^ 160 < 2 ^ 256
        exact Nat.pow_lt_pow_right (by decide) (by decide))
    simpa [addressToWord, Verity.Core.Address.toNat, Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hlt] using hval
  · rintro rfl
    rfl

namespace EVMHyp

theorem addressToWord_sender_ne_zero {s : ContractState} (h : EVMHyp s) :
    addressToWord s.sender ≠ 0 := by
  rw [ne_eq, addressToWord_eq_zero_iff]
  exact h.msgSender_ne_zero

theorem addressToWord_thisAddress_ne_zero {s : ContractState} (h : EVMHyp s) :
    addressToWord s.thisAddress ≠ 0 := by
  rw [ne_eq, addressToWord_eq_zero_iff]
  exact h.thisAddress_ne_zero

@[simp] theorem sender_beq_zero_eq_false {s : ContractState} (h : EVMHyp s) :
    (addressToWord s.sender == 0) = false :=
  beq_false_of_ne h.addressToWord_sender_ne_zero

@[simp] theorem zero_beq_sender_eq_false {s : ContractState} (h : EVMHyp s) :
    (0 == addressToWord s.sender) = false :=
  beq_false_of_ne (Ne.symm h.addressToWord_sender_ne_zero)

theorem writeSlot {s : ContractState} (h : EVMHyp s) (slot : Nat) (val : Uint256) :
    EVMHyp (s.writeSlot slot val) :=
  ⟨h.1, h.2, h.3⟩

theorem writeAddrSlot {s : ContractState} (h : EVMHyp s) (slot : Nat) (val : Address) :
    EVMHyp (s.writeAddrSlot slot val) :=
  ⟨h.1, h.2, h.3⟩

theorem writeMap {s : ContractState} (h : EVMHyp s) (slot : Nat) (key : Address) (val : Uint256) :
    EVMHyp (s.writeMap slot key val) :=
  ⟨h.1, h.2, h.3⟩

theorem writeMapUint {s : ContractState} (h : EVMHyp s) (slot : Nat) (key val : Uint256) :
    EVMHyp (s.writeMapUint slot key val) :=
  ⟨h.1, h.2, h.3⟩

theorem writeMap2 {s : ContractState} (h : EVMHyp s) (slot : Nat) (k1 k2 : Address) (val : Uint256) :
    EVMHyp (s.writeMap2 slot k1 k2 val) :=
  ⟨h.1, h.2, h.3⟩

theorem writeTransient {s : ContractState} (h : EVMHyp s) (slot : Nat) (val : Uint256) :
    EVMHyp (s.writeTransient slot val) :=
  ⟨h.1, h.2, h.3⟩

theorem withCallbackContext {s : ContractState}
    {ctx : Compiler.CompilationModel.DenoteExternalCalls.CallbackContext}
    (hs : EVMHyp s) (hsender : ctx.sender ≠ 0) :
    EVMHyp (Compiler.CompilationModel.DenoteExternalCalls.withCallbackContext ctx s) :=
  { msgSender_ne_zero := hsender
    thisAddress_ne_zero := hs.thisAddress_ne_zero
    chainId_ne_zero := hs.chainId_ne_zero }

end EVMHyp

end Verity

