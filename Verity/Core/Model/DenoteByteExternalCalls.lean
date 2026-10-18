import Verity.Core.Model.Denote
import Verity.Core.Model.ByteExternalCall

/-!
Byte-exact boundary attached to the actual Denote frame/world. This is a
separate executable call step, not yet an arm of `Denote.execStmt`. Raw bytes
stay separate from the legacy word-valued `ContractState.returndata`; clients
must use these observations until the canonical returndata carrier is migrated.
No external Solidity construct is admitted by this module.
-/
namespace Compiler.CompilationModel.DenoteByteExternalCalls

open Compiler.CompilationModel
open ByteExternalCall

abbrev Adversary := ByteExternalCall.Adversary Verity.ContractState Verity.StorageKey

/-- Configurable readonly adversary. The supplied response depends on the
complete request and current world; it never receives a fictitious call-index
oracle in place of the target/calldata. Returned accesses remain explicit. -/
def staticAdversary
    (respond : Request → Verity.ContractState → Bool × Bytes × List Verity.StorageKey) :
    Adversary where
  respond := fun request world =>
    let (success, data, touched) := respond request world
    if success then .success world data touched else .revert data touched
  valid := by
    intro request world
    dsimp
    split
    · exact fun _ => rfl
    · trivial

/-- Configurable adversary for `CALL` and `STATICCALL`. The supplied response
sees the complete request and current world and may return an updated world
(for example a reentrant callback's writes and logs). That world is committed
only by a successful non-static request; a successful `STATICCALL` always keeps
the input world, so validity holds by construction. -/
def callAdversary
    (respond : Request → Verity.ContractState →
      Bool × Verity.ContractState × Bytes × List Verity.StorageKey) :
    Adversary where
  respond := fun request world =>
    let (success, after, data, touched) := respond request world
    if success then
      .success (if request.kind = .staticcall then world else after) data touched
    else .revert data touched
  valid := by
    intro request world
    dsimp
    split
    · intro hkind
      simp [hkind]
    · trivial

@[simp] theorem callAdversary_respond
    (respond : Request → Verity.ContractState →
      Bool × Verity.ContractState × Bytes × List Verity.StorageKey)
    (request : Request) (world : Verity.ContractState) :
    (callAdversary respond).respond request world =
      if (respond request world).1 then
        .success (if request.kind = .staticcall then world else (respond request world).2.1)
          (respond request world).2.2.1 (respond request world).2.2.2
      else .revert (respond request world).2.2.1 (respond request world).2.2.2 := rfl

structure State where
  frame : Denote.DenoteState
  returndata : Bytes := []
  touched : List Verity.StorageKey := []

structure Observation where
  success : Bool
  state : State

/-- Big-endian value of the first (at most 32) returned bytes. Callers check
that a complete word is present before trusting it as an ABI word. -/
def firstWord (data : Bytes) : Nat :=
  (data.take 32).foldl (fun accumulator byte => accumulator * 256 + byte.toNat) 0

/-- Decode the uint256 return of a Solidity typed interface staticcall. Extra
bytes are accepted; an incomplete first word reverts with empty payload. A
failed child call forwards its bytes without padding. The state already holds
the checked staticcall world and accesses from `execute`. -/
def decodeStaticUint256 (observed : Observation) : Denote.StmtOutcome :=
  if observed.success then
    if observed.state.returndata.length < 32 then .revertWithData []
    else .return (firstWord observed.state.returndata) observed.state.frame
  else .revertWithData observed.state.returndata

theorem decodeStaticUint256_failure (state : State) :
    decodeStaticUint256 { success := false, state } =
      .revertWithData state.returndata := rfl

theorem decodeStaticUint256_short (state : State) (hshort : state.returndata.length < 32) :
    decodeStaticUint256 { success := true, state } = .revertWithData [] := by
  simp [decodeStaticUint256, hshort]

/-- Decode the bool return of a Solidity typed interface staticcall. As for
`decodeStaticUint256`, extra bytes are accepted, an incomplete first word
reverts empty and a failed child forwards its bytes. ABI validation of the
returned bool reverts empty unless the first word is exactly `0` or `1`. -/
def decodeStaticBool (observed : Observation) : Denote.StmtOutcome :=
  if observed.success then
    if observed.state.returndata.length < 32 then .revertWithData []
    else if firstWord observed.state.returndata ≤ 1 then
      .return (firstWord observed.state.returndata) observed.state.frame
    else .revertWithData []
  else .revertWithData observed.state.returndata

theorem decodeStaticBool_failure (state : State) :
    decodeStaticBool { success := false, state } = .revertWithData state.returndata := rfl

theorem decodeStaticBool_short (state : State) (hshort : state.returndata.length < 32) :
    decodeStaticBool { success := true, state } = .revertWithData [] := by
  simp [decodeStaticBool, hshort]

theorem decodeStaticBool_of_le_one (state : State) (hlength : 32 ≤ state.returndata.length)
    (hword : firstWord state.returndata ≤ 1) :
    decodeStaticBool { success := true, state } =
      .return (firstWord state.returndata) state.frame := by
  simp [decodeStaticBool, Nat.not_lt.mpr hlength, hword]

theorem decodeStaticBool_of_one_lt (state : State) (hlength : 32 ≤ state.returndata.length)
    (hword : 1 < firstWord state.returndata) :
    decodeStaticBool { success := true, state } = .revertWithData [] := by
  simp [decodeStaticBool, Nat.not_lt.mpr hlength, Nat.not_le.mpr hword]

/-- Optional-bool check of a low-level `.call(bytes)` (the Solady
`SafeTransferLib` convention for tokens that may return nothing): the call
succeeds when the child succeeded and either returned no bytes or returned a
complete first word equal to `1`. Any other observation reverts empty; the
caller's own error payload and any separate code-existence check (for example
`extCodeSize`) are composed outside this decoder. -/
def decodeOptionalBoolCall (observed : Observation) : Denote.StmtOutcome :=
  if observed.success ∧ (observed.state.returndata.isEmpty ∨
      (32 ≤ observed.state.returndata.length ∧ firstWord observed.state.returndata = 1)) then
    .return 1 observed.state.frame
  else .revertWithData []

theorem decodeOptionalBoolCall_eq_return_iff (observed : Observation) :
    decodeOptionalBoolCall observed = .return 1 observed.state.frame ↔
      observed.success = true ∧ (observed.state.returndata.isEmpty ∨
        (32 ≤ observed.state.returndata.length ∧ firstWord observed.state.returndata = 1)) := by
  unfold decodeOptionalBoolCall
  split <;> simp_all

theorem decodeOptionalBoolCall_failure (state : State) :
    decodeOptionalBoolCall { success := false, state } = .revertWithData [] := by
  simp [decodeOptionalBoolCall]

theorem decodeOptionalBoolCall_empty (state : State) (hempty : state.returndata = []) :
    decodeOptionalBoolCall { success := true, state } = .return 1 state.frame := by
  simp [decodeOptionalBoolCall, hempty]

theorem decodeOptionalBoolCall_true (state : State) (hlength : 32 ≤ state.returndata.length)
    (hword : firstWord state.returndata = 1) :
    decodeOptionalBoolCall { success := true, state } = .return 1 state.frame := by
  simp [decodeOptionalBoolCall, hlength, hword]

theorem decodeOptionalBoolCall_short (state : State) (hnonempty : state.returndata ≠ [])
    (hshort : state.returndata.length < 32) :
    decodeOptionalBoolCall { success := true, state } = .revertWithData [] := by
  simp [decodeOptionalBoolCall, hnonempty, Nat.not_le.mpr hshort]

theorem decodeOptionalBoolCall_of_ne_one (state : State) (hnonempty : state.returndata ≠ [])
    (hword : firstWord state.returndata ≠ 1) :
    decodeOptionalBoolCall { success := true, state } = .revertWithData [] := by
  simp [decodeOptionalBoolCall, hnonempty, hword]

/-- Decode the single 32-byte word (`uint256` or `bytes32`) returned by a
state-changing typed interface call. Extra bytes are accepted; an incomplete
first word reverts empty and a failed child forwards its bytes without padding.
The state already holds the committed callee world and accesses from
`execute`. -/
def decodeCallWord (observed : Observation) : Denote.StmtOutcome :=
  if observed.success then
    if observed.state.returndata.length < 32 then .revertWithData []
    else .return (firstWord observed.state.returndata) observed.state.frame
  else .revertWithData observed.state.returndata

@[simp] theorem decodeCallWord_failure (state : State) :
    decodeCallWord { success := false, state } = .revertWithData state.returndata := rfl

@[simp] theorem decodeCallWord_short (state : State) (hshort : state.returndata.length < 32) :
    decodeCallWord { success := true, state } = .revertWithData [] := by
  simp [decodeCallWord, hshort]

@[simp] theorem decodeCallWord_of_ge (state : State) (hlength : 32 ≤ state.returndata.length) :
    decodeCallWord { success := true, state } =
      .return (firstWord state.returndata) state.frame := by
  simp [decodeCallWord, Nat.not_lt.mpr hlength]

def execute (adversary : Adversary) (request : Request) (state : State) : Observation :=
  let observed := ByteExternalCall.execute adversary request state.frame.world
  { success := observed.success
    state :=
      { frame := { state.frame with world := observed.world }
        returndata := observed.returndata
        touched := state.touched ++ observed.touched } }

/-- The calldata of a static interface call is its four-byte selector followed
by complete ABI words. Bounded inputs prohibit silently truncating a selector
or address. The explicit gas allowance belongs to the EVM call boundary. -/
def staticRequest (state : State) (target : Verity.Address)
    (selector : Fin (2^32)) (arguments : List Verity.Uint256) (gas : Nat) : Request :=
  { kind := .staticcall
    caller := state.frame.world.thisAddress.val
    target := target.val
    value := 0
    calldata := (List.range 4).map
      (fun index => UInt8.ofNat (selector.val / 256 ^ (3 - index) % 256)) ++
      arguments.flatMap (fun word => Denote.wordBytes word.val)
    gas }

/-- A readonly call with arbitrary, already-encoded calldata. -/
def staticBytesRequest (state : State) (target : Verity.Address) (calldata : Bytes)
    (gas : Nat) : Request :=
  { kind := .staticcall
    caller := state.frame.world.thisAddress.val
    target := target.val
    value := 0
    calldata
    gas }

/-- A value-free `CALL` with arbitrary, already-encoded calldata. -/
def callBytesRequest (state : State) (target : Verity.Address) (calldata : Bytes)
    (gas : Nat) : Request :=
  { kind := .call
    caller := state.frame.world.thisAddress.val
    target := target.val
    value := 0
    calldata
    gas }

section BytesRequests

variable (state : State) (target : Verity.Address) (calldata : Bytes) (gas : Nat)

@[simp] theorem staticBytesRequest_kind :
    (staticBytesRequest state target calldata gas).kind = .staticcall := rfl

@[simp] theorem staticBytesRequest_caller :
    (staticBytesRequest state target calldata gas).caller =
      state.frame.world.thisAddress.val := rfl

@[simp] theorem staticBytesRequest_target :
    (staticBytesRequest state target calldata gas).target = target.val := rfl

@[simp] theorem staticBytesRequest_value :
    (staticBytesRequest state target calldata gas).value = 0 := rfl

@[simp] theorem staticBytesRequest_calldata :
    (staticBytesRequest state target calldata gas).calldata = calldata := rfl

@[simp] theorem staticBytesRequest_gas :
    (staticBytesRequest state target calldata gas).gas = gas := rfl

@[simp] theorem callBytesRequest_kind :
    (callBytesRequest state target calldata gas).kind = .call := rfl

@[simp] theorem callBytesRequest_caller :
    (callBytesRequest state target calldata gas).caller =
      state.frame.world.thisAddress.val := rfl

@[simp] theorem callBytesRequest_target :
    (callBytesRequest state target calldata gas).target = target.val := rfl

@[simp] theorem callBytesRequest_value :
    (callBytesRequest state target calldata gas).value = 0 := rfl

@[simp] theorem callBytesRequest_calldata :
    (callBytesRequest state target calldata gas).calldata = calldata := rfl

@[simp] theorem callBytesRequest_gas :
    (callBytesRequest state target calldata gas).gas = gas := rfl

end BytesRequests

def executeStaticUint256 (adversary : Adversary) (state : State) (target : Verity.Address)
    (selector : Fin (2^32)) (arguments : List Verity.Uint256) (gas : Nat) :
    Denote.StmtOutcome × List Verity.StorageKey :=
  let observed := execute adversary (staticRequest state target selector arguments gas) state
  (decodeStaticUint256 observed, observed.state.touched)

section BytesExecutors

variable (adversary : Adversary) (state : State) (target : Verity.Address) (calldata : Bytes)
  (gas : Nat)

/-- Typed interface staticcall with already-encoded calldata returning `uint256`. -/
def executeBytesStaticUint256 : Denote.StmtOutcome × List Verity.StorageKey :=
  let observed := execute adversary (staticBytesRequest state target calldata gas) state
  (decodeStaticUint256 observed, observed.state.touched)

/-- Typed interface staticcall with already-encoded calldata returning `bool`. -/
def executeBytesStaticBool : Denote.StmtOutcome × List Verity.StorageKey :=
  let observed := execute adversary (staticBytesRequest state target calldata gas) state
  (decodeStaticBool observed, observed.state.touched)

/-- Low-level value-free `.call(bytes)` checked with the optional-bool convention. -/
def executeBytesOptionalBoolCall : Denote.StmtOutcome × List Verity.StorageKey :=
  let observed := execute adversary (callBytesRequest state target calldata gas) state
  (decodeOptionalBoolCall observed, observed.state.touched)

/-- State-changing typed interface call with already-encoded calldata returning a
single 32-byte word. A successful callee's world is committed into the frame. -/
def executeBytesCallWord : Denote.StmtOutcome × List Verity.StorageKey :=
  let observed := execute adversary (callBytesRequest state target calldata gas) state
  (decodeCallWord observed, observed.state.touched)

@[simp] theorem executeBytesStaticUint256_eq :
    executeBytesStaticUint256 adversary state target calldata gas =
      let observed := execute adversary (staticBytesRequest state target calldata gas) state
      (decodeStaticUint256 observed, observed.state.touched) := rfl

@[simp] theorem executeBytesStaticBool_eq :
    executeBytesStaticBool adversary state target calldata gas =
      let observed := execute adversary (staticBytesRequest state target calldata gas) state
      (decodeStaticBool observed, observed.state.touched) := rfl

@[simp] theorem executeBytesOptionalBoolCall_eq :
    executeBytesOptionalBoolCall adversary state target calldata gas =
      let observed := execute adversary (callBytesRequest state target calldata gas) state
      (decodeOptionalBoolCall observed, observed.state.touched) := rfl

@[simp] theorem executeBytesCallWord_eq :
    executeBytesCallWord adversary state target calldata gas =
      let observed := execute adversary (callBytesRequest state target calldata gas) state
      (decodeCallWord observed, observed.state.touched) := rfl

/-- A byte-request staticcall never changes the Denote world. -/
@[simp] theorem execute_staticBytesRequest_world :
    (execute adversary (staticBytesRequest state target calldata gas) state).state.frame.world =
      state.frame.world :=
  ByteExternalCall.execute_static_world adversary _ state.frame.world rfl

end BytesExecutors

theorem staticRequest_value (state : State) (target : Verity.Address)
    (selector : Fin (2^32)) (arguments : List Verity.Uint256) (gas : Nat) :
    (staticRequest state target selector arguments gas).value = 0 := rfl

theorem staticRequest_caller (state : State) (target : Verity.Address)
    (selector : Fin (2^32)) (arguments : List Verity.Uint256) (gas : Nat) :
    (staticRequest state target selector arguments gas).caller =
      state.frame.world.thisAddress.val := rfl

theorem execute_bindings (adversary : Adversary) (request : Request) (state : State) :
    (execute adversary request state).state.frame.bindings = state.frame.bindings := rfl

theorem execute_static_world (adversary : Adversary) (request : Request) (state : State)
    (hkind : request.kind = .staticcall) :
    (execute adversary request state).state.frame.world = state.frame.world :=
  ByteExternalCall.execute_static_world adversary request state.frame.world hkind

theorem execute_revert_world (adversary : Adversary) (request : Request) (state : State)
    (data : Bytes) (accesses : List Verity.StorageKey)
    (hresponse : adversary.respond request state.frame.world = .revert data accesses) :
    (execute adversary request state).state.frame.world = state.frame.world := by
  simp [execute, ByteExternalCall.execute, hresponse, Response.commit]

theorem execute_revert_bytes (adversary : Adversary) (request : Request) (state : State)
    (data : Bytes) (accesses : List Verity.StorageKey)
    (hresponse : adversary.respond request state.frame.world = .revert data accesses) :
    (execute adversary request state).state.returndata = data := by
  simp [execute, ByteExternalCall.execute, hresponse, Response.returndata]

theorem execute_revert_touched (adversary : Adversary) (request : Request) (state : State)
    (data : Bytes) (accesses : List Verity.StorageKey)
    (hresponse : adversary.respond request state.frame.world = .revert data accesses) :
    (execute adversary request state).state.touched = state.touched ++ accesses := by
  simp [execute, ByteExternalCall.execute, hresponse, Response.accesses]

/-- Outer rollback restores the entire saved Denote frame, not only the
caller's unscoped slots. The access list remains observable. -/
def rollbackOuter (entry : Denote.DenoteState) (state : State) (data : Bytes) : State :=
  { state with frame := entry, returndata := data }

theorem rollbackOuter_storageWords (entry : Denote.DenoteState) (state : State)
    (data : Bytes) (key : Verity.StorageKey) :
    (rollbackOuter entry state data).frame.world.storageWords key =
      entry.world.storageWords key := rfl

theorem rollbackOuter_events (entry : Denote.DenoteState) (state : State) (data : Bytes) :
    (rollbackOuter entry state data).frame.world.events = entry.world.events := rfl

theorem rollbackOuter_accesses (entry : Denote.DenoteState) (state : State) (data : Bytes) :
    (rollbackOuter entry state data).touched = state.touched := rfl

end Compiler.CompilationModel.DenoteByteExternalCalls
