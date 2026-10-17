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

structure State where
  frame : Denote.DenoteState
  returndata : Bytes := []
  touched : List Verity.StorageKey := []

structure Observation where
  success : Bool
  state : State

/-- Decode the uint256 return of a Solidity typed interface staticcall. Extra
bytes are accepted; an incomplete first word reverts with empty payload. A
failed child call forwards its bytes without padding. The state already holds
the checked staticcall world and accesses from `execute`. -/
def decodeStaticUint256 (observed : Observation) : Denote.StmtOutcome :=
  if observed.success then
    if observed.state.returndata.length < 32 then .revertWithData []
    else
      let value := (observed.state.returndata.take 32).foldl
        (fun accumulator byte => accumulator * 256 + byte.toNat) 0
      .return value observed.state.frame
  else .revertWithData observed.state.returndata

theorem decodeStaticUint256_failure (state : State) :
    decodeStaticUint256 { success := false, state } =
      .revertWithData state.returndata := rfl

theorem decodeStaticUint256_short (state : State) (hshort : state.returndata.length < 32) :
    decodeStaticUint256 { success := true, state } = .revertWithData [] := by
  simp [decodeStaticUint256, hshort]

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

def executeStaticUint256 (adversary : Adversary) (state : State) (target : Verity.Address)
    (selector : Fin (2^32)) (arguments : List Verity.Uint256) (gas : Nat) :
    Denote.StmtOutcome × List Verity.StorageKey :=
  let observed := execute adversary (staticRequest state target selector arguments gas) state
  (decodeStaticUint256 observed, observed.state.touched)

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
