import Verity.Core.Model.Denote

/-! Transaction boundaries for the differential Denote adapter. These helpers
execute the real model semantics. They do not encode events or recover access
traces; the adapter must provide those before claiming complete observations. -/
namespace Compiler.CompilationModel.SolidityImport.Transactions
open Denote Verity.Core

/-- Transient keys can be parked under another account during external calls. -/
def isTransientKey : Verity.StorageKey → Bool
  | .transient _ => true
  | .scoped _ key => isTransientKey key
  | _ => false

/-- Start a fresh top-level frame while preserving persistent world state.
The caller supplies the explicit transaction environment in `world` first.
Value transfers, dispatch and ABI decoding are separate adapter obligations. -/
def beginTransaction (world : Verity.ContractState) : Verity.ContractState :=
  let fresh := world.withStorageWords fun key =>
    if isTransientKey key then 0 else world.storageWords key
  { fresh with
    memory := fun _ => 0
    returndata := []
    events := []
    calls := [] }

structure FrameResult where
  success : Bool
  data : List UInt8
  world : Verity.ContractState

/-- Preserve exact bytes and select the committed or rolled-back world.
A payload-free Denote failure is an instrumentation error, never an invented
empty revert. Events remain in the returned world for subsequent ABI encoding. -/
def finishFrame (initial : Verity.ContractState) : StmtOutcome → Except String FrameResult
  | .continue _ => .error "Denote frame fell through without an explicit return"
  | .stop final =>
      if final.observedStop then .ok ⟨true, [], final.world⟩ else
      match final.observedReturnWords with
      | none => .error "Denote frame stopped without an explicit return observation"
      | some words => .ok ⟨true, words.flatMap wordBytes, final.world⟩
  | .return value final => .ok ⟨true, wordBytes value, final.world⟩
  | .revert => .error "Denote failure has no exact revert payload"
  | .revertWithData bytes => .ok ⟨false, bytes, initial⟩

/-- Execute a body through Denote, after installing fresh frame-local state.
This function is a frame runner, not yet a full ABI/dispatch transaction runner. -/
def executeBody (oracle : DenoteOracle) (fields : List Field)
    (world : Verity.ContractState) (bindings : Env) (body : List Stmt)
    (errors : List ErrorDef := []) :
    Except String FrameResult :=
  let initial := beginTransaction world
  finishFrame initial (execStmtList oracle fields { world := initial, bindings, errors } body)

@[simp] theorem beginTransaction_storage (world : Verity.ContractState) (slot : Nat) :
    (beginTransaction world).storageWords (.slot slot) = world.storageWords (.slot slot) := rfl

@[simp] theorem beginTransaction_foreignStorage (world : Verity.ContractState)
    (account slot : Nat) :
    (beginTransaction world).storageWords (.contractSlot account slot) =
      world.storageWords (.contractSlot account slot) := rfl

@[simp] theorem beginTransaction_transient (world : Verity.ContractState) (slot : Nat) :
    (beginTransaction world).storageWords (.transient slot) = 0 := rfl

@[simp] theorem beginTransaction_parkedTransient (world : Verity.ContractState)
    (account slot : Nat) :
    (beginTransaction world).storageWords (.scoped account (.transient slot)) = 0 := rfl

/-- Rollback retains the original persistent world and exact revert bytes. -/
theorem finishFrame_revert (initial : Verity.ContractState) (bytes : List UInt8) :
    finishFrame initial (.revertWithData bytes) = .ok ⟨false, bytes, initial⟩ := rfl

end Compiler.CompilationModel.SolidityImport.Transactions
