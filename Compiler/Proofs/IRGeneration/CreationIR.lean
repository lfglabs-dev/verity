import Compiler.Proofs.IRGeneration.PhysicalMemory
import Compiler.Proofs.IRGeneration.SourceCreation

/-! Explicit IR creation-boundary carrier. The canonical world is mandatory:
IRState alone has no other-account nonce/code/balance/storage projection. No
empty account map or caller-supplied postworld substitutes for those inputs.
This companion entry point is not yet the generic IR builtin dispatcher or
the native EVMYulLean CREATE2 bridge. -/
namespace Compiler.Proofs.IRGeneration.CreationIR
open Verity.Core.Model

def Matches (world : Verity.ContractState) (state : IRState) : Prop :=
  PhysicalMemoryMatches world state ∧
  world.thisAddress.val = state.thisAddress ∧
  (∀ query, (world.codeSize query).val = state.codeSize query) ∧
  (∀ slot, state.storage slot = IRStorageWord.ofNat (world.readSlot slot.toNat).val) ∧
  world.returndata = state.returndata ∧
  state.creationWorld = some world

structure Frame where
  world : Verity.ContractState
  state : IRState
  consistent : Matches world state

/-- Project an actual canonical world into IR observations. Local bindings
and all other IR fields stay with the IR executor. Missing context stays none. -/
def project (world : Verity.ContractState) (state : IRState)
    (context : Option ExecutionContext) : IRState :=
  { state with
    creationWorld := some world
    executionContext := context
    byteMemory := world.byteMemory
    memory := fun offset => (world.memory offset).val
    thisAddress := world.thisAddress.val
    codeSize := fun query => (world.codeSize query).val
    storage := fun slot => IRStorageWord.ofNat (world.readSlot slot.toNat).val
    returndata := world.returndata }

theorem project_matches (world : Verity.ContractState) (state : IRState)
    (context : Option ExecutionContext) : Matches world (project world state context) := by
  exact ⟨⟨rfl, fun _ => rfl⟩, rfl, (fun _ => rfl), (fun _ => rfl), rfl, rfl⟩

def ofWorld (world : Verity.ContractState) (state : IRState)
    (context : Option ExecutionContext) : Frame :=
  { world := world, state := project world state context, consistent := project_matches world state context }

theorem ofWorld_creationWorld (world : Verity.ContractState) (state : IRState)
    (context : Option ExecutionContext) :
    (ofWorld world state context).state.creationWorld = some world := rfl

theorem initial_creationWorld (sender : Nat) :
    (IRState.initial sender).creationWorld = none := rfl

theorem ofWorld_world (world : Verity.ContractState) (state : IRState)
    (context : Option ExecutionContext) : (ofWorld world state context).world = world := rfl

theorem ofWorld_vars (world : Verity.ContractState) (state : IRState)
    (context : Option ExecutionContext) : (ofWorld world state context).state.vars = state.vars := rfl

theorem ofWorld_context (world : Verity.ContractState) (state : IRState)
    (context : Option ExecutionContext) : (ofWorld world state context).state.executionContext = context := rfl

def execCreate2Boundary (before : Frame) (destination : String)
    (offset size salt : Verity.Core.Uint256) : Except String (CreationOutcome Frame) :=
  match before.state.executionContext with
  | none => .error "CREATE2 requires an actual opcode-entry execution context"
  | some context =>
      match Create2Operation.run
          { world := before.world, context := context.opcode, warm := context.warm } offset size salt with
      | .error message => .error message
      | .ok (.exceptional frame) => .ok (.exceptional (ofWorld frame.world before.state
          (some { opcode := frame.context, warm := frame.warm })))
      | .ok (.continued value frame) => .ok (.continued (ofWorld frame.world
          (before.state.setVar destination value.val) (some { opcode := frame.context, warm := frame.warm })))

theorem execCreate2Boundary_missing_context (before : Frame) (destination : String)
    (offset size salt : Verity.Core.Uint256) (missing : before.state.executionContext = none) :
    execCreate2Boundary before destination offset size salt =
      .error "CREATE2 requires an actual opcode-entry execution context" := by
  simp only [execCreate2Boundary, missing]

def toSourceState (template : SourceSemantics.RuntimeState) (frame : Frame) : SourceSemantics.RuntimeState :=
  { template with world := frame.world, executionContext := frame.state.executionContext, bindings := frame.state.vars }

/-- Complete source-state agreement at the primitive boundary, including
bindings/context/world, not just the returned address. The IR frame retains
all other-account state in its mandatory canonical-world companion. -/
theorem source_boundary_eq (template : SourceSemantics.RuntimeState) (before : Frame)
    (destination : String) (offset size salt : Verity.Core.Uint256)
    (world : template.world = before.world)
    (context : template.executionContext = before.state.executionContext)
    (bindings : template.bindings = before.state.vars) :
    SourceSemantics.execCreate2Boundary template destination offset size salt =
      (execCreate2Boundary before destination offset size salt).map
        (CreationOutcome.map (toSourceState template)) := by
  simp only [SourceSemantics.execCreate2Boundary, execCreate2Boundary, context, world]
  cases hc : before.state.executionContext with
  | none => rfl
  | some actualContext =>
      cases computed : Create2Operation.run
          { world := before.world, context := actualContext.opcode, warm := actualContext.warm } offset size salt with
      | error message => simp only [computed, Except.map]
      | ok result =>
          cases result with
          | exceptional frame =>
              simp only [computed, Except.map, CreationOutcome.map]
              simp only [SourceSemantics.applyCreationFrame, toSourceState, ofWorld, project, bindings]
          | continued value frame =>
              simp only [computed, Except.map, CreationOutcome.map]
              simp only [SourceSemantics.applyCreationFrame, toSourceState, ofWorld, project,
                IRState.setVar, bindings, SourceSemantics.bindValue]

/-- Same-caller rollback restores the complete global world and local IR
snapshot, while retaining current gas/depth/mode and restoring access state. -/
def restoreCreationSnapshot (snapshot current : Frame) : Except String Frame :=
  match snapshot.state.executionContext, current.state.executionContext with
  | some saved, some now => .ok (ofWorld snapshot.world snapshot.state (some (saved.rollback now)))
  | _, _ => .error "creation rollback requires both actual execution contexts"

theorem restoreCreationSnapshot_eq (snapshot current : Frame) (saved now : ExecutionContext)
    (hs : snapshot.state.executionContext = some saved) (hc : current.state.executionContext = some now) :
    restoreCreationSnapshot snapshot current =
      .ok (ofWorld snapshot.world snapshot.state (some (saved.rollback now))) := by
  simp only [restoreCreationSnapshot, hs, hc]

end Compiler.Proofs.IRGeneration.CreationIR
