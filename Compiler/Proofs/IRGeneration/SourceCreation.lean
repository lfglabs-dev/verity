import Compiler.Proofs.IRGeneration.SourceSemantics
import Verity.Core.Model.DenoteCreation

/-! Source-state counterpart of the explicit metered CREATE2 boundary. The
generic source statement executor remains unmetered; no source is admitted by
these entry points without a real caller executor and compiled lowering. -/
namespace Compiler.Proofs.IRGeneration.SourceSemantics
open Verity.Core.Model

def applyCreationFrame (state : RuntimeState) (frame : Create2Operation.Frame) : RuntimeState :=
  { state with world := frame.world, executionContext := some { opcode := frame.context, warm := frame.warm } }

def execCreate2Boundary (state : RuntimeState) (destination : String)
    (offset size salt : Verity.Core.Uint256) : Except String (CreationOutcome RuntimeState) :=
  match state.executionContext with
  | none => .error "CREATE2 requires an actual opcode-entry execution context"
  | some context =>
      match Create2Operation.run { world := state.world, context := context.opcode, warm := context.warm }
          offset size salt with
      | .error message => .error message
      | .ok (.exceptional frame) => .ok (.exceptional (applyCreationFrame state frame))
      | .ok (.continued value frame) => .ok (.continued
          { applyCreationFrame state frame with bindings := bindValue state.bindings destination value.val })

theorem execCreate2Boundary_missing_context (state : RuntimeState) (destination : String)
    (offset size salt : Verity.Core.Uint256) (missing : state.executionContext = none) :
    execCreate2Boundary state destination offset size salt =
      .error "CREATE2 requires an actual opcode-entry execution context" := by
  simp only [execCreate2Boundary, missing]

theorem applyCreationFrame_world (state : RuntimeState) (frame : Create2Operation.Frame) :
    (applyCreationFrame state frame).world = frame.world := rfl

theorem applyCreationFrame_context (state : RuntimeState) (frame : Create2Operation.Frame) :
    (applyCreationFrame state frame).executionContext =
      some { opcode := frame.context, warm := frame.warm } := rfl

def restoreCreationSnapshot (snapshot current : RuntimeState) : Except String RuntimeState :=
  match snapshot.executionContext, current.executionContext with
  | some saved, some now => .ok { snapshot with executionContext := some (saved.rollback now) }
  | _, _ => .error "creation rollback requires both actual execution contexts"

theorem restoreCreationSnapshot_world (snapshot current : RuntimeState)
    (saved now : ExecutionContext)
    (hs : snapshot.executionContext = some saved) (hc : current.executionContext = some now) :
    restoreCreationSnapshot snapshot current =
      .ok { snapshot with executionContext := some (saved.rollback now) } := by
  simp only [restoreCreationSnapshot, hs, hc]

end Compiler.Proofs.IRGeneration.SourceSemantics
