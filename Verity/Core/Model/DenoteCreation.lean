import Verity.Core.Model.Denote
import Verity.Core.Model.Create2Operation

/-! Creation at an actual opcode-entry boundary in the canonical Denote state.
This entry point does not invent caller gas, run unmetered caller instructions,
or use the external-call postworld oracle. It is not an importer admission. -/
namespace Verity.Core.Model

/-- Exceptional creation entry preserves the exhausted frame, unlike the
legacy stateless revert projection. Unsupported interpretation is Except.error. -/
inductive CreationOutcome (State : Type) where
  | continued (state : State)
  | exceptional (state : State)

def CreationOutcome.map (f : α → β) : CreationOutcome α → CreationOutcome β
  | .continued state => .continued (f state)
  | .exceptional state => .exceptional (f state)

end Verity.Core.Model

namespace Compiler.CompilationModel.Denote
open Verity.Core.Model

def applyCreationFrame (state : DenoteState) (frame : Create2Operation.Frame) : DenoteState :=
  { state with world := frame.world, executionContext := some { opcode := frame.context, warm := frame.warm } }

/-- The input context is gas at the actual CREATE2 opcode, after argument
evaluation. A metered caller executor must produce it before invoking this API. -/
def execCreate2Boundary (state : DenoteState) (destination : String)
    (offset size salt : Verity.Core.Uint256) : Except String (CreationOutcome DenoteState) :=
  match state.executionContext with
  | none => .error "CREATE2 requires an actual opcode-entry execution context"
  | some context =>
      match Create2Operation.run { world := state.world, context := context.opcode, warm := context.warm }
          offset size salt with
      | .error message => .error message
      | .ok (.exceptional frame) => .ok (.exceptional (applyCreationFrame state frame))
      | .ok (.continued value frame) => .ok (.continued
          { applyCreationFrame state frame with bindings := bindValue state.bindings destination value.val })

theorem execCreate2Boundary_missing_context (state : DenoteState) (destination : String)
    (offset size salt : Verity.Core.Uint256) (missing : state.executionContext = none) :
    execCreate2Boundary state destination offset size salt =
      .error "CREATE2 requires an actual opcode-entry execution context" := by
  simp only [execCreate2Boundary, missing]

theorem applyCreationFrame_world (state : DenoteState) (frame : Create2Operation.Frame) :
    (applyCreationFrame state frame).world = frame.world := rfl

theorem applyCreationFrame_context (state : DenoteState) (frame : Create2Operation.Frame) :
    (applyCreationFrame state frame).executionContext =
      some { opcode := frame.context, warm := frame.warm } := rfl

theorem applyCreationFrame_oracle_index (state : DenoteState) (frame : Create2Operation.Frame) :
    (applyCreationFrame state frame).externalCallIndex = state.externalCallIndex := rfl

/-- Restoring a same-caller snapshot restores all Denote fields except actual
remaining gas/depth/mode. Both contexts must exist; unknown context is an error. -/
def restoreCreationSnapshot (snapshot current : DenoteState) : Except String DenoteState :=
  match snapshot.executionContext, current.executionContext with
  | some saved, some now => .ok { snapshot with executionContext := some (saved.rollback now) }
  | _, _ => .error "creation rollback requires both actual execution contexts"

theorem restoreCreationSnapshot_world (snapshot current : DenoteState)
    (saved now : ExecutionContext)
    (hs : snapshot.executionContext = some saved) (hc : current.executionContext = some now) :
    restoreCreationSnapshot snapshot current =
      .ok { snapshot with executionContext := some (saved.rollback now) } := by
  simp only [restoreCreationSnapshot, hs, hc]

end Compiler.CompilationModel.Denote
