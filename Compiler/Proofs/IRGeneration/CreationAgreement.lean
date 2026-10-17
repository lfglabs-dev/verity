import Compiler.Proofs.IRGeneration.DenoteAgreement
import Compiler.Proofs.IRGeneration.SourceCreation

/-! Exact agreement at the explicit creation boundary, including the required
ephemeral context and the exceptional exhausted frame. Existing general Denote
agreement statements remain unchanged; generic caller metering is still open. -/
namespace Compiler.Proofs.IRGeneration.DenoteAgreement
open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Verity.Core.Model

theorem toRuntimeState_executionContext (state : DenoteState) :
    (toRuntimeState state).executionContext = state.executionContext := rfl

theorem toRuntimeState_applyCreationFrame (state : DenoteState) (frame : Create2Operation.Frame) :
    toRuntimeState (Denote.applyCreationFrame state frame) =
      SourceSemantics.applyCreationFrame (toRuntimeState state) frame := rfl

theorem denote_creation_boundary_eq (state : DenoteState) (destination : String)
    (offset size salt : Verity.Core.Uint256) :
    SourceSemantics.execCreate2Boundary (toRuntimeState state) destination offset size salt =
      (Denote.execCreate2Boundary state destination offset size salt).map
        (CreationOutcome.map toRuntimeState) := by
  simp only [SourceSemantics.execCreate2Boundary, Denote.execCreate2Boundary,
    toRuntimeState_executionContext]
  cases hc : state.executionContext with
  | none => rfl
  | some actualContext =>
      cases computed : Create2Operation.run
          { world := state.world, context := actualContext.opcode, warm := actualContext.warm } offset size salt with
      | error message => simp only [toRuntimeState, computed, Except.map]
      | ok result =>
          cases result with
          | exceptional frame =>
              simp only [toRuntimeState, computed, Except.map, CreationOutcome.map]
              rfl
          | continued value frame =>
              simp only [toRuntimeState, computed, Except.map, CreationOutcome.map]
              rfl

theorem denote_creation_rollback_eq (snapshot current : DenoteState) :
    SourceSemantics.restoreCreationSnapshot (toRuntimeState snapshot) (toRuntimeState current) =
      (Denote.restoreCreationSnapshot snapshot current).map toRuntimeState := by
  cases saved : snapshot.executionContext <;> cases now : current.executionContext <;>
    simp only [SourceSemantics.restoreCreationSnapshot, Denote.restoreCreationSnapshot,
      toRuntimeState_executionContext, saved, now, Except.map]
  rfl

end Compiler.Proofs.IRGeneration.DenoteAgreement
