import Compiler.Proofs.IRGeneration.NativeHashedWorldCaller
import Verity.Core.Model.Denote

namespace Compiler.Proofs.IRGeneration.NativeHashedDenote
open EvmYul Compiler.CompilationModel NativeCreationWorldCaller NativeMidnightConstructor
open Verity.Core.Model

/-- The actual reached frame supplies the whole world and ephemeral context.
This is a boundary projection, not a claim of source-prefix equivalence. -/
def atBoundary (state : Denote.DenoteState) (frame : Frame) : Denote.DenoteState :=
  { state with
    world := (CreationBytecode.atBoundary frame).world
    executionContext := some (CreationCaller.context frame.machine frame.warm) }

/-- Same computed operation result in Denote; no external-call outcome is used. -/
theorem exec_creation_result (oracle : Denote.DenoteOracle) (fields : List Field)
    (state : Denote.DenoteState) (frame : Frame) (destination : String)
    (offset size salt : UInt256) (value : Verity.Core.Uint256) (final : Create2Operation.Frame)
    (computed : Create2Operation.run (CreationBytecode.atBoundary frame)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued value final)) :
    Denote.execCreation oracle fields (atBoundary state frame) destination
      (.literal offset.toNat) (.literal size.toNat) (.literal salt.toNat) =
      .continue { (atBoundary state frame) with
        world := final.world
        executionContext := some { opcode := final.context, warm := final.warm }
        bindings := Denote.bindValue state.bindings destination value.val } := by
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  have saltValue : (Verity.Core.Uint256.ofNat salt.toNat).val = salt.toNat := Nat.mod_eq_of_lt salt.val.isLt
  simp only [Denote.execCreation, Denote.evalExprList, Denote.evalExpr, Denote.wordNormalize,
    atBoundary, Bind.bind, Option.bind, Pure.pure, offsetValue, sizeValue, saltValue]
  change (match Create2Operation.run (CreationBytecode.atBoundary frame)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) with
    | .error message => Denote.StmtOutcome.interpretationError message
    | .ok (.exceptional computed) => .exceptional _
    | .ok (.continued address computed) => .continue _) = _
  rw [computed]


/-- Denote and native creation share the actual decoded, storage-updated boundary.
The source-prefix relation and operation guards remain explicit obligations. -/
theorem run_ready_denote (prefixFuel : Nat) (before boundary : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (agrees : NativeCreationWorld.Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (ready : NativeHashedWorldCaller.run prefixFuel before = .ok (.ready boundary))
    (payload : ByteArray) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerOperationGuards boundary.machine payload fuel rest offset size salt)
    (limit : boundary.machine.stack.length ≤ 1024)
    (oracle : Denote.DenoteOracle) (fields : List Field) (state : Denote.DenoteState)
    (destination : String) :
    ∃ (steps : Nat) (next : EVM.State) (value : Verity.Core.Uint256) (final : Create2Operation.Frame), steps < prefixFuel ∧
      EVM.X (steps + fuel + 4) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
        EVM.X (fuel + 3) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next ∧
      Denote.execCreation oracle fields (atBoundary state boundary) destination
        (.literal offset.toNat) (.literal size.toNat) (.literal salt.toNat) =
        .continue { (atBoundary state boundary) with
          world := final.world
          executionContext := some { opcode := final.context, warm := final.warm }
          bindings := Denote.bindValue state.bindings destination value.val } ∧
      NativeCreationWorld.Agreement final.world next final.warm ∧
      next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations boundary.machine next rest offset size value := by
  obtain ⟨steps, next, value, final, within, stepped, continued, computed, agreement, gas, observations, physical, frames⟩ :=
    NativeHashedWorldCaller.run_ready_creation_native prefixFuel before boundary bounded agrees allocated ready
      payload fuel rest offset size salt guards limit
  exact ⟨steps, next, value, final, within, continued,
    exec_creation_result oracle fields state boundary destination offset size salt value final computed,
    agreement, gas, observations⟩

end Compiler.Proofs.IRGeneration.NativeHashedDenote
