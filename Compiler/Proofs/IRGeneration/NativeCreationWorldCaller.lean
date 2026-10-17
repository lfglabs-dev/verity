import Compiler.Proofs.IRGeneration.NativeCreationLocalFrames
import Compiler.Proofs.IRGeneration.CreationBytecode

/-! Paired native/canonical caller prefix instrument. Native instruction execution
and exceptional prechecks are retained. Only flat native word writes are paired;
this is not a source hashed-channel or full-function admission certificate. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationWorldCaller
open EvmYul NativeCreationWorld NativeCreationStorageOpcodes NativeCreationLocalFrames
abbrev Frame := CreationBytecode.Frame

/-- Pair the actual storage operands with the corresponding canonical channel.
Account presence is checked rather than assumed from the zero account view. -/
def worldAfter (before : Frame) (op : Operation .EVM) : Except String Verity.ContractState := do
  if op = .SSTORE || op = .TSTORE then
    match before.machine.stack with
    | slot :: value :: _ =>
      if (before.machine.toState.lookupAccount before.machine.executionEnv.codeOwner).isNone then
        throw s!"native caller storage account absent at bytecode pc {before.machine.pc.toNat}"
      pure (if op = .SSTORE then
        before.world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)
        else before.world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat))
    | _ => throw s!"native caller storage operands absent at bytecode pc {before.machine.pc.toNat}"
  else pure before.world

inductive StepOutcome where
  | continued (frame : Frame)
  | exceptional (reason : EVM.ExecutionException) (frame : Frame)

inductive Outcome where
  | ready (frame : Frame)
  | exceptional (reason : EVM.ExecutionException) (frame : Frame)

/-- Keep the actual checked native step and distinguish unsupported execution
from an actual EVM exception. No scalar write occurs on exceptional paths. -/
def advance (before : Frame) (op : Operation .EVM) (arg : Option (UInt256 × Nat)) :
    Except String StepOutcome := do
  if !(CreationCaller.supported op || op = .SSTORE || op = .TSTORE) then
    throw s!"unsupported world caller instruction at bytecode pc {before.machine.pc.toNat}"
  match CreationCaller.checkedStep before.machine op arg with
  | .error reason => pure (.exceptional reason
      { before with machine := CreationCaller.exhausted before.machine })
  | .ok next =>
      let world ← worldAfter before op
      pure (.continued { before with world := world, machine := next })

/-- Actual prefix execution transports the computed canonical world at every
step. CREATE2 is a boundary, not executed by this interpreter. -/
def run : Nat → Frame → Except String Outcome
  | 0, before => .error s!"world caller fuel exhausted at bytecode pc {before.machine.pc.toNat}"
  | fuel + 1, before =>
      match EVM.decode before.machine.executionEnv.code before.machine.pc with
      | none => .error s!"unsupported world caller opcode at bytecode pc {before.machine.pc.toNat}"
      | some (op, arg) =>
        if op = .CREATE2 then .ok (.ready before)
        else do
          match ← advance before op arg with
          | .continued next => run fuel next
          | .exceptional reason frame => pure (.exceptional reason frame)

private theorem sstore_arg (machine : EVM.State) (arg : Option (UInt256 × Nat)) :
    CreationCaller.checkedStep machine .SSTORE arg = CreationCaller.checkedStep machine .SSTORE none := by
  rfl

private theorem tstore_arg (machine : EVM.State) (arg : Option (UInt256 × Nat)) :
    CreationCaller.checkedStep machine .TSTORE arg = CreationCaller.checkedStep machine .TSTORE none := by
  rfl

private theorem checked_sstore_of_stack (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) (tail : Stack UInt256) (arg : Option (UInt256 × Nat))
    (stack : machine.stack = slot :: value :: tail)
    (success : CreationCaller.checkedStep machine .SSTORE arg = .ok after) :
    Agreement (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)) after warm := by
  have restored : { machine with stack := slot :: value :: tail } = machine := by
    rw [← stack]
  apply checked_sstore_agreement world machine warm entry present agrees slot value tail after
  rw [sstore_arg] at success
  simpa only [restored] using success

private theorem checked_tstore_of_stack (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) (tail : Stack UInt256) (arg : Option (UInt256 × Nat))
    (stack : machine.stack = slot :: value :: tail)
    (success : CreationCaller.checkedStep machine .TSTORE arg = .ok after) :
    Agreement (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)) after warm := by
  have restored : { machine with stack := slot :: value :: tail } = machine := by
    rw [← stack]
  apply checked_tstore_agreement world machine warm entry present agrees slot value tail after
  rw [tstore_arg] at success
  simpa only [restored] using success

private theorem worldAfter_sstore_agreement (before : Frame) (next : EVM.State)
    (world : Verity.ContractState) (arg : Option (UInt256 × Nat))
    (agrees : Agreement before.world before.machine before.warm)
    (stepped : CreationCaller.checkedStep before.machine .SSTORE arg = .ok next)
    (updated : worldAfter before .SSTORE = .ok world) :
    Agreement world next before.warm := by
  dsimp only [worldAfter, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw,
    Except.bind, Except.pure] at updated
  cases stack : before.machine.stack with
  | nil => simp only [stack] at updated; cases updated
  | cons slot rest =>
    cases rest with
    | nil => simp only [stack] at updated; cases updated
    | cons value tail =>
      simp only [stack] at updated
      cases present : before.machine.toState.lookupAccount before.machine.executionEnv.codeOwner with
      | none => simp only [present] at updated; cases updated
      | some entry =>
        simp only [present] at updated
        cases updated
        exact checked_sstore_of_stack before.world before.machine next before.warm entry
          present agrees slot value tail arg stack stepped

private theorem worldAfter_tstore_agreement (before : Frame) (next : EVM.State)
    (world : Verity.ContractState) (arg : Option (UInt256 × Nat))
    (agrees : Agreement before.world before.machine before.warm)
    (stepped : CreationCaller.checkedStep before.machine .TSTORE arg = .ok next)
    (updated : worldAfter before .TSTORE = .ok world) :
    Agreement world next before.warm := by
  dsimp only [worldAfter, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw,
    Except.bind, Except.pure] at updated
  cases stack : before.machine.stack with
  | nil => simp only [stack] at updated; cases updated
  | cons slot rest =>
    cases rest with
    | nil => simp only [stack] at updated; cases updated
    | cons value tail =>
      simp only [stack] at updated
      cases present : before.machine.toState.lookupAccount before.machine.executionEnv.codeOwner with
      | none => simp only [present] at updated; cases updated
      | some entry =>
        simp only [present] at updated
        cases updated
        exact checked_tstore_of_stack before.world before.machine next before.warm entry
          present agrees slot value tail arg stack stepped

/-- Pairing actual supported local/storage effects preserves raw Agreement. -/
theorem worldAfter_agreement (before : Frame) (next : EVM.State)
    (world : Verity.ContractState) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true)
    (agrees : Agreement before.world before.machine before.warm)
    (stepped : CreationCaller.checkedStep before.machine op arg = .ok next)
    (updated : worldAfter before op = .ok world) :
    Agreement world next before.warm := by
  by_cases store : op = .SSTORE
  · subst op
    exact worldAfter_sstore_agreement before next world arg agrees stepped updated
  · by_cases transient : op = .TSTORE
    · subst op
      exact worldAfter_tstore_agreement before next world arg agrees stepped updated
    · have same : before.world = world := by
        simpa [worldAfter, store, transient, Pure.pure, Except.pure] using updated
      rw [← same]
      have allowed : CreationCaller.supported op = true := by simpa [store, transient] using admitted
      exact agreement_of_state_eq before.world before.machine next before.warm agrees
        (supported_checked_state op before.machine next arg allowed stepped)

/-- Every successful advance exposes both the computed world and actual native
poststate. Exceptional/refusal outcomes cannot be used as continued evidence. -/
theorem advance_agreement (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (agrees : Agreement before.world before.machine before.warm)
    (success : advance before op arg = .ok (.continued after)) :
    Agreement after.world after.machine after.warm := by
  unfold advance at success
  dsimp only [Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw,
    Except.bind, Except.pure] at success
  cases admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) with
  | false => simp only [admitted] at success; cases success
  | true =>
    simp only [admitted] at success
    cases stepped : CreationCaller.checkedStep before.machine op arg with
    | error reason => simp only [stepped] at success; cases success
    | ok next =>
      simp only [stepped] at success
      cases updated : worldAfter before op with
      | error message => simp only [updated] at success; cases success
      | ok world =>
        simp only [updated] at success
        cases success
        exact worldAfter_agreement before next world op arg admitted agrees stepped updated

/-- The actual paired prefix reaches CREATE2 with the computed canonical world
and raw native Agreement, including every preceding persistent/transient write. -/
theorem run_ready_agreement (fuel : Nat) (before after : Frame)
    (agrees : Agreement before.world before.machine before.warm)
    (success : run fuel before = .ok (.ready after)) :
    Agreement after.world after.machine after.warm := by
  induction fuel generalizing before with
  | zero => cases success
  | succ fuel ih =>
    cases decoded : EVM.decode before.machine.executionEnv.code before.machine.pc with
    | none => simp only [run, decoded] at success; cases success
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      simp only [run, decoded] at success
      by_cases creation : op = .CREATE2
      · simp only [creation, ite_true] at success
        cases success
        exact agrees
      · simp only [creation, ite_false] at success
        cases advanced : advance before op arg with
        | error message => simp only [advanced] at success; cases success
        | ok outcome =>
          cases outcome with
          | exceptional reason frame => simp only [advanced] at success; cases success
          | continued next =>
            simp only [advanced] at success
            exact ih next (advance_agreement before next op arg agrees advanced) success

end Compiler.Proofs.IRGeneration.NativeCreationWorldCaller
