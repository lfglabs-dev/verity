import Compiler.Proofs.IRGeneration.NativeCreate2CallerCollision
import Compiler.Proofs.IRGeneration.NativeCreationWorldCaller

namespace Compiler.Proofs.IRGeneration.NativePairedCallerAllocation
open EvmYul NativeMidnightConstructor NativeCreationWorldCaller

private theorem storage_step_allocation (machine after : EVM.State) (cost : Nat)
    (arg : Option (UInt256 × Nat)) (allocated : CallerAllocated machine) (op : Operation .EVM)
    (store : op = .SSTORE ∨ op = .TSTORE)
    (stepped : EVM.step 1 cost (some (op, arg)) machine = .ok after) : CallerAllocated after := by
  rcases store with rfl | rfl
  · change EVM.binaryStateOp EvmYul.State.sstore { machine with
      gasAvailable := machine.gasAvailable - UInt256.ofNat cost, execLength := machine.execLength + 1 } = .ok after at stepped
    unfold EVM.binaryStateOp at stepped
    split at stepped
    · cases stepped
      exact allocated
    · cases stepped
  · change EVM.binaryStateOp EvmYul.State.tstore { machine with
      gasAvailable := machine.gasAvailable - UInt256.ofNat cost, execLength := machine.execLength + 1 } = .ok after at stepped
    unfold EVM.binaryStateOp at stepped
    split at stepped
    · cases stepped
      exact allocated
    · cases stepped

/-- Every actual checked opcode admitted by the paired prefix preserves allocation. -/
theorem paired_checked_allocation (op : Operation .EVM) (machine after : EVM.State)
    (allocated : CallerAllocated machine) (arg : Option (UInt256 × Nat))
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true)
    (success : CreationCaller.checkedStep machine op arg = .ok after) : CallerAllocated after := by
  by_cases store : op = .SSTORE ∨ op = .TSTORE
  · have step := NativeCreationStorageOpcodes.checkedStep_delegates machine after op arg success
    let expanded : EVM.State := { machine with gasAvailable := machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine op) }
    exact storage_step_allocation expanded after (EVM.C' expanded op) arg allocated op store step
  · have allowed : CreationCaller.supported op = true := by
      have persistent : op ≠ .SSTORE := fun h => store (.inl h)
      have transient : op ≠ .TSTORE := fun h => store (.inr h)
      simpa [persistent, transient] using admitted
    exact NativeCallerAllocationSteps.supported_checked_allocation op machine after allocated arg allowed success

/-- Pairing actual storage writes cannot invent unallocated caller bytes. -/
theorem advance_allocation (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (allocated : CallerAllocated before.machine)
    (success : advance before op arg = .ok (.continued after)) : CallerAllocated after.machine := by
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
        exact paired_checked_allocation op before.machine next allocated arg admitted stepped

/-- Every real paired caller prefix reaching CREATE2 preserves physical allocation. -/
theorem run_ready_allocation (fuel : Nat) (before after : Frame)
    (allocated : CallerAllocated before.machine)
    (success : run fuel before = .ok (.ready after)) : CallerAllocated after.machine := by
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
        exact allocated
      · simp only [creation, ite_false] at success
        cases advanced : advance before op arg with
        | error message => simp only [advanced] at success; cases success
        | ok outcome =>
          cases outcome with
          | exceptional reason frame => simp only [advanced] at success; cases success
          | continued next =>
            simp only [advanced] at success
            exact ih next (advance_allocation before next op arg allocated advanced) success

/-- The paired prefix supplies both required initial relations at the actual boundary. -/
theorem run_ready_boundary (fuel : Nat) (before after : Frame)
    (agrees : NativeCreationWorld.Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (success : run fuel before = .ok (.ready after)) :
    NativeCreationWorld.Agreement after.world after.machine after.warm ∧ CallerAllocated after.machine :=
  ⟨NativeCreationWorldCaller.run_ready_agreement fuel before after agrees success,
    run_ready_allocation fuel before after allocated success⟩

/-- Complete checked creation after the actual paired storage-writing prefix.
The canonical result starts from its computed world, never the stale entry world. -/
theorem run_ready_creation (prefixFuel : Nat) (before boundary : Frame)
    (agrees : NativeCreationWorld.Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (ready : run prefixFuel before = .ok (.ready boundary))
    (payload : ByteArray) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerOperationGuards boundary.machine payload fuel rest offset size salt)
    (jumps : Array UInt256) (decoded : EVM.Proof.decodeAt boundary.machine = (.CREATE2, none))
    (limit : boundary.machine.stack.length ≤ 1024) :
    ∃ next value final,
      EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) = .ok next ∧
      EVM.X (fuel + 4) jumps boundary.machine = EVM.X (fuel + 3) jumps next ∧
      Verity.Core.Model.Create2Operation.run (CreationBytecode.atBoundary boundary)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued value final) ∧
      NativeCreationWorld.Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations boundary.machine next rest offset size value ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement boundary.world final.world boundary.machine.substate next.substate
        (nativeCreate2Target boundary.machine.executionEnv.codeOwner salt.toByteArray
          (Verity.Core.Model.MidnightInitcode.initcode payload)) := by
  obtain ⟨agreement, allocation⟩ := run_ready_boundary prefixFuel before boundary agrees allocated ready
  exact caller_checked_operation_completed boundary.world boundary.machine boundary.warm agreement allocation
    payload fuel rest offset size salt guards jumps decoded limit

end Compiler.Proofs.IRGeneration.NativePairedCallerAllocation
