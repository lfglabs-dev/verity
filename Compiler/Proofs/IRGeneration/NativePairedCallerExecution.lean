import Compiler.Proofs.IRGeneration.NativePairedCallerChecks

namespace Compiler.Proofs.IRGeneration.NativePairedCallerExecution
open EvmYul NativeCreationWorldCaller NativePairedCallerChecks

/-- Persistent/transient writes retain the actual executing code and environment. -/
private theorem storage_step_environment (machine after : EVM.State) (cost : Nat)
    (arg : Option (UInt256 × Nat)) (op : Operation .EVM)
    (store : op = .SSTORE ∨ op = .TSTORE)
    (stepped : EVM.step 1 cost (some (op, arg)) machine = .ok after) :
    after.executionEnv = machine.executionEnv := by
  rcases store with rfl | rfl
  · change EVM.binaryStateOp EvmYul.State.sstore { machine with
      gasAvailable := machine.gasAvailable - UInt256.ofNat cost, execLength := machine.execLength + 1 } = .ok after at stepped
    unfold EVM.binaryStateOp at stepped
    split at stepped
    · cases stepped
      exact (NativeCreationWorldSteps.sstore_frame _ _ _).2.1
    · cases stepped
  · change EVM.binaryStateOp EvmYul.State.tstore { machine with
      gasAvailable := machine.gasAvailable - UInt256.ofNat cost, execLength := machine.execLength + 1 } = .ok after at stepped
    unfold EVM.binaryStateOp at stepped
    split at stepped
    · cases stepped
      exact (NativeCreationWorldSteps.tstore_frame _ _ _).2.1
    · cases stepped

/-- Every admitted successful prefix step retains its executing bytecode. -/
theorem checked_environment (op : Operation .EVM) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat))
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true)
    (success : CreationCaller.checkedStep machine op arg = .ok after) :
    after.executionEnv = machine.executionEnv := by
  by_cases store : op = .SSTORE ∨ op = .TSTORE
  · have step := NativeCreationStorageOpcodes.checkedStep_delegates machine after op arg success
    let expanded : EVM.State := { machine with gasAvailable := machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine op) }
    exact storage_step_environment expanded after (EVM.C' expanded op) arg op store step
  · have persistent : op ≠ .SSTORE := fun h => store (.inl h)
    have transient : op ≠ .TSTORE := fun h => store (.inr h)
    have allowed : CreationCaller.supported op = true := by simpa [persistent, transient] using admitted
    exact congrArg (fun state => state.executionEnv)
      (NativeCreationLocalFrames.supported_checked_state op machine after arg allowed success)

/-- Extract the actual successful checked step from paired advancement. -/
theorem advance_checked (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (success : advance before op arg = .ok (.continued after)) :
    (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true ∧
      CreationCaller.checkedStep before.machine op arg = .ok after.machine := by
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
        exact ⟨rfl, rfl⟩

/-- Paired advancement has the same native continuation and preserves its code. -/
theorem advance_native (fuel : Nat) (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (decoded : EVM.Proof.decodeAt before.machine = (op, arg))
    (success : advance before op arg = .ok (.continued after)) :
    after.machine.executionEnv = before.machine.executionEnv ∧
      EVM.X (fuel + 2) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
        EVM.X (fuel + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) after.machine := by
  obtain ⟨admitted, stepped⟩ := advance_checked before after op arg success
  exact ⟨checked_environment op before.machine after.machine arg admitted stepped,
    checked_native_x fuel before.machine after.machine op arg bounded admitted decoded stepped⟩

/-- A ready paired run supplies its own step count and actual native continuation. -/
theorem run_ready_native (fuel : Nat) (before after : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (success : run fuel before = .ok (.ready after)) :
    after.machine.executionEnv = before.machine.executionEnv ∧
      ∃ remaining, 0 < remaining ∧ remaining ≤ fuel ∧ ∀ extra,
        EVM.X (fuel + extra + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
          EVM.X (remaining + extra + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) after.machine := by
  induction fuel generalizing before with
  | zero => cases success
  | succ fuel ih =>
    cases decoded : EVM.decode before.machine.executionEnv.code before.machine.pc with
    | none => simp only [run, decoded] at success; cases success
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      have decodedAt : EVM.Proof.decodeAt before.machine = (op, arg) := by
        simp only [EVM.Proof.decodeAt, decoded, Option.getD_some]
      simp only [run, decoded] at success
      by_cases creation : op = .CREATE2
      · simp only [creation, ite_true] at success
        cases success
        exact ⟨rfl, fuel + 1, by omega, by omega, fun _ => rfl⟩
      · simp only [creation, ite_false] at success
        cases advanced : advance before op arg with
        | error message => simp only [advanced] at success; cases success
        | ok outcome =>
          cases outcome with
          | exceptional reason frame => simp only [advanced] at success; cases success
          | continued next =>
            simp only [advanced] at success
            have environment := (advance_native 0 before next op arg bounded decodedAt advanced).1
            have nextBound : next.machine.executionEnv.code.size < UInt256.size := by
              simpa only [environment] using bounded
            obtain ⟨finalEnv, remaining, positive, within, continuation⟩ := ih next nextBound success
            refine ⟨finalEnv.trans environment, remaining, positive, by omega, ?_⟩
            intro extra
            have step := (advance_native (fuel + extra) before next op arg bounded decodedAt advanced).2
            have tail := continuation extra
            rw [environment] at tail
            calc
              _ = EVM.X (fuel + extra + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next.machine := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
              _ = _ := tail

end Compiler.Proofs.IRGeneration.NativePairedCallerExecution
