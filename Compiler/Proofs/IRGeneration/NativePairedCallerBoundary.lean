import Compiler.Proofs.IRGeneration.NativePairedCallerExecution

namespace Compiler.Proofs.IRGeneration.NativePairedCallerBoundary
open EvmYul NativeCreationWorldCaller NativePairedCallerExecution NativeMidnightConstructor

/-- A ready paired run supplies its own step count and actual native continuation. -/
theorem run_ready_steps (fuel : Nat) (before after : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (success : run fuel before = .ok (.ready after)) :
    after.machine.executionEnv = before.machine.executionEnv ∧
      ∃ steps, steps < fuel ∧ ∀ extra,
        EVM.X (steps + extra + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
          EVM.X (extra + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) after.machine := by
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
        exact ⟨rfl, 0, by omega, fun _ => by simp only [Nat.zero_add]⟩
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
            obtain ⟨finalEnv, steps, within, continuation⟩ := ih next nextBound success
            refine ⟨finalEnv.trans environment, steps + 1, by omega, ?_⟩
            intro extra
            have step := (advance_native (steps + extra) before next op arg bounded decodedAt advanced).2
            have tail := continuation extra
            rw [environment] at tail
            calc
              _ = EVM.X (steps + extra + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next.machine := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
              _ = _ := tail


/-- The real decoder never attaches a PUSH argument to CREATE2. -/
theorem decode_create2_argument (code : ByteArray) (pc : UInt256)
    (arg : Option (UInt256 × Nat)) (decoded : EVM.decode code pc = some (.CREATE2, arg)) :
    arg = none := by
  unfold EVM.decode at decoded
  dsimp only [Bind.bind, Option.bind] at decoded
  cases byteEq : code.get? pc.toNat with
  | none => simp only [byteEq] at decoded; cases decoded
  | some byte =>
    simp only [byteEq] at decoded
    cases parsed : EVM.parseInstr byte with
    | none => simp only [parsed] at decoded; cases decoded
    | some op =>
      simp only [parsed, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, argument⟩ := decoded
      simpa only [EVM.argOnNBytesOfInstr, beq_self_eq_true, ite_true] using argument.symm


/-- Ready is evidence of the actual decoded boundary instruction, not an oracle. -/
theorem run_ready_decoded (fuel : Nat) (before boundary : Frame)
    (ready : run fuel before = .ok (.ready boundary)) :
    EVM.Proof.decodeAt boundary.machine = (.CREATE2, none) := by
  induction fuel generalizing before with
  | zero => cases ready
  | succ fuel ih =>
    cases decoded : EVM.decode before.machine.executionEnv.code before.machine.pc with
    | none => simp only [run, decoded] at ready; cases ready
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      simp only [run, decoded] at ready
      by_cases creation : op = .CREATE2
      · subst op
        simp only [ite_true] at ready
        cases ready
        have argument := decode_create2_argument _ _ arg decoded
        simp only [EVM.Proof.decodeAt, decoded, Option.getD_some, argument]
      · simp only [creation, ite_false] at ready
        cases advanced : advance before op arg with
        | error message => simp only [advanced] at ready; cases ready
        | ok outcome =>
          cases outcome with
          | exceptional reason frame => simp only [advanced] at ready; cases ready
          | continued next =>
            simp only [advanced] at ready
            exact ih next ready

/-- Complete checked creation after the actual paired storage-writing prefix.
The canonical result starts from its computed world, never the stale entry world. -/
theorem run_ready_creation_native (prefixFuel : Nat) (before boundary : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (agrees : NativeCreationWorld.Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (ready : run prefixFuel before = .ok (.ready boundary))
    (payload : ByteArray) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerOperationGuards boundary.machine payload fuel rest offset size salt)
    (limit : boundary.machine.stack.length ≤ 1024) :
    ∃ steps next value final, steps < prefixFuel ∧
      EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) = .ok next ∧
      EVM.X (steps + fuel + 4) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
        EVM.X (fuel + 3) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next ∧
      Verity.Core.Model.Create2Operation.run (CreationBytecode.atBoundary boundary)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued value final) ∧
      NativeCreationWorld.Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations boundary.machine next rest offset size value ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement boundary.world final.world boundary.machine.substate next.substate
        (nativeCreate2Target boundary.machine.executionEnv.codeOwner salt.toByteArray
          (Verity.Core.Model.MidnightInitcode.initcode payload)) := by
  obtain ⟨environment, steps, within, continuation⟩ := run_ready_steps prefixFuel before boundary bounded ready
  have decoded := run_ready_decoded prefixFuel before boundary ready
  let jumps := EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)
  obtain ⟨next, value, final, stepped, created, operation, agreement, gas, observations, physical, frames⟩ :=
    NativePairedCallerAllocation.run_ready_creation prefixFuel before boundary agrees allocated ready
      payload fuel rest offset size salt guards jumps decoded limit
  have prefixRun := continuation (fuel + 3)
  have combined : EVM.X (steps + fuel + 4) jumps before.machine = EVM.X (fuel + 3) jumps next := by
    calc
      _ = EVM.X (fuel + 4) jumps boundary.machine := by
        simpa only [Nat.add_assoc] using prefixRun
      _ = _ := created
  exact ⟨steps, next, value, final, within, stepped, combined, operation, agreement, gas, observations, physical, frames⟩

end Compiler.Proofs.IRGeneration.NativePairedCallerBoundary
