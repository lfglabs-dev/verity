import Compiler.Proofs.IRGeneration.NativeMappingStorageExecution

namespace Compiler.Proofs.IRGeneration.NativeMappingCallerFrames
open EvmYul NativeMidnightConstructor NativeCreationWorld

/-- KECCAK ignores an immediate argument in the actual interpreter; real decoding still supplies none. -/
theorem checked_keccak_arg (machine : EVM.State) (arg : Option (UInt256 × Nat)) :
    CreationCaller.checkedStep machine .KECCAK256 arg =
      CreationCaller.checkedStep machine .KECCAK256 none := by rfl

/-- Native KECCAK reads physical memory and grows its charged extent without allocating bytes. -/
theorem keccak_allocated (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset size : UInt256) :
    (machine.keccak256 offset size).2.memory.size ≤
      (machine.keccak256 offset size).2.activeWords.toNat * 32 := by
  have nowrap := native_memory_words_nowrap machine.activeWords offset size
  have conversion : (UInt256.ofNat (MachineState.M machine.activeWords.toNat offset.toNat size.toNat)).toNat =
      MachineState.M machine.activeWords.toNat offset.toNat size.toNat := Nat.mod_eq_of_lt nowrap
  change machine.memory.size ≤ (UInt256.ofNat (MachineState.M machine.activeWords.toNat offset.toNat size.toNat)).toNat * 32
  rw [conversion]
  have extent : machine.activeWords.toNat ≤ MachineState.M machine.activeWords.toNat offset.toNat size.toNat := by
    cases count : size.toNat with
    | zero => exact Nat.le_refl _
    | succ n => exact Nat.le_max_left _ _
  exact allocated.trans (Nat.mul_le_mul_right 32 extent)

/-- The actual checked KECCAK step preserves allocation; no operand or extent oracle is needed. -/
theorem checked_keccak_allocated (machine after : EVM.State)
    (allocated : CallerAllocated machine)
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    CallerAllocated after := by
  have enough := (NativePairedCallerChecks.checked_guards machine after .KECCAK256 none success).stack
  simp only [EVM.δ, Option.getD] at enough
  cases stack : machine.stack with
  | nil => simp only [stack, List.length_nil] at enough; omega
  | cons offset rest =>
    cases rest with
    | nil => simp only [stack, List.length_cons, List.length_nil] at enough; omega
    | cons size tail =>
      let mid := EVM.Proof.zMid machine .KECCAK256
      have midStack : mid.stack = offset :: size :: tail := stack
      have restored : { mid with stack := offset :: size :: tail } = mid := by rw [← midStack]
      have actual := NativeMappingKeccak.step_keccak mid offset size tail (EVM.C' mid .KECCAK256)
      rw [restored] at actual
      have delegated := NativeCreationStorageOpcodes.checkedStep_delegates machine after .KECCAK256 none success
      have same := Except.ok.inj (delegated.symm.trans actual)
      rw [same]
      exact keccak_allocated (EVM.Proof.stepPre (EVM.C' mid .KECCAK256) mid).toMachineState allocated offset size

/-- The checked hash preserves all twelve canonical/native account-world relations. -/
theorem checked_keccak_agreement (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world machine warm)
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    Agreement world after warm := by
  exact NativeCreationLocalFrames.agreement_of_state_eq world machine after warm agrees
    (NativeMappingStorageExecution.checked_keccak_state machine after success)

/-- Account-world agreement and physical allocation survive the same actual hash step. -/
theorem checked_keccak_boundary (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world machine warm) (allocated : CallerAllocated machine)
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    Agreement world after warm ∧ CallerAllocated after :=
  ⟨checked_keccak_agreement world machine after warm agrees success,
    checked_keccak_allocated machine after allocated success⟩

/-- The byte-decoded checked hash has exactly the native continuation for every positive fuel. -/
theorem checked_keccak_native (fuel : Nat) (machine after : EVM.State)
    (decoded : EVM.Proof.decodeAt machine = (.KECCAK256, none))
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    EVM.X (fuel + 2) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) machine =
      EVM.X (fuel + 1) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) after := by
  apply EVM.Proof.X_succ_of_continue decoded (NativeMappingKeccak.checked_keccak_z machine after success)
  · change EVM.step (fuel + 1) (EVM.C' (EVM.Proof.zMid machine .KECCAK256) .KECCAK256)
      (some (.KECCAK256, none)) (EVM.Proof.zMid machine .KECCAK256) = .ok after
    rw [NativeMappingKeccak.step_keccak_fuel]
    exact NativeCreationStorageOpcodes.checkedStep_delegates machine after .KECCAK256 none success
  · rfl

/-- The same actual hash transports world agreement, physical allocation and native execution. -/
theorem checked_keccak_complete (fuel : Nat) (world : Verity.ContractState) (machine after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world machine warm) (allocated : CallerAllocated machine)
    (decoded : EVM.Proof.decodeAt machine = (.KECCAK256, none))
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    Agreement world after warm ∧ CallerAllocated after ∧
      EVM.X (fuel + 2) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) machine =
        EVM.X (fuel + 1) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) after :=
  ⟨checked_keccak_agreement world machine after warm agrees success,
    checked_keccak_allocated machine after allocated success,
    checked_keccak_native fuel machine after decoded success⟩

end Compiler.Proofs.IRGeneration.NativeMappingCallerFrames

namespace Compiler.Proofs.IRGeneration.NativeHashedWorldCaller
open EvmYul NativeCreationWorldCaller NativeCreationWorld NativeMidnightConstructor

/-- Extend the checked paired prefix with the actual native memory hash.
The canonical world is unchanged only for this proved read-only opcode. -/
def advance (before : Frame) (op : Operation .EVM) (arg : Option (UInt256 × Nat)) :
    Except String StepOutcome := do
  if op = .KECCAK256 then
    match CreationCaller.checkedStep before.machine op arg with
    | .error reason => pure (.exceptional reason
        { before with machine := CreationCaller.exhausted before.machine })
    | .ok next => pure (.continued { before with machine := next })
  else NativeCreationWorldCaller.advance before op arg

/-- Decode each computed PC, stopping at CREATE2 without executing or inventing its result. -/
def run : Nat → Frame → Except String Outcome
  | 0, before => .error s!"hashed caller fuel exhausted at bytecode pc {before.machine.pc.toNat}"
  | fuel + 1, before =>
    match EVM.decode before.machine.executionEnv.code before.machine.pc with
    | none => .error s!"unsupported hashed caller opcode at bytecode pc {before.machine.pc.toNat}"
    | some (op, arg) =>
      if op = .CREATE2 then .ok (.ready before)
      else do
        match ← advance before op arg with
        | .continued next => run fuel next
        | .exceptional reason frame => pure (.exceptional reason frame)

/-- The extension delegates every other opcode to the unchanged checked paired prefix. -/
theorem advance_other (before : Frame) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (other : op ≠ .KECCAK256) :
    advance before op arg = NativeCreationWorldCaller.advance before op arg := by
  simp only [advance, other, ↓reduceIte]

/-- A successful hash advancement supplies its own real checked poststate. -/
theorem advance_hash_checked (before after : Frame) (arg : Option (UInt256 × Nat))
    (success : advance before .KECCAK256 arg = .ok (.continued after)) :
    CreationCaller.checkedStep before.machine .KECCAK256 none = .ok after.machine ∧
      after.world = before.world ∧ after.warm = before.warm := by
  simp only [advance, ↓reduceIte] at success
  rw [NativeMappingCallerFrames.checked_keccak_arg] at success
  cases step : CreationCaller.checkedStep before.machine .KECCAK256 none with
  | error reason => simp only [step] at success; cases success
  | ok next =>
    simp only [step] at success
    cases success
    exact ⟨rfl, rfl, rfl⟩

/-- The actual hash-aware advancement retains the complete canonical/native relation. -/
theorem advance_agreement (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (agrees : Agreement before.world before.machine before.warm)
    (success : advance before op arg = .ok (.continued after)) :
    Agreement after.world after.machine after.warm := by
  by_cases hash : op = .KECCAK256
  · subst op
    have result := advance_hash_checked before after arg success
    rw [result.2.1, result.2.2]
    exact NativeMappingCallerFrames.checked_keccak_agreement before.world before.machine after.machine
      before.warm agrees result.1
  · rw [advance_other before op arg hash] at success
    exact NativeCreationWorldCaller.advance_agreement before after op arg agrees success

/-- The actual hash-aware advancement preserves materialized-memory allocation. -/
theorem advance_allocation (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (allocated : CallerAllocated before.machine)
    (success : advance before op arg = .ok (.continued after)) : CallerAllocated after.machine := by
  by_cases hash : op = .KECCAK256
  · subst op
    exact NativeMappingCallerFrames.checked_keccak_allocated before.machine after.machine allocated
      (advance_hash_checked before after arg success).1
  · rw [advance_other before op arg hash] at success
    exact NativePairedCallerAllocation.advance_allocation before after op arg allocated success

/-- A real decoded prefix reaching CREATE2 transports its own world and allocated memory. -/
theorem run_ready_boundary (fuel : Nat) (before after : Frame)
    (agrees : Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (success : run fuel before = .ok (.ready after)) :
    Agreement after.world after.machine after.warm ∧ CallerAllocated after.machine := by
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
        exact ⟨agrees, allocated⟩
      · simp only [creation, ite_false] at success
        cases advanced : advance before op arg with
        | error message => simp only [advanced] at success; cases success
        | ok outcome =>
          cases outcome with
          | exceptional reason frame => simp only [advanced] at success; cases success
          | continued next =>
            simp only [advanced] at success
            exact ih next (advance_agreement before next op arg agrees advanced)
              (advance_allocation before next op arg allocated advanced) success

end Compiler.Proofs.IRGeneration.NativeHashedWorldCaller

namespace Compiler.Proofs.IRGeneration.NativeHashedWorldCaller
open EvmYul NativeCreationWorldCaller NativeCreationWorld NativeMidnightConstructor

/-- A real decoded KECCAK cannot carry a PUSH immediate. -/
theorem decode_hash_none (code : ByteArray) (pc : UInt256) (arg : Option (UInt256 × Nat))
    (decoded : EVM.decode code pc = some (.KECCAK256, arg)) : arg = none := by
  unfold EVM.decode at decoded
  cases fetched : code.get? pc.toNat with
  | none => simp [fetched] at decoded
  | some byte =>
    cases parsed : EVM.parseInstr byte with
    | none => simp [fetched, parsed] at decoded
    | some op =>
      simp only [fetched, parsed, Bind.bind, Option.bind] at decoded
      have identity : op = .KECCAK256 := congrArg Prod.fst (Option.some.inj decoded)
      subst op
      exact (congrArg Prod.snd (Option.some.inj decoded)).symm

/-- Hash-aware advancement preserves bytecode and follows the actual native iterator. -/
theorem advance_native (fuel : Nat) (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (decoded : EVM.decode before.machine.executionEnv.code before.machine.pc = some (op, arg))
    (success : advance before op arg = .ok (.continued after)) :
    after.machine.executionEnv = before.machine.executionEnv ∧
      EVM.X (fuel + 2) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
        EVM.X (fuel + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) after.machine := by
  have decodedAt : EVM.Proof.decodeAt before.machine = (op, arg) := by
    simp only [EVM.Proof.decodeAt, decoded, Option.getD_some]
  by_cases hash : op = .KECCAK256
  · subst op
    have immediate := decode_hash_none _ _ arg decoded
    subst arg
    have step := (advance_hash_checked before after none success).1
    have frame := NativeMappingStorageExecution.checked_keccak_state before.machine after.machine step
    exact ⟨congrArg (fun state => state.executionEnv) frame, NativeMappingCallerFrames.checked_keccak_native fuel _ _ decodedAt step⟩
  · rw [advance_other before op arg hash] at success
    exact NativePairedCallerExecution.advance_native fuel before after op arg bounded decodedAt success

/-- A ready hash-aware run supplies its own step count and actual native continuation. -/
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
            have environment := (advance_native 0 before next op arg bounded decoded advanced).1
            have nextBound : next.machine.executionEnv.code.size < UInt256.size := by
              simpa only [environment] using bounded
            obtain ⟨finalEnv, remaining, positive, within, continuation⟩ := ih next nextBound success
            refine ⟨finalEnv.trans environment, remaining, positive, by omega, ?_⟩
            intro extra
            have step := (advance_native (fuel + extra) before next op arg bounded decoded advanced).2
            have tail := continuation extra
            rw [environment] at tail
            calc
              _ = EVM.X (fuel + extra + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next.machine := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
              _ = _ := tail


end Compiler.Proofs.IRGeneration.NativeHashedWorldCaller

namespace Compiler.Proofs.IRGeneration.NativeHashedWorldCaller
open EvmYul NativeCreationWorldCaller NativeMidnightConstructor

/-- A ready hash-aware run supplies its own step count and actual native continuation. -/
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
            have environment := (advance_native 0 before next op arg bounded decoded advanced).1
            have nextBound : next.machine.executionEnv.code.size < UInt256.size := by
              simpa only [environment] using bounded
            obtain ⟨finalEnv, steps, within, continuation⟩ := ih next nextBound success
            refine ⟨finalEnv.trans environment, steps + 1, by omega, ?_⟩
            intro extra
            have step := (advance_native (steps + extra) before next op arg bounded decoded advanced).2
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

/-- Complete checked creation after the actual hash-aware storage-writing prefix.
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
  obtain ⟨agreementBefore, allocationBefore⟩ := run_ready_boundary prefixFuel before boundary agrees allocated ready
  obtain ⟨next, value, final, stepped, created, operation, agreement, gas, observations, physical, frames⟩ :=
    caller_checked_operation_completed boundary.world boundary.machine boundary.warm agreementBefore allocationBefore
      payload fuel rest offset size salt guards jumps decoded limit
  have prefixRun := continuation (fuel + 3)
  have combined : EVM.X (steps + fuel + 4) jumps before.machine = EVM.X (fuel + 3) jumps next := by
    calc
      _ = EVM.X (fuel + 4) jumps boundary.machine := by
        simpa only [Nat.add_assoc] using prefixRun
      _ = _ := created
  exact ⟨steps, next, value, final, within, stepped, combined, operation, agreement, gas, observations, physical, frames⟩

end Compiler.Proofs.IRGeneration.NativeHashedWorldCaller
