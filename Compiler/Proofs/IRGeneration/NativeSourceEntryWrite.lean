import Compiler.Proofs.IRGeneration.NativeSourceAbiWrite

namespace Compiler.Proofs.IRGeneration.NativeSourceEntryWrite
open EvmYul NativeSourceAbiWrite CapturedMappingHelper NativeCreationWorld

/-- Stop at an actual computed PC. Only the existing proved local whitelist is
executed; unsupported instructions and fuel exhaustion are interpretation errors. -/
def runTo (target : UInt256) : Nat → EVM.State → Except String EVM.State
  | 0, _ => .error "source entry fuel exhausted"
  | fuel + 1, state =>
    if state.pc = target then .ok state
    else match EVM.decode state.executionEnv.code state.pc with
    | none => .error "source entry unsupported opcode"
    | some (op, arg) =>
      if CreationCaller.supported op then
        match CreationCaller.checkedStep state op arg with
        | .error reason => .error s!"source entry native exception: {repr reason}"
        | .ok next => runTo target fuel next
      else .error "source entry instruction outside local whitelist"

/-- A successful actual entry run derives its target PC and whole native world
frame, including every account and the original transaction calldata. -/
theorem runTo_frame (target : UInt256) (fuel : Nat) (initial final : EVM.State)
    (success : runTo target fuel initial = .ok final) :
    final.pc = target ∧ final.toState = initial.toState := by
  induction fuel generalizing initial with
  | zero => cases success
  | succ fuel ih =>
    by_cases reached : initial.pc = target
    · simp only [runTo, reached, ite_true] at success
      cases success
      exact ⟨reached, rfl⟩
    · simp only [runTo, reached, ite_false] at success
      cases decoded : EVM.decode initial.executionEnv.code initial.pc with
      | none => simp only [decoded] at success; cases success
      | some instruction =>
        rcases instruction with ⟨op, arg⟩
        simp only [decoded] at success
        cases allowed : CreationCaller.supported op with
        | false => simp only [allowed, Bool.false_eq_true, ite_false] at success; cases success
        | true =>
          simp only [allowed, ite_true] at success
          cases step : CreationCaller.checkedStep initial op arg with
          | error reason => simp only [step] at success; cases success
          | ok next =>
            simp only [step] at success
            obtain ⟨position, world⟩ := ih next success
            exact ⟨position, world.trans
              (NativeCreationLocalFrames.supported_checked_state op initial next arg allowed step)⟩

/-- The same local execution preserves physical-memory allocation bounds. -/
theorem runTo_allocated (target : UInt256) (fuel : Nat) (initial final : EVM.State)
    (allocated : NativeMidnightConstructor.CallerAllocated initial)
    (success : runTo target fuel initial = .ok final) :
    NativeMidnightConstructor.CallerAllocated final := by
  induction fuel generalizing initial with
  | zero => cases success
  | succ fuel ih =>
    by_cases reached : initial.pc = target
    · simp only [runTo, reached, ite_true] at success
      cases success
      exact allocated
    · simp only [runTo, reached, ite_false] at success
      cases decoded : EVM.decode initial.executionEnv.code initial.pc with
      | none => simp only [decoded] at success; cases success
      | some instruction =>
        rcases instruction with ⟨op, arg⟩
        simp only [decoded] at success
        cases allowed : CreationCaller.supported op with
        | false => simp only [allowed, Bool.false_eq_true, ite_false] at success; cases success
        | true =>
          simp only [allowed, ite_true] at success
          cases step : CreationCaller.checkedStep initial op arg with
          | error reason => simp only [step] at success; cases success
          | ok next =>
            simp only [step] at success
            exact ih next (NativeCallerAllocationSteps.supported_checked_allocation
              op initial next allocated arg allowed step) success

/-- The computed entry result has an actual bounded checked instruction run,
whose intermediate states and exact count are obtained from execution. -/
theorem runTo_steps (target : UInt256) (fuel : Nat) (initial final : EVM.State)
    (success : runTo target fuel initial = .ok final) :
    ∃ steps, steps < fuel ∧ checkedSteps steps initial = .ok final := by
  induction fuel generalizing initial with
  | zero => cases success
  | succ fuel ih =>
    by_cases reached : initial.pc = target
    · simp only [runTo, reached, ite_true] at success
      cases success
      exact ⟨0, by omega, rfl⟩
    · simp only [runTo, reached, ite_false] at success
      cases decoded : EVM.decode initial.executionEnv.code initial.pc with
      | none => simp only [decoded] at success; cases success
      | some instruction =>
        rcases instruction with ⟨op, arg⟩
        simp only [decoded] at success
        cases allowed : CreationCaller.supported op with
        | false => simp only [allowed, Bool.false_eq_true, ite_false] at success; cases success
        | true =>
          simp only [allowed, ite_true] at success
          cases step : CreationCaller.checkedStep initial op arg with
          | error reason => simp only [step] at success; cases success
          | ok next =>
            simp only [step] at success
            obtain ⟨count, bound, rest⟩ := ih next success
            refine ⟨count + 1, by omega, ?_⟩
            have fetched : EVM.Proof.decodeAt initial = (op, arg) := by
              simp only [EVM.Proof.decodeAt, decoded, Option.getD_some]
            simpa only [checkedSteps, fetched, step, Bind.bind, Except.bind] using rest

/-- Checked source entry execution follows the actual native EVM iterator;
the exact step count is obtained from execution and all gas/jump guards remain. -/
theorem runTo_native (target : UInt256) (fuel : Nat) (initial final : EVM.State)
    (bounded : initial.executionEnv.code.size < UInt256.size)
    (success : runTo target fuel initial = .ok final) :
    ∃ steps, steps < fuel ∧ ∀ extra,
      EVM.X (steps + extra + 1) (EVM.D_J initial.executionEnv.code (UInt256.ofNat 0)) initial =
        EVM.X (extra + 1) (EVM.D_J initial.executionEnv.code (UInt256.ofNat 0)) final := by
  induction fuel generalizing initial with
  | zero => cases success
  | succ fuel ih =>
    by_cases reached : initial.pc = target
    · simp only [runTo, reached, ite_true] at success
      cases success
      exact ⟨0, by omega, fun _ => by simp only [Nat.zero_add]⟩
    · simp only [runTo, reached, ite_false] at success
      cases decoded : EVM.decode initial.executionEnv.code initial.pc with
      | none => simp only [decoded] at success; cases success
      | some instruction =>
        rcases instruction with ⟨op, arg⟩
        simp only [decoded] at success
        cases allowed : CreationCaller.supported op with
        | false => simp only [allowed, Bool.false_eq_true, ite_false] at success; cases success
        | true =>
          simp only [allowed, ite_true] at success
          cases step : CreationCaller.checkedStep initial op arg with
          | error reason => simp only [step] at success; cases success
          | ok next =>
            simp only [step] at success
            have world := NativeCreationLocalFrames.supported_checked_state op initial next arg allowed step
            have nextCode : next.executionEnv.code = initial.executionEnv.code :=
              congrArg (fun s : State .EVM => s.executionEnv.code) world
            have boundNext : next.executionEnv.code.size < UInt256.size := by rw [nextCode]; exact bounded
            obtain ⟨count, bound, rest⟩ := ih next boundNext success
            refine ⟨count + 1, by omega, ?_⟩
            intro extra
            have fetched : EVM.Proof.decodeAt initial = (op, arg) := by
              simp only [EVM.Proof.decodeAt, decoded, Option.getD_some]
            have admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true := by
              simp only [allowed, Bool.true_or]
            have one := NativePairedCallerChecks.checked_native_x (count + extra) initial next op arg
              bounded admitted fetched step
            have tail := rest extra
            rw [nextCode] at tail
            calc
              _ = EVM.X (count + extra + 1) (EVM.D_J initial.executionEnv.code (UInt256.ofNat 0)) next := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using one
              _ = _ := tail

/-- Execute the actual entry to the mapping fragment, then all thirteen checked
source instructions. No boundary world or storage operands are supplied. -/
def entryWrite (fuel : Nat) (initial : EVM.State) : Except String EVM.State := do
  let ready ← runTo (UInt256.ofNat 404) fuel initial
  match checkedSteps 13 ready with
  | .error reason => .error s!"source mapping native exception: {repr reason}"
  | .ok final => .ok final

/-- Successful composition supplies the real entry boundary and fragment run. -/
theorem entryWrite_split (fuel : Nat) (initial final : EVM.State)
    (success : entryWrite fuel initial = .ok final) :
    ∃ ready, runTo (UInt256.ofNat 404) fuel initial = .ok ready ∧
      checkedSteps 13 ready = .ok final := by
  unfold entryWrite at success
  cases entry : runTo (UInt256.ofNat 404) fuel initial with
  | error reason => simp only [entry, Bind.bind, Except.bind] at success; cases success
  | ok ready =>
    simp only [entry, Bind.bind, Except.bind] at success
    cases write : checkedSteps 13 ready with
    | error reason => simp only [write] at success; cases success
    | ok result =>
      simp only [write] at success
      cases success
      exact ⟨ready, rfl, write⟩

/-- From original source entry, every successful composition derives the actual
mapping effect using ORIGINAL transaction calldata, never boundary operands. -/
theorem entryWrite_agreement (world : Verity.ContractState) (fuel : Nat) (initial final : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (same : initial.executionEnv.code = NativeSourceAbiWrite.code)
    (present : initial.toState.lookupAccount initial.executionEnv.codeOwner = some account)
    (agrees : Agreement world initial warm)
    (success : entryWrite fuel initial = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (initial.toState.calldataload (UInt256.ofNat 36)).toNat)) :
    Agreement (world.writeSlot (Compiler.Proofs.solidityMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat)
      (Verity.Core.Uint256.ofNat (initial.toState.calldataload (UInt256.ofNat 68)).toNat)) final warm := by
  obtain ⟨ready, entry, write⟩ := entryWrite_split fuel initial final success
  obtain ⟨position, frame⟩ := runTo_frame _ fuel initial ready entry
  have current := NativeCreationLocalFrames.agreement_of_state_eq world initial ready warm agrees frame
  have code : ready.executionEnv.code = NativeSourceAbiWrite.code := by rw [frame]; exact same
  have accountAt : ready.toState.lookupAccount ready.executionEnv.codeOwner = some account := by
    rw [frame]; exact present
  have hashAt : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (ready.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (ready.toState.calldataload (UInt256.ofNat 36)).toNat) := by rw [frame]; exact hash
  have actual := source_write world ready final warm account code position accountAt current write hashAt
  simpa only [frame] using actual

/-- The complete canonical write is expressed using original entry calldata;
the local entry prefix supplies only computed machine states, never a postworld. -/
theorem entryWrite_paired (world : Verity.ContractState) (fuel : Nat) (initial final : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (same : initial.executionEnv.code = NativeSourceAbiWrite.code)
    (present : initial.toState.lookupAccount initial.executionEnv.codeOwner = some account)
    (success : entryWrite fuel initial = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (initial.toState.calldataload (UInt256.ofNat 36)).toNat)) :
    ∃ ready middle, runTo (UInt256.ofNat 404) fuel initial = .ok ready ∧
      checkedSteps 12 ready = .ok middle ∧ CreationCaller.checkedStep middle .SSTORE none = .ok final ∧
      NativeCreationWorldCaller.worldAfter ⟨world, middle, warm⟩ .SSTORE = .ok
        (world.writeSlot (Compiler.Proofs.solidityMappingSlot 0
          (initial.toState.calldataload (UInt256.ofNat 36)).toNat)
          (Verity.Core.Uint256.ofNat (initial.toState.calldataload (UInt256.ofNat 68)).toNat)) := by
  obtain ⟨ready, entry, write⟩ := entryWrite_split fuel initial final success
  obtain ⟨position, frame⟩ := runTo_frame _ fuel initial ready entry
  have code : ready.executionEnv.code = NativeSourceAbiWrite.code := by rw [frame]; exact same
  have accountAt : ready.toState.lookupAccount ready.executionEnv.codeOwner = some account := by
    rw [frame]; exact present
  have hashAt : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (ready.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (ready.toState.calldataload (UInt256.ofNat 36)).toNat) := by rw [frame]; exact hash
  obtain ⟨middle, steps, stored, effect⟩ := source_paired_write world ready final warm account
    code position accountAt write hashAt
  refine ⟨ready, middle, entry, steps, stored, ?_⟩
  simpa only [frame] using effect

end Compiler.Proofs.IRGeneration.NativeSourceEntryWrite


