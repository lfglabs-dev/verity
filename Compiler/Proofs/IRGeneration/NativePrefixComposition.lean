import Compiler.Proofs.IRGeneration.NativeSourceEntryWrite
import Compiler.Proofs.IRGeneration.NativeHashedWorldCaller

namespace Compiler.Proofs.IRGeneration.NativePrefixComposition
open EvmYul NativeCreationWorldCaller

/-- The existing local whitelist excludes the four boundary/world instructions. -/
theorem local_excludes (op : Operation .EVM) (allowed : CreationCaller.supported op = true) :
    op ≠ .CREATE2 ∧ op ≠ .KECCAK256 ∧ op ≠ .SSTORE ∧ op ≠ .TSTORE := by
  have exclude : ∀ other ∈ [Operation.CREATE2, .KECCAK256, .SSTORE, .TSTORE], op ≠ other := by
    intro other member equal
    subst op
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp [CreationCaller.supported, Operation.isPush, Operation.isDup, Operation.isSwap] at allowed
  exact ⟨exclude _ (by simp), exclude _ (by simp), exclude _ (by simp), exclude _ (by simp)⟩

/-- A real successful local step is the SAME hash-aware paired step, with every
canonical world field retained. No selected poststate or world is substituted. -/
theorem local_advance (world : Verity.ContractState)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (machine after : EVM.State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (allowed : CreationCaller.supported op = true)
    (step : CreationCaller.checkedStep machine op arg = .ok after) :
    NativeHashedWorldCaller.advance ⟨world, machine, warm⟩ op arg =
      .ok (.continued ⟨world, after, warm⟩) := by
  obtain ⟨_, hash, store, transient⟩ := local_excludes op allowed
  simp only [NativeHashedWorldCaller.advance, hash, ite_false,
    NativeCreationWorldCaller.advance, allowed, Bool.true_or, Bool.not_true, Bool.false_eq_true,
    step, Bind.bind, Except.bind, NativeCreationWorldCaller.worldAfter, store, transient,
    Pure.pure, Except.pure, decide_false, Bool.false_or]

/-- Successful stop-PC execution supplies its own count and transports ANY
existing hash-aware continuation. It is not merely a separate native calibration. -/
theorem entry_compose (target : UInt256) (fuel : Nat) (initial ready : EVM.State)
    (success : NativeSourceEntryWrite.runTo target fuel initial = .ok ready) :
    ∃ steps, steps < fuel ∧ ∀ world warm tail,
      NativeHashedWorldCaller.run (steps + tail) ⟨world, initial, warm⟩ =
        NativeHashedWorldCaller.run tail ⟨world, ready, warm⟩ := by
  induction fuel generalizing initial with
  | zero => cases success
  | succ fuel ih =>
    by_cases reached : initial.pc = target
    · simp only [NativeSourceEntryWrite.runTo, reached, ite_true] at success
      cases success
      exact ⟨0, by omega, fun _ _ _ => by rw [Nat.zero_add]⟩
    · simp only [NativeSourceEntryWrite.runTo, reached, ite_false] at success
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
            obtain ⟨count, bound, continuation⟩ := ih next success
            refine ⟨count + 1, by omega, ?_⟩
            intro world warm tail
            have composed := continuation world warm tail
            have advance := local_advance world warm initial next op arg allowed step
            rw [show count + 1 + tail = (count + tail) + 1 from by omega]
            simpa only [NativeHashedWorldCaller.run, decoded, (local_excludes op allowed).1,
              ite_false, advance, Bind.bind, Except.bind] using composed

/-- A fixed number of actual paired steps; every decoded PC, checked native
step and canonical worldAfter is the existing hash-aware advancement. -/
def pairedSteps : Nat → Frame → Except String Frame
  | 0, frame => .ok frame
  | count + 1, frame => do
    let some (op, arg) := EVM.decode frame.machine.executionEnv.code frame.machine.pc
      | .error "paired fragment unsupported opcode"
    match ← NativeHashedWorldCaller.advance frame op arg with
    | .exceptional _ _ => .error "paired fragment native exception"
    | .continued next => pairedSteps count next

/-- The existing hash-aware checked advance never continues through CREATE2. -/
theorem advance_not_creation (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (success : NativeHashedWorldCaller.advance before op arg = .ok (.continued after)) : op ≠ .CREATE2 := by
  intro creation
  subst op
  rw [NativeHashedWorldCaller.advance_other before .CREATE2 arg (by decide)] at success
  have allowed := (NativePairedCallerExecution.advance_checked before after .CREATE2 arg success).1
  change false = true at allowed
  cases allowed

/-- The fixed paired fragment transports the full existing interpreter result,
including exceptions in its continuation, without recomputing or selecting a world. -/
theorem paired_compose (count : Nat) (initial final : Frame)
    (success : pairedSteps count initial = .ok final) :
    ∀ tail, NativeHashedWorldCaller.run (count + tail) initial =
      NativeHashedWorldCaller.run tail final := by
  induction count generalizing initial with
  | zero => cases success; exact fun _ => by rw [Nat.zero_add]
  | succ count ih =>
    cases decoded : EVM.decode initial.machine.executionEnv.code initial.machine.pc with
    | none => simp only [pairedSteps, decoded] at success; cases success
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      simp only [pairedSteps, decoded] at success
      cases advanced : NativeHashedWorldCaller.advance initial op arg with
      | error message => simp only [advanced, Bind.bind, Except.bind] at success; cases success
      | ok outcome =>
        cases outcome with
        | exceptional reason frame => simp only [advanced, Bind.bind, Except.bind] at success; cases success
        | continued next =>
          simp only [advanced, Bind.bind, Except.bind] at success
          intro tail
          have composed := ih next success tail
          have noncreation := advance_not_creation initial next op arg advanced
          simpa only [Nat.succ_add, NativeHashedWorldCaller.run, decoded, noncreation,
            ite_false, advanced, Bind.bind, Except.bind] using composed

/-- A successful local suffix to CREATE2 is exactly the existing paired run,
retaining the entire canonical world and warm set. -/
theorem suffix_ready (fuel : Nat) (initial final : EVM.State)
    (success : CreationCaller.run fuel initial = .ok (.ready final))
    (world : Verity.ContractState) (warm : Verity.Core.Model.Create2Access.WarmAccounts) :
    NativeHashedWorldCaller.run fuel ⟨world, initial, warm⟩ = .ok (.ready ⟨world, final, warm⟩) := by
  induction fuel generalizing initial with
  | zero => cases success
  | succ fuel ih =>
    cases decoded : EVM.decode initial.executionEnv.code initial.pc with
    | none => simp only [CreationCaller.run, decoded] at success; cases success
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      simp only [CreationCaller.run, decoded] at success
      by_cases creation : op = .CREATE2
      · simp only [creation, ite_true] at success
        cases success
        simp only [NativeHashedWorldCaller.run, decoded, creation, ite_true]
      · simp only [creation, ite_false] at success
        cases allowed : CreationCaller.supported op with
        | false => simp only [allowed, Bool.not_false, ite_true] at success; cases success
        | true =>
          simp only [allowed, Bool.not_true, Bool.false_eq_true, ite_false] at success
          cases step : CreationCaller.checkedStep initial op arg with
          | error reason => simp only [step] at success; cases success
          | ok next =>
            simp only [step] at success
            have advance := local_advance world warm initial next op arg allowed step
            simpa only [NativeHashedWorldCaller.run, decoded, creation, ite_false,
              advance, Bind.bind, Except.bind] using ih next success

/-- Successful paired advancement exposes its real checked native successor. -/
theorem advance_checked (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (success : NativeHashedWorldCaller.advance before op arg = .ok (.continued after)) :
    CreationCaller.checkedStep before.machine op arg = .ok after.machine := by
  by_cases hash : op = .KECCAK256
  · subst op
    have actual := (NativeHashedWorldCaller.advance_hash_checked before after arg success).1
    simpa only [NativeMappingCallerFrames.checked_keccak_arg] using actual
  · rw [NativeHashedWorldCaller.advance_other before op arg hash] at success
    exact (NativePairedCallerExecution.advance_checked before after op arg success).2

/-- Every successful hash-aware step retains its exact code and calldata. -/
theorem advance_environment (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (success : NativeHashedWorldCaller.advance before op arg = .ok (.continued after)) :
    after.machine.executionEnv = before.machine.executionEnv := by
  by_cases hash : op = .KECCAK256
  · subst op
    have actual := (NativeHashedWorldCaller.advance_hash_checked before after arg success).1
    exact congrArg (fun s : State .EVM => s.executionEnv)
      (NativeMappingStorageExecution.checked_keccak_state before.machine after.machine actual)
  · rw [NativeHashedWorldCaller.advance_other before op arg hash] at success
    obtain ⟨admitted, step⟩ := NativePairedCallerExecution.advance_checked before after op arg success
    exact NativePairedCallerExecution.checked_environment op before.machine after.machine arg admitted step

/-- A successful fixed fragment supplies its first actual decoded paired step. -/
theorem paired_split (count : Nat) (initial final : Frame)
    (success : pairedSteps (count + 1) initial = .ok final) :
    ∃ op arg next, EVM.decode initial.machine.executionEnv.code initial.machine.pc = some (op, arg) ∧
      NativeHashedWorldCaller.advance initial op arg = .ok (.continued next) ∧
      pairedSteps count next = .ok final := by
  cases decoded : EVM.decode initial.machine.executionEnv.code initial.machine.pc with
  | none => simp only [pairedSteps, decoded] at success; cases success
  | some instruction =>
    rcases instruction with ⟨op, arg⟩
    simp only [pairedSteps, decoded] at success
    cases advanced : NativeHashedWorldCaller.advance initial op arg with
    | error message => simp only [advanced, Bind.bind, Except.bind] at success; cases success
    | ok outcome =>
      cases outcome with
      | exceptional reason frame => simp only [advanced, Bind.bind, Except.bind] at success; cases success
      | continued next =>
          simp only [advanced, Bind.bind, Except.bind] at success
          exact ⟨op, arg, next, rfl, advanced, success⟩

/-- Projecting actual paired execution yields the same bounded checked native
run; it does not use a supplied native final-state observation. -/
theorem paired_native (count : Nat) (initial final : Frame)
    (success : pairedSteps count initial = .ok final) :
    CapturedMappingHelper.checkedSteps count initial.machine = .ok final.machine := by
  induction count generalizing initial with
  | zero => cases success; rfl
  | succ count ih =>
    obtain ⟨op, arg, next, decoded, advanced, rest⟩ := paired_split count initial final success
    have fetched : EVM.Proof.decodeAt initial.machine = (op, arg) := by
      simp only [EVM.Proof.decodeAt, decoded, Option.getD_some]
    have checked := advance_checked initial next op arg advanced
    simpa only [CapturedMappingHelper.checkedSteps, fetched, checked, Bind.bind, Except.bind] using ih next rest

/-- Successful local caller execution and its original hash-aware continuation
compose directly, preserving every world field throughout the suffix. -/
def execute (entryFuel suffixFuel : Nat) (initial : Frame) : Except String Outcome := do
  let ready ← NativeSourceEntryWrite.runTo (UInt256.ofNat 404) entryFuel initial.machine
  let stored ← pairedSteps 13 { initial with machine := ready }
  match ← CreationCaller.run suffixFuel stored.machine with
  | .ready final => pure (.ready { stored with machine := final })
  | .exceptional reason final => pure (.exceptional reason { stored with machine := final })

/-- A ready composition supplies the ACTUAL three stage executions. -/
theorem execute_split (entryFuel suffixFuel : Nat) (initial final : Frame)
    (success : execute entryFuel suffixFuel initial = .ok (.ready final)) :
    ∃ ready stored, NativeSourceEntryWrite.runTo (UInt256.ofNat 404) entryFuel initial.machine = .ok ready ∧
      pairedSteps 13 { initial with machine := ready } = .ok stored ∧
      CreationCaller.run suffixFuel stored.machine = .ok (.ready final.machine) ∧
      final.world = stored.world ∧ final.warm = stored.warm := by
  unfold execute at success
  cases entry : NativeSourceEntryWrite.runTo (UInt256.ofNat 404) entryFuel initial.machine with
  | error message => simp only [entry, Bind.bind, Except.bind] at success; cases success
  | ok ready =>
    simp only [entry, Bind.bind, Except.bind] at success
    cases middle : pairedSteps 13 { initial with machine := ready } with
    | error message => simp only [middle] at success; cases success
    | ok stored =>
      simp only [middle] at success
      cases suffix : CreationCaller.run suffixFuel stored.machine with
      | error message => simp only [suffix] at success; cases success
      | ok outcome =>
        cases outcome with
        | exceptional reason machine => simp only [suffix, Pure.pure, Except.pure] at success; cases success
        | ready machine =>
          simp only [suffix, Pure.pure, Except.pure] at success
          cases success
          exact ⟨ready, stored, rfl, middle, suffix, rfl, rfl⟩

/-- Every ready staged execution is the EXISTING original hash-aware caller,
with a derived fuel count and exactly the same complete ready frame. -/
theorem execute_run (entryFuel suffixFuel : Nat) (initial final : Frame)
    (success : execute entryFuel suffixFuel initial = .ok (.ready final)) :
    ∃ steps, steps < entryFuel ∧
      NativeHashedWorldCaller.run (steps + 13 + suffixFuel) initial = .ok (.ready final) := by
  obtain ⟨ready, stored, entry, middle, suffix, world, warm⟩ := execute_split entryFuel suffixFuel initial final success
  obtain ⟨steps, bound, continuation⟩ := entry_compose _ entryFuel initial.machine ready entry
  have tail := suffix_ready suffixFuel stored.machine final.machine suffix stored.world stored.warm
  have same : (⟨stored.world, final.machine, stored.warm⟩ : Frame) = final := by
    cases final
    simp only at world warm
    cases world
    cases warm
    rfl
  rw [same] at tail
  refine ⟨steps, bound, ?_⟩
  have fragment := paired_compose 13 _ stored middle suffixFuel
  have prefixRun := continuation initial.world initial.warm (13 + suffixFuel)
  rw [Nat.add_assoc] 
  exact prefixRun.trans (fragment.trans tail)

/-- Splitting paired execution derives the intermediate frame from execution. -/
theorem paired_add (left right : Nat) (initial : Frame) :
    pairedSteps (left + right) initial = (pairedSteps left initial >>= pairedSteps right) := by
  induction left generalizing initial with
  | zero => simp only [Nat.zero_add]; rfl
  | succ left ih =>
    simp only [Nat.succ_add, pairedSteps]
    cases decoded : EVM.decode initial.machine.executionEnv.code initial.machine.pc with
    | none => rfl
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      dsimp only
      cases advanced : NativeHashedWorldCaller.advance initial op arg with
      | error message => simp only [Bind.bind, Except.bind]
      | ok outcome =>
        cases outcome with
        | exceptional reason frame => simp only [Bind.bind, Except.bind]
        | continued next => simpa only [Bind.bind, Except.bind] using ih next

/-- Actual paired prefixes factor without an intermediate-world hypothesis. -/
theorem paired_add_split (left right : Nat) (initial final : Frame)
    (success : pairedSteps (left + right) initial = .ok final) :
    ∃ middle, pairedSteps left initial = .ok middle ∧ pairedSteps right middle = .ok final := by
  rw [paired_add] at success
  cases step : pairedSteps left initial with
  | error message => simp only [step, Bind.bind, Except.bind] at success; cases success
  | ok middle => exact ⟨middle, rfl, by simpa only [step, Bind.bind, Except.bind] using success⟩

/-- A successful hash-aware step exposes its actual canonical update. -/
theorem advance_world (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (success : NativeHashedWorldCaller.advance before op arg = .ok (.continued after)) :
    worldAfter before op = .ok after.world := by
  by_cases hash : op = .KECCAK256
  · subst op
    have world := (NativeHashedWorldCaller.advance_hash_checked before after arg success).2.1
    simpa [worldAfter, Pure.pure, Except.pure] using congrArg (fun w : Verity.ContractState => (Except.ok w : Except String Verity.ContractState)) world.symm
  · rw [NativeHashedWorldCaller.advance_other before op arg hash] at success
    have allowed := (NativePairedCallerExecution.advance_checked before after op arg success).1
    unfold NativeCreationWorldCaller.advance at success
    simp only [allowed, Bool.not_true, Bool.false_eq_true, ite_false,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at success
    cases step : CreationCaller.checkedStep before.machine op arg with
    | error reason => simp only [step] at success; cases success
    | ok next =>
      simp only [step] at success
      cases update : worldAfter before op with
      | error message => simp only [update] at success; cases success
      | ok world =>
        simp only [update] at success
        cases success
        rfl

end Compiler.Proofs.IRGeneration.NativePrefixComposition









