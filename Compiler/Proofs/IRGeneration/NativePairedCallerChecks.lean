import Compiler.Proofs.IRGeneration.NativePairedCallerFuel

namespace Compiler.Proofs.IRGeneration.NativePairedCallerChecks
open EvmYul EVM.Proof

/-- Each actual guard of the paired noncreation checked step, before reordering. -/
structure CheckedGuards (pre : EVM.State) (op : Operation .EVM) : Prop where
  valid : ¬ EVM.δ op = none
  stack : ¬ pre.stack.length < (EVM.δ op).getD 0
  limit : ¬ pre.stack.length - (EVM.δ op).getD 0 + (EVM.α op).getD 0 > 1024
  jump : ¬ (op = .JUMP && !(CreationCaller.jumpDestinations pre.executionEnv.code).contains
    (pre.stack.getD 0 (UInt256.ofNat 0))) = true
  jumpi : ¬ (op = .JUMPI && pre.stack.getD 1 (UInt256.ofNat 0) != UInt256.ofNat 0 &&
    !(CreationCaller.jumpDestinations pre.executionEnv.code).contains (pre.stack.getD 0 (UInt256.ofNat 0))) = true
  copy : ¬ (op = .RETURNDATACOPY &&
    (pre.stack.getD 1 (UInt256.ofNat 0)).toNat + (pre.stack.getD 2 (UInt256.ofNat 0)).toNat > pre.returnData.size) = true
  memory : ¬ pre.gasAvailable.toNat < EVM.memoryExpansionCost pre op
  instruction : let mid := zMid pre op
    ¬ mid.gasAvailable.toNat < EVM.C' mid op
  staticMode : ¬ (!pre.executionEnv.perm && decide (op ∈ [.SSTORE, .TSTORE, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4])) = true
  stipend : let mid := zMid pre op
    ¬ (op = .SSTORE && mid.gasAvailable.toNat ≤ GasConstants.Gcallstipend) = true

private theorem success_guard (condition : Prop) [Decidable condition]
    (reason : EVM.ExecutionException) (tail : Except EVM.ExecutionException EVM.State) (next : EVM.State)
    (success : (if condition then .error reason else tail) = .ok next) :
    ¬ condition ∧ tail = .ok next := by
  by_cases guard : condition
  · rw [if_pos guard] at success
    cases success
  · exact ⟨guard, by simpa only [if_neg guard] using success⟩

/-- Successful checked execution entails every real initial check separately. -/
theorem checked_guards (pre next : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (success : CreationCaller.checkedStep pre op arg = .ok next) : CheckedGuards pre op := by
  unfold CreationCaller.checkedStep at success
  dsimp only [Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw, Except.bind, Except.pure] at success
  obtain ⟨valid, success⟩ := success_guard _ _ _ _ success
  obtain ⟨stack, success⟩ := success_guard _ _ _ _ success
  obtain ⟨limit, success⟩ := success_guard _ _ _ _ success
  obtain ⟨jump, success⟩ := success_guard _ _ _ _ success
  obtain ⟨jumpi, success⟩ := success_guard _ _ _ _ success
  obtain ⟨copy, success⟩ := success_guard _ _ _ _ success
  obtain ⟨memory, success⟩ := success_guard _ _ _ _ success
  obtain ⟨instruction, success⟩ := success_guard _ _ _ _ success
  obtain ⟨staticMode, success⟩ := success_guard _ _ _ _ success
  obtain ⟨stipend, success⟩ := success_guard _ _ _ _ success
  exact ⟨valid, stack, limit, jump, jumpi, copy, memory, instruction, staticMode, stipend⟩

/-- The native optional lookup and checked default lookup agree on a present head. -/
theorem jump_lookup (stack : Stack UInt256) (destinations : Array UInt256)
    (present : 0 < stack.length) :
    EVM.X.notIn stack[0]? destinations =
      !(destinations.contains (stack.getD 0 (UInt256.ofNat 0))) := by
  cases stack with
  | nil => simp at present
  | cons head tail => rfl

/-- Use the actual native scanner, with its proved code-size bound. -/
theorem jump_lookup_scanners (pre : EVM.State)
    (bounded : pre.executionEnv.code.size < UInt256.size)
    (present : 0 < pre.stack.length) :
    EVM.X.notIn pre.stack[0]? (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) =
      !((CreationCaller.jumpDestinations pre.executionEnv.code).contains
        (pre.stack.getD 0 (UInt256.ofNat 0))) := by
  rw [← NativePairedCallerFuel.jump_scanners pre.executionEnv.code bounded]
  exact jump_lookup pre.stack _ present

/-- A successful checked JUMP cannot fail the actual native destination guard. -/
theorem checked_jump (pre next : EVM.State) (arg : Option (UInt256 × Nat))
    (bounded : pre.executionEnv.code.size < UInt256.size)
    (success : CreationCaller.checkedStep pre .JUMP arg = .ok next) :
    ¬ EVM.X.notIn pre.stack[0]? (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) = true := by
  have guards := checked_guards pre next .JUMP arg success
  have present : 0 < pre.stack.length := by
    have stack := guards.stack
    simp only [EVM.δ, Option.getD] at stack
    omega
  rw [jump_lookup_scanners pre bounded present]
  simpa only [Bool.true_and, decide_true] using guards.jump

/-- A successful JUMPI supplies both words before translating its conditional guard. -/
theorem checked_jumpi (pre next : EVM.State) (arg : Option (UInt256 × Nat))
    (bounded : pre.executionEnv.code.size < UInt256.size)
    (success : CreationCaller.checkedStep pre .JUMPI arg = .ok next) :
    ¬ (pre.stack[1]? ≠ some (UInt256.ofNat 0) ∧
      EVM.X.notIn pre.stack[0]? (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) = true) := by
  have guards := checked_guards pre next .JUMPI arg success
  have present : 1 < pre.stack.length := by
    have stack := guards.stack
    simp only [EVM.δ, Option.getD] at stack
    omega
  rw [jump_lookup_scanners pre bounded (by omega)]
  have denied := guards.jumpi
  cases stackEq : pre.stack with
  | nil => simp [stackEq] at present
  | cons head tail =>
    cases tail with
    | nil => simp [stackEq] at present
    | cons condition rest =>
      by_cases zero : condition = UInt256.ofNat 0
      · simp [zero]
      · have different : (condition != UInt256.ofNat 0) = true := by
          change (!(condition.val == (UInt256.ofNat 0).val)) = true
          have unequal : condition.val ≠ (UInt256.ofNat 0).val :=
            fun equal => zero (congrArg UInt256.mk equal)
          simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using unequal
        simpa [stackEq, different, zero] using denied

/-- The paired whitelist excludes creation, external calls and destructive/log effects. -/
theorem paired_excludes (op : Operation .EVM)
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true) :
    op ∉ [.CREATE, .CREATE2, .CALL, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4] := by
  intro forbidden
  simp only [List.mem_cons, List.not_mem_nil, or_false] at forbidden
  rcases forbidden with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [CreationCaller.supported, Operation.isPush, Operation.isDup, Operation.isSwap] at admitted

/-- For the full paired whitelist, native W is precisely the storage-write predicate. -/
theorem paired_static (op : Operation .EVM) (stack : Stack UInt256)
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true) :
    W op stack = decide (op ∈ [.SSTORE, .TSTORE, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4]) := by
  have excluded := paired_excludes op admitted
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at excluded
  simp [W, excluded.1, excluded.2.1, excluded.2.2.1, excluded.2.2.2.1,
    excluded.2.2.2.2.1, excluded.2.2.2.2.2.1, excluded.2.2.2.2.2.2.1,
    excluded.2.2.2.2.2.2.2.1, excluded.2.2.2.2.2.2.2.2]

/-- Admitted paired-prefix instructions never take the native initcode-size branch. -/
theorem paired_not_create (op : Operation .EVM)
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true) :
    op.isCreate = false := by
  have excluded := paired_excludes op admitted
  have first : op ≠ .CREATE := fun equal => excluded (by simp [equal])
  have second : op ≠ .CREATE2 := fun equal => excluded (by simp [equal])
  cases op <;> simp_all [Operation.isCreate]

/-- Reordering successful checks retains every native Z guard and the exact gas debit. -/
theorem checked_native_z (pre next : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (bounded : pre.executionEnv.code.size < UInt256.size)
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true)
    (success : CreationCaller.checkedStep pre op arg = .ok next) :
    Z (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) op pre =
      .ok (zMid pre op, EVM.C' (zMid pre op) op) := by
  have guards := checked_guards pre next op arg success
  have jump : ¬ (op = .JUMP ∧ EVM.X.notIn pre.stack[0]?
      (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) = true) := by
    rintro ⟨rfl, bad⟩
    exact checked_jump pre next arg bounded success bad
  have jumpi : ¬ (op = .JUMPI ∧ pre.stack[1]? ≠ some (UInt256.ofNat 0) ∧
      EVM.X.notIn pre.stack[0]? (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) = true) := by
    rintro ⟨rfl, bad⟩
    exact checked_jumpi pre next arg bounded success bad
  have copy := guards.copy
  have staticMode := guards.staticMode
  have stipend := guards.stipend
  simp only [Bool.and_eq_true, decide_eq_true_eq] at copy stipend
  have staticEq := paired_static op pre.stack admitted
  rw [← staticEq] at staticMode
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at staticMode
  have instruction := guards.instruction
  dsimp only [zMid] at instruction stipend
  have zeroEq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
  simp only [zeroEq] at jump jumpi copy
  simp only [Z, zeroEq, guards.memory, if_false, instruction, guards.valid, guards.stack,
    guards.limit, jump, jumpi, copy, stipend, staticMode, paired_not_create op admitted,
    Bool.false_eq_true, false_and, if_false, Pure.pure, Except.pure,
    Bind.bind, Except.bind]
  rfl

/-- None of the paired-prefix instructions terminates the native frame. -/
theorem paired_nonhalting (op : Operation .EVM) (machine : MachineState)
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true) :
    H machine op = none := by
  have excluded : op ∉ [.RETURN, .REVERT, .STOP, .SELFDESTRUCT] := by
    intro forbidden
    simp only [List.mem_cons, List.not_mem_nil, or_false] at forbidden
    rcases forbidden with rfl | rfl | rfl | rfl
    all_goals simp [CreationCaller.supported, Operation.isPush, Operation.isDup, Operation.isSwap] at admitted
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at excluded
  simp [H, excluded.1, excluded.2.1, excluded.2.2.1, excluded.2.2.2]

/-- The actual native iterator continues through the same successful paired step. -/
theorem checked_native_x (fuel : Nat) (pre next : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (bounded : pre.executionEnv.code.size < UInt256.size)
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true)
    (decoded : decodeAt pre = (op, arg))
    (success : CreationCaller.checkedStep pre op arg = .ok next) :
    EVM.X (fuel + 2) (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J pre.executionEnv.code (UInt256.ofNat 0)) next := by
  apply X_succ_of_continue decoded (checked_native_z pre next op arg bounded admitted success)
  · exact NativePairedCallerFuel.paired_checked_step fuel op pre next arg admitted success
  · exact paired_nonhalting op next.toMachineState admitted

end Compiler.Proofs.IRGeneration.NativePairedCallerChecks
