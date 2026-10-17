import Compiler.Proofs.IRGeneration.NativeCreationStorageOpcodes

/-! Native primitive frames for composing an actual local caller prefix. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationLocalFrames
open EvmYul NativeCreationWorld

theorem unary_state (op : Primop.Unary) (before after : EVM.State)
    (success : EVM.execUnOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.execUnOp at success
  split at success
  · cases success; rfl
  · cases success

theorem binary_state (op : Primop.Binary) (before after : EVM.State)
    (success : EVM.execBinOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.execBinOp at success
  split at success
  · cases success; rfl
  · cases success

theorem ternary_state (op : Primop.Ternary) (before after : EVM.State)
    (success : EVM.execTriOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.execTriOp at success
  split at success
  · cases success; rfl
  · cases success

theorem quaternary_state (op : Primop.Quaternary) (before after : EVM.State)
    (success : EVM.execQuadOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.execQuadOp at success
  split at success
  · cases success; rfl
  · cases success

theorem environment_state (op : ExecutionEnv .EVM → UInt256) (before after : EVM.State)
    (success : EVM.executionEnvOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.executionEnvOp at success
  cases success
  rfl

theorem unaryEnvironment_state (op : ExecutionEnv .EVM → UInt256 → UInt256) (before after : EVM.State)
    (success : EVM.unaryExecutionEnvOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.unaryExecutionEnvOp at success
  split at success
  · cases success; rfl
  · cases success

theorem machine_state (op : MachineState → UInt256) (before after : EVM.State)
    (success : EVM.machineStateOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.machineStateOp at success
  cases success
  rfl

theorem binaryMachine_state (op : MachineState → UInt256 → UInt256 → MachineState) (before after : EVM.State)
    (success : EVM.binaryMachineStateOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.binaryMachineStateOp at success
  split at success
  · cases success; rfl
  · cases success

theorem binaryMachineResult_state (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) (before after : EVM.State)
    (success : EVM.binaryMachineStateOp' op before = .ok after) : after.toState = before.toState := by
  unfold EVM.binaryMachineStateOp' at success
  split at success
  · cases success; rfl
  · cases success

theorem ternaryMachine_state (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) (before after : EVM.State)
    (success : EVM.ternaryMachineStateOp op before = .ok after) : after.toState = before.toState := by
  unfold EVM.ternaryMachineStateOp at success
  split at success
  · cases success; rfl
  · cases success

/-- Raw boundary agreement depends on actual State, independently of local
machine gas/memory/PC/stack/return buffers and execution counters. -/
theorem agreement_of_state_eq (world : Verity.ContractState) (before after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world before warm) (unchanged : after.toState = before.toState) :
    Agreement world after warm := by
  rcases before with ⟨⟨state, machine⟩, pc, stack, length⟩
  rcases after with ⟨⟨state', machine'⟩, pc', stack', length'⟩
  dsimp only at unchanged
  subst state'
  exact {
    caller := agrees.caller
    source := agrees.source
    origin := agrees.origin
    value := agrees.value
    accounts := agrees.accounts
    selfBalance := agrees.selfBalance
    codeSizes := agrees.codeSizes
    persistent := agrees.persistent
    transient := agrees.transient
    parkedPersistent := agrees.parkedPersistent
    parkedTransient := agrees.parkedTransient
    accountAccess := agrees.accountAccess
  }

/-- Exact native frame for the arithmetic, bitwise and standard memory/env
operations already allowed in the local caller subset. -/
theorem basic_step_state (op : Operation .EVM) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE, .SHL, .SHR, .SAR, .MSTORE, .MSTORE8, .MCOPY, .MSIZE, .GAS, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .RETURNDATASIZE])
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact unary_state _ charged after success
    | exact binary_state _ charged after success
    | exact ternary_state _ charged after success
    | exact quaternary_state _ charged after success
    | exact environment_state _ charged after success
    | exact unaryEnvironment_state _ charged after success
    | exact machine_state _ charged after success
    | exact binaryMachine_state _ charged after success
    | exact binaryMachineResult_state _ charged after success
    | exact ternaryMachine_state _ charged after success

theorem read_state (op : EvmYul.State .EVM → UInt256 → UInt256) (before after : EVM.State)
    (success : EVM.unaryStateOp (fun state value => (state, op state value)) before = .ok after) :
    after.toState = before.toState := by
  unfold EVM.unaryStateOp at success
  split at success
  · cases success; rfl
  · cases success

theorem copy_state (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    (frame : ∀ state a b c, (op state a b c).toState = state.toState)
    (before after : EVM.State) (success : EVM.ternaryCopyOp op before = .ok after) :
    after.toState = before.toState := by
  unfold EVM.ternaryCopyOp at success
  split at success
  · cases success
    exact frame _ _ _ _
  · cases success

private theorem pop_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.POP, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .POP arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; rfl
  · cases success

private theorem mload_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.MLOAD, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .MLOAD arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; rfl
  · cases success

private theorem jump_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.JUMP, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .JUMP arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; rfl
  · cases success

private theorem jumpi_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.JUMPI, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .JUMPI arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; rfl
  · cases success

private theorem jumpdest_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.JUMPDEST, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .JUMPDEST arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  cases success
  rfl

private theorem pc_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.PC, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .PC arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  cases success
  rfl

private theorem calldataload_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.CALLDATALOAD, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .CALLDATALOAD arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  exact read_state _ charged after success

private theorem calldatacopy_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.CALLDATACOPY, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .CALLDATACOPY arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  exact copy_state _ (by intros; rfl) charged after success

private theorem codecopy_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.CODECOPY, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .CODECOPY arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  exact copy_state _ (by intros; rfl) charged after success

private theorem returndatacopy_step_state (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.RETURNDATACOPY, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .RETURNDATACOPY arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; rfl
  · cases success

/-- The remaining fixed opcodes in the existing local caller subset. -/
theorem remaining_step_state (op : Operation .EVM) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.POP, .MLOAD, .JUMP, .JUMPI, .JUMPDEST, .PC,
      .CALLDATALOAD, .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY])
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
  | exact pop_step_state machine after arg gasCost success
  | exact mload_step_state machine after arg gasCost success
  | exact jump_step_state machine after arg gasCost success
  | exact jumpi_step_state machine after arg gasCost success
  | exact jumpdest_step_state machine after arg gasCost success
  | exact pc_step_state machine after arg gasCost success
  | exact calldataload_step_state machine after arg gasCost success
  | exact calldatacopy_step_state machine after arg gasCost success
  | exact codecopy_step_state machine after arg gasCost success
  | exact returndatacopy_step_state machine after arg gasCost success

theorem dup_state (n : Nat) (before after : EVM.State)
    (success : EvmYul.dup n before = .ok after) : after.toState = before.toState := by
  unfold EvmYul.dup at success
  dsimp only at success
  split at success
  · cases success; rfl
  · cases success

theorem swap_state (n : Nat) (before after : EVM.State)
    (success : EvmYul.swap n before = .ok after) : after.toState = before.toState := by
  unfold EvmYul.swap at success
  dsimp only at success
  split at success
  · cases success; rfl
  · cases success

theorem dup_step_state (kind : Operation.DOp) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.Dup kind, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  cases kind <;> exact dup_state _ charged after success

theorem swap_step_state (kind : Operation.ExOp) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.Exchange kind, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  cases kind <;> exact swap_state _ charged after success

theorem push_step_state (kind : Operation.POp) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.Push kind, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  cases kind <;> cases arg <;>
    dsimp only [EVM.step, EvmYul.step, Id.run, Bind.bind, Pure.pure, Except.bind, Except.pure] at success <;>
    cases success <;> rfl

private theorem fixed_step_state (op : Operation .EVM) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE, .SHL, .SHR, .SAR, .POP, .MLOAD, .MSTORE, .MSTORE8, .MCOPY, .JUMP, .JUMPI, .JUMPDEST, .PC, .MSIZE, .GAS, .CALLVALUE, .CALLDATALOAD, .CALLDATASIZE, .CALLDATACOPY, .CODESIZE, .CODECOPY, .RETURNDATASIZE, .RETURNDATACOPY])
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals solve
    | (refine basic_step_state _ machine after arg gasCost ?_ success; simp)
    | (refine remaining_step_state _ machine after arg gasCost ?_ success; simp)

/-- Every actual native step in the existing caller whitelist retains State. -/
theorem supported_step_state (op : Operation .EVM) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : CreationCaller.supported op = true)
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  unfold CreationCaller.supported at admitted
  simp only [Bool.or_eq_true, decide_eq_true_eq] at admitted
  rcases admitted with ((push | duplicate) | exchange) | fixed
  · cases op <;> simp only [Operation.isPush, Bool.false_eq_true] at push
    exact push_step_state _ machine after arg gasCost success
  · cases op <;> simp only [Operation.isDup, Bool.false_eq_true] at duplicate
    exact dup_step_state _ machine after arg gasCost success
  · cases op <;> simp only [Operation.isSwap, Bool.false_eq_true] at exchange
    exact swap_step_state _ machine after arg gasCost success
  · exact fixed_step_state op machine after arg gasCost fixed success

/-- Checked local execution retains the entire actual account/original/substate
world, not just sampled current storage. -/
theorem supported_checked_state (op : Operation .EVM) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat))
    (admitted : CreationCaller.supported op = true)
    (success : CreationCaller.checkedStep machine op arg = .ok after) :
    after.toState = machine.toState := by
  have step := NativeCreationStorageOpcodes.checkedStep_delegates machine after op arg success
  let expanded : EVM.State := { machine with gasAvailable :=
    (machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine op)) }
  exact supported_step_state op expanded after arg (EVM.C' expanded op) admitted step

/-- The actual bounded caller prefix preserves the whole native State on
reaching CREATE2. Fuel failure and exceptional outcomes are not successes. -/
theorem run_ready_state (fuel : Nat) (machine after : EVM.State)
    (success : CreationCaller.run fuel machine = .ok (.ready after)) :
    after.toState = machine.toState := by
  induction fuel generalizing machine with
  | zero => cases success
  | succ fuel ih =>
    cases decoded : EVM.decode machine.executionEnv.code machine.pc with
    | none => simp only [CreationCaller.run, decoded] at success; cases success
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      simp only [CreationCaller.run, decoded] at success
      by_cases creation : op = .CREATE2
      · simp only [creation, ite_true] at success
        cases success
        rfl
      · simp only [creation, ite_false] at success
        cases allowed : CreationCaller.supported op with
        | false =>
          simp only [allowed, Bool.not_false, ite_true] at success
          cases success
        | true =>
          simp only [allowed, Bool.not_true, Bool.false_eq_true, ite_false] at success
          cases executed : CreationCaller.checkedStep machine op arg with
          | error reason => simp only [executed] at success; cases success
          | ok next =>
            simp only [executed] at success
            exact (ih next success).trans (supported_checked_state op machine next arg allowed executed)

/-- Agreement is retained by the executed local caller prefix, not merely
by a supplied boundary snapshot. World-changing prefixes still need pairing. -/
theorem run_ready_agreement (world : Verity.ContractState) (fuel : Nat)
    (machine after : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world machine warm)
    (success : CreationCaller.run fuel machine = .ok (.ready after)) :
    Agreement world after warm :=
  agreement_of_state_eq world machine after warm agrees (run_ready_state fuel machine after success)

end Compiler.Proofs.IRGeneration.NativeCreationLocalFrames
