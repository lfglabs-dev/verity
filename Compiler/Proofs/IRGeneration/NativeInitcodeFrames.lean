import Compiler.Proofs.IRGeneration.NativeCreationLocalFrames

/-! Fuel-independent native local steps for constructor world-frame proofs.
Constructor fuel is distinct from execution gas. No caller whitelist changes. -/
namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul NativeCreationLocalFrames

private theorem fixed_step_fuel_0 (fuel : Nat) (op : Operation .EVM)
    (machine : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND]) :
    EVM.step (fuel + 1) gasCost (some (op, arg)) machine =
      EVM.step 1 gasCost (some (op, arg)) machine := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem fixed_step_fuel_1 (fuel : Nat) (op : Operation .EVM)
    (machine : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE]) :
    EVM.step (fuel + 1) gasCost (some (op, arg)) machine =
      EVM.step 1 gasCost (some (op, arg)) machine := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem fixed_step_fuel_2 (fuel : Nat) (op : Operation .EVM)
    (machine : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.SHL, .SHR, .SAR, .POP, .MLOAD, .MSTORE, .MSTORE8, .MCOPY, .JUMP, .JUMPI, .JUMPDEST]) :
    EVM.step (fuel + 1) gasCost (some (op, arg)) machine =
      EVM.step 1 gasCost (some (op, arg)) machine := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem fixed_step_fuel_3 (fuel : Nat) (op : Operation .EVM)
    (machine : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.PC, .MSIZE, .GAS, .CALLVALUE, .CALLDATALOAD, .CALLDATASIZE, .CALLDATACOPY, .CODESIZE, .CODECOPY, .RETURNDATASIZE, .RETURNDATACOPY]) :
    EVM.step (fuel + 1) gasCost (some (op, arg)) machine =
      EVM.step 1 gasCost (some (op, arg)) machine := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem fixed_step_fuel (fuel : Nat) (op : Operation .EVM)
    (machine : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE, .SHL, .SHR, .SAR, .POP, .MLOAD, .MSTORE, .MSTORE8, .MCOPY, .JUMP, .JUMPI, .JUMPDEST, .PC, .MSIZE, .GAS, .CALLVALUE, .CALLDATALOAD, .CALLDATASIZE, .CALLDATACOPY, .CODESIZE, .CODECOPY, .RETURNDATASIZE, .RETURNDATACOPY]) :
    EVM.step (fuel + 1) gasCost (some (op, arg)) machine =
      EVM.step 1 gasCost (some (op, arg)) machine := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals solve
    | (apply fixed_step_fuel_0; simp)
    | (apply fixed_step_fuel_1; simp)
    | (apply fixed_step_fuel_2; simp)
    | (apply fixed_step_fuel_3; simp)

/-- All supported local instructions execute the same step independently of
positive constructor fuel. Only recursive call/creation instructions use it. -/
theorem supported_step_fuel (fuel : Nat) (op : Operation .EVM)
    (machine : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : CreationCaller.supported op = true) :
    EVM.step (fuel + 1) gasCost (some (op, arg)) machine =
      EVM.step 1 gasCost (some (op, arg)) machine := by
  unfold CreationCaller.supported at admitted
  simp only [Bool.or_eq_true, decide_eq_true_eq] at admitted
  rcases admitted with ((push | duplicate) | exchange) | fixed
  · cases op <;> simp only [Operation.isPush, Bool.false_eq_true] at push
    simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]
  · cases op <;> simp only [Operation.isDup, Bool.false_eq_true] at duplicate
    simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]
  · cases op <;> simp only [Operation.isSwap, Bool.false_eq_true] at exchange
    simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]
  · exact fixed_step_fuel fuel op machine arg gasCost fixed

/-- The existing whole-native-State frame applies to any positive fuel. -/
theorem supported_step_state (fuel : Nat) (op : Operation .EVM)
    (machine after : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : CreationCaller.supported op = true)
    (success : EVM.step (fuel + 1) gasCost (some (op, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  rw [supported_step_fuel fuel op machine arg gasCost admitted] at success
  exact NativeCreationLocalFrames.supported_step_state op machine after arg gasCost admitted success

/-- RETURN changes the machine's return memory window, not the global state. -/
theorem return_step_state (fuel : Nat) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step (fuel + 1) gasCost (some (.RETURN, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure] at success
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  exact binaryMachine_state _ charged after success

/-- Zero interpreter fuel cannot supply successful local execution evidence. -/
theorem supported_step_state_any (fuel : Nat) (op : Operation .EVM)
    (machine after : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : CreationCaller.supported op = true)
    (success : EVM.step fuel gasCost (some (op, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  cases fuel with
  | zero => simp only [EVM.step] at success; cases success
  | succ fuel => exact supported_step_state fuel op machine after arg gasCost admitted success

/-- The actual native STOP is a local halt, preserving all account state. -/
theorem stop_step_state (fuel : Nat) (machine after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step (fuel + 1) gasCost (some (.STOP, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure] at success
  change Except.ok _ = Except.ok after at success
  cases success
  rfl

/-- Local constructor operations include the halting RETURN and STOP, without
changing the caller interpreter's admission whitelist. -/
def localOperation (op : Operation .EVM) : Bool :=
  CreationCaller.supported op || op = .RETURN || op = .STOP

/-- An actual successful local/return/stop step preserves the entire native
State, for any fuel, gas cost, operands, memory, and account/original map. -/
theorem local_step_state (fuel : Nat) (op : Operation .EVM)
    (machine after : EVM.State) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : localOperation op = true)
    (success : EVM.step fuel gasCost (some (op, arg)) machine = .ok after) :
    after.toState = machine.toState := by
  cases fuel with
  | zero => simp only [EVM.step] at success; cases success
  | succ fuel =>
    by_cases returning : op = .RETURN
    · subst op
      exact return_step_state fuel machine after arg gasCost success
    · by_cases stopped : op = .STOP
      · subst op
        exact stop_step_state fuel machine after arg gasCost success
      · have allowed : CreationCaller.supported op = true := by
          simpa [localOperation, returning, stopped] using admitted
        exact supported_step_state fuel op machine after arg gasCost allowed success

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames
