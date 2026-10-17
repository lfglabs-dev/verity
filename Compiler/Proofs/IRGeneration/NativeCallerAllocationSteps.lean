import Compiler.Proofs.IRGeneration.NativeCallerAllocationBounds
import Compiler.Proofs.IRGeneration.NativeCreationLocalFrames

namespace Compiler.Proofs.IRGeneration.NativeCallerAllocationSteps
open EvmYul NativeMidnightConstructor

private theorem unary_allocation (op : Primop.Unary) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.execUnOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.execUnOp at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem binary_allocation (op : Primop.Binary) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.execBinOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.execBinOp at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem ternary_allocation (op : Primop.Ternary) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.execTriOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.execTriOp at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem quaternary_allocation (op : Primop.Quaternary) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.execQuadOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.execQuadOp at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem environment_allocation (op : ExecutionEnv .EVM → UInt256) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.executionEnvOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.executionEnvOp at success
  cases success
  exact allocated

private theorem unaryEnvironment_allocation (op : ExecutionEnv .EVM → UInt256 → UInt256) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.unaryExecutionEnvOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.unaryExecutionEnvOp at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem machine_allocation (op : MachineState → UInt256) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.machineStateOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.machineStateOp at success
  cases success
  exact allocated

private theorem binaryMachine_allocation
    (op : MachineState → UInt256 → UInt256 → MachineState)
    (frame : ∀ state a b, state.memory.size ≤ state.activeWords.toNat * 32 →
      (op state a b).memory.size ≤ (op state a b).activeWords.toNat * 32)
    (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.binaryMachineStateOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.binaryMachineStateOp at success
  split at success
  · cases success; exact frame _ _ _ allocated
  · cases success

private theorem ternaryMachine_allocation
    (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState)
    (frame : ∀ state a b c, state.memory.size ≤ state.activeWords.toNat * 32 →
      (op state a b c).memory.size ≤ (op state a b c).activeWords.toNat * 32)
    (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.ternaryMachineStateOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.ternaryMachineStateOp at success
  split at success
  · cases success; exact frame _ _ _ _ allocated
  · cases success

private theorem copy_allocation
    (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    (frame : ∀ state a b c, state.memory.size ≤ state.activeWords.toNat * 32 →
      (op state a b c).memory.size ≤ (op state a b c).activeWords.toNat * 32)
    (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.ternaryCopyOp op before = .ok after) : CallerAllocated after := by
  unfold EVM.ternaryCopyOp at success
  split at success
  · cases success; exact frame _ _ _ _ allocated
  · cases success

/-- Exact native frame for the arithmetic, bitwise and standard memory/env
operations already allowed in the local caller subset. -/
private theorem basic_step_allocation (op : Operation .EVM) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE, .SHL, .SHR, .SAR, .MSTORE, .MSTORE8, .MCOPY, .MSIZE, .GAS, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .RETURNDATASIZE])
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact unary_allocation _ charged after allocated success
    | exact binary_allocation _ charged after allocated success
    | exact ternary_allocation _ charged after allocated success
    | exact quaternary_allocation _ charged after allocated success
    | exact environment_allocation _ charged after allocated success
    | exact unaryEnvironment_allocation _ charged after allocated success
    | exact machine_allocation _ charged after allocated success
    | exact binaryMachine_allocation _ (fun state a b h => caller_mstore_allocated state h a b) charged after allocated success
    | exact binaryMachine_allocation _ (fun state a b h => caller_mstore8_allocated state h a b) charged after allocated success
    | exact ternaryMachine_allocation _ (fun state a b c h => caller_mcopy_allocated state h a b c) charged after allocated success

private theorem read_allocation (op : EvmYul.State .EVM → UInt256 → UInt256) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EVM.unaryStateOp (fun state value => (state, op state value)) before = .ok after) :
    CallerAllocated after := by
  unfold EVM.unaryStateOp at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem pop_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.POP, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .POP arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem mload_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.MLOAD, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .MLOAD arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; exact caller_mload_allocated charged.toMachineState allocated _
  · cases success

private theorem jump_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.JUMP, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .JUMP arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem jumpi_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.JUMPI, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .JUMPI arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem jumpdest_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.JUMPDEST, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .JUMPDEST arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  cases success
  exact allocated

private theorem pc_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.PC, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .PC arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  cases success
  exact allocated

private theorem calldataload_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.CALLDATALOAD, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .CALLDATALOAD arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  exact read_allocation _ charged after allocated success

private theorem calldatacopy_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.CALLDATACOPY, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .CALLDATACOPY arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  exact copy_allocation _ (fun state a b c h => caller_calldatacopy_allocated state h a b c) charged after allocated success

private theorem codecopy_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.CODECOPY, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .CODECOPY arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  exact copy_allocation _ (fun state a b c h => caller_codecopy_allocated state h a b c) charged after allocated success

private theorem returndatacopy_step_allocation (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.RETURNDATACOPY, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  change EvmYul.step (τ := .EVM) .RETURNDATACOPY arg charged = Except.ok after at success
  unfold EvmYul.step at success
  dsimp only [Id.run] at success
  split at success
  · cases success; exact caller_returndatacopy_allocated charged.toMachineState allocated _ _ _
  · cases success

/-- The remaining fixed opcodes in the existing local caller subset. -/
private theorem remaining_step_allocation (op : Operation .EVM) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.POP, .MLOAD, .JUMP, .JUMPI, .JUMPDEST, .PC,
      .CALLDATALOAD, .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY])
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    CallerAllocated after := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
  | exact pop_step_allocation machine after allocated arg gasCost success
  | exact mload_step_allocation machine after allocated arg gasCost success
  | exact jump_step_allocation machine after allocated arg gasCost success
  | exact jumpi_step_allocation machine after allocated arg gasCost success
  | exact jumpdest_step_allocation machine after allocated arg gasCost success
  | exact pc_step_allocation machine after allocated arg gasCost success
  | exact calldataload_step_allocation machine after allocated arg gasCost success
  | exact calldatacopy_step_allocation machine after allocated arg gasCost success
  | exact codecopy_step_allocation machine after allocated arg gasCost success
  | exact returndatacopy_step_allocation machine after allocated arg gasCost success

private theorem dup_allocation (n : Nat) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EvmYul.dup n before = .ok after) : CallerAllocated after := by
  unfold EvmYul.dup at success
  dsimp only at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem swap_allocation (n : Nat) (before after : EVM.State) (allocated : CallerAllocated before)
    (success : EvmYul.swap n before = .ok after) : CallerAllocated after := by
  unfold EvmYul.swap at success
  dsimp only at success
  split at success
  · cases success; exact allocated
  · cases success

private theorem dup_step_allocation (kind : Operation.DOp) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.Dup kind, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  cases kind <;> exact dup_allocation _ charged after allocated success

private theorem swap_step_allocation (kind : Operation.ExOp) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.Exchange kind, arg)) machine = .ok after) :
    CallerAllocated after := by
  let charged := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost
    execLength := machine.execLength + 1 }
  cases kind <;> exact swap_allocation _ charged after allocated success

private theorem push_step_allocation (kind : Operation.POp) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.Push kind, arg)) machine = .ok after) :
    CallerAllocated after := by
  cases kind <;> cases arg <;>
    dsimp only [EVM.step, EvmYul.step, Id.run, Bind.bind, Pure.pure, Except.bind, Except.pure] at success <;>
    cases success <;> exact allocated

private theorem fixed_step_allocation (op : Operation .EVM) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : op ∈ [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP, .SIGNEXTEND, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT, .BYTE, .SHL, .SHR, .SAR, .POP, .MLOAD, .MSTORE, .MSTORE8, .MCOPY, .JUMP, .JUMPI, .JUMPDEST, .PC, .MSIZE, .GAS, .CALLVALUE, .CALLDATALOAD, .CALLDATASIZE, .CALLDATACOPY, .CODESIZE, .CODECOPY, .RETURNDATASIZE, .RETURNDATACOPY])
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    CallerAllocated after := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals solve
    | (refine basic_step_allocation _ machine after allocated arg gasCost ?_ success; simp)
    | (refine remaining_step_allocation _ machine after allocated arg gasCost ?_ success; simp)

/-- Every actual native step in the existing caller whitelist preserves allocation. -/
theorem supported_step_allocation (op : Operation .EVM) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (admitted : CreationCaller.supported op = true)
    (success : EVM.step 1 gasCost (some (op, arg)) machine = .ok after) :
    CallerAllocated after := by
  unfold CreationCaller.supported at admitted
  simp only [Bool.or_eq_true, decide_eq_true_eq] at admitted
  rcases admitted with ((push | duplicate) | exchange) | fixed
  · cases op <;> simp only [Operation.isPush, Bool.false_eq_true] at push
    exact push_step_allocation _ machine after allocated arg gasCost success
  · cases op <;> simp only [Operation.isDup, Bool.false_eq_true] at duplicate
    exact dup_step_allocation _ machine after allocated arg gasCost success
  · cases op <;> simp only [Operation.isSwap, Bool.false_eq_true] at exchange
    exact swap_step_allocation _ machine after allocated arg gasCost success
  · exact fixed_step_allocation op machine after allocated arg gasCost fixed success

/-- The actual checked step preserves the memory allocation invariant. -/
theorem supported_checked_allocation (op : Operation .EVM) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (arg : Option (UInt256 × Nat))
    (admitted : CreationCaller.supported op = true)
    (success : CreationCaller.checkedStep machine op arg = .ok after) :
    CallerAllocated after := by
  have step := NativeCreationStorageOpcodes.checkedStep_delegates machine after op arg success
  let expanded : EVM.State := { machine with gasAvailable :=
    (machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine op)) }
  exact supported_step_allocation op expanded after allocated arg (EVM.C' expanded op) admitted step

/-- The actual bounded caller prefix preserves allocation on
reaching CREATE2. Fuel failure and exceptional outcomes are not successes. -/
theorem run_ready_allocation (fuel : Nat) (machine after : EVM.State) (allocated : CallerAllocated machine)
    (success : CreationCaller.run fuel machine = .ok (.ready after)) :
    CallerAllocated after := by
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
        exact allocated
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
            exact ih next (supported_checked_allocation op machine next allocated arg allowed executed) success


/-- The actual executed caller prefix supplies the allocation obligation needed
by the physical CREATE2 slice bridge; no boundary allocation certificate is supplied. -/
theorem run_ready_physical_slice (world : Verity.ContractState) (fuel : Nat)
    (machine after : EVM.State) (allocated : CallerAllocated machine)
    (success : CreationCaller.run fuel machine = .ok (.ready after))
    (offset size : Nat) (bounded : size ≤ 49152) :
    Verity.Core.Model.Create2.physicalInitcodeBytes
      (world.installPhysicalMemory (CreationBytecode.callerMemory after)) offset size =
      after.memory.readWithPadding offset size :=
  caller_physical_slice world after (run_ready_allocation fuel machine after allocated success) offset size bounded

end Compiler.Proofs.IRGeneration.NativeCallerAllocationSteps
