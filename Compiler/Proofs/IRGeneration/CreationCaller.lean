import EvmYul.EVM.Semantics
import Verity.Core.Model.ExecutionContext

/-! Bounded bytecode caller execution up to CREATE2. This uses the pinned
EVMYulLean instruction and gas semantics, not a gas budget projected through
unmetered source statements. Calibration against the target EVM is required
before connecting it to importer admission. All initial machine/environment
fields are supplied by the caller; no fabricated initial gas or account map. -/
namespace Compiler.Proofs.IRGeneration.CreationCaller
open EvmYul

/-- Bytecode jump destinations, skipping PUSH immediate data. The bounded
scanner uses code length fuel; each step advances by at least one byte. -/
def jumpDestinationsAux (code : ByteArray) : Nat → Nat → Array UInt256 → Array UInt256
  | 0, _, found => found
  | remaining + 1, pc, found =>
      if pc ≥ code.size then found else
      match EVM.decode code (.ofNat pc) with
      | none => jumpDestinationsAux code remaining (pc + 1) found
      | some (op, _) => jumpDestinationsAux code remaining
          (pc + 1 + EVM.argOnNBytesOfInstr op)
          (if op = .JUMPDEST then found.push (.ofNat pc) else found)

def jumpDestinations (code : ByteArray) : Array UInt256 :=
  jumpDestinationsAux code code.size 0 #[]

/-- Local stack/memory/control and calldata operations needed by caller
preparation. Calls, storage, logs, block observations and halting instructions
are not delegated to an uncalibrated world/environment projection. -/
def supported (op : Operation .EVM) : Bool :=
  op.isPush || op.isDup || op.isSwap || decide (op ∈
    [.ADD, .MUL, .SUB, .DIV, .SDIV, .MOD, .SMOD, .ADDMOD, .MULMOD, .EXP,
     .SIGNEXTEND, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .NOT,
     .BYTE, .SHL, .SHR, .SAR, .POP, .MLOAD, .MSTORE, .MSTORE8, .MCOPY,
     .JUMP, .JUMPI, .JUMPDEST, .PC, .MSIZE, .GAS, .CALLVALUE, .CALLDATALOAD,
     .CALLDATASIZE, .CALLDATACOPY, .CODESIZE, .CODECOPY, .RETURNDATASIZE,
     .RETURNDATACOPY])

inductive Outcome where
  | ready (state : EVM.State)
  | exceptional (reason : EVM.ExecutionException) (state : EVM.State)

/-- Exceptional caller entry consumes all its remaining gas. The global-world
rollback belongs to the surrounding transaction/frame executor. -/
def exhausted (state : EVM.State) : EVM.State :=
  { state with gasAvailable := .ofNat 0 }

/-- Checked non-creation step, matching the corresponding prechecks of EVM.X.
Stack arity is checked before gas functions access stack entries. -/
def checkedStep (state : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) : Except EVM.ExecutionException EVM.State := do
  if EVM.δ op = none then throw .InvalidInstruction
  if state.stack.length < (EVM.δ op).getD 0 then throw .StackUnderflow
  if state.stack.length - (EVM.δ op).getD 0 + (EVM.α op).getD 0 > 1024 then
    throw .StackOverflow
  let invalidJump := !(jumpDestinations state.executionEnv.code).contains (state.stack.getD 0 (.ofNat 0))
  if op = .JUMP && invalidJump then throw .BadJumpDestination
  if op = .JUMPI && state.stack.getD 1 (.ofNat 0) != .ofNat 0 && invalidJump then
    throw .BadJumpDestination
  if op = .RETURNDATACOPY &&
      (state.stack.getD 1 (.ofNat 0)).toNat + (state.stack.getD 2 (.ofNat 0)).toNat > state.returnData.size then
    throw .InvalidMemoryAccess
  let memoryGas := EVM.memoryExpansionCost state op
  if state.gasAvailable.toNat < memoryGas then throw .OutOfGass
  let expanded := { state with gasAvailable := state.gasAvailable - UInt256.ofNat memoryGas }
  let instructionGas := EVM.C' expanded op
  if expanded.gasAvailable.toNat < instructionGas then throw .OutOfGass
  -- These checks belong to EVM.X, not EVM.step. Storage/log instructions
  -- remain refused by run until world preservation is connected.
  if !expanded.executionEnv.perm && decide (op ∈
      [.SSTORE, .TSTORE, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4]) then
    throw .StaticModeViolation
  if op = .SSTORE && expanded.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    throw .OutOfGass
  EVM.step 1 instructionGas (some (op, arg)) expanded

/-- Fuel is an interpreter bound, never an EVM revert. Ready means the CREATE2
instruction has not run or charged gas yet. Its arity/gas/static/nonce checks
remain the creation operation's responsibility. -/
def run : Nat → EVM.State → Except String Outcome
  | 0, state => .error s!"caller execution fuel exhausted at bytecode pc {state.pc.toNat}"
  | remaining + 1, state =>
      match EVM.decode state.executionEnv.code state.pc with
      | none => .error s!"unsupported caller opcode at bytecode pc {state.pc.toNat}"
      | some (op, arg) =>
          if op = .CREATE2 then .ok (.ready state)
          else if !supported op then
            .error s!"unsupported caller instruction at bytecode pc {state.pc.toNat}"
          else match checkedStep state op arg with
          | .error reason => .ok (.exceptional reason (exhausted state))
          | .ok next => run remaining next

/-- Actual caller gas/depth/static context read from the executed machine.
The warm set is not fabricated; it must be supplied by the canonical account
access projection, whose agreement is still a separate integration duty. -/
def context (state : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts) :
    Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := state.gasAvailable.toNat, depth := state.executionEnv.depth,
                isStatic := !state.executionEnv.perm }, warm := warm }

/-- Physical active-memory observation. EVMYulLean stores only materialized
bytes; the active zero suffix is an observable part of memory, not absent data. -/
def physicalBytes (state : EVM.State) : ByteArray :=
  ⟨Array.ofFn (fun i : Fin (state.activeWords.toNat * 32) => state.memory.data[i.val]?.getD 0)⟩

theorem physicalBytes_size (state : EVM.State) :
    (physicalBytes state).size = state.activeWords.toNat * 32 := by
  simp only [physicalBytes, ByteArray.size, Array.size_ofFn]

theorem exhausted_gas (state : EVM.State) : (exhausted state).gasAvailable = UInt256.ofNat 0 := rfl

theorem context_gas (state : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts) :
    (context state warm).opcode.gas = state.gasAvailable.toNat := rfl

theorem context_depth (state : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts) :
    (context state warm).opcode.depth = state.executionEnv.depth := rfl

theorem context_static (state : EVM.State) (warm : Verity.Core.Model.Create2Access.WarmAccounts) :
    (context state warm).opcode.isStatic = !state.executionEnv.perm := rfl

theorem run_fuel_zero (state : EVM.State) : run 0 state =
    .error s!"caller execution fuel exhausted at bytecode pc {state.pc.toNat}" := rfl

theorem run_ready (remaining : Nat) (state : EVM.State) (arg : Option (UInt256 × Nat))
    (decoded : EVM.decode state.executionEnv.code state.pc = some (.CREATE2, arg)) :
    run (remaining + 1) state = .ok (.ready state) := by
  simp only [run, decoded, ite_true]

end Compiler.Proofs.IRGeneration.CreationCaller
