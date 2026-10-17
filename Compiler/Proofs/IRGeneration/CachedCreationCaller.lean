import Compiler.Proofs.IRGeneration.NativeHashedWorldCaller

/-! Reuse an authenticated byte-decoded jump table. All stack/gas/static/jump
checks and the entire native outcome remain unchanged. This is not a runner. -/
namespace Compiler.Proofs.IRGeneration.CachedCaller
open EvmYul CreationCaller

def checkedStep (jumps : Array UInt256) (state : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) : Except EVM.ExecutionException EVM.State := do
  if EVM.δ op = none then throw .InvalidInstruction
  if state.stack.length < (EVM.δ op).getD 0 then throw .StackUnderflow
  if state.stack.length - (EVM.δ op).getD 0 + (EVM.α op).getD 0 > 1024 then
    throw .StackOverflow
  let invalidJump := !(jumps).contains (state.stack.getD 0 (.ofNat 0))
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

/-- A caller must prove the cached table is exactly the native byte decoder's
result for this frame's actual code; an arbitrary table is not accepted. -/
theorem checkedStep_eq (jumps : Array UInt256) (state : EVM.State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (computed : jumps = CreationCaller.jumpDestinations state.executionEnv.code) :
    checkedStep jumps state op arg = CreationCaller.checkedStep state op arg := by
  subst jumps
  rfl

end Compiler.Proofs.IRGeneration.CachedCaller

namespace Compiler.Proofs.IRGeneration.CachedCaller
open EvmYul NativeCreationWorldCaller

structure Cache where
  code : ByteArray
  jumps : Array UInt256
  computed : jumps = CreationCaller.jumpDestinations code

def Cache.make (code : ByteArray) : Cache :=
  ⟨code, CreationCaller.jumpDestinations code, rfl⟩

/-- Recompute if code actually changes; reuse only with exact byte equality. -/
def Cache.choose (cache : Cache) (code : ByteArray) : { next : Cache // next.code = code } :=
  if same : cache.code = code then ⟨cache, same⟩ else ⟨Cache.make code, rfl⟩

/-- Full checked native step, with a proof tying the cached decoder to this frame. -/
def advance (cache : Cache) (before : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (_same : cache.code = before.machine.executionEnv.code) :
    Except String StepOutcome := do
  if op = .KECCAK256 then
    match checkedStep cache.jumps before.machine op arg with
    | .error reason => pure (.exceptional reason
        { before with machine := CreationCaller.exhausted before.machine })
    | .ok next => pure (.continued { before with machine := next })
  else
    if !(CreationCaller.supported op || op = .SSTORE || op = .TSTORE) then
      throw s!"unsupported world caller instruction at bytecode pc {before.machine.pc.toNat}"
    match checkedStep cache.jumps before.machine op arg with
    | .error reason => pure (.exceptional reason
        { before with machine := CreationCaller.exhausted before.machine })
    | .ok next =>
      let world ← worldAfter before op
      pure (.continued { before with world := world, machine := next })

theorem advance_eq (cache : Cache) (before : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (same : cache.code = before.machine.executionEnv.code) :
    advance cache before op arg same = NativeHashedWorldCaller.advance before op arg := by
  have table : cache.jumps = CreationCaller.jumpDestinations before.machine.executionEnv.code :=
    cache.computed.trans (congrArg CreationCaller.jumpDestinations same)
  simp only [advance, NativeHashedWorldCaller.advance, NativeCreationWorldCaller.advance,
    checkedStep_eq cache.jumps before.machine op arg table]
  rfl

/-- Fuel and all errors/outcomes are identical to the original hashed caller. -/
def run : Nat → Cache → Frame → Except String Outcome
  | 0, _, before => .error s!"hashed caller fuel exhausted at bytecode pc {before.machine.pc.toNat}"
  | fuel + 1, cache, before =>
    match EVM.decode before.machine.executionEnv.code before.machine.pc with
    | none => .error s!"unsupported hashed caller opcode at bytecode pc {before.machine.pc.toNat}"
    | some (op, arg) =>
      if op = .CREATE2 then .ok (.ready before)
      else do
        let chosen := cache.choose before.machine.executionEnv.code
        match ← advance chosen.val before op arg chosen.property with
        | .continued next => run fuel chosen.val next
        | .exceptional reason frame => pure (.exceptional reason frame)

theorem run_eq (fuel : Nat) (cache : Cache) (before : Frame) :
    run fuel cache before = NativeHashedWorldCaller.run fuel before := by
  induction fuel generalizing cache before with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, NativeHashedWorldCaller.run]
    cases decoded : EVM.decode before.machine.executionEnv.code before.machine.pc with
    | none => rfl
    | some instruction =>
      rcases instruction with ⟨op, arg⟩
      by_cases creation : op = .CREATE2
      · simp only [creation, if_true]
      · simp only [creation, if_false, advance_eq]
        cases advanced : NativeHashedWorldCaller.advance before op arg with
        | error message => rfl
        | ok outcome =>
          cases outcome with
          | exceptional reason frame => rfl
          | continued next => exact ih _ next

end Compiler.Proofs.IRGeneration.CachedCaller
