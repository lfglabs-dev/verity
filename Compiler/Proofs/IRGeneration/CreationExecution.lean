import Compiler.Proofs.IRGeneration.CreationBytecode

/-! Complete bounded execution of the calibrated local caller/CREATE2 subset.
This bytecode companion does not replace Source/IR/Yul lowering or prove their
agreement. Unknown opcodes and interpreter fuel exhaustion are precise errors,
not simulated EVM reverts. -/
namespace Compiler.Proofs.IRGeneration.CreationExecution
open EvmYul
open CreationBytecode

inductive Outcome where
  | succeeded (output : ByteArray) (frame : Frame)
  | reverted (output : ByteArray) (frame : Frame)
  | exceptional (frame : Frame)

/-- Synchronize executed physical memory; all other canonical world fields are
retained from actual computed creation. -/
def synchronize (before : Frame) (machine : EVM.State) : Frame :=
  { before with world := before.world.installPhysicalMemory (callerMemory machine), machine := machine }

/-- Terminal caller rollback restores its canonical world and warm snapshot.
Gas and terminal local-machine observations remain current. This terminal result
must not be reused as a resumed caller frame with mismatching snapshot memory. -/
def rollback (snapshot current : Frame) : Frame :=
  { current with world := snapshot.world, warm := snapshot.warm }

def fail (snapshot current : Frame) : Outcome :=
  .exceptional (rollback snapshot { current with machine := CreationCaller.exhausted current.machine })

/-- One shared instruction bound covers the prefix, creation and continuation.
Every nonhalting step consumes exactly one unit, including CREATE2. -/
def runSteps (snapshot : Frame) : Nat → Frame → Except String Outcome
  | 0, current => .error s!"caller execution fuel exhausted at bytecode pc {current.machine.pc.toNat}"
  | remaining + 1, current =>
      match EVM.decode current.machine.executionEnv.code current.machine.pc with
      | none => .error s!"unsupported caller opcode at bytecode pc {current.machine.pc.toNat}"
      | some (op, arg) =>
          if op = .CREATE2 then do
            let result ← CreationBytecode.execReady current
            match result with
            | .exceptional next => pure (fail snapshot next)
            | .continued next => runSteps snapshot remaining next
          else if op = .RETURN || op = .REVERT || op = .STOP then
            match CreationCaller.checkedStep current.machine op arg with
            | .error _ => .ok (fail snapshot current)
            | .ok machine =>
                let next := synchronize current machine
                let output := if op = .STOP then ByteArray.empty else machine.H_return
                if op = .REVERT then .ok (.reverted output (rollback snapshot next))
                else .ok (.succeeded output next)
          else if !CreationCaller.supported op then
            .error s!"unsupported caller instruction at bytecode pc {current.machine.pc.toNat}"
          else match CreationCaller.checkedStep current.machine op arg with
          | .error _ => .ok (fail snapshot current)
          | .ok machine => runSteps snapshot remaining (synchronize current machine)

/-- Root caller identity/code must be actual even for paths without CREATE2. -/
def run (fuel : Nat) (before : Frame) : Except String Outcome := do
  if before.world.thisAddress.val != before.machine.executionEnv.codeOwner then
    throw s!"caller address mismatch at bytecode pc {before.machine.pc.toNat}"
  if (before.world.creationAccounts before.world.thisAddress.val).code.data != before.machine.executionEnv.code.data then
    throw s!"caller code mismatch at bytecode pc {before.machine.pc.toNat}"
  runSteps before fuel before

theorem synchronize_accounts (before : Frame) (machine : EVM.State) :
    (synchronize before machine).world.creationAccounts = before.world.creationAccounts := rfl

theorem rollback_world (snapshot current : Frame) :
    (rollback snapshot current).world = snapshot.world := rfl

theorem rollback_warm (snapshot current : Frame) :
    (rollback snapshot current).warm = snapshot.warm := rfl

theorem rollback_gas (snapshot current : Frame) :
    (rollback snapshot current).machine.gasAvailable = current.machine.gasAvailable := rfl

theorem fail_gas (snapshot current : Frame) :
    match fail snapshot current with
    | .exceptional next => next.machine.gasAvailable = UInt256.ofNat 0
    | _ => False := rfl

theorem runSteps_zero (snapshot current : Frame) : runSteps snapshot 0 current =
    .error s!"caller execution fuel exhausted at bytecode pc {current.machine.pc.toNat}" := rfl

end Compiler.Proofs.IRGeneration.CreationExecution
