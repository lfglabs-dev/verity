import Compiler.Proofs.IRGeneration.CreationCaller
import Verity.Core.Model.Create2Operation

/-! Executed caller/creation bridge with a mandatory canonical-world companion.
The native local machine carries gas/stack/PC/memory. Other-account creation
state stays in the actual canonical world, not a fabricated native account map.
Subsequent account-observing instructions require a separate native world bridge. -/
namespace Compiler.Proofs.IRGeneration.CreationBytecode
open EvmYul
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory

structure Frame where
  world : Verity.ContractState
  machine : EVM.State
  warm : Create2Access.WarmAccounts

inductive Outcome where
  | continued (frame : Frame)
  | exceptional (frame : Frame)

/-- Install actual executed caller memory, preserving all canonical accounts
and storage. The native memory representation has an implicit active zero tail. -/
def callerMemory (state : EVM.State) : Memory :=
  { size := state.activeWords.toNat * 32
    bytes := fun offset =>
      let byte := state.memory.data[offset]?.getD 0
      ⟨byte.toNat, UInt8.toNat_lt_size byte⟩ }

def atBoundary (frame : Frame) : Create2Operation.Frame :=
  { world := frame.world.installPhysicalMemory (callerMemory frame.machine)
    context := (CreationCaller.context frame.machine frame.warm).opcode
    warm := frame.warm }

/-- Synchronize local observations after computed creation. Canonical accounts
are retained in Frame.world; native accountMap is deliberately not an oracle for
creation or a claimed synchronized account projection. -/
def install (before : Frame) (computed : Create2Operation.Frame) : Frame :=
  { world := computed.world
    warm := computed.warm
    machine := { before.machine with
      gasAvailable := UInt256.ofNat computed.context.gas
      activeWords := UInt256.ofNat (computed.world.byteMemory.size / 32)
      memory := MidnightInitcode.memorySlice computed.world.byteMemory 0 computed.world.byteMemory.size } }

/-- Validate identity before interpreting the actual opcode and stack. Nonzero
value is unsupported interpretation, not simulated failed creation. -/
def execReady (before : Frame) : Except String Outcome := do
  if before.world.thisAddress.val != before.machine.executionEnv.codeOwner then
    throw s!"CREATE2 caller address mismatch at bytecode pc {before.machine.pc.toNat}"
  if (before.world.creationAccounts before.world.thisAddress.val).code.data != before.machine.executionEnv.code.data then
    throw s!"CREATE2 caller code mismatch at bytecode pc {before.machine.pc.toNat}"
  match EVM.decode before.machine.executionEnv.code before.machine.pc with
  | some (.CREATE2, _) =>
      if before.machine.stack.length > 1024 then
        pure (.exceptional { before with machine := CreationCaller.exhausted before.machine })
      else match before.machine.stack with
      | value :: offset :: size :: salt :: tail =>
          if value.toNat != 0 then
            throw s!"unsupported nonzero CREATE2 value at bytecode pc {before.machine.pc.toNat}"
          let result ← Create2Operation.run (atBoundary before)
            (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
            (Verity.Core.Uint256.ofNat salt.toNat)
          match result with
          | .exceptional computed => pure (.exceptional (install before computed))
          | .continued address computed =>
              let next := install before computed
              pure (.continued { next with machine := { next.machine with
                stack := UInt256.ofNat address.val :: tail
                pc := before.machine.pc + UInt256.ofNat 1
                execLength := before.machine.execLength + 1
                returnData := ByteArray.empty } })
      | _ => pure (.exceptional { before with machine := CreationCaller.exhausted before.machine })
  | _ => throw s!"expected CREATE2 at bytecode pc {before.machine.pc.toNat}"

/-- Root/caller-prefix execution followed by computed CREATE2. No opcode gas,
address, constructor receipt or postworld is supplied by the caller. -/
def run (fuel : Nat) (before : Frame) : Except String Outcome := do
  let executed ← CreationCaller.run fuel before.machine
  match executed with
  | .exceptional _ machine => pure (.exceptional
      { before with world := before.world.installPhysicalMemory (callerMemory machine), machine := machine })
  | .ready machine => execReady { before with machine := machine }

theorem atBoundary_gas (frame : Frame) :
    (atBoundary frame).context.gas = frame.machine.gasAvailable.toNat := rfl

theorem atBoundary_size (frame : Frame) :
    (atBoundary frame).world.byteMemory.size = frame.machine.activeWords.toNat * 32 := rfl

theorem install_world (before : Frame) (computed : Create2Operation.Frame) :
    (install before computed).world = computed.world := rfl

theorem install_gas (before : Frame) (computed : Create2Operation.Frame) :
    (install before computed).machine.gasAvailable = UInt256.ofNat computed.context.gas := rfl

theorem install_warm (before : Frame) (computed : Create2Operation.Frame) :
    (install before computed).warm = computed.warm := rfl

end Compiler.Proofs.IRGeneration.CreationBytecode
