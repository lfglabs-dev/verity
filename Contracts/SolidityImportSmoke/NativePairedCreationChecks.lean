import Compiler.Proofs.IRGeneration.NativeCreationWorldExecution

namespace SolidityImportSmoke.NativePairedCreationChecks
open EvmYul Compiler.Proofs.IRGeneration.NativeCreationWorld
open Compiler.Proofs.IRGeneration.NativeCreationWorldCaller

private def owner : AccountAddress := AccountAddress.ofUInt256 (.ofNat 8193)
private def initial (code : ByteArray) (gas : Nat) (stack : Stack UInt256) : Frame :=
  let entry := ({ (Inhabited.default : Account .EVM) with code := code }).updateStorage (.ofNat 7) (.ofNat 23)
  let accounts := (Inhabited.default : AccountMap .EVM).insert owner entry
  { world := ({ Verity.defaultState with
      thisAddress := Verity.Core.Address.ofNat 8193
      creationAccounts := fun address => if address == 8193 then { code := code } else {}
      codeSize := fun address => if address == 8193 then Verity.Core.Uint256.ofNat code.size else 0
    }).writeSlot 7 (Verity.Core.Uint256.ofNat 23)
    warm := fun address => address == 8193
    machine := { (Inhabited.default : EVM.State) with
      accountMap := accounts
      σ₀ := accounts
      gasAvailable := .ofNat gas
      stack := stack
      executionEnv := { (Inhabited.default : ExecutionEnv .EVM) with codeOwner := owner, code := code, perm := true }
      substate := { (Inhabited.default : Substate) with
        accessedAccounts := (Inhabited.default : Substate).accessedAccounts.insert owner } } }

/-- Saved real-EVM persistent-write reference: code, initial slot23, 1000000
execution gas, CREATE2 pc46/gas994973/memory/header/operands and slot99.
This is native/canonical component calibration, not whole-function A/B/C. -/
private def persistentReference : ByteArray := ⟨#[0x60, 0x63, 0x60, 0x07, 0x55, 0x7f, 0x60, 0x0b, 0x38, 0x03, 0x80, 0x60, 0x0b, 0x5f, 0x39, 0x5f, 0xf3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5f, 0x52, 0x60, 0x07, 0x60, 0x0b, 0x5f, 0x5f, 0xf5, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def runChecks : IO Unit := do
  let before := initial persistentReference 1000000 []
  let after ← match run 40 before with
    | .ok (.ready after) => pure after
    | _ => throw (IO.userError "paired persistent reference failed to reach CREATE2")
  unless after.machine.pc.toNat == 46 && after.machine.gasAvailable.toNat == 994973 &&
      after.machine.stack == [UInt256.ofNat 0, .ofNat 0, .ofNat 11, .ofNat 7] &&
      after.machine.activeWords.toNat == 1 &&
      after.machine.memory.data == #[0x60,0x0b,0x38,0x03,0x80,0x60,0x0b,0x5f,0x39,0x5f,0xf3,
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] &&
      (after.world.readSlot 7).val == 99 &&
      (persistentWord after.machine owner (.ofNat 7)).val == 99 &&
      (originalPersistentWord after.machine owner (.ofNat 7)).val == 23 &&
      (transientWord after.machine owner (.ofNat 7)).val == 0 &&
      (creationAccount after.machine owner).nonce == 0 &&
      (after.world.creationAccounts 8193).nonce == 0 &&
      storageWarm after.machine owner (.ofNat 7) && (rawLogs after.machine).isEmpty do
    throw (IO.userError "paired persistent reference differs in actual gas/operands/memory/world")
  let transientBefore := initial ⟨#[0x5d,0x00]⟩ 10000 [.ofNat 7, .ofNat 99]
  let transientAfter ← match advance transientBefore .TSTORE none with
    | .ok (.continued after) => pure after
    | _ => throw (IO.userError "paired transient write failed")
  unless transientAfter.machine.gasAvailable.toNat == 9900 &&
      (transientAfter.world.transientStorage 7).val == 99 &&
      (transientWord transientAfter.machine owner (.ofNat 7)).val == 99 &&
      (transientAfter.world.readSlot 7).val == 23 &&
      (persistentWord transientAfter.machine owner (.ofNat 7)).val == 23 &&
      (originalPersistentWord transientAfter.machine owner (.ofNat 7)).val == 23 do
    throw (IO.userError "paired transient write lost canonical/native channel agreement")
  let absent := { transientBefore with machine := { transientBefore.machine with accountMap := Inhabited.default } }
  match advance absent .TSTORE none with
  | .error _ => pure ()
  | _ => throw (IO.userError "paired write manufactured an absent account")
  let static := { transientBefore with machine := { transientBefore.machine with
    executionEnv := { transientBefore.machine.executionEnv with perm := false } } }
  match advance static .TSTORE none with
  | .ok (.exceptional .StaticModeViolation after) =>
      unless (after.world.transientStorage 7).val == 0 && after.machine.gasAvailable.toNat == 0 do
        throw (IO.userError "paired static failure wrote canonical storage or retained gas")
  | _ => throw (IO.userError "paired static failure changed status")
  let created ← match Compiler.Proofs.IRGeneration.NativeCreationWorldExecution.run 40 before with
    | .ok (.continued frame) => pure frame
    | _ => throw (IO.userError "paired prefix creation failed")
  let address := 0xe317ec6689ba1293927261f8acda33b2db0bb1ba
  unless created.machine.pc.toNat == 47 && created.machine.gasAvailable.toNat == 962944 &&
      created.machine.stack == [UInt256.ofNat address] &&
      (created.world.readSlot 7).val == 99 &&
      (persistentWord created.machine owner (.ofNat 7)).val == 99 &&
      (originalPersistentWord created.machine owner (.ofNat 7)).val == 23 &&
      (created.world.creationAccounts 8193).nonce == 1 &&
      (created.world.creationAccounts address).nonce == 1 &&
      (created.world.creationAccounts address).code.isEmpty &&
      created.warm address do
    throw (IO.userError "paired prefix creation disagrees with real EVM reference")
  -- A component exception retains the actually executed prefix frame; root
  -- transaction rollback is a separate caller obligation.
  let failing := initial ⟨#[0x60,0x63,0x60,0x07,0x55,0x55]⟩ 10000 []
  match Compiler.Proofs.IRGeneration.NativeCreationWorldExecution.run 5 failing with
  | .ok (.exceptional frame) =>
      unless frame.machine.gasAvailable.toNat == 0 && frame.machine.pc.toNat == 5 &&
          (frame.world.readSlot 7).val == 99 &&
          (persistentWord frame.machine owner (.ofNat 7)).val == 99 do
        throw (IO.userError "paired creation exception discarded the executed prefix frame")
  | _ => throw (IO.userError "paired creation exception lost its outcome")
  match Compiler.Proofs.IRGeneration.NativeCreationWorldExecution.run 0 before with
  | .error _ => pure ()
  | _ => throw (IO.userError "paired creation fuel refusal became an execution result")
  IO.println "paired prefix through CREATE2 reference checks passed"
end SolidityImportSmoke.NativePairedCreationChecks

def main : IO Unit := SolidityImportSmoke.NativePairedCreationChecks.runChecks
