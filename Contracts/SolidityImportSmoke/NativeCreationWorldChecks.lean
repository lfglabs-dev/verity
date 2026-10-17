import Compiler.Proofs.IRGeneration.NativeCreationLocalFrames

namespace SolidityImportSmoke.NativeCreationWorldChecks
open EvmYul Compiler.Proofs.IRGeneration.NativeCreationWorld

private def owner : AccountAddress := AccountAddress.ofUInt256 (.ofNat 4096)
private def foreign : AccountAddress := AccountAddress.ofUInt256 (.ofNat 12288)
private def missing : AccountAddress := AccountAddress.ofUInt256 (.ofNat 8192)
private def native : EVM.State :=
  { (Inhabited.default : EVM.State) with
    accountMap := (Inhabited.default : AccountMap .EVM).insert owner
      (({ (Inhabited.default : Account .EVM) with
          nonce := .ofNat 7, balance := .ofNat 100, code := ⟨#[0x5f, 0x00]⟩ } : Account .EVM).updateStorage (.ofNat 7) (.ofNat 23) |>.updateStorage (.ofNat 9) (.ofNat 88)
        |>.updateTransientStorage (.ofNat 7) (.ofNat 99) |>.updateTransientStorage (.ofNat 9) (.ofNat 77))
      |>.insert foreign (({ (Inhabited.default : Account .EVM) with
        nonce := .ofNat 9, balance := .ofNat 200, code := ⟨#[0x00]⟩ } : Account .EVM).updateStorage
          (.ofNat 7) (.ofNat 44) |>.updateTransientStorage (.ofNat 7) (.ofNat 101))
    σ₀ := (Inhabited.default : AccountMap .EVM).insert owner
      ((Inhabited.default : Account .EVM).updateStorage (.ofNat 7) (.ofNat 11))
    executionEnv := { (Inhabited.default : ExecutionEnv .EVM) with codeOwner := owner }
    substate := { (Inhabited.default : Substate) with
      accessedAccounts := (Inhabited.default : Substate).accessedAccounts.insert owner
      accessedStorageKeys := (Inhabited.default : Substate).accessedStorageKeys.insert (owner, .ofNat 7)
      logSeries := #[{ address := owner, topics := #[.ofNat 13], data := ⟨#[0xab]⟩ }] } }

/-- Entry states reproduce the saved real-EVM exceptional reference operands.
Only the opcode under test plus STOP is executed. This is component calibration,
not authentication of a solc caller prefix or source function. -/
private def entry (opcode : UInt8) (gas : Nat) (isStatic : Bool) : EVM.State :=
  let account : Account .EVM :=
    (Inhabited.default : Account .EVM).updateStorage (.ofNat 7) (.ofNat 23)
  let accounts := (Inhabited.default : AccountMap .EVM).insert owner account
  { (Inhabited.default : EVM.State) with
    accountMap := accounts, σ₀ := accounts, gasAvailable := .ofNat gas
    stack := if opcode == 0xa0 then [.ofNat 0, .ofNat 0] else [.ofNat 7, .ofNat 23]
    executionEnv := { (Inhabited.default : ExecutionEnv .EVM) with
      codeOwner := owner
      perm := !isStatic
      depth := 1
      code := ⟨#[opcode, 0x00]⟩ } }

private def expectStaticFailure (opcode : UInt8) (op : Operation .EVM) (gas : Nat) : IO Unit := do
  match Compiler.Proofs.IRGeneration.CreationCaller.checkedStep (entry opcode gas true) op none with
  | .error .StaticModeViolation => pure ()
  | _ => throw (IO.userError "checked native static write bypassed exceptional gate")
  match EVM.X 4 #[] (entry opcode gas true) with
  | .error .StaticModeViolation => pure ()
  | _ => throw (IO.userError "native static write did not fail as saved real EVM reference")

private def checkExceptionalReferences : IO Unit := do
  expectStaticFailure 0x55 .SSTORE 9994
  expectStaticFailure 0x5d .TSTORE 9994
  expectStaticFailure 0xa0 .LOG0 9996
  match Compiler.Proofs.IRGeneration.CreationCaller.checkedStep (entry 0x55 2300 false) .SSTORE none with
  | .error .OutOfGass => pure ()
  | _ => throw (IO.userError "checked native SSTORE2300 bypassed stipend gate")
  match Compiler.Proofs.IRGeneration.CreationCaller.checkedStep (entry 0x55 2301 false) .SSTORE none with
  | .ok after =>
      unless after.gasAvailable.toNat == 101 &&
          (persistentWord after owner (.ofNat 7)).val == 23 &&
          storageWarm after owner (.ofNat 7) do
        throw (IO.userError "checked native SSTORE2301 differs from EVM reference")
  | _ => throw (IO.userError "checked native SSTORE2301 did not succeed")
  match EVM.X 4 #[] (entry 0x55 2300 false) with
  | .error .OutOfGass => pure ()
  | _ => throw (IO.userError "native SSTORE stipend boundary2300 did not fail")
  match EVM.X 4 #[] (entry 0x55 2301 false) with
  | .ok (.success after output) =>
      unless after.gasAvailable.toNat == 101 && output.size == 0 &&
          (persistentWord after owner (.ofNat 7)).val == 23 &&
          (originalPersistentWord after owner (.ofNat 7)).val == 23 &&
          storageWarm after owner (.ofNat 7) && (rawLogs after).size == 0 do
        throw (IO.userError "native SSTORE2301 storage/gas/access differs from real EVM reference")
  | _ => throw (IO.userError "native SSTORE stipend boundary2301 did not succeed")
  IO.println "native exceptional component reference checks passed:5"

private def checkStorageOpcodeWrites : IO Unit := do
  let persistent := { entry 0x55 9994 false with stack := [.ofNat 7, .ofNat 55] }
  let transient := { entry 0x5d 9994 false with stack := [.ofNat 7, .ofNat 66] }
  for (before, op, expectedGas, persistentValue, transientValue, warm) in
      [(persistent, Operation.SSTORE, 4994, 55, 0, true),
       (transient, Operation.TSTORE, 9894, 23, 66, false)] do
    let checked ← match Compiler.Proofs.IRGeneration.CreationCaller.checkedStep before op none with
      | .ok after => pure after
      | .error _ => throw (IO.userError "checked native storage write unexpectedly failed")
    let executed ← match EVM.X 4 #[] before with
      | .ok (.success after output) =>
          unless output.size == 0 do throw (IO.userError "native storage step returned data")
          pure after
      | _ => throw (IO.userError "actual native storage opcode execution unexpectedly failed")
    -- X executes the trailing STOP too; checkedStep executes one storage opcode.
    for (after, expectedLength) in [(checked, 1), (executed, 2)] do
      unless after.gasAvailable.toNat == expectedGas && after.pc.toNat == 1 &&
          after.execLength == expectedLength && after.stack.isEmpty &&
          (persistentWord after owner (.ofNat 7)).val == persistentValue &&
          (transientWord after owner (.ofNat 7)).val == transientValue &&
          (originalPersistentWord after owner (.ofNat 7)).val == 23 &&
          storageWarm after owner (.ofNat 7) == warm && (rawLogs after).isEmpty do
        throw (IO.userError "checked/actual native storage step gas/stack/PC/world frame mismatch")

def runChecks : IO Unit := do
  checkExceptionalReferences
  checkStorageOpcodeWrites
  unless (account? native owner).isSome && (account? native missing).isNone do
    throw (IO.userError "native account presence lost")
  let projected := creationAccount native owner
  unless projected.nonce == 7 && projected.balance.val == 100 && projected.code.data == #[0x5f, 0x00] do
    throw (IO.userError "native creation-account projection changed")
  unless (persistentWord native owner (.ofNat 7)).val == 23 &&
      (transientWord native owner (.ofNat 7)).val == 99 &&
      (persistentWord native owner (.ofNat 8)).val == 0 &&
      (persistentWord native missing (.ofNat 7)).val == 0 do
    throw (IO.userError "native persistent/transient/account storage conflated")
  unless accountWarm native owner && !accountWarm native missing do
    throw (IO.userError "native warm account projection changed")
  unless (originalPersistentWord native owner (.ofNat 7)).val == 11 &&
      storageWarm native owner (.ofNat 7) && !storageWarm native owner (.ofNat 8) &&
      !storageWarm native missing (.ofNat 7) do
    throw (IO.userError "original storage or per-slot warmth conflated")
  let stored := { native with toState := native.toState.sstore (.ofNat 7) (.ofNat 55) }
  unless (persistentWord stored owner (.ofNat 7)).val == 55 &&
      (originalPersistentWord stored owner (.ofNat 7)).val == 11 &&
      (transientWord stored owner (.ofNat 7)).val == 99 &&
      (rawLogs stored).size == 1 && (creationAccount stored owner).nonce == 7 do
    throw (IO.userError "native SSTORE effect/frame did not preserve original/transient/log/account metadata")
  let transient := { native with toState := native.toState.tstore (.ofNat 7) (.ofNat 66) }
  unless (transientWord transient owner (.ofNat 7)).val == 66 &&
      (persistentWord transient owner (.ofNat 7)).val == 23 &&
      (originalPersistentWord transient owner (.ofNat 7)).val == 11 &&
      (rawLogs transient).size == 1 && (creationAccount transient owner).nonce == 7 do
    throw (IO.userError "native TSTORE effect/frame changed persistent/original/log/account metadata")
  for after in [stored, transient] do
    unless (persistentWord after owner (.ofNat 9)).val == 88 &&
        (transientWord after owner (.ofNat 9)).val == 77 do
      throw (IO.userError "native write changed a distinct slot")
  for after in [stored, transient] do
    unless (account? after foreign).isSome && (account? after missing).isNone &&
        (creationAccount after foreign).nonce == 9 &&
        (creationAccount after foreign).balance.val == 200 &&
        (creationAccount after foreign).code.data == #[0x00] &&
        (persistentWord after foreign (.ofNat 7)).val == 44 &&
        (transientWord after foreign (.ofNat 7)).val == 101 &&
        (creationAccount after owner).balance.val == 100 &&
        (creationAccount after owner).code.data == #[0x5f, 0x00] do
      throw (IO.userError "native storage write changed foreign account/presence or own metadata")
  let cleared := { native with toState := native.toState.sstore (.ofNat 7) (.ofNat 0) }
  let transientCleared := { native with toState := native.toState.tstore (.ofNat 7) (.ofNat 0) }
  unless (persistentWord cleared owner (.ofNat 7)).val == 0 &&
      !(account cleared owner).storage.contains (.ofNat 7) &&
      (transientWord cleared owner (.ofNat 7)).val == 99 &&
      (persistentWord cleared owner (.ofNat 9)).val == 88 &&
      (originalPersistentWord cleared owner (.ofNat 7)).val == 11 do
    throw (IO.userError "native zero SSTORE erase/read/frame changed")
  unless (transientWord transientCleared owner (.ofNat 7)).val == 0 &&
      !(account transientCleared owner).tstorage.contains (.ofNat 7) &&
      (persistentWord transientCleared owner (.ofNat 7)).val == 23 &&
      (transientWord transientCleared owner (.ofNat 9)).val == 77 do
    throw (IO.userError "native zero TSTORE erase/read/frame changed")
  for opcode in [0x55, 0x5d, 0xa0] do
    match Compiler.Proofs.IRGeneration.CreationCaller.run 4 (entry opcode 9994 false) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "world opcode admitted before canonical agreement")
  let localState : EVM.State :=
    { native with
      gasAvailable := .ofNat 123
      pc := .ofNat 17
      stack := [.ofNat 5]
      memory := ⟨#[0xaa]⟩ }
  unless (creationAccount localState owner).nonce == projected.nonce do
    throw (IO.userError "localState machine update changed account view")
  unless (rawLogs localState).size == 1 &&
      ((rawLogs localState)[0]!).address == owner &&
      ((rawLogs localState)[0]!).topics == #[UInt256.ofNat 13] &&
      ((rawLogs localState)[0]!).data.data == #[0xab] &&
      localState.memory.data == #[0xaa] do
    throw (IO.userError "native raw log snapshot replaced by final memory")
  IO.println "native creation account/presence/storage/access view checks passed"

end SolidityImportSmoke.NativeCreationWorldChecks

def main : IO Unit := SolidityImportSmoke.NativeCreationWorldChecks.runChecks
