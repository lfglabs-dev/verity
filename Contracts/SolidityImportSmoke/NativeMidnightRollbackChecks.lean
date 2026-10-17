import Contracts.SolidityImportSmoke.NativeMidnightRollbackData

namespace MidnightSourceRollback
open EvmYul Compiler.Proofs.IRGeneration.NativeCreationWorld
open Compiler.Proofs.IRGeneration.NativeCreationWorldCaller
open Compiler.Proofs.IRGeneration.NativeMidnightConstructor
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


def runChecks (verbose : Bool := true) : IO Unit := do
  for (count, key, calldata, payload) in cases do
    let entry := initial code 5000000 []
    let before := { entry with machine := { entry.machine with
      executionEnv := { entry.machine.executionEnv with calldata := calldata } } }
    let boundary ← match Compiler.Proofs.IRGeneration.NativeHashedWorldCaller.run 3000 before with
      | .ok (.ready frame) => pure frame
      | .error message => throw (IO.userError message)
      | _ => throw (IO.userError "source caller native prefix exceptional")
    let (offset, size, salt) ← match boundary.machine.stack with
      | zero :: offset :: size :: salt :: _ =>
        unless zero.toNat == 0 && salt.toNat == 0 do throw (IO.userError "source caller creation operands")
        pure (offset, size, salt)
      | _ => throw (IO.userError "source caller creation stack")
    unless size.toNat == payload.size + 11 &&
        boundary.machine.memory.readWithPadding offset.toNat size.toNat ==
          Verity.Core.Model.MidnightInitcode.initcode payload do
      throw (IO.userError "source caller ABI/initcode mismatch")
    let slot := UInt256.ofNat (Compiler.Proofs.solidityMappingSlot 0 key)
    unless (boundary.world.readSlot slot.toNat).val == 99 &&
        (persistentWord boundary.machine owner slot).val == 99 do
      throw (IO.userError "source caller mapping mismatch")
    let computed ← match Compiler.Proofs.IRGeneration.CreationBytecode.execReady boundary with
      | .ok (.continued frame) => pure frame
      | .error message => throw (IO.userError message)
      | _ => throw (IO.userError "source caller canonical creation exceptional")
    let native ← match EVM.step 30 (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) with
      | .ok machine => pure machine
      | _ => throw (IO.userError "source caller native creation exceptional")
    let address ← match native.stack with
      | address :: _ => pure address
      | _ => throw (IO.userError "source caller omitted address")
    unless address.toNat != 0 && native.gasAvailable == computed.machine.gasAvailable &&
        native.stack == computed.machine.stack &&
        (creationAccount native (AccountAddress.ofUInt256 address)).code == payload &&
        (computed.world.creationAccounts address.toNat).code == payload do
      throw (IO.userError "source caller native/model mismatch")
    let seed : Compiler.CompilationModel.Denote.DenoteState := { world := before.world, bindings := [] }
    let state := Compiler.Proofs.IRGeneration.NativeHashedDenote.atBoundary seed boundary
    let oracle : Compiler.CompilationModel.Denote.DenoteOracle :=
      { mappingSlot := fun _ _ => 9999, keccakMemorySlice := fun _ _ _ => 9999 }
    match Compiler.CompilationModel.Denote.execStmt oracle [] state
        (.create2 "created" (.literal offset.toNat) (.literal size.toNat) (.literal salt.toNat)) with
    | .continue final =>
      unless Compiler.CompilationModel.Denote.lookupBinding? final.bindings "created" == some address.toNat &&
          final.executionContext.map (fun c => c.opcode.gas) == some native.gasAvailable.toNat &&
          (final.world.readSlot slot.toNat).val == 99 &&
          (final.world.creationAccounts address.toNat).code == payload do
        throw (IO.userError "source caller Denote mismatch")
    | _ => throw (IO.userError "source caller Denote failure")
    match EVM.X 5000 (EVM.D_J code (UInt256.ofNat 0)) before.machine with
    | .ok (.revert gas output) =>
      let expected := (KeccakEngine.keccak256 "AfterDeploy(address)".toUTF8).extract 0 4 ++ address.toByteArray
      unless output == expected do throw (IO.userError "source rollback exact revert mismatch")
      if verbose then IO.println s!"ROLLBACK_OBS:{count}:{key}:{boundary.machine.pc.toNat}:{boundary.machine.gasAvailable.toNat}:{native.gasAvailable.toNat}:{gas.toNat}:{slot.toNat}:{address.toNat}:{offset.toNat}:{size.toNat}"
    | _ => throw (IO.userError "source rollback whole iterator failure")
  IO.println "SOURCE_ROLLBACK_SUCCESS:6 actual pinned IdLib successful-creation then event/revert cases"

end MidnightSourceRollback
