import Contracts.SolidityImportSmoke.NativeMidnightSourceData

namespace MidnightSourceCaller
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


def runFailures (verbose : Bool := true) : IO Unit := do
  for (count, key, calldata, payload) in cases do
    for collision in [1, 2] do
      let target := nativeCreate2Target owner (UInt256.ofNat 0).toByteArray
        (Verity.Core.Model.MidnightInitcode.initcode payload)
      let collisionAccount : Account .EVM := { (Inhabited.default : Account .EVM) with
        nonce := .ofNat (if collision == 1 then 1 else 0)
        code := if collision == 2 then ⟨#[0x00]⟩ else ByteArray.empty }
      let entry := initial code 5000000 []
      let accounts := entry.machine.accountMap.insert target collisionAccount
      let world := { entry.world with
        creationAccounts := fun address => if address == target.val then
          { nonce := if collision == 1 then 1 else 0
            code := if collision == 2 then ⟨#[0x00]⟩ else ByteArray.empty }
          else entry.world.creationAccounts address
        codeSize := fun address => if address == target.val then
          Verity.Core.Uint256.ofNat (if collision == 2 then 1 else 0) else entry.world.codeSize address }
      let before := { entry with world := world, machine := { entry.machine with
        accountMap := accounts, σ₀ := accounts
        executionEnv := { entry.machine.executionEnv with calldata := calldata } } }
      let boundary ← match Compiler.Proofs.IRGeneration.NativeHashedWorldCaller.run 3000 before with
        | .ok (.ready frame) => pure frame
        | _ => throw (IO.userError "source collision prefix failed")
      let computed ← match Compiler.Proofs.IRGeneration.CreationBytecode.execReady boundary with
        | .ok (.continued frame) => pure frame
        | _ => throw (IO.userError "source collision canonical refused")
      let native ← match EVM.step 30 (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
          (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) with
        | .ok machine => pure machine
        | _ => throw (IO.userError "source collision native refused")
      let slot := UInt256.ofNat (Compiler.Proofs.solidityMappingSlot 0 key)
      unless native.stack.head? == some (UInt256.ofNat 0) && native.stack == computed.machine.stack &&
          native.gasAvailable == computed.machine.gasAvailable &&
          (persistentWord native owner slot).val == 99 &&
          (creationAccount native owner).nonce == 1 &&
          (computed.world.creationAccounts 8193).nonce == 1 &&
          (creationAccount native target).nonce == collisionAccount.nonce.toNat &&
          (creationAccount native target).code == collisionAccount.code do
        throw (IO.userError "source collision native/model effects mismatch")
      match EVM.X 5000 (EVM.D_J code (UInt256.ofNat 0)) before.machine with
      | .ok (.revert gas output) =>
        let expected := (KeccakEngine.keccak256 "SStore2DeploymentFailed()".toUTF8).extract 0 4
        unless output == expected do throw (IO.userError "source collision custom revert mismatch")
        if verbose then IO.println s!"COLLISION_OBS:{count}:{key}:{collision}:{boundary.machine.gasAvailable.toNat}:{native.gasAvailable.toNat}:{gas.toNat}:{(uInt256OfByteArray output).toNat}:{output.size}:{target.val}"
      | _ => throw (IO.userError "source collision whole native result mismatch")
  IO.println "SOURCE_COLLISION_SUCCESS:12 actual pinned IdLib collision/revert cases"
end MidnightSourceCaller
