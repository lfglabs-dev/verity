import Contracts.SolidityImportSmoke.NativeMidnightInvalidData

namespace MidnightSourceCaller
open EvmYul Compiler.Proofs.IRGeneration.NativeCreationWorldCaller
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


def runInvalid (verbose : Bool := true) : IO Unit := do
  for (name, calldata) in invalidCases do
    let entry := initial code 5000000 []
    let before := { entry.machine with
      executionEnv := { entry.machine.executionEnv with calldata := calldata } }
    match EVM.X 5000 (EVM.D_J code (UInt256.ofNat 0)) before with
    | .ok (.revert gas output) =>
      unless output.isEmpty do throw (IO.userError s!"invalid ABI revert bytes changed: {name}")
      if verbose then IO.println s!"INVALID_OBS:{name}:{gas.toNat}"
    | _ => throw (IO.userError s!"invalid ABI accepted or wrong status: {name}")
  IO.println "SOURCE_INVALID_SUCCESS:24 malformed ABI native rejections"
end MidnightSourceCaller
