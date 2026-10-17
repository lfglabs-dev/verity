import Compiler.Proofs.IRGeneration.NativeConstructorXiResult
import Compiler.Proofs.IRGeneration.NativeConstructorLambdaResult
import Compiler.Proofs.IRGeneration.NativeConstructorRuntimeGuard

namespace SolidityImportSmoke.NativeInitcodeFrameChecks
open EvmYul
open Compiler.Proofs.IRGeneration.NativeCreationWorld
open Verity.Core.Model.MidnightInitcode

private def owner : AccountAddress := AccountAddress.ofUInt256 (.ofNat 8193)

private def initial (payload : ByteArray) : EVM.State :=
  let stored := ({ (Inhabited.default : Account .EVM) with
      nonce := .ofNat 3, balance := .ofNat 19 }).updateStorage (.ofNat 7) (.ofNat 99)
  let account := stored.updateTransientStorage (.ofNat 8) (.ofNat 41)
  let accounts := (Inhabited.default : AccountMap .EVM).insert owner account
  { (Inhabited.default : EVM.State) with
    accountMap := accounts
    σ₀ := accounts
    gasAvailable := .ofNat 1000000
    executionEnv := { (Inhabited.default : ExecutionEnv .EVM) with
      codeOwner := owner, code := initcode payload, perm := true } }

/-- Actual native X executes the constructor, without executing its arbitrary
runtime payload. Ten fuel units are needed: nine instructions plus positive
fuel for the final step. Canonical gas/output are checked separately below. -/
def runChecks : IO Unit := do
  let payloads : List ByteArray := [ByteArray.empty, ⟨#[0x00]⟩,
    ⟨#[0x55,0xf5,0xf1,0xff,0xfd,0xfe,0xef]⟩,
    ⟨Array.replicate 32 0x81⟩, ⟨Array.replicate 33 0x42⟩,
    ⟨Array.replicate 257 0xa7⟩]
  for payload in payloads do
    let before := initial payload
    match EVM.X 9 #[] before with
    | .error .OutOfFuel => pure ()
    | _ => throw (IO.userError "native constructor underfuel was accepted")
    for fuel in [10, 11, 13, 32] do
      let after ← match EVM.X fuel #[] before with
        | .ok (.success after output) =>
          unless output == payload do
            throw (IO.userError "native constructor output differs from arbitrary payload")
          pure after
        | _ => throw (IO.userError "native constructor failed with sufficient fuel")
      match runMetered 9 (initcode payload) Verity.Core.Model.MidnightInitcode.initial 1000000 with
      | .ok (.returned data _ remaining) =>
        unless data == payload && after.gasAvailable.toNat == remaining do
          throw (IO.userError "native constructor gas/output differs from canonical metering")
      | _ => throw (IO.userError "canonical constructor failed")
      unless (persistentWord after owner (.ofNat 7)).val == 99 &&
          (originalPersistentWord after owner (.ofNat 7)).val == 99 &&
          (transientWord after owner (.ofNat 8)).val == 41 &&
          (creationAccount after owner).nonce == 3 &&
          (creationAccount after owner).balance == 19 &&
          (rawLogs after).isEmpty && after.pc.toNat == 11 && after.execLength == 9 do
        throw (IO.userError "native constructor changed world or executed runtime payload")
    let runXi := fun fuel => EVM.Ξ fuel before.createdAccounts before.genesisBlockHeader
      before.blocks before.accountMap before.σ₀ before.gasAvailable before.substate before.executionEnv
    match runXi 10 with
    | .error .OutOfFuel => pure ()
    | _ => throw (IO.userError "native Xi constructor underfuel was accepted")
    for fuel in [11, 14, 33] do
      match runXi fuel with
      | .ok (.success (created, accounts, remaining, substate) output) =>
        let observed := { before with
          accountMap := accounts
          createdAccounts := created
          gasAvailable := remaining
          substate := substate }
        unless output == payload && remaining.toNat == 1000000 - prefixCost payload.size &&
            (persistentWord observed owner (.ofNat 7)).val == 99 &&
            (originalPersistentWord observed owner (.ofNat 7)).val == 99 &&
            (transientWord observed owner (.ofNat 8)).val == 41 &&
            (creationAccount observed owner).nonce == 3 &&
            (creationAccount observed owner).balance == 19 &&
            (rawLogs observed).isEmpty && created.toList == before.createdAccounts.toList do
          throw (IO.userError "native Xi constructor output/gas/world differs")
      | _ => throw (IO.userError "native Xi constructor failed with sufficient fuel")
    let salt : ByteArray := ⟨Array.replicate 32 0x17⟩
    let target := Compiler.Proofs.IRGeneration.NativeMidnightConstructor.nativeCreate2Target
      owner salt (initcode payload)
    if target == owner then
      throw (IO.userError "native Lambda fixture target aliases its creator")
    let storedTarget := ({ (Inhabited.default : Account .EVM) with
      balance := .ofNat 19 }).updateStorage (.ofNat 9) (.ofNat 77)
    let accounts := before.accountMap.insert target storedTarget
    let runLambda := fun fuel => EVM.Lambda fuel [] before.createdAccounts before.genesisBlockHeader
      before.blocks accounts accounts before.substate owner before.executionEnv.sender
      before.gasAvailable (.ofNat 0) (.ofNat 7) (initcode payload) (.ofNat 1) (some salt)
      before.executionEnv.header true
    match runLambda 11 with
    | .error .OutOfFuel => pure ()
    | _ => throw (IO.userError "native Lambda constructor underfuel was accepted")
    for fuel in [15, 16, 34] do
      match runLambda fuel with
      | .ok (address, created, result, remaining, substate, success, returned) =>
        let observed := { before with
          accountMap := result
          createdAccounts := created
          gasAvailable := remaining
          substate := substate }
        let account := result.getD target default
        unless success && address == target && created.contains target && returned.isEmpty &&
            account.nonce.toNat == 1 && account.balance.toNat == 26 && account.code == payload &&
            (account.storage.getD (.ofNat 9) (.ofNat 0)).toNat == 0 &&
            (persistentWord observed owner (.ofNat 7)).val == 99 &&
            (transientWord observed owner (.ofNat 8)).val == 41 &&
            (creationAccount observed owner).nonce == 3 &&
            (creationAccount observed owner).balance == 12 &&
            remaining.toNat == 1000000 - prefixCost payload.size - 200 * payload.size &&
            substate.accessedAccounts.contains target && (rawLogs observed).isEmpty do
          throw (IO.userError "native Lambda constructor commit/gas differs")
      | _ => throw (IO.userError "native Lambda constructor failed with sufficient fuel")
    let cost := prefixCost payload.size
    for gas in [0, cost - 1, cost, cost + 1] do
      let metered := { before with gasAvailable := .ofNat gas }
      if gas < cost then
        match EVM.X 13 #[] metered with
        | .error .OutOfGass => pure ()
        | _ => throw (IO.userError "native constructor low gas was not a real EVM gas exception")
      else
        match EVM.X 13 #[] metered with
        | .ok (.success after output) =>
          unless output == payload && after.gasAvailable.toNat == gas - cost do
            throw (IO.userError "native constructor gas boundary differs")
        | _ => throw (IO.userError "native constructor sufficient gas boundary failed")
  IO.println "native constructor frames:6 payloads,24 successful runs,6 underfuel rejections,24 gas boundaries"

  IO.println "native constructor xi:6 payloads,18 successful runs,6 underfuel rejections"

  IO.println "native constructor lambda:6 payloads,18 successful runs,6 underfuel rejections"

end SolidityImportSmoke.NativeInitcodeFrameChecks

def main : IO Unit := SolidityImportSmoke.NativeInitcodeFrameChecks.runChecks
