import Compiler.Proofs.IRGeneration.NativeConstructorCreate2Fuel
import Verity.Core.Model.Create2Callee
import Compiler.Proofs.IRGeneration.NativeConstructorXiResult
import Compiler.Proofs.IRGeneration.NativeConstructorLambdaResult
import Compiler.Proofs.IRGeneration.NativeConstructorRuntimeGuard

namespace SolidityImportSmoke.NativeConstructorBoundaryChecks
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

/-- Actual native Lambda against canonical callee gas/runtime classification,
with independent account observations and both native collision criteria. -/
def runChecks : IO Unit := do
  let payloads : List ByteArray := [ByteArray.empty, ⟨#[0x00]⟩, ⟨#[0xef]⟩,
    ⟨Array.replicate 33 0x42⟩, ⟨Array.replicate 24576 0x00⟩,
    ⟨Array.replicate 24577 0x00⟩]
  for payload in payloads do
    let before := initial payload
    let salt : ByteArray := ⟨Array.replicate 32 0x17⟩
    let target := Compiler.Proofs.IRGeneration.NativeMidnightConstructor.nativeCreate2Target
      owner salt (initcode payload)
    unless target != owner do
      throw (IO.userError "native boundary target aliases creator")
    let cost := prefixCost payload.size
    let total := cost + 200 * payload.size
    for collision in [0, 1, 2] do
      let base : Account .EVM := { (Inhabited.default : Account .EVM) with
        balance := .ofNat 19
        nonce := .ofNat (if collision == 1 then 1 else 0)
        code := if collision == 2 then ⟨#[0x00]⟩ else ByteArray.empty }
      let stored := (base.updateStorage (.ofNat 9) (.ofNat 77)).updateTransientStorage (.ofNat 8) (.ofNat 41)
      let accounts := before.accountMap.insert target stored
      for gas in [0, cost - 1, cost, total - 1, total, total + 1] do
        let canonical ← match Verity.Core.Model.Create2Callee.execute payload gas with
          | .ok result => pure result
          | .error message => throw (IO.userError ("canonical boundary error: " ++ message))
        let expectedSuccess := collision == 0 && match canonical.result with
          | .returned _ true => true
          | _ => false
        let expectedGas := if collision == 0 then canonical.gasLeft else 0
        for fuel in [12, 16] do
          match EVM.Lambda fuel [] before.createdAccounts before.genesisBlockHeader before.blocks
              accounts accounts before.substate owner before.executionEnv.sender (.ofNat gas)
              (.ofNat 0) (.ofNat 7) (initcode payload) (.ofNat 1) (some salt)
              before.executionEnv.header true with
          | .error _ => throw (IO.userError "native Lambda boundary unexpectedly errored")
          | .ok (address, created, result, remaining, substate, success, returned) =>
            let sender := result.getD owner default
            let account := result.getD target default
            unless address == target && success == expectedSuccess && returned.isEmpty &&
                remaining.toNat == expectedGas && substate.accessedAccounts.contains target &&
                created.contains target == (collision == 0) && substate.logSeries.isEmpty &&
                sender.nonce.toNat == 3 && sender.balance.toNat == (if expectedSuccess then 12 else 19) &&
                sender.code.isEmpty && (sender.storage.getD (.ofNat 7) (.ofNat 0)).toNat == 99 &&
                (sender.tstorage.getD (.ofNat 8) (.ofNat 0)).toNat == 41 &&
                account.nonce.toNat == (if expectedSuccess then 1 else if collision == 1 then 1 else 0) &&
                account.balance.toNat == (if expectedSuccess then 26 else 19) &&
                account.code == (if expectedSuccess then payload else base.code) &&
                (account.storage.getD (.ofNat 9) (.ofNat 0)).toNat == (if expectedSuccess then 0 else 77) &&
                (account.tstorage.getD (.ofNat 8) (.ofNat 0)).toNat == 41 do
              throw (IO.userError s!"native boundary differs: size={payload.size} collision={collision} gas={gas} fuel={fuel}")
  IO.println "native constructor lambda boundaries:6 payloads,216 runs,gas/deposit/runtime/collision"

end SolidityImportSmoke.NativeConstructorBoundaryChecks

def main : IO Unit := SolidityImportSmoke.NativeConstructorBoundaryChecks.runChecks
