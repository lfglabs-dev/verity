import Compiler.Proofs.IRGeneration.NativeCreate2MemorySlice
import Compiler.Proofs.IRGeneration.NativeConstructorLambdaCallee
import Compiler.Proofs.IRGeneration.NativeConstructorCanonicalGas
import Compiler.Proofs.IRGeneration.NativeConstructorCanonicalSuccess
import Compiler.Proofs.IRGeneration.NativeConstructorAccountEffects
import Compiler.Proofs.IRGeneration.NativeConstructorCompletionGuard
import Compiler.Proofs.IRGeneration.NativeConstructorVacancy
import Compiler.Proofs.IRGeneration.NativeConstructorAccountFrames
import Compiler.Proofs.IRGeneration.NativeConstructorCreate2Fuel
import Verity.Core.Model.Create2Callee
import Compiler.Proofs.IRGeneration.NativeConstructorXiResult
import Compiler.Proofs.IRGeneration.NativeConstructorLambdaResult
import Compiler.Proofs.IRGeneration.NativeConstructorRuntimeGuard

namespace SolidityImportSmoke.NativeCreate2FuelChecks
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

/-- Actual CREATE2 step, with canonical callee classification and native
EIP-150 forwarding, checked on both adequate interpreter fuel values. -/
def runChecks : IO Unit := do
  let payloads : List ByteArray := [ByteArray.empty, ⟨#[0x00]⟩, ⟨#[0xef]⟩,
    ⟨Array.replicate 33 0x42⟩, ⟨Array.replicate 24576 0x00⟩,
    ⟨Array.replicate 24577 0x00⟩]
  for payload in payloads do
    let before := initial payload
    let salt : UInt256 := .ofNat 23
    let target := Compiler.Proofs.IRGeneration.NativeMidnightConstructor.nativeCreate2Target
      owner salt.toByteArray (initcode payload)
    unless target != owner do
      throw (IO.userError "native step target aliases creator")
    let total := prefixCost payload.size + 200 * payload.size
    for collision in [0, 1, 2] do
      let base : Account .EVM := { (Inhabited.default : Account .EVM) with
        balance := .ofNat 19
        nonce := .ofNat (if collision == 1 then 1 else 0)
        code := if collision == 2 then ⟨#[0x00]⟩ else ByteArray.empty }
      let stored := (base.updateStorage (.ofNat 9) (.ofNat 77)).updateTransientStorage (.ofNat 8) (.ofNat 41)
      let accounts := before.accountMap.insert target stored
      let entry := { before with
        accountMap := accounts
        σ₀ := accounts
        memory := initcode payload
        activeWords := .ofNat (((initcode payload).size + 31) / 32)
        stack := [.ofNat 7, .ofNat 0, .ofNat (initcode payload).size, salt] }
      let cost := EVM.C' entry .CREATE2
      for budget in [0, prefixCost payload.size - 1, prefixCost payload.size, total, total + 1, 10000000] do
        let pre := { entry with gasAvailable := .ofNat (cost + budget) }
        let forwarded := EVM.L budget
        let canonical ← match Verity.Core.Model.Create2Callee.execute payload forwarded with
          | .ok result => pure result
          | .error message => throw (IO.userError ("canonical step error: " ++ message))
        let expectedSuccess := collision == 0 && match canonical.result with
          | .returned _ true => true
          | _ => false
        let expectedGas := budget - forwarded + (if collision == 0 then canonical.gasLeft else 0)
        for fuel in [13, 17] do
          let post ← match EVM.step fuel cost (some (.CREATE2, none)) pre with
            | .ok post => pure post
            | .error _ => throw (IO.userError "native CREATE2 step unexpectedly errored")
          let sender := post.accountMap.getD owner default
          let account := post.accountMap.getD target default
          unless post.stack == [.ofNat (if expectedSuccess then target.val else 0)] &&
              post.pc.toNat == 1 && post.execLength == 1 && post.returnData.isEmpty &&
              post.gasAvailable.toNat == expectedGas && post.memory == pre.memory &&
              post.substate.accessedAccounts.contains target && post.substate.logSeries.isEmpty &&
              post.createdAccounts.contains target == (collision == 0) &&
              sender.nonce.toNat == 4 && sender.balance.toNat == (if expectedSuccess then 12 else 19) &&
              (sender.storage.getD (.ofNat 7) (.ofNat 0)).toNat == 99 &&
              (sender.tstorage.getD (.ofNat 8) (.ofNat 0)).toNat == 41 &&
              (post.σ₀.getD owner default).nonce.toNat == 3 &&
              account.nonce.toNat == (if expectedSuccess then 1 else if collision == 1 then 1 else 0) &&
              account.balance.toNat == (if expectedSuccess then 26 else 19) &&
              account.code == (if expectedSuccess then payload else base.code) &&
              (account.storage.getD (.ofNat 9) (.ofNat 0)).toNat == (if expectedSuccess then 0 else 77) &&
              (account.tstorage.getD (.ofNat 8) (.ofNat 0)).toNat == 41 do
            throw (IO.userError s!"native CREATE2 differs: size={payload.size} collision={collision} budget={budget} fuel={fuel}")
  IO.println "native create2 fuel:6 payloads,216 runs,gas/nonce/deposit/runtime/collision"

end SolidityImportSmoke.NativeCreate2FuelChecks

def main : IO Unit := SolidityImportSmoke.NativeCreate2FuelChecks.runChecks
