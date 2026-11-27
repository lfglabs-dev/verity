import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

/-!
Low-level `target.call{value: v}(data)` declarations (`ValueCallSequence.sol`) run through
the imported model against an explicit byte-call adversary:

* `echo` succeeds, returns its calldata and records the received value and calldata
  length in its own slots 0 and 1;
* `failing` reverts with two bytes and changes nothing;
* `silent` succeeds with empty return data and changes nothing.

Each observation is the call's success, its return or revert bytes, the executing
account's balance after the call, the `sent` counter and `echo`'s two slots. A value
above the balance fails before the target runs; a failed call refunds the value.
-/
namespace SolidityImportSmoke.ValueCallChecks
open Compiler.CompilationModel Denote ByteExternalCall
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_import imported from "Contracts/SolidityImportSmoke" entry "ValueCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EthSender
  function execute(address,uint256,bytes)
  function sendValue(address,uint256)
  function forward(address,uint256,bytes)
  function probe(address,uint256)
  function sendViaHelper(address,uint256)
  function sendValueAndLog(address,uint256)
  function read()

private def self : Nat := 0xc0de
private def echo : Nat := 0xa1
private def failing : Nat := 0xb2
private def silent : Nat := 0xc3

/-- The answer to a `call`; every other request kind reverts (`respond`). -/
private def callResponse (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.target == echo then
    let recorded := world.withStorageWords fun key =>
      if key == .contractSlot echo 0 then Verity.Core.Uint256.ofNat request.value
      else if key == .contractSlot echo 1 then Verity.Core.Uint256.ofNat request.calldata.length
      else world.storageWords key
    .success recorded request.calldata [.contractSlot echo 0, .contractSlot echo 1]
  else if request.target == failing then .revert [0xde, 0xad] []
  else .success world [] []

private def respond (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.kind == .call then callResponse request world else .revert [] []

private def environment : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some
      { respond
        valid := by
          intro request world
          unfold respond
          split
          · rename_i hcall
            have hstatic : request.kind ≠ .staticcall := by
              intro h
              rw [h] at hcall
              exact absurd hcall (by decide)
            cases callResponse request world <;> simp [Response.valid, hstatic]
          · simp [Response.valid] } }

/-- ABI tail of a `bytes` argument: length word, then the bytes in padded words. -/
private def bytesTail (data : List UInt8) : List Nat :=
  data.length :: (List.range ((data.length + 31) / 32)).map fun word =>
    (List.range 32).foldl (fun acc lane => acc * 256 + (data.getD (32 * word + lane) 0).toNat) 0

private def observe (name : String) (args : List Nat) (balance : Nat := 1000) :
    Option (Bool × List UInt8 × Nat × Nat × Nat × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let tx : DenoteTransaction := { sender := 0x5e, thisAddress := self, functionSelector := 0, args }
  let world := { withTransactionContext Verity.defaultState tx with
    selfBalance := Verity.Core.Uint256.ofNat balance }
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match executeBody SolidityImport.Differential.oracle (effectiveFields imported.model) world
      bindings fn.body imported.model.errors environment with
  | .ok r => some (r.success, r.data, r.world.selfBalance.val, (r.world.readSlot 0).val,
      (r.world.storageWords (.contractSlot echo 0)).val,
      (r.world.storageWords (.contractSlot echo 1)).val)
  | .error _ => none

/-- `FailedCall()`. -/
private def failedCall : List UInt8 := [0xd6, 0xbd, 0xa2, 0x75]

-- `execute`: the value and calldata reach the target and the balance is debited.
#guard observe "execute" ([echo, 10, 96] ++ bytesTail [1, 2, 3]) ==
  some (true, [], 990, 10, 10, 3)
-- A failed call reverts with the custom error and rolls everything back.
#guard observe "execute" ([failing, 10, 96] ++ bytesTail []) ==
  some (false, failedCall, 1000, 0, 0, 0)
-- An underfunded call fails without running the target.
#guard observe "execute" ([echo, 2000, 96] ++ bytesTail [1]) ==
  some (false, failedCall, 1000, 0, 0, 0)

-- `sendValue`: empty calldata; a failure becomes `Error("send failed")`.
#guard observe "sendValue" [silent, 5] == some (true, [], 995, 5, 0, 0)
#guard observe "sendValue" [echo, 5] == some (true, [], 995, 5, 5, 0)
#guard observe "sendValue" [failing, 5] ==
  some (false, errorStringBytes "send failed", 1000, 0, 0, 0)

-- `forward`: the complete return data is measured on success and forwarded on failure.
#guard observe "forward" ([echo, 0, 96] ++ bytesTail [9, 8, 7, 6]) ==
  some (true, wordBytes 4, 1000, 1, 0, 4)
#guard observe "forward" ([silent, 7, 96] ++ bytesTail [9]) ==
  some (true, wordBytes 0, 993, 1, 0, 0)
#guard observe "forward" ([failing, 1, 96] ++ bytesTail [9]) ==
  some (false, [0xde, 0xad], 1000, 0, 0, 0)

-- `probe`: a failure is a result, not a revert; the echoed calldata is selector + one word.
#guard observe "probe" [failing, 1] == some (true, wordBytes 0 ++ wordBytes 2, 1000, 2, 0, 0)
#guard observe "probe" [echo, 3] == some (true, wordBytes 1 ++ wordBytes 36, 997, 2, 3, 36)
#guard observe "probe" [echo, 3] (balance := 2) ==
  some (true, wordBytes 0 ++ wordBytes 0, 2, 2, 0, 0)

-- The inlined `void` helper performs the same transfer.
#guard observe "sendViaHelper" [echo, 7] == some (true, [], 993, 3, 7, 0)
#guard observe "sendViaHelper" [failing, 7] == some (false, failedCall, 1000, 0, 0, 0)

-- Post-value-call storage update and log succeed on funded calls and roll back on failure.
#guard observe "sendValueAndLog" [echo, 7] == some (true, [], 993, 7, 7, 0)
#guard observe "sendValueAndLog" [failing, 7] == some (false, failedCall, 1000, 0, 0, 0)
#guard observe "sendValueAndLog" [echo, 2000] == some (false, failedCall, 1000, 0, 0, 0)

-- Every call is the closed value-transferring memory call.
private partial def valueCalls : List Stmt → Nat
  | [] => 0
  | .ecm mod _ :: rest =>
      (if mod.byteTransport.any (· matches .yulMemoryValueCall _) then 1 else 0) + valueCalls rest
  | .ite _ yes no :: rest => valueCalls yes + valueCalls no + valueCalls rest
  | _ :: rest => valueCalls rest

#guard ["execute", "sendValue", "forward", "probe", "sendViaHelper", "sendValueAndLog"].all fun name =>
  (imported.model.functions.find? (·.name == name)).any (valueCalls ·.body == 1)

end SolidityImportSmoke.ValueCallChecks
