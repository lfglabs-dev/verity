import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

/-!
External `try` statements of interface members (`TryCatchSequence.sol`) run through the
imported model against an explicit byte-call adversary. Every responder changes no state,
so `call` and `staticcall` requests are answered alike:

* `good` answers `onReceived` with its own selector, `quote(x)` with `2 * x`, `flag` with
  `true` and `notify` with empty return data;
* `dirty` answers everything with the word `7` (a dirty `bytes4`, an out-of-range `bool`);
* `wrong` answers everything with the selector `0x12345678`;
* `failing` reverts with two bytes, `silent` reverts with no data;
* `short` succeeds with three bytes;
* `codeless` has no code and answers like an empty account.

Each observation is the call's success, its return or revert bytes and the `calls` counter.
-/
namespace SolidityImportSmoke.TryCatchChecks
open Compiler.CompilationModel Denote ByteExternalCall
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_import imported from "Contracts/SolidityImportSmoke" entry "TryCatchSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract TryCatchMock
  function check(address,uint256)
  function quoteOr(address,uint256,uint256)
  function poke(address)
  function notifyOr(address,uint256)
  function checkViaHelper(address,uint256)
  function read()

private def self : Nat := 0xc0de
private def good : Nat := 0xa1
private def dirty : Nat := 0xa2
private def wrong : Nat := 0xa3
private def failing : Nat := 0xb2
private def silent : Nat := 0xb3
private def short : Nat := 0xc4
private def codeless : Nat := 0xd5

private def onReceivedSelector : List UInt8 := [0xd6, 0x70, 0x11, 0x8a]
private def quoteSelector : List UInt8 := [0xed, 0x1b, 0xd7, 0x6c]
private def flagSelector : List UInt8 := [0x89, 0x0e, 0xba, 0x68]

/-- Big-endian word of `calldata` at byte `offset`, zero padded. -/
private def calldataWord (calldata : List UInt8) (offset : Nat) : Nat :=
  (List.range 32).foldl (fun acc lane => acc * 256 + (calldata.getD (offset + lane) 0).toNat) 0

/-- Return data on success (`.ok`) or revert data (`.error`) of one request. -/
private def outcome (request : Request) : Except (List UInt8) (List UInt8) :=
  let selector := request.calldata.take 4
  if request.target == good then
    if selector == onReceivedSelector then .ok (onReceivedSelector ++ List.replicate 28 0)
    else if selector == quoteSelector then .ok (wordBytes (2 * calldataWord request.calldata 4))
    else if selector == flagSelector then .ok (wordBytes 1)
    else .ok []
  else if request.target == dirty then .ok (wordBytes 7)
  else if request.target == wrong then .ok ([0x12, 0x34, 0x56, 0x78] ++ List.replicate 28 0)
  else if request.target == failing then .error [0xde, 0xad]
  else if request.target == silent then .error []
  else if request.target == short then .ok [1, 2, 3]
  else .ok []

private def environment : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some
      { respond := fun request world => match outcome request with
          | .ok data => .success world data []
          | .error data => .revert data []
        valid := by
          intro request world
          cases outcome request <;> simp [Response.valid] } }

private def observe (name : String) (args : List Nat) : Option (Bool × List UInt8 × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let tx : DenoteTransaction := { sender := 0x5e, thisAddress := self, functionSelector := 0, args }
  let world := [good, dirty, wrong, failing, silent, short].foldl
    (fun world account => world.writeAccount (Verity.Core.Address.ofNat account) { code := [0] })
    (withTransactionContext Verity.defaultState tx)
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match executeBody SolidityImport.Differential.oracle (effectiveFields imported.model) world
      bindings fn.body imported.model.errors environment with
  | .ok r => some (r.success, r.data, (r.world.readSlot 0).val)
  | .error _ => none

/-- `BadReceiver(to)`. -/
private def badReceiver (to : Nat) : List UInt8 := [0x41, 0x64, 0xd5, 0xb2] ++ wordBytes to

-- `check`: the decoded `bytes4` is compared; revert data is forwarded or replaced.
#guard observe "check" [good, 9] == some (true, [], 1)
#guard observe "check" [wrong, 9] == some (false, badReceiver wrong, 0)
#guard observe "check" [failing, 9] == some (false, [0xde, 0xad], 0)
#guard observe "check" [silent, 9] == some (false, badReceiver silent, 0)
-- Undecodable return data reverts uncaught with no data: dirty padding, short data, and an
-- account without code (no code check when return data is expected).
#guard observe "check" [dirty, 9] == some (false, [], 0)
#guard observe "check" [short, 9] == some (false, [], 0)
#guard observe "check" [codeless, 9] == some (false, [], 0)

-- `quoteOr`: a `view` callee through `staticcall`; its result or the fallback.
#guard observe "quoteOr" [good, 21, 5] == some (true, wordBytes 42, 0)
#guard observe "quoteOr" [dirty, 21, 5] == some (true, wordBytes 7, 0)
#guard observe "quoteOr" [failing, 21, 5] == some (true, wordBytes 5, 0)
#guard observe "quoteOr" [short, 21, 5] == some (false, [], 0)

-- `poke`: the unnamed `bool` result is still validated; the catch clause sees the revert data.
#guard observe "poke" [good] == some (true, wordBytes 1, 2)
#guard observe "poke" [failing] == some (true, wordBytes 102, 2)
#guard observe "poke" [silent] == some (true, wordBytes 100, 2)
#guard observe "poke" [dirty] == some (false, [], 0)

-- `notifyOr`: no return value, so a codeless account reverts uncaught before the call.
#guard observe "notifyOr" [good, 3] == some (true, wordBytes 0, 3)
#guard observe "notifyOr" [dirty, 3] == some (true, wordBytes 0, 3)
#guard observe "notifyOr" [failing, 3] == some (true, wordBytes 1002, 3)
#guard observe "notifyOr" [codeless, 3] == some (false, [], 0)

-- The inlined `void` helper with a catch-all clause.
#guard observe "checkViaHelper" [good, 1] == some (true, [], 4)
#guard observe "checkViaHelper" [failing, 1] == some (false, badReceiver failing, 0)
#guard observe "checkViaHelper" [dirty, 1] == some (false, [], 0)

end SolidityImportSmoke.TryCatchChecks
