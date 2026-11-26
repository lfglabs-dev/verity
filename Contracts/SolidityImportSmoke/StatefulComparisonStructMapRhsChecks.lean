import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.AdversarialEntryPointInvariants
import Compiler.CompilationModel.TrustSurface

/-!
Smoke, trust-surface/CEI, Denote execution, and near-miss checks for stateful external,
internal, and linked-library calls in binary comparisons (`==`, `!=`, `<`, `<=`, `>`, `>=`)
and storage-struct mapping element writes (`s.map[k] = rhs`) (#2976).
-/
namespace SolidityImportSmoke.StatefulComparisonStructMapRhsChecks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.ByteExternalCall

solidity_import rhsIr from "Contracts/SolidityImportSmoke"
  entry "StatefulComparisonStructMapRhs.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := true }
  contract StatefulComparisonStructMapRhs
  function assertDeployMatch(address,bytes,address)
  function compareCallAndState(address,uint256,uint256,address)
  function setDirectKeyInternal(address,bytes32,bytes32,bytes)
  function setComputedKeyLinked(address,bytes32,address,bytes4,uint256)
  function setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)
  function setReentrantStorageKeys(address,bytes4,uint256)
  function reenterMutate(bytes32,address,uint256)

solidity_import rhsLegacy from "Contracts/SolidityImportSmoke"
  entry "StatefulComparisonStructMapRhs.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := true }
  contract StatefulComparisonStructMapRhs
  function assertDeployMatch(address,bytes,address)
  function compareCallAndState(address,uint256,uint256,address)
  function setDirectKeyInternal(address,bytes32,bytes32,bytes)
  function setComputedKeyLinked(address,bytes32,address,bytes4,uint256)
  function setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)
  function setReentrantStorageKeys(address,bytes4,uint256)
  function reenterMutate(bytes32,address,uint256)

-- Kernel coverage theorems hold on both pipelines.
example := rhsIr.covered
example := rhsLegacy.covered

private def flags (model : CompilationModel) (name : String) :
    Option (Bool × Bool × Bool × List String) :=
  (model.functions.find? (·.name == name)).map fun f =>
    (f.allowPostInteractionWrites, f.reentrancyTrusted, f.reentrancyAdversarial,
      f.localObligations.map (·.name))

-- Barrier / CEI preservation:
-- 1. `assertDeployMatch` has a trailing CALL inside `assert(pointer == deployWord(...))` with no
--    post-call storage read, write or log -> `reentrancyTrusted = true`, `reentrancyAdversarial = false`.
#guard flags rhsIr.model "assertDeployMatch" ==
  some (false, true, false, ["solidity_explicit_abi", "solidity_trailing_low_level_call_reentrancy"])
#guard flags rhsLegacy.model "assertDeployMatch" ==
  some (false, true, false, ["solidity_explicit_abi", "solidity_trailing_low_level_call_reentrancy"])

-- 2. Struct-mapping RHS writes with external CALLs open the post-CALL state window:
--    `allowPostInteractionWrites = true`, `reentrancyTrusted = false`, `reentrancyAdversarial = true`.
#guard flags rhsIr.model "setDirectKeyInternal" ==
  some (true, false, true, ["solidity_explicit_abi", "solidity_post_call_state_access"])
#guard flags rhsIr.model "setComputedKeyLinked" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_post_call_state_access",
   "solidity_linked_library_matches_source"])
#guard flags rhsIr.model "setSideEffectKeysOrder" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_post_call_state_access",
   "solidity_linked_library_matches_source"])
#guard flags rhsIr.model "setReentrantStorageKeys" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_post_call_state_access",
   "solidity_linked_library_matches_source"])
#guard flags rhsLegacy.model "setComputedKeyLinked" == some (true, false, true,
  ["solidity_scalar_abi_entry", "solidity_post_call_state_access",
   "solidity_linked_library_matches_source"])

-- 3. `reenterMutate` makes no external call: no CEI opt-out or reentrancy flag.
#guard flags rhsIr.model "reenterMutate" ==
  some (false, false, false, ["solidity_scalar_abi_entry"])

private def self : Nat := 0xc0ffee
private def user : Nat := 0x1111
private def callee : Nat := 0x7a11
private def gas : Nat := 30000000

private def world0 : Verity.ContractState :=
  { Verity.defaultState with
    accountWorld := Verity.Core.AccountWorld.write Verity.Core.AccountWorld.empty
      (Verity.Core.Address.ofNat callee) { code := [0] } }

private def runFn (model : CompilationModel) (name : String) (args : List Nat)
    (world : Verity.ContractState) (byteCalls : Denote.ByteCallEnvironment) :
    Option (Bool × List UInt8 × Verity.ContractState) :=
  match model.functions.find? (·.name == name) with
  | none => none
  | some fn =>
      let tx : Denote.DenoteTransaction :=
        { sender := user, txOrigin := user, thisAddress := self, functionSelector := 0, args }
      let initial := Transactions.beginTransaction (Denote.withTransactionContext world tx)
      match Denote.bindExternalParams 0 fn.bindingParams args with
      | none => some (false, [], world)
      | some bindings =>
          match Transactions.executeBody Differential.oracle (Denote.effectiveFields model)
              initial bindings fn.body model.errors byteCalls with
          | .ok r => some (r.success, r.data, r.world)
          | .error _ => none

private def wordResponder (retWord : Nat) : Denote.ByteCallEnvironment :=
  { gas := some gas
    adversary := some
      { respond := fun request world =>
          if request.kind = .call then .success world (Denote.wordBytes retWord) []
          else .success world [] []
        valid := by
          intro request world
          by_cases h : request.kind = .call <;> simp [h, Response.valid] } }

private def revertResponder (payload : List UInt8) : Denote.ByteCallEnvironment :=
  { gas := some gas
    adversary := some
      { respond := fun request world =>
          if request.kind = .call then .revert payload [] else .success world [] []
        valid := by
          intro request world
          by_cases h : request.kind = .call <;> simp [h, Response.valid] } }

-- Pipeline evaluation order in Denote:
-- mode 0 (`stored == _stepWord(2, 9, 5)` with initial `stored = 5`):
-- via-IR evaluates left first (`5 == 5` -> 100009); legacy evaluates right first (`9 == 5` -> 9).
#guard (runFn rhsIr.model "compareCallAndState" [callee, 0, 0, 0] world0
  (wordResponder 0)).map (fun (ok, d, _) => (ok, d)) ==
  some (true, Denote.wordBytes 100009)
#guard (runFn rhsLegacy.model "compareCallAndState" [callee, 0, 0, 0] world0
  (wordResponder 0)).map (fun (ok, d, _) => (ok, d)) ==
  some (true, Denote.wordBytes 9)

-- mode 1 (`_stepWord(1, 9, 5) == stored` with initial `stored = 5`):
-- via-IR evaluates left first (`5 == 9` -> 9); legacy evaluates right first (`5 == 5` -> 100009).
#guard (runFn rhsIr.model "compareCallAndState" [callee, 1, 0, 0] world0
  (wordResponder 0)).map (fun (ok, d, _) => (ok, d)) ==
  some (true, Denote.wordBytes 9)
#guard (runFn rhsLegacy.model "compareCallAndState" [callee, 1, 0, 0] world0
  (wordResponder 0)).map (fun (ok, d, _) => (ok, d)) ==
  some (true, Denote.wordBytes 100009)

-- mode 5 (`address(uint160(100 / 0)) == deployWord(reverting)`):
-- via-IR panics with 0x12 before the call; legacy runs the call and bubbles `[0xde, 0xad]`.
private def panicDivZero : List UInt8 := [0x4e, 0x48, 0x7b, 0x71] ++ Denote.wordBytes 0x12

#guard (runFn rhsIr.model "compareCallAndState" [callee, 5, 0, 0] world0
  (revertResponder [0xde, 0xad])).map (fun (ok, d, _) => (ok, d)) ==
  some (false, panicDivZero)
#guard (runFn rhsLegacy.model "compareCallAndState" [callee, 5, 0, 0] world0
  (revertResponder [0xde, 0xad])).map (fun (ok, d, _) => (ok, d)) ==
  some (false, [0xde, 0xad])

end SolidityImportSmoke.StatefulComparisonStructMapRhsChecks
