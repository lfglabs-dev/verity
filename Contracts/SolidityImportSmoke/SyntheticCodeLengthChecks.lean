import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.SyntheticCodeLengthChecks
open Compiler.CompilationModel

/-! Emptiness tests of the executing contract's own code. The read is `EXTCODESIZE(ADDRESS())`
through the closed code-length transport, so the answer depends on the account world. With no
code at the executing account (construction, or a delegatecall from a constructor) every test
reports "constructing"; with code deployed there (any runtime call) none does. -/

solidity_import imported from "Contracts/SolidityImportSmoke" entry "SyntheticCodeLength.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticCodeLength
  function isConstructing()
  function hasCode()
  function mirrored()
  function «initialize»(uint256)
  function guarded(uint256)

private def self : Verity.Address := Verity.defaultState.thisAddress

/-- The default world (no code at the executing account), or that world with a one-byte
runtime code installed at it, plus an initial storage. -/
private def world (deployed : Bool) (storage : Nat → Nat) : Verity.ContractState :=
  let base := Verity.defaultState.withStorageWords fun
    | .slot i => Verity.Core.Uint256.ofNat (storage i)
    | _ => 0
  if deployed then base.writeAccount self { base.accountWorld self with code := [0] } else base

private def run (name : String) (args : List Nat) (deployed : Bool)
    (storage : Nat → Nat := fun _ => 0) : Option Denote.DenoteResult := do
  let f ← imported.model.functions.find? (·.name == name)
  return Denote.denoteFunction SolidityImport.Differential.oracle imported.model f
    { sender := 1, functionSelector := 0, args } (world deployed storage)

private def observes (name : String) (args : List Nat) (deployed : Bool) (words : List Nat) :
    Bool :=
  match run name args deployed with
  | some r => r.success && (r.returnWords == words ||
      (words.length == 1 && r.returnValue == words.head?))
  | none => false

-- Deployed: the code is nonempty.
#guard observes "isConstructing" [] true [0]
#guard observes "hasCode" [] true [1, 1, 1]
#guard observes "mirrored" [] true [0, 0]
-- No code at the executing account: the code is empty.
#guard observes "isConstructing" [] false [1]
#guard observes "hasCode" [] false [0, 0, 0]
#guard observes "mirrored" [] false [1, 1]

-- The initializer guard: a second initialization reverts once code is deployed, and is
-- allowed while the executing account has no code.
#guard match run "initialize" [5] true (fun slot => if slot == 0 then 3 else 0) with
  | some r => !r.success
  | none => false
#guard match run "initialize" [5] false (fun slot => if slot == 0 then 3 else 0) with
  | some r => r.success && r.finalStorage 0 == 5
  | none => false
#guard match run "initialize" [5] true with
  | some r => r.success && r.finalStorage 0 == 5
  | none => false
-- `require(address(this).code.length != 0, ...)`.
#guard match run "guarded" [4] true (fun slot => if slot == 0 then 3 else 0) with
  | some r => r.success && r.returnWords == [7] && r.finalStorage 0 == 7
  | none => false
#guard match run "guarded" [4] false with
  | some r => !r.success
  | none => false

-- The length value itself, tests against other constants and aliases stay rejected.
/--
error: SyntheticCodeLength.sol:46:16: MemberAccess: [solidity-import:unsupported] code length of the executing contract is unsupported
closure: SyntheticCodeLengthUnsupported.selfLength
address(this).code
-/
#guard_msgs in
solidity_import selfLength from "Contracts/SolidityImportSmoke" entry "SyntheticCodeLength.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticCodeLengthUnsupported
  function selfLength()

/--
error: SyntheticCodeLength.sol:50:16: MemberAccess: [solidity-import:unsupported] code length of the executing contract is unsupported
closure: SyntheticCodeLengthUnsupported.selfLengthCompare
address(this).code
-/
#guard_msgs in
solidity_import selfLengthCompare from "Contracts/SolidityImportSmoke" entry "SyntheticCodeLength.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticCodeLengthUnsupported
  function selfLengthCompare()

/--
error: SyntheticCodeLength.sol:55:16: MemberAccess: [solidity-import:unsupported] code length of an account that may be the executing contract is unsupported
closure: SyntheticCodeLengthUnsupported.selfAlias
self.code
-/
#guard_msgs in
solidity_import selfAlias from "Contracts/SolidityImportSmoke" entry "SyntheticCodeLength.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticCodeLengthUnsupported
  function selfAlias()

end SolidityImportSmoke.SyntheticCodeLengthChecks
