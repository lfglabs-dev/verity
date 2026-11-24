import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.SyntheticNarrowYulChecks
open Compiler.CompilationModel

/-! Inline-assembly assignments of dirty words to `bool` / `address` locals and named
results (via-IR). Expected words were observed on anvil with the pinned solc 0.8.34
(via-IR, osaka, 466 runs). -/

solidity_import ir from "Contracts/SolidityImportSmoke" entry "SyntheticNarrowYul.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNarrowYul
  function boolResult(uint256)
  function addressResult(uint256)
  function boolLocalBranch(uint256)
  function boolCompare(uint256,uint256)
  function addressCompare(uint256)
  function storeDirty(uint256,uint256)
  function helperNamedBool(uint256)
  function copiedBool(uint256)

private def run (name : String) (args : List Nat) : Option Denote.DenoteResult := do
  let f ← ir.model.functions.find? (·.name == name)
  return Denote.denoteFunction SolidityImport.Differential.oracle ir.model f
    { sender := 1, functionSelector := 0, args } Verity.defaultState

private def observes (name : String) (args words : List Nat) : Bool :=
  match run name args with
  | some r => r.success && (r.returnWords == words || (words.length == 1 && r.returnValue == words.head?))
  | none => false

private def dirtyAddress : Nat := 0xff * 2 ^ 248 + 0x101

#guard observes "boolResult" [0] [0]
#guard observes "boolResult" [2] [1]
#guard observes "boolResult" [2 ^ 255] [1]
#guard observes "addressResult" [dirtyAddress] [0x101]
#guard observes "boolLocalBranch" [0xff] [2]
#guard observes "boolLocalBranch" [0x100] [1]
#guard observes "boolCompare" [2, 1] [1, 0]
#guard observes "boolCompare" [0, 0] [1, 1]
#guard observes "boolCompare" [0, 5] [0, 1]
#guard observes "addressCompare" [dirtyAddress] [1, 0x101]
#guard observes "storeDirty" [6, dirtyAddress] [1, 0x101]
#guard observes "storeDirty" [0, dirtyAddress + 1] [0, 0x102]
#guard observes "helperNamedBool" [4] [7]
#guard observes "helperNamedBool" [0] [9]
#guard observes "copiedBool" [9] [1]

-- The packed slot holds the cleaned `bool` byte and the cleaned address above it, and the
-- event carries the cleaned words.
#guard match run "storeDirty" [6, dirtyAddress] with
  | some r => r.finalStorage 0 == 0x10101 && r.events == [[1, 0x101]]
  | none => false
#guard match run "helperNamedBool" [4] with
  | some r => r.finalStorage 1 == 1
  | none => false

-- Legacy codegen carries dirty bits through conversions: assignments to `address` locals stay rejected
-- (while `bool` retains the raw stack word under both legacy and via-IR, #2912).
/--
error: SyntheticNarrowYul.sol:43:20: YulAssignment: [solidity-import:unsupported] Yul assignment to narrow local a is unsupported
closure: SyntheticNarrowYul.addressCompare
a := x
-/
#guard_msgs in
solidity_import legacy from "Contracts/SolidityImportSmoke" entry "SyntheticNarrowYul.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNarrowYul
  function addressCompare(uint256)

-- Raw Yul reads of a cleaned `address` local, its copies, or a helper parameter bound to it; in a
-- loop, the accumulator the cleaned word flows into is reported first.
/--
error: SyntheticNarrowYul.sol:85:20: YulIdentifier: [solidity-import:unsupported] Yul read of a narrow local assigned a possibly dirty word in Yul is unsupported
closure: SyntheticNarrowYulUnsupported.readBack
a
-/
#guard_msgs in
solidity_import readBack from "Contracts/SolidityImportSmoke" entry "SyntheticNarrowYul.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNarrowYulUnsupported
  function readBack(uint256)

/--
error: SyntheticNarrowYul.sol:93:27: YulIdentifier: [solidity-import:unsupported] Yul read of a narrow local assigned a possibly dirty word in Yul is unsupported
closure: SyntheticNarrowYulUnsupported.readCopyLater
copy
-/
#guard_msgs in
solidity_import readCopyLater from "Contracts/SolidityImportSmoke" entry "SyntheticNarrowYul.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNarrowYulUnsupported
  function readCopyLater(uint256)

/--
error: SyntheticNarrowYul.sol:97:27: YulIdentifier: [solidity-import:unsupported] Yul read of a narrow local assigned a possibly dirty word in Yul is unsupported
closure: SyntheticNarrowYulUnsupported.readThroughHelper
b
-/
#guard_msgs in
solidity_import readThroughHelper from "Contracts/SolidityImportSmoke" entry "SyntheticNarrowYul.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNarrowYulUnsupported
  function readThroughHelper(uint256)

/--
error: SyntheticNarrowYul.sol:110:28: YulIdentifier: [solidity-import:unsupported] Yul read of a narrow local assigned a possibly dirty word in Yul is unsupported
closure: SyntheticNarrowYulUnsupported.readInLoop
raw
-/
#guard_msgs in
solidity_import readInLoop from "Contracts/SolidityImportSmoke" entry "SyntheticNarrowYul.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNarrowYulUnsupported
  function readInLoop(uint256)

end SolidityImportSmoke.SyntheticNarrowYulChecks
