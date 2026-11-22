import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
Root functions returning a scalar array lower the same way whatever the state-variable count
(#2830). `RootArrayReturnOneSlot.sol` declares one state variable and `RootArrayReturnTwoSlots.sol`
the same contract plus one unrelated state variable and one unused function.

The calldata-keyed batch slot reads and the range read (`loadSlots`, `loadTransientSlots`,
`loadRange`: the exact blocks `extsloadBatchYulFingerprint`, `exttloadBatchYulFingerprint` and
`extsloadRangeYulFingerprint` select) took their fixed lowerings only with more than one state
variable; with one, the block reached the ordinary assembly lowering and was rejected.
`T[] memory` results were already lowered the same way. `T[] calldata` results were rejected on
both sides with different diagnostics; they now share one located rejection at the return
parameter (`check_storage_rejections.py`, `root-array-return-*-rejected`).

Values: solc 0.8.34 on Anvil (osaka, runs 466), both contracts and both pipelines, from the
storage the constructor leaves (`initial`). Not checked here: `narrowCopied` of a dirty `uint8`
element (`[1, 256]`) returns `[1, 0]` on legacy and reverts on via-IR, while the model reverts on
both (the calldata-to-memory copy, unchanged by #2830).
-/
namespace SolidityImportSmoke.RootArrayReturnStateCountChecks
open Compiler.CompilationModel Denote Verity.Core

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "RootArrayReturnOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract RootArrayReturnOneSlot
  function loadSlots(«bytes32[]»)
  function loadTransientSlots(«bytes32[]»)
  function loadRange(bytes32, uint256)
  function copied(«uint256[]»)
  function narrowCopied(«uint8[]»)
  function fromStorage()
  function built(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "RootArrayReturnTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract RootArrayReturnTwoSlots
  function loadSlots(«bytes32[]»)
  function loadTransientSlots(«bytes32[]»)
  function loadRange(bytes32, uint256)
  function copied(«uint256[]»)
  function narrowCopied(«uint8[]»)
  function fromStorage()
  function built(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "RootArrayReturnOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract RootArrayReturnOneSlot
  function loadSlots(«bytes32[]»)
  function loadTransientSlots(«bytes32[]»)
  function loadRange(bytes32, uint256)
  function copied(«uint256[]»)
  function narrowCopied(«uint8[]»)
  function fromStorage()
  function built(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "RootArrayReturnTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract RootArrayReturnTwoSlots
  function loadSlots(«bytes32[]»)
  function loadTransientSlots(«bytes32[]»)
  function loadRange(bytes32, uint256)
  function copied(«uint256[]»)
  function narrowCopied(«uint8[]»)
  function fromStorage()
  function built(uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

/-- `keccak256(0)`: the first element slot of `items` (slot 0). -/
private def itemsData : Nat :=
  0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563

/-- Storage as the constructor leaves it on both contracts: `items = [7, 9]` (the unrelated
slot 1 of the two-slot contract stays zero). -/
private def initial : Verity.ContractState :=
  ((Verity.defaultState.writePhysicalSlot 0 (Uint256.ofNat 2)).writePhysicalSlot itemsData
    (Uint256.ofNat 7)).writePhysicalSlot (itemsData + 1) (Uint256.ofNat 9)

/-- Status and returned words of `name` on ABI argument words `args`. -/
private def observe (model : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × List Nat) := do
  let fn ← model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle model fn
    { sender := 1, functionSelector := 0, args } initial
  return (r.success, if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords)

/-- `name` reverts on `args`. -/
private def reverts (model : CompilationModel) (name : String) (args : List Nat) : Bool :=
  (observe model name args).map Prod.fst == some false

/-- `name` reverts with `Panic(0x11)` on `args`. -/
private def panics (model : CompilationModel) (name : String) (args : List Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | some fn =>
      let r := denoteFunction SolidityImport.Differential.oracle model fn
        { sender := 1, functionSelector := 0, args } initial
      !r.success && r.revertData == some ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x11])
  | none => false

private def maxWord : Nat := 2 ^ 256 - 1

#guard sameBody oneLegacy.model twoLegacy.model "loadSlots"
#guard sameBody oneLegacy.model twoLegacy.model "loadTransientSlots"
#guard sameBody oneLegacy.model twoLegacy.model "loadRange"
#guard sameBody oneLegacy.model twoLegacy.model "copied"
#guard sameBody oneLegacy.model twoLegacy.model "narrowCopied"
#guard sameBody oneLegacy.model twoLegacy.model "fromStorage"
#guard sameBody oneLegacy.model twoLegacy.model "built"
#guard sameBody oneIr.model twoIr.model "loadSlots"
#guard sameBody oneIr.model twoIr.model "loadTransientSlots"
#guard sameBody oneIr.model twoIr.model "loadRange"
#guard sameBody oneIr.model twoIr.model "copied"
#guard sameBody oneIr.model twoIr.model "narrowCopied"
#guard sameBody oneIr.model twoIr.model "fromStorage"
#guard sameBody oneIr.model twoIr.model "built"

#guard observe oneLegacy.model "loadSlots" [32, 0] == some (true, [32, 0])
#guard observe oneLegacy.model "loadSlots" [32, 1, 0] == some (true, [32, 1, 2])
#guard observe oneLegacy.model "loadSlots" [32, 4, 0, itemsData, itemsData + 1, maxWord] ==
  some (true, [32, 4, 2, 7, 9, 0])
#guard observe oneLegacy.model "loadSlots" [64, 0xdead, 2, itemsData + 1, 1] ==
  some (true, [32, 2, 9, 0])
#guard observe oneLegacy.model "loadTransientSlots" [32, 2, 0, itemsData] ==
  some (true, [32, 2, 0, 0])
#guard observe oneLegacy.model "loadTransientSlots" [32, 0] == some (true, [32, 0])
#guard observe oneLegacy.model "loadRange" [itemsData, 2] == some (true, [32, 2, 7, 9])
#guard observe oneLegacy.model "loadRange" [0, 0] == some (true, [32, 0])
#guard observe oneLegacy.model "loadRange" [maxWord, 2] == some (true, [32, 2, 0, 2])
#guard observe oneLegacy.model "loadRange" [0, 2 ^ 251 + 1] == some (true, [32, 2 ^ 251 + 1, 2])
#guard observe oneLegacy.model "loadRange" [0, maxWord] == some (true, [32])
#guard observe oneLegacy.model "loadRange" [0, 2 ^ 252 - 2] == some (true, [])
#guard observe oneLegacy.model "copied" [32, 3, 1, maxWord, 0] ==
  some (true, [32, 3, 1, maxWord, 0])
#guard observe oneLegacy.model "copied" [32, 0] == some (true, [32, 0])
#guard observe oneLegacy.model "narrowCopied" [32, 2, 255, 0] == some (true, [32, 2, 255, 0])
#guard observe oneLegacy.model "fromStorage" [] == some (true, [32, 2, 7, 9])
#guard observe oneLegacy.model "built" [5] == some (true, [32, 2, 5, 14])
#guard reverts oneLegacy.model "loadSlots" [32, 3, 0]
#guard reverts oneLegacy.model "loadSlots" [32, 2 ^ 64, 0]
#guard reverts oneLegacy.model "loadSlots" [2 ^ 64, 1, 0]
#guard panics oneLegacy.model "built" [maxWord]
#guard observe twoLegacy.model "loadSlots" [32, 0] == some (true, [32, 0])
#guard observe twoLegacy.model "loadSlots" [32, 1, 0] == some (true, [32, 1, 2])
#guard observe twoLegacy.model "loadSlots" [32, 4, 0, itemsData, itemsData + 1, maxWord] ==
  some (true, [32, 4, 2, 7, 9, 0])
#guard observe twoLegacy.model "loadSlots" [64, 0xdead, 2, itemsData + 1, 1] ==
  some (true, [32, 2, 9, 0])
#guard observe twoLegacy.model "loadTransientSlots" [32, 2, 0, itemsData] ==
  some (true, [32, 2, 0, 0])
#guard observe twoLegacy.model "loadTransientSlots" [32, 0] == some (true, [32, 0])
#guard observe twoLegacy.model "loadRange" [itemsData, 2] == some (true, [32, 2, 7, 9])
#guard observe twoLegacy.model "loadRange" [0, 0] == some (true, [32, 0])
#guard observe twoLegacy.model "loadRange" [maxWord, 2] == some (true, [32, 2, 0, 2])
#guard observe twoLegacy.model "loadRange" [0, 2 ^ 251 + 1] == some (true, [32, 2 ^ 251 + 1, 2])
#guard observe twoLegacy.model "loadRange" [0, maxWord] == some (true, [32])
#guard observe twoLegacy.model "loadRange" [0, 2 ^ 252 - 2] == some (true, [])
#guard observe twoLegacy.model "copied" [32, 3, 1, maxWord, 0] ==
  some (true, [32, 3, 1, maxWord, 0])
#guard observe twoLegacy.model "copied" [32, 0] == some (true, [32, 0])
#guard observe twoLegacy.model "narrowCopied" [32, 2, 255, 0] == some (true, [32, 2, 255, 0])
#guard observe twoLegacy.model "fromStorage" [] == some (true, [32, 2, 7, 9])
#guard observe twoLegacy.model "built" [5] == some (true, [32, 2, 5, 14])
#guard reverts twoLegacy.model "loadSlots" [32, 3, 0]
#guard reverts twoLegacy.model "loadSlots" [32, 2 ^ 64, 0]
#guard reverts twoLegacy.model "loadSlots" [2 ^ 64, 1, 0]
#guard panics twoLegacy.model "built" [maxWord]
#guard observe oneIr.model "loadSlots" [32, 0] == some (true, [32, 0])
#guard observe oneIr.model "loadSlots" [32, 1, 0] == some (true, [32, 1, 2])
#guard observe oneIr.model "loadSlots" [32, 4, 0, itemsData, itemsData + 1, maxWord] ==
  some (true, [32, 4, 2, 7, 9, 0])
#guard observe oneIr.model "loadSlots" [64, 0xdead, 2, itemsData + 1, 1] ==
  some (true, [32, 2, 9, 0])
#guard observe oneIr.model "loadTransientSlots" [32, 2, 0, itemsData] == some (true, [32, 2, 0, 0])
#guard observe oneIr.model "loadTransientSlots" [32, 0] == some (true, [32, 0])
#guard observe oneIr.model "loadRange" [itemsData, 2] == some (true, [32, 2, 7, 9])
#guard observe oneIr.model "loadRange" [0, 0] == some (true, [32, 0])
#guard observe oneIr.model "loadRange" [maxWord, 2] == some (true, [32, 2, 0, 2])
#guard observe oneIr.model "loadRange" [0, 2 ^ 251 + 1] == some (true, [32, 2 ^ 251 + 1, 2])
#guard observe oneIr.model "loadRange" [0, maxWord] == some (true, [32])
#guard observe oneIr.model "loadRange" [0, 2 ^ 252 - 2] == some (true, [])
#guard observe oneIr.model "copied" [32, 3, 1, maxWord, 0] == some (true, [32, 3, 1, maxWord, 0])
#guard observe oneIr.model "copied" [32, 0] == some (true, [32, 0])
#guard observe oneIr.model "narrowCopied" [32, 2, 255, 0] == some (true, [32, 2, 255, 0])
#guard observe oneIr.model "fromStorage" [] == some (true, [32, 2, 7, 9])
#guard observe oneIr.model "built" [5] == some (true, [32, 2, 5, 14])
#guard reverts oneIr.model "loadSlots" [32, 3, 0]
#guard reverts oneIr.model "loadSlots" [32, 2 ^ 64, 0]
#guard reverts oneIr.model "loadSlots" [2 ^ 64, 1, 0]
#guard panics oneIr.model "built" [maxWord]
#guard observe twoIr.model "loadSlots" [32, 0] == some (true, [32, 0])
#guard observe twoIr.model "loadSlots" [32, 1, 0] == some (true, [32, 1, 2])
#guard observe twoIr.model "loadSlots" [32, 4, 0, itemsData, itemsData + 1, maxWord] ==
  some (true, [32, 4, 2, 7, 9, 0])
#guard observe twoIr.model "loadSlots" [64, 0xdead, 2, itemsData + 1, 1] ==
  some (true, [32, 2, 9, 0])
#guard observe twoIr.model "loadTransientSlots" [32, 2, 0, itemsData] == some (true, [32, 2, 0, 0])
#guard observe twoIr.model "loadTransientSlots" [32, 0] == some (true, [32, 0])
#guard observe twoIr.model "loadRange" [itemsData, 2] == some (true, [32, 2, 7, 9])
#guard observe twoIr.model "loadRange" [0, 0] == some (true, [32, 0])
#guard observe twoIr.model "loadRange" [maxWord, 2] == some (true, [32, 2, 0, 2])
#guard observe twoIr.model "loadRange" [0, 2 ^ 251 + 1] == some (true, [32, 2 ^ 251 + 1, 2])
#guard observe twoIr.model "loadRange" [0, maxWord] == some (true, [32])
#guard observe twoIr.model "loadRange" [0, 2 ^ 252 - 2] == some (true, [])
#guard observe twoIr.model "copied" [32, 3, 1, maxWord, 0] == some (true, [32, 3, 1, maxWord, 0])
#guard observe twoIr.model "copied" [32, 0] == some (true, [32, 0])
#guard observe twoIr.model "narrowCopied" [32, 2, 255, 0] == some (true, [32, 2, 255, 0])
#guard observe twoIr.model "fromStorage" [] == some (true, [32, 2, 7, 9])
#guard observe twoIr.model "built" [5] == some (true, [32, 2, 5, 14])
#guard reverts twoIr.model "loadSlots" [32, 3, 0]
#guard reverts twoIr.model "loadSlots" [32, 2 ^ 64, 0]
#guard reverts twoIr.model "loadSlots" [2 ^ 64, 1, 0]
#guard panics twoIr.model "built" [maxWord]

-- Both contracts list the same shortcut for the batch reads and none for the other roots.
private def shortcuts (r : SolidityImport.ImportReport) : List (String × List String) :=
  r.functions.map fun st => (st.function, st.shortcuts.map (·.fingerprintName))

#guard shortcuts oneLegacy.report == shortcuts twoLegacy.report
#guard shortcuts oneLegacy.report == [("loadSlots", ["extsloadBatchYulFingerprint"]),
  ("loadTransientSlots", ["exttloadBatchYulFingerprint"]),
  ("loadRange", ["extsloadRangeYulFingerprint"]), ("copied", []), ("narrowCopied", []),
  ("fromStorage", []), ("built", [])]
#guard shortcuts oneIr.report == shortcuts twoIr.report
#guard shortcuts oneIr.report == [("loadSlots", ["extsloadBatchYulFingerprint"]),
  ("loadTransientSlots", ["exttloadBatchYulFingerprint"]),
  ("loadRange", ["extsloadRangeYulFingerprint"]), ("copied", []), ("narrowCopied", []),
  ("fromStorage", []), ("built", [])]

end SolidityImportSmoke.RootArrayReturnStateCountChecks
