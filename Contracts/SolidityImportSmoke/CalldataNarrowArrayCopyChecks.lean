import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
A narrow `T[] calldata` array copied to memory: returned as `T[] memory` (alone or in a tuple,
`lowerDynamicTupleReturn`) and passed to a `T[] memory` helper (`bindHelperParams`). solc 0.8.34's
legacy pipeline cleans each element of the copy (`uint8` / `uint64` / `address` masked, `bool`
`iszero(iszero(x))`, `bytes4` low bytes cleared); via-IR reverts with empty data, as every ABI
decoder does. The model used to validate on both pipelines, so a legacy import reverted where solc
returned. `CalldataNarrowArrayCopySolc0810Sequence` runs the legacy side through the stateful
A/B/C harness (solc 0.8.10); this table pins the 0.8.34 legacy values the harness does not run.

Values: solc 0.8.34 on Anvil (osaka, runs 466), both pipelines, `eth_call` on a freshly deployed
`CalldataNarrowArrayCopySequence` (zero storage).
-/
namespace SolidityImportSmoke.CalldataNarrowArrayCopyChecks
open Compiler.CompilationModel Denote Verity.Core

solidity_import legacy from "Contracts/SolidityImportSmoke" entry "CalldataNarrowArrayCopySequence.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function keepNarrow(«uint8[]»)
  function keepWide(«uint64[]»)
  function keepAddrs(«address[]»)
  function keepFlags(«bool[]»)
  function keepSelectors(«bytes4[]»)
  function weighOnly(«uint8[]»)
  function passFlags(«bool[]»)

solidity_import ir from "Contracts/SolidityImportSmoke" entry "CalldataNarrowArrayCopySequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function keepNarrow(«uint8[]»)
  function keepWide(«uint64[]»)
  function keepAddrs(«address[]»)
  function keepFlags(«bool[]»)
  function keepSelectors(«bytes4[]»)
  function weighOnly(«uint8[]»)
  function passFlags(«bool[]»)

/-- Status and returned words of `name` on ABI argument words `args`, from zero storage. -/
private def observe (model : CompilationModel) (name : String) (args : List Nat) :
    Option (Bool × List Nat) := do
  let fn ← model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle model fn
    { sender := 1, functionSelector := 0, args } Verity.defaultState
  return (r.success, if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords)

/-- `name` reverts on `args` with empty data. -/
private def revertsEmpty (model : CompilationModel) (name : String) (args : List Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | some fn =>
      let r := denoteFunction SolidityImport.Differential.oracle model fn
        { sender := 1, functionSelector := 0, args } Verity.defaultState
      !r.success && r.revertData == some []
  | none => false

private def maxWord : Nat := 2 ^ 256 - 1

#guard observe legacy.model "keepNarrow" [32, 0] == some (true, [32, 0])
#guard observe legacy.model "keepNarrow" [32, 3, 7, 0, 255] == some (true, [32, 3, 7, 0, 255])
#guard observe legacy.model "keepNarrow" [32, 3, 1, 256, 3] == some (true, [32, 3, 1, 0, 3])
#guard observe legacy.model "keepNarrow" [32, 2, 1, maxWord] == some (true, [32, 2, 1, 255])
#guard observe legacy.model "keepWide" [32, 2, 5, (2 ^ 64 - 1)] == some (true, [2, 64, 2, 5, (2 ^ 64 - 1)])
#guard observe legacy.model "keepWide" [32, 3, 1, 2 ^ 64, 9] == some (true, [3, 64, 3, 1, 0, 9])
#guard observe legacy.model "keepWide" [32, 1, (2 ^ 64 + 7)] == some (true, [1, 64, 1, 7])
#guard observe legacy.model "keepAddrs" [32, 2, 4660, (2 ^ 160 - 1)] == some (true, [32, 2, 4660, (2 ^ 160 - 1)])
#guard observe legacy.model "keepAddrs" [32, 2, 4660, (2 ^ 160 + 0x55)] == some (true, [32, 2, 4660, 85])
#guard observe legacy.model "keepFlags" [32, 3, 1, 0, 1] == some (true, [64, 3, 3, 1, 0, 1])
#guard observe legacy.model "keepFlags" [32, 3, 1, 2, 0] == some (true, [64, 3, 3, 1, 1, 0])
#guard observe legacy.model "keepFlags" [32, 1, maxWord] == some (true, [64, 1, 1, 1])
#guard observe legacy.model "keepSelectors" [32, 2, 0x11223344 * 2 ^ 224, 0xdeadbeef * 2 ^ 224] == some (true, [32, 2, 0x11223344 * 2 ^ 224, 0xdeadbeef * 2 ^ 224])
#guard observe legacy.model "keepSelectors" [32, 2, 0x11223344 * 2 ^ 224, (0xdeadbeef * 2 ^ 224 + 1)] == some (true, [32, 2, 0x11223344 * 2 ^ 224, 0xdeadbeef * 2 ^ 224])
#guard observe legacy.model "keepSelectors" [32, 1, (2 ^ 224 - 1)] == some (true, [32, 1, 0])
#guard observe legacy.model "weighOnly" [32, 2, 3, 4] == some (true, [11])
#guard observe legacy.model "weighOnly" [32, 2, 3, 260] == some (true, [11])
#guard observe legacy.model "passFlags" [32, 2, 0, 1] == some (true, [32, 2, 0, 1])
#guard observe legacy.model "passFlags" [32, 2, 1, 3] == some (true, [32, 2, 1, 1])
#guard observe ir.model "keepNarrow" [32, 0] == some (true, [32, 0])
#guard observe ir.model "keepNarrow" [32, 3, 7, 0, 255] == some (true, [32, 3, 7, 0, 255])
#guard revertsEmpty ir.model "keepNarrow" [32, 3, 1, 256, 3]
#guard revertsEmpty ir.model "keepNarrow" [32, 2, 1, maxWord]
#guard observe ir.model "keepWide" [32, 2, 5, (2 ^ 64 - 1)] == some (true, [2, 64, 2, 5, (2 ^ 64 - 1)])
#guard revertsEmpty ir.model "keepWide" [32, 3, 1, 2 ^ 64, 9]
#guard revertsEmpty ir.model "keepWide" [32, 1, (2 ^ 64 + 7)]
#guard observe ir.model "keepAddrs" [32, 2, 4660, (2 ^ 160 - 1)] == some (true, [32, 2, 4660, (2 ^ 160 - 1)])
#guard revertsEmpty ir.model "keepAddrs" [32, 2, 4660, (2 ^ 160 + 0x55)]
#guard observe ir.model "keepFlags" [32, 3, 1, 0, 1] == some (true, [64, 3, 3, 1, 0, 1])
#guard revertsEmpty ir.model "keepFlags" [32, 3, 1, 2, 0]
#guard revertsEmpty ir.model "keepFlags" [32, 1, maxWord]
#guard observe ir.model "keepSelectors" [32, 2, 0x11223344 * 2 ^ 224, 0xdeadbeef * 2 ^ 224] == some (true, [32, 2, 0x11223344 * 2 ^ 224, 0xdeadbeef * 2 ^ 224])
#guard revertsEmpty ir.model "keepSelectors" [32, 2, 0x11223344 * 2 ^ 224, (0xdeadbeef * 2 ^ 224 + 1)]
#guard revertsEmpty ir.model "keepSelectors" [32, 1, (2 ^ 224 - 1)]

#guard observe ir.model "weighOnly" [32, 2, 3, 4] == some (true, [11])
#guard revertsEmpty ir.model "weighOnly" [32, 2, 3, 260]
#guard observe ir.model "passFlags" [32, 2, 0, 1] == some (true, [32, 2, 0, 1])
#guard revertsEmpty ir.model "passFlags" [32, 2, 1, 3]

end SolidityImportSmoke.CalldataNarrowArrayCopyChecks
