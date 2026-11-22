import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-! `abi.encodeCall` with a `bytes` parameter does not depend on the state-variable count (#2830).

`EncodeCallBytesOneSlot` declares one state variable and `EncodeCallBytesTwoSlots` is the same
contract plus an unrelated `uint256` and an unused function. Every function imports to the same
body from both, on both solc pipelines, and its denotation matches solc 0.8.34 on Anvil (osaka,
runs 466; legacy and via-IR, both contracts, from empty storage): the selector followed by the
arguments ABI-encoded against the declared parameter types, for empty, 31-, 32-, 33- and 74-byte
literal, memory, helper, calldata and storage `bytes`, beside static and dynamic siblings. Before
this change the one-slot contract rejected every function and the two-slot contract encoded the
buffer's memory pointer and size as two words. -/

namespace SolidityImportSmoke.EncodeCallBytesStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "EncodeCallBytesOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EncodeCallBytesOneSlot
  function literalEmpty()
  function literalLong()
  function memoryArg(uint256)
  function memoryLength(uint256)
  function helperArg(uint256)
  function calldataArg(bytes)
  function storageArg(uint256)
  function staticSiblings(uint256,bytes,address)
  function dynamicSiblings(bytes,uint256,uint256)
  function helperRevert(uint256,uint256)
  function returned(uint256)

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "EncodeCallBytesTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EncodeCallBytesTwoSlots
  function literalEmpty()
  function literalLong()
  function memoryArg(uint256)
  function memoryLength(uint256)
  function helperArg(uint256)
  function calldataArg(bytes)
  function storageArg(uint256)
  function staticSiblings(uint256,bytes,address)
  function dynamicSiblings(bytes,uint256,uint256)
  function helperRevert(uint256,uint256)
  function returned(uint256)

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "EncodeCallBytesOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EncodeCallBytesOneSlot
  function literalEmpty()
  function literalLong()
  function memoryArg(uint256)
  function memoryLength(uint256)
  function helperArg(uint256)
  function calldataArg(bytes)
  function storageArg(uint256)
  function staticSiblings(uint256,bytes,address)
  function dynamicSiblings(bytes,uint256,uint256)
  function helperRevert(uint256,uint256)
  function returned(uint256)

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "EncodeCallBytesTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EncodeCallBytesTwoSlots
  function literalEmpty()
  function literalLong()
  function memoryArg(uint256)
  function memoryLength(uint256)
  function helperArg(uint256)
  function calldataArg(bytes)
  function storageArg(uint256)
  function staticSiblings(uint256,bytes,address)
  function dynamicSiblings(bytes,uint256,uint256)
  function helperRevert(uint256,uint256)
  function returned(uint256)

private def body (model : CompilationModel) (name : String) : String :=
  match model.functions.find? (·.name == name) with
  | some f => (repr f.body).pretty 100000
  | none => ""

/-- The function imports and its body does not depend on the unrelated slot. -/
private def sameBody (one two : CompilationModel) (name : String) : Bool :=
  body one name != "" && body one name == body two name

private def run (model : CompilationModel) (name : String) (args : List Nat) :
    Option Denote.DenoteResult :=
  (model.functions.find? (·.name == name)).map fun f =>
    Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState

private def allModels : List CompilationModel :=
  [oneLegacy.model, twoLegacy.model, oneIr.model, twoIr.model]

private def returns (model : CompilationModel) (name : String) (args : List Nat) (n : Nat) : Bool :=
  match run model name args with
  | some r => r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

/-- A `bytes` result: the offset word, the length, then the zero-padded data words. -/
private def returnsWords (model : CompilationModel) (name : String) (args : List Nat)
    (words : List Nat) : Bool :=
  match run model name args with
  | some r => r.success && r.returnWords == words
  | none => false

/-- solc reverts with `Rejected(code)` (selector `0x94064f91`). -/
private def rejected (model : CompilationModel) (name : String) (args : List Nat) (code : Nat) :
    Bool :=
  match run model name args with
  | some r => !r.success && r.revertData == some ([0x94, 0x06, 0x4f, 0x91] ++ List.replicate 31 0 ++ [code.toUInt8])
  | none => false

#guard sameBody oneLegacy.model twoLegacy.model "literalEmpty"
#guard sameBody oneLegacy.model twoLegacy.model "literalLong"
#guard sameBody oneLegacy.model twoLegacy.model "memoryArg"
#guard sameBody oneLegacy.model twoLegacy.model "memoryLength"
#guard sameBody oneLegacy.model twoLegacy.model "helperArg"
#guard sameBody oneLegacy.model twoLegacy.model "calldataArg"
#guard sameBody oneLegacy.model twoLegacy.model "storageArg"
#guard sameBody oneLegacy.model twoLegacy.model "staticSiblings"
#guard sameBody oneLegacy.model twoLegacy.model "dynamicSiblings"
#guard sameBody oneLegacy.model twoLegacy.model "helperRevert"
#guard sameBody oneLegacy.model twoLegacy.model "returned"
#guard sameBody oneIr.model twoIr.model "literalEmpty"
#guard sameBody oneIr.model twoIr.model "literalLong"
#guard sameBody oneIr.model twoIr.model "memoryArg"
#guard sameBody oneIr.model twoIr.model "memoryLength"
#guard sameBody oneIr.model twoIr.model "helperArg"
#guard sameBody oneIr.model twoIr.model "calldataArg"
#guard sameBody oneIr.model twoIr.model "storageArg"
#guard sameBody oneIr.model twoIr.model "staticSiblings"
#guard sameBody oneIr.model twoIr.model "dynamicSiblings"
#guard sameBody oneIr.model twoIr.model "helperRevert"
#guard sameBody oneIr.model twoIr.model "returned"

#guard allModels.all (returns · "literalEmpty" [] 0xb754ebc0eb6ddc3cae0db7f8ad933c361ebf7363c7bd11bb5d66c5387afd15f6)
#guard allModels.all (returns · "literalLong" [] 0x3767e548adb478e85291b49e1810cfea49da7f56d7a0a4581ce3b9030b5368d9)
#guard allModels.all (returns · "memoryArg" [0] 0xb754ebc0eb6ddc3cae0db7f8ad933c361ebf7363c7bd11bb5d66c5387afd15f6)
#guard allModels.all (returns · "memoryArg" [1] 0xc8e54e28cff73e8e1a440031c0ccee62fec871f105ebc21cd55585a67e368423)
#guard allModels.all (returns · "memoryArg" [2] 0xcda70f95264b60841b062ce185cd13596f21aa7d89a5fec3fcefae298d197b3e)
#guard allModels.all (returns · "memoryArg" [3] 0xfb59a82d8bcd11ff1246016717ace638ea41008a890f915a8d0848aed14c0bf1)
#guard allModels.all (returns · "memoryArg" [4] 0x3767e548adb478e85291b49e1810cfea49da7f56d7a0a4581ce3b9030b5368d9)
#guard allModels.all (returns · "memoryLength" [0] 68)
#guard allModels.all (returns · "memoryLength" [3] 132)
#guard allModels.all (returns · "memoryLength" [4] 164)
#guard allModels.all (returns · "helperArg" [3] 0xfb59a82d8bcd11ff1246016717ace638ea41008a890f915a8d0848aed14c0bf1)
#guard allModels.all (returns · "calldataArg" [32, 0] 0xb754ebc0eb6ddc3cae0db7f8ad933c361ebf7363c7bd11bb5d66c5387afd15f6)
#guard allModels.all (returns · "calldataArg" [32, 5, 455867356318211655669198171616910294656723054863879369520075368192163184640] 0x5f2e2c62c2d54eaa9f26cf26cc2a73df0a0bed9332ca38e6a486050da2dccd3d)
#guard allModels.all (returns · "storageArg" [1] 0xc8e54e28cff73e8e1a440031c0ccee62fec871f105ebc21cd55585a67e368423)
#guard allModels.all (returns · "storageArg" [4] 0x3767e548adb478e85291b49e1810cfea49da7f56d7a0a4581ce3b9030b5368d9)
#guard allModels.all (returns · "staticSiblings" [7, 96, 170, 3, 77224992616523589168109820555166644084464138706973000561478295394838187606016] 0x779a30695e9eaa856c28a8a31331ee172dd24067713a92914a1eb38c8e1f60c)
#guard allModels.all (returns · "dynamicSiblings" [96, 9, 4, 3, 77224992616523589168109820555166644084464138706973000561478295394838187606016] 0x140a3a08ec55474d7968079cd5d93387ecd2efff12044bb6332695ffb134ef39)
#guard allModels.all (rejected · "helperRevert" [2, 5] 2)
#guard allModels.all (returns · "helperRevert" [3, 5] 0xbfec6e83d67d8f80ebf10869456cae40f87ca167c6dc75deecd9f7531349c769)
#guard allModels.all (returnsWords · "returned" [3] [0x20, 0x84, 0xcce9195700000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000000000000000000000000000000000, 0x2130313233343536373839616263646566303132333435363738396162, 0x6364656630000000000000000000000000000000000000000000000000000000, 0x0])
#guard allModels.all (rejected · "helperRevert" [0, 5] 2)
#guard allModels.all (returnsWords · "returned" [0] [0x20, 0x44, 0xcce9195700000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000000000000000000000000000000000, 0x0])
#guard allModels.all (returnsWords · "returned" [4] [0x20, 0xa4, 0xcce9195700000000000000000000000000000000000000000000000000000000, 0x2000000000000000000000000000000000000000000000000000000000, 0x4a30313233343536373839616263646566303132333435363738396162, 0x6364656630313233343536373839616263646566303132333435363738396162, 0x6364656630313233343536373839000000000000000000000000000000000000, 0x0])

end SolidityImportSmoke.EncodeCallBytesStateCountChecks
