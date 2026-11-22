import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.StorageMappingArgumentStateCountChecks
open Compiler.CompilationModel

solidity_import oneLegacy from "Contracts/SolidityImportSmoke" entry "StorageMappingArgumentOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract StorageMappingArgumentOneSlot
  function deposit(uint256,address,uint256)
  function forwarded(uint256,address,uint256)
  function cleared(uint256,address)
  function aliased(uint256,address)
  function shifted(uint256,uint256,int256)
  function entry(uint256,uint256,uint256)
  function signedKey(uint256,int8,uint256)
  function packedEntry(uint256,uint256,uint128,uint64)
  function pointer(uint256,address,uint256)
  function keyOrder(uint256,address)
  function slotOfMember(uint256)
  function rawSlot(address,uint256)
  function rawSlotOf()

solidity_import twoLegacy from "Contracts/SolidityImportSmoke" entry "StorageMappingArgumentTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract StorageMappingArgumentTwoSlots
  function deposit(uint256,address,uint256)
  function forwarded(uint256,address,uint256)
  function cleared(uint256,address)
  function aliased(uint256,address)
  function shifted(uint256,uint256,int256)
  function entry(uint256,uint256,uint256)
  function signedKey(uint256,int8,uint256)
  function packedEntry(uint256,uint256,uint128,uint64)
  function pointer(uint256,address,uint256)
  function keyOrder(uint256,address)
  function slotOfMember(uint256)
  function rawSlot(address,uint256)
  function rawSlotOf()

solidity_import oneIr from "Contracts/SolidityImportSmoke" entry "StorageMappingArgumentOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract StorageMappingArgumentOneSlot
  function deposit(uint256,address,uint256)
  function forwarded(uint256,address,uint256)
  function cleared(uint256,address)
  function aliased(uint256,address)
  function shifted(uint256,uint256,int256)
  function entry(uint256,uint256,uint256)
  function signedKey(uint256,int8,uint256)
  function packedEntry(uint256,uint256,uint128,uint64)
  function pointer(uint256,address,uint256)
  function keyOrder(uint256,address)
  function slotOfMember(uint256)
  function rawSlot(address,uint256)
  function rawSlotOf()

solidity_import twoIr from "Contracts/SolidityImportSmoke" entry "StorageMappingArgumentTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract StorageMappingArgumentTwoSlots
  function deposit(uint256,address,uint256)
  function forwarded(uint256,address,uint256)
  function cleared(uint256,address)
  function aliased(uint256,address)
  function shifted(uint256,uint256,int256)
  function entry(uint256,uint256,uint256)
  function signedKey(uint256,int8,uint256)
  function packedEntry(uint256,uint256,uint128,uint64)
  function pointer(uint256,address,uint256)
  function keyOrder(uint256,address)
  function slotOfMember(uint256)
  function rawSlot(address,uint256)
  function rawSlotOf()

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

private def maxWord : Nat := 2 ^ 256 - 1
private def who : Nat := 0xaa

/-- solc 0.8.34 on Anvil (osaka, runs 466), both pipelines and both contracts, from empty
storage: deposit(1, who, 5) = 5055, deposit(7, who, 0) = 0, forwarded(1, who, 5) = 6,
cleared(1, who) = 0, aliased(1, who) = 1212, shifted(1, 2, -7) = -7, entry(1, 2, 3) = 30044,
signedKey(1, -3, 4) = 44, pointer(1, who, 5) = 55, keyOrder(3, who) = 43,
slotOfMember(1) = keccak256(1 . 0) + 1, slotOfMember(0) = keccak256(0 . 0) + 1,
rawSlot(who, 5) = 55, rawSlotOf() = 0x1235, packedEntry(1, 2, 7, 9) = 9000007009879,
packedEntry(3, 4, 2^128 - 1, 5) = (2^128 - 1) * 10^6 + 5879 + 5 * 10^12. -/
private def returns (model : CompilationModel) (name : String) (args : List Nat) (n : Nat) : Bool :=
  match run model name args with
  | some r => r.success && (r.returnWords == [n] || (r.returnWords.isEmpty && r.returnValue == some n))
  | none => false

/-- solc 0.8.34 on Anvil: deposit(1, who, 2^256 - 1) (`r * 1000`), forwarded(1, who,
2^256 - 1) (`r + 1`) and entry(1, 2, 2^256 - 1) (`v + 1` in the helper) revert with
`Panic(0x11)`, as does packedEntry(3, 4, 2^128 - 1, 2^64 - 1) (checked `uint64` `b * 1000`). -/
private def panics (model : CompilationModel) (name : String) (args : List Nat) : Bool :=
  match run model name args with
  | some r => !r.success && r.revertData == some ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x11])
  | none => false

private def slotOfOne : Nat :=
  78541660797044910968829902406342334108369226379826116161446442989268089806462
private def slotOfZero : Nat :=
  78338746147236970124700731725183845421594913511827187288591969170390706184118

#guard sameBody oneLegacy.model twoLegacy.model "deposit"
#guard sameBody oneLegacy.model twoLegacy.model "forwarded"
#guard sameBody oneLegacy.model twoLegacy.model "cleared"
#guard sameBody oneLegacy.model twoLegacy.model "aliased"
#guard sameBody oneLegacy.model twoLegacy.model "shifted"
#guard sameBody oneLegacy.model twoLegacy.model "entry"
#guard sameBody oneLegacy.model twoLegacy.model "signedKey"
#guard sameBody oneLegacy.model twoLegacy.model "packedEntry"
#guard sameBody oneLegacy.model twoLegacy.model "pointer"
#guard sameBody oneLegacy.model twoLegacy.model "keyOrder"
#guard sameBody oneLegacy.model twoLegacy.model "slotOfMember"
#guard sameBody oneLegacy.model twoLegacy.model "rawSlot"
#guard sameBody oneLegacy.model twoLegacy.model "rawSlotOf"
#guard sameBody oneIr.model twoIr.model "deposit"
#guard sameBody oneIr.model twoIr.model "forwarded"
#guard sameBody oneIr.model twoIr.model "cleared"
#guard sameBody oneIr.model twoIr.model "aliased"
#guard sameBody oneIr.model twoIr.model "shifted"
#guard sameBody oneIr.model twoIr.model "entry"
#guard sameBody oneIr.model twoIr.model "signedKey"
#guard sameBody oneIr.model twoIr.model "packedEntry"
#guard sameBody oneIr.model twoIr.model "pointer"
#guard sameBody oneIr.model twoIr.model "keyOrder"
#guard sameBody oneIr.model twoIr.model "slotOfMember"
#guard sameBody oneIr.model twoIr.model "rawSlot"
#guard sameBody oneIr.model twoIr.model "rawSlotOf"
#guard returns oneLegacy.model "deposit" [1, who, 5] 5055
#guard returns oneLegacy.model "deposit" [7, who, 0] 0
#guard returns oneLegacy.model "forwarded" [1, who, 5] 6
#guard returns oneLegacy.model "cleared" [1, who] 0
#guard returns oneLegacy.model "aliased" [1, who] 1212
#guard returns oneLegacy.model "shifted" [1, 2, (2 ^ 256 - 7)] (2 ^ 256 - 7)
#guard returns oneLegacy.model "entry" [1, 2, 3] 30044
#guard returns oneLegacy.model "signedKey" [1, (2 ^ 256 - 3), 4] 44
#guard returns oneLegacy.model "pointer" [1, who, 5] 55
#guard returns oneLegacy.model "keyOrder" [3, who] 43
#guard returns oneLegacy.model "slotOfMember" [1] slotOfOne
#guard returns oneLegacy.model "slotOfMember" [0] slotOfZero
#guard returns oneLegacy.model "rawSlot" [who, 5] 55
#guard returns oneLegacy.model "rawSlotOf" [] 4661
#guard returns oneLegacy.model "packedEntry" [1, 2, 7, 9] 9000007009879
#guard returns oneLegacy.model "packedEntry" [3, 4, 2 ^ 128 - 1, 5] ((2 ^ 128 - 1) * 10 ^ 6 + 5879 + 5 * 10 ^ 12)
#guard panics oneLegacy.model "deposit" [1, who, maxWord]
#guard panics oneLegacy.model "forwarded" [1, who, maxWord]
#guard panics oneLegacy.model "entry" [1, 2, maxWord]
#guard panics oneLegacy.model "packedEntry" [3, 4, 2 ^ 128 - 1, 2 ^ 64 - 1]
#guard returns twoLegacy.model "deposit" [1, who, 5] 5055
#guard returns twoLegacy.model "deposit" [7, who, 0] 0
#guard returns twoLegacy.model "forwarded" [1, who, 5] 6
#guard returns twoLegacy.model "cleared" [1, who] 0
#guard returns twoLegacy.model "aliased" [1, who] 1212
#guard returns twoLegacy.model "shifted" [1, 2, (2 ^ 256 - 7)] (2 ^ 256 - 7)
#guard returns twoLegacy.model "entry" [1, 2, 3] 30044
#guard returns twoLegacy.model "signedKey" [1, (2 ^ 256 - 3), 4] 44
#guard returns twoLegacy.model "pointer" [1, who, 5] 55
#guard returns twoLegacy.model "keyOrder" [3, who] 43
#guard returns twoLegacy.model "slotOfMember" [1] slotOfOne
#guard returns twoLegacy.model "slotOfMember" [0] slotOfZero
#guard returns twoLegacy.model "rawSlot" [who, 5] 55
#guard returns twoLegacy.model "rawSlotOf" [] 4661
#guard returns twoLegacy.model "packedEntry" [1, 2, 7, 9] 9000007009879
#guard returns twoLegacy.model "packedEntry" [3, 4, 2 ^ 128 - 1, 5] ((2 ^ 128 - 1) * 10 ^ 6 + 5879 + 5 * 10 ^ 12)
#guard panics twoLegacy.model "deposit" [1, who, maxWord]
#guard panics twoLegacy.model "forwarded" [1, who, maxWord]
#guard panics twoLegacy.model "entry" [1, 2, maxWord]
#guard panics twoLegacy.model "packedEntry" [3, 4, 2 ^ 128 - 1, 2 ^ 64 - 1]
#guard returns oneIr.model "deposit" [1, who, 5] 5055
#guard returns oneIr.model "deposit" [7, who, 0] 0
#guard returns oneIr.model "forwarded" [1, who, 5] 6
#guard returns oneIr.model "cleared" [1, who] 0
#guard returns oneIr.model "aliased" [1, who] 1212
#guard returns oneIr.model "shifted" [1, 2, (2 ^ 256 - 7)] (2 ^ 256 - 7)
#guard returns oneIr.model "entry" [1, 2, 3] 30044
#guard returns oneIr.model "signedKey" [1, (2 ^ 256 - 3), 4] 44
#guard returns oneIr.model "pointer" [1, who, 5] 55
#guard returns oneIr.model "keyOrder" [3, who] 43
#guard returns oneIr.model "slotOfMember" [1] slotOfOne
#guard returns oneIr.model "slotOfMember" [0] slotOfZero
#guard returns oneIr.model "rawSlot" [who, 5] 55
#guard returns oneIr.model "rawSlotOf" [] 4661
#guard returns oneIr.model "packedEntry" [1, 2, 7, 9] 9000007009879
#guard returns oneIr.model "packedEntry" [3, 4, 2 ^ 128 - 1, 5] ((2 ^ 128 - 1) * 10 ^ 6 + 5879 + 5 * 10 ^ 12)
#guard panics oneIr.model "deposit" [1, who, maxWord]
#guard panics oneIr.model "forwarded" [1, who, maxWord]
#guard panics oneIr.model "entry" [1, 2, maxWord]
#guard panics oneIr.model "packedEntry" [3, 4, 2 ^ 128 - 1, 2 ^ 64 - 1]
#guard returns twoIr.model "deposit" [1, who, 5] 5055
#guard returns twoIr.model "deposit" [7, who, 0] 0
#guard returns twoIr.model "forwarded" [1, who, 5] 6
#guard returns twoIr.model "cleared" [1, who] 0
#guard returns twoIr.model "aliased" [1, who] 1212
#guard returns twoIr.model "shifted" [1, 2, (2 ^ 256 - 7)] (2 ^ 256 - 7)
#guard returns twoIr.model "entry" [1, 2, 3] 30044
#guard returns twoIr.model "signedKey" [1, (2 ^ 256 - 3), 4] 44
#guard returns twoIr.model "pointer" [1, who, 5] 55
#guard returns twoIr.model "keyOrder" [3, who] 43
#guard returns twoIr.model "slotOfMember" [1] slotOfOne
#guard returns twoIr.model "slotOfMember" [0] slotOfZero
#guard returns twoIr.model "rawSlot" [who, 5] 55
#guard returns twoIr.model "rawSlotOf" [] 4661
#guard returns twoIr.model "packedEntry" [1, 2, 7, 9] 9000007009879
#guard returns twoIr.model "packedEntry" [3, 4, 2 ^ 128 - 1, 5] ((2 ^ 128 - 1) * 10 ^ 6 + 5879 + 5 * 10 ^ 12)
#guard panics twoIr.model "deposit" [1, who, maxWord]
#guard panics twoIr.model "forwarded" [1, who, maxWord]
#guard panics twoIr.model "entry" [1, 2, maxWord]
#guard panics twoIr.model "packedEntry" [3, 4, 2 ^ 128 - 1, 2 ^ 64 - 1]

end SolidityImportSmoke.StorageMappingArgumentStateCountChecks
