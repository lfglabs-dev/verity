import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.SyntheticGapStorageChecks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport

/-! Static-array members of storage structs: footprints and the placement of later members.
Physical slots were observed on anvil with the pinned solc 0.8.34 (via-IR, osaka, 466 runs). -/

-- solc's footprint of a static storage array type (`staticArrayStorageWords?`).
#guard staticArrayStorageWords? "uint256[50]" none == some 50
#guard staticArrayStorageWords? "uint64[5]" none == some 2
#guard staticArrayStorageWords? "uint128[3]" none == some 2
#guard staticArrayStorageWords? "bool[33]" none == some 2
#guard staticArrayStorageWords? "bytes20[3]" none == some 3
#guard staticArrayStorageWords? "address[2][3]" none == some 6
#guard staticArrayStorageWords? "uint8[][4]" none == some 4
#guard staticArrayStorageWords? "struct C.S[3]" (some 2) == some 6
#guard staticArrayStorageWords? "uint256[]" none == none
#guard staticArrayStorageWords? "uint256[0]" none == none
#guard staticArrayStorageWords? "string[2]" none == none
#guard staticArrayStorageWords? "struct C.S[3]" none == none

solidity_import raw from "Contracts/SolidityImportSmoke" entry "SyntheticGapStorage.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticGapStorage
  function setAll(uint128,address,bool,uint256)
  function getAll()
  function setOuter(uint8,uint256,uint256)
  function getOuter()

solidity_import mapped from "Contracts/SolidityImportSmoke" entry "SyntheticGapStorage.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticGapStorageMapped
  function setRecord(uint256,uint256,uint128)
  function getRecord(uint256)

private def layoutSlot : Nat := 0x5d8e1f0a7c2b3e4d5f60718293a4b5c6d7e8f9011223344556677889900aab00
private def outerSlot : Nat := 0x6e9f20b18d3c4f5e607182a3b4c5d6e7f8091a2b3c4d5e6f708192a3b4c5d600

private def run (model : CompilationModel) (name : String) (args : List Nat)
    (storage : Nat → Nat := fun _ => 0) : Option Denote.DenoteResult := do
  let f ← model.functions.find? (·.name == name)
  return Denote.denoteFunction SolidityImport.Differential.oracle model f
    { sender := 1, functionSelector := 0, args }
    (Verity.defaultState.withStorageWords fun
      | .slot i => Verity.Core.Uint256.ofNat (storage i)
      | _ => 0)

-- `head` at +0, `__gap` +1..+3, `admin`/`paused` packed at +4, `packedGap` +5..+6,
-- `nestedGap` +7..+10, `pairs` +11..+14, `tail` at +15; the round trip reads them back.
#guard match run raw.model "setAll" [7, 0xaa, 1, 99] with
  | some w =>
      w.success && w.finalStorage layoutSlot == 7 &&
      w.finalStorage (layoutSlot + 4) == 0xaa + 2 ^ 160 &&
      w.finalStorage (layoutSlot + 15) == 99 &&
      [1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16].all
        (fun i => w.finalStorage (layoutSlot + i) == 0) &&
      (match run raw.model "getAll" [] w.finalStorage with
        | some r => r.success && r.returnWords == [7, 0xaa, 1, 99]
        | none => false)
  | none => false

-- A struct nesting the gapped struct: `Layout` takes 16 slots, so `inner.tail` is at +16
-- and `after_` at +17.
#guard match run raw.model "setOuter" [3, 55, 66] with
  | some w =>
      w.success && w.finalStorage outerSlot == 3 && w.finalStorage (outerSlot + 16) == 55 &&
      w.finalStorage (outerSlot + 17) == 66 &&
      (match run raw.model "getOuter" [] w.finalStorage with
        | some r => r.success && r.returnWords == [3, 55, 66]
        | none => false)
  | none => false

-- Layout-backed structs: `address[3] gap` +1..+3, `bool[5] flags` +4, `last` at +5.
#guard match run mapped.model "setRecord" [5, 11, 22] with
  | some w =>
      w.success && w.finalStorage 5 == 22 &&
      (match run mapped.model "getRecord" [5] w.finalStorage with
        | some r => r.success && r.returnWords == [11, 22, 22]
        | none => false)
  | none => false

-- The static-array member itself is opaque: reads and writes fail closed.
/--
error: SyntheticGapStorage.sol:116:16: MemberAccess: [solidity-import:unsupported] __gap of Layout has a storage type outside this slice
closure: SyntheticGapStorageUnsupported.readGap
_layout().__gap
-/
#guard_msgs in
solidity_import readGap from "Contracts/SolidityImportSmoke" entry "SyntheticGapStorage.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticGapStorageUnsupported
  function readGap(uint256)

/--
error: SyntheticGapStorage.sol:120:9: MemberAccess: [solidity-import:unsupported] __gap of Layout has a storage type outside this slice
closure: SyntheticGapStorageUnsupported.writeGap
_layout().__gap
-/
#guard_msgs in
solidity_import writeGap from "Contracts/SolidityImportSmoke" entry "SyntheticGapStorage.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticGapStorageUnsupported
  function writeGap(uint256)

end SolidityImportSmoke.SyntheticGapStorageChecks
