import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.StorageStructEnumChecks
open Compiler.CompilationModel Denote

solidity_profile enumProfile where
  evmVersion := "cancun"
  viaIR := true
  optimizerRuns := some 10
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "StorageStructEnum.sol"
  using enumProfile
  contract StorageStructEnum
  function mode(bytes32)
  function level(bytes32,address)
  function unused(bytes32,address)
  function set(bytes32,address)
  function clear(bytes32,address)
  function setNeighbors(bytes32,uint16,uint8)

private def oracle := SolidityImport.Differential.oracle
private def packedSlot := oracle.mappingSlot 0 7
private def leafSlot := oracle.mappingSlot (packedSlot + 1) 11

private def observe (name : String) (args : List Nat) (packed leaf : Nat) :
    Option (Bool × Option (List UInt8) × List Nat × Nat × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let world := (Verity.defaultState.writePhysicalSlot packedSlot (.ofNat packed)).writePhysicalSlot
    leafSlot (.ofNat leaf)
  let r := denoteFunction oracle imported.model fn {sender := 0, functionSelector := 0, args} world
  return (r.success, r.revertData, r.returnWords, r.finalStorage packedSlot, r.finalStorage leafSlot)

-- The out-of-range byte is 3 (the first invalid ordinal), not an oversized ABI word.
#guard observe "mode" [7] 0xab031234 0xcd03 ==
  some (false, some (panicBytes 0x21), [], 0xab031234, 0xcd03)
#guard observe "level" [7, 11] 0xab031234 0xcd03 ==
  some (false, some (panicBytes 0x21), [], 0xab031234, 0xcd03)
#guard observe "unused" [7, 11] 0xab031234 0xcd03 ==
  some (true, none, [0x1234], 0xab031234, 0xcd03)
#guard observe "set" [7, 11] 0xab031234 0xcd03 ==
  some (true, none, [], 0xab021234, 0xcd01)
#guard observe "clear" [7, 11] 0xab031234 0xcd03 ==
  some (true, none, [], 0xab001234, 0xcd00)
#guard observe "setNeighbors" [7, 0xbeef, 0x99] 0xab031234 0xcd03 ==
  some (true, none, [], 0x9903beef, 0xcd03)
#guard observe "mode" [7] 0xab021234 0xcd01 == some (true, none, [2], 0xab021234, 0xcd01)
#guard observe "level" [7, 11] 0xab021234 0xcd01 == some (true, none, [1], 0xab021234, 0xcd01)

/--
error: StorageStructEnum.sol:34:16: MemberAccess: [solidity-import:unsupported] storage enum read requires a direct ABI return or an unused local initializer
closure: StorageStructEnum.compare
entries[id].mode
-/
#guard_msgs in
solidity_import comparison from "Contracts/SolidityImportSmoke" entry "StorageStructEnum.sol"
  using enumProfile
  contract StorageStructEnum
  function compare(bytes32)

/--
error: StorageStructEnum.sol:38:55: IndexAccess: [solidity-import:unsupported] whole-struct delete with packed enum members is outside this slice
closure: StorageStructEnum.clearWhole
packed[id]
-/
#guard_msgs in
solidity_import whole from "Contracts/SolidityImportSmoke" entry "StorageStructEnum.sol"
  using enumProfile
  contract StorageStructEnum
  function clearWhole(bytes32)

/--
error: StorageStructEnum.sol:42:28: Identifier: [solidity-import:unsupported] storage enum assignment requires an enum literal
closure: StorageStructEnum.dirtyPacked
x
-/
#guard_msgs in
solidity_import dirtyPacked from "Contracts/SolidityImportSmoke" entry "StorageStructEnum.sol"
  using enumProfile
  contract StorageStructEnum
  function dirtyPacked(bytes32)

/--
error: StorageStructEnum.sol:47:33: Identifier: [solidity-import:unsupported] storage enum assignment requires an enum literal
closure: StorageStructEnum.dirtyMapped
x
-/
#guard_msgs in
solidity_import dirtyMapped from "Contracts/SolidityImportSmoke" entry "StorageStructEnum.sol"
  using enumProfile
  contract StorageStructEnum
  function dirtyMapped(bytes32,address)

end SolidityImportSmoke.StorageStructEnumChecks
