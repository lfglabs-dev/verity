import Compiler.SolidityImport.Import

namespace SolidityImportSmoke.NestedStorageStructChecks
open Compiler.CompilationModel Compiler.CompilationModel.Denote

solidity_profile profile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructSingleVar
  function fromMemory(address, Part)
  function fromCalldata(address, Part)
  function readPart(address)

-- Place the selected mapping entry at 100 and seed independent sibling and padding bits.
private def oracle : DenoteOracle := ⟨fun _ k => 100 * k, fun _ _ _ => 0⟩
private def initial (slot : Nat) : Nat :=
  if slot == 100 then 91 else if slot == 101 then 2^248 else if slot == 103 then 73 else 0

private def run (name : String) (args : List Nat) (storage : Nat → Nat) : Option DenoteResult := do
  let fn ← imported.model.functions.find? (·.name == name)
  return denoteFunction oracle imported.model fn { sender := 1, functionSelector := 0, args }
    (Verity.defaultState.withStorageWords fun
      | .slot i => Verity.Core.Uint256.ofNat (storage i)
      | _ => 0)

private def roundTrip (writer : String) : Bool := Id.run do
  let words := [2^127 + 3, 1, 2^63 + 5, 2^255 + 7]
  let some w := run writer (1 :: words) initial | return false
  let some r := run "readPart" [1] w.finalStorage | return false
  return w.success && r.success && r.returnWords == words && w.finalStorage 100 == 91 &&
    w.finalStorage 101 == 2^248 + (2^63 + 5) * 2^136 + 2^128 + 2^127 + 3 &&
    w.finalStorage 102 == 2^255 + 7 && w.finalStorage 103 == 73

#guard roundTrip "fromMemory"
#guard roundTrip "fromCalldata"

/--
error: NestedStorageStructSequence.sol:78:9: MemberAccess: [solidity-import:unsupported] whole struct storage assignment requires a scalar-member struct layout
closure: NestedStorageStructUnsupported.assignDynamicSubStruct
holders[k].dynPart
-/
#guard_msgs in
solidity_import dynWrite from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructUnsupported
  function assignDynamicSubStruct(address, DynamicPart)

/--
error: NestedStorageStructSequence.sol:82:9: MemberAccess: [solidity-import:unsupported] whole struct storage assignment requires a scalar-member struct layout
closure: NestedStorageStructUnsupported.assignOpaqueSubStruct
holders[k].opaquePart
-/
#guard_msgs in
solidity_import opaqueWrite from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructUnsupported
  function assignOpaqueSubStruct(address, OpaquePart)

/--
error: NestedStorageStructSequence.sol:86:16: MemberAccess: [solidity-import:unsupported] dynamic struct returns require abi.decode or a memory struct variable
closure: NestedStorageStructUnsupported.returnDynamicSubStruct
holders[k].dynPart
-/
#guard_msgs in
solidity_import dynRead from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructUnsupported
  function returnDynamicSubStruct(address)

/--
error: NestedStorageStructSequence.sol:90:38: MemberAccess: [solidity-import:unsupported] struct storage read requires a scalar-member struct layout
closure: NestedStorageStructUnsupported.readFixedArraySubStruct
holders[k].fixedPart
-/
#guard_msgs in
solidity_import arrayRead from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructUnsupported
  function readFixedArraySubStruct(address)

/--
error: NestedStorageStructSequence.sol:95:33: MemberAccess: [solidity-import:unsupported] nested struct assignment requires a memory or calldata source
closure: NestedStorageStructUnsupported.assignStorageToStorageSubStruct
holders[b].scalarPart
-/
#guard_msgs in
solidity_import storageCopy from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructUnsupported
  function assignStorageToStorageSubStruct(address, address)

/--
error: NestedStorageStructSequence.sol:99:16: MemberAccess: [solidity-import:unsupported] member assignment requires a supported layout member
closure: NestedStorageStructUnsupported.deleteSubStruct
holders[k].scalarPart
-/
#guard_msgs in
solidity_import subDelete from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructUnsupported
  function deleteSubStruct(address)

/--
error: NestedStorageStructSequence.sol:103:16: MemberAccess: [solidity-import:unsupported] nested storage struct return requires a flat memory result
closure: NestedStorageStructUnsupported.returnSubStructStoragePtr
holders[k].scalarPart
-/
#guard_msgs in
solidity_import storagePtrRet from "Contracts/SolidityImportSmoke" entry "NestedStorageStructSequence.sol"
  using profile
  contract NestedStorageStructUnsupported
  function returnSubStructStoragePtr(address)

end SolidityImportSmoke.NestedStorageStructChecks
