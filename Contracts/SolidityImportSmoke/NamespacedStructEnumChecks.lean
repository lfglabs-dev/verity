import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.NamespacedStructEnumChecks
open Compiler.CompilationModel Denote

solidity_profile enumProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function mode()
  function entryMode(uint256)
  function unused(uint256)
  function set(uint256)
  function clear(uint256)
  function setNeighbors(uint256,uint16,uint8)

private def oracle := SolidityImport.Differential.oracle
-- The namespace base, and member `entries` at word 1 of the struct.
private def baseSlot : Nat := 0x5d137fa045f8e23ba9b67ac5983f40ee54e497f58d893afb34609c91a4384800
private def entrySlot := oracle.mappingSlot (baseSlot + 1) 7

private def observe (name : String) (args : List Nat) (base entry : Nat) :
    Option (Bool × Option (List UInt8) × List Nat × Nat × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let world := (Verity.defaultState.writePhysicalSlot baseSlot (.ofNat base)).writePhysicalSlot
    entrySlot (.ofNat entry)
  let r := denoteFunction oracle imported.model fn {sender := 0, functionSelector := 0, args} world
  return (r.success, r.revertData, r.returnWords, r.finalStorage baseSlot, r.finalStorage entrySlot)

-- Layout: `head` bytes 0..7, `mode` byte 8, `tail` bytes 9..10 of the base word; in an entry,
-- `amount` bytes 0..15, `mode` byte 16, `flag` byte 17. Dirty bytes above the members
-- (0xab.., 0xcd..) are never part of a member. The ordinal 3 is the first invalid one.
private def dirtyBase : Nat := 0xab <<< 96 ||| 0xbeef <<< 72 ||| 3 <<< 64 ||| 0xa5
private def dirtyEntry : Nat := 0xcd <<< 160 ||| 0x99 <<< 136 ||| 3 <<< 128 ||| 0x1234

#guard observe "mode" [] dirtyBase dirtyEntry ==
  some (false, some (panicBytes 0x21), [], dirtyBase, dirtyEntry)
#guard observe "entryMode" [7] dirtyBase dirtyEntry ==
  some (false, some (panicBytes 0x21), [], dirtyBase, dirtyEntry)
#guard observe "unused" [7] dirtyBase dirtyEntry ==
  some (true, none, [0xbeef + 0x99], dirtyBase, dirtyEntry)
#guard observe "set" [7] dirtyBase dirtyEntry ==
  some (true, none, [], 0xab <<< 96 ||| 0xbeef <<< 72 ||| 2 <<< 64 ||| 0xa5,
    0xcd <<< 160 ||| 0x99 <<< 136 ||| 1 <<< 128 ||| 0x1234)
#guard observe "clear" [7] dirtyBase dirtyEntry ==
  some (true, none, [], 0xab <<< 96 ||| 0xbeef <<< 72 ||| 0xa5, 0xcd <<< 160 ||| 0x99 <<< 136 ||| 0x1234)
#guard observe "setNeighbors" [7, 0x4242, 0x77] dirtyBase dirtyEntry ==
  some (true, none, [], 0xab <<< 96 ||| 0x4242 <<< 72 ||| 3 <<< 64 ||| 0xa5,
    0xcd <<< 160 ||| 0x77 <<< 136 ||| 3 <<< 128 ||| 0x1234)
-- In range, the upper dirty bytes are masked off the ordinal.
#guard observe "mode" [] (0xab <<< 96 ||| 2 <<< 64) 0 == some (true, none, [2], 0xab <<< 96 ||| 2 <<< 64, 0)
#guard observe "entryMode" [7] 0 (0xcd <<< 160 ||| 1 <<< 128) ==
  some (true, none, [1], 0, 0xcd <<< 160 ||| 1 <<< 128)

-- Every other consumer of a read, non-literal writes and whole-struct operations reject.
/--
error: NamespacedStructEnum.sol:52:62: MemberAccess: [solidity-import:unsupported] storage enum read requires a direct ABI return or an unused local initializer
closure: NamespacedStructEnum.compare
_storage().mode
-/
#guard_msgs in
solidity_import compareImport from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function compare()

/--
error: NamespacedStructEnum.sol:53:73: MemberAccess: [solidity-import:unsupported] storage enum read requires a direct ABI return or an unused local initializer
closure: NamespacedStructEnum.convert
_storage().mode
-/
#guard_msgs in
solidity_import convertImport from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function convert()

/--
error: NamespacedStructEnum.sol:54:63: Identifier: [solidity-import:unsupported] storage enum assignment requires an enum literal
closure: NamespacedStructEnum.assignParam
x
-/
#guard_msgs in
solidity_import assignParamImport from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function assignParam(Mode)

/--
error: NamespacedStructEnum.sol:56:40: MemberAccess: [solidity-import:unsupported] storage enum assignment requires an enum literal
closure: NamespacedStructEnum.assignTuple
_storage().mode
-/
#guard_msgs in
solidity_import assignTupleImport from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function assignTuple()

/--
error: NamespacedStructEnum.sol:58:26: IndexAccess: [solidity-import:unsupported] struct storage read requires a scalar-member struct layout
closure: NamespacedStructEnum.copyEntry
_storage().entries[k]
-/
#guard_msgs in
solidity_import copyEntryImport from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function copyEntry(uint256)

/--
error: NamespacedStructEnum.sol:61:19: VariableDeclaration: [solidity-import:unsupported] struct storage-to-memory parameter copy requires a scalar-member struct layout
closure: NamespacedStructEnum.passEntry -> NamespacedStructEnum.take
Entry memory e
-/
#guard_msgs in
solidity_import passEntryImport from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function passEntry(uint256)

/--
error: NamespacedStructEnum.sol:63:55: IndexAccess: [solidity-import:unsupported] cannot delete struct with members outside this slice
closure: NamespacedStructEnum.deleteEntry
_storage().entries[k]
-/
#guard_msgs in
solidity_import deleteEntryImport from "Contracts/SolidityImportSmoke" entry "NamespacedStructEnum.sol"
  using enumProfile
  contract NamespacedStructEnum
  function deleteEntry(uint256)

end SolidityImportSmoke.NamespacedStructEnumChecks
