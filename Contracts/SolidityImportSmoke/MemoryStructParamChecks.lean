import Compiler.SolidityImport.Import

/-!
Memory struct parameters bound from the caller's own memory struct (`MemoryStructParam.sol`).

A memory struct is a reference. When a caller passes its own memory struct to an internal helper,
a member write in the helper changes the caller's struct, and returning the parameter hands the
caller its own struct back. The importer binds the parameter as a copy, so both are rejected with
a located error, whatever the syntax of the write or the return. The rule is conservative: a
return is rejected even when the caller never writes either struct afterwards. Reads, writes to a
struct built in the argument or copied from storage, and writes to the helper's own struct import.
-/
namespace SolidityImportSmoke.MemoryStructParamChecks

solidity_profile memoryStruct where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- A member write in the helper.
/--
error: MemoryStructParam.sol:18:9: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeDirect -> MemoryStructParam.setA
p.a
-/
#guard_msgs in
solidity_import case1 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeDirect(uint256)

-- A compound member write.
/--
error: MemoryStructParam.sol:22:9: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeCompound -> MemoryStructParam.addA
p.a
-/
#guard_msgs in
solidity_import case2 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeCompound(uint256)

-- A member increment.
/--
error: MemoryStructParam.sol:26:9: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeIncrement -> MemoryStructParam.incA
p.a
-/
#guard_msgs in
solidity_import case3 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeIncrement(uint256)

-- A member decrement.
/--
error: MemoryStructParam.sol:139:9: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeDecrement -> MemoryStructParam.decA
p.a
-/
#guard_msgs in
solidity_import case4 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeDecrement(uint256)

-- A member delete.
/--
error: MemoryStructParam.sol:30:16: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeDelete -> MemoryStructParam.clearA
p.a
-/
#guard_msgs in
solidity_import case5 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeDelete(uint256)

-- A member as a tuple-assignment target.
/--
error: MemoryStructParam.sol:135:10: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeTuple -> MemoryStructParam.tupleA
p.a
-/
#guard_msgs in
solidity_import case6 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeTuple(uint256)

-- A member write in a helper the first helper passes the struct to.
/--
error: MemoryStructParam.sol:18:9: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeNested -> MemoryStructParam.forward -> MemoryStructParam.setA
p.a
-/
#guard_msgs in
solidity_import case7 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeNested(uint256)

-- A member write in a `using for` library function called on the struct.
/--
error: MemoryStructParam.sol:172:9: MemberAccess: [solidity-import:unsupported] member write through a memory struct parameter is outside this slice (it would change the caller's struct)
closure: MemoryStructParam.writeReceiver -> MemoryStructParamLib.bumpA
p.a
-/
#guard_msgs in
solidity_import case8 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeReceiver(uint256)

-- Returning the parameter.
/--
error: MemoryStructParam.sol:38:16: Identifier: [solidity-import:unsupported] returning a memory struct parameter (an alias) is outside this slice
closure: MemoryStructParam.returnDirect -> MemoryStructParam.same
p
-/
#guard_msgs in
solidity_import case9 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function returnDirect(uint256)

-- Returning the parameter in parentheses.
/--
error: MemoryStructParam.sol:41:16: TupleExpression: [solidity-import:unsupported] returning a memory struct parameter (an alias) is outside this slice
closure: MemoryStructParam.returnParen -> MemoryStructParam.sameParen
(p)
-/
#guard_msgs in
solidity_import case10 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function returnParen(uint256)

-- Returning the parameter from one branch of a conditional.
/--
error: MemoryStructParam.sol:44:16: Conditional: [solidity-import:unsupported] returning a memory struct parameter (an alias) is outside this slice
closure: MemoryStructParam.returnConditional -> MemoryStructParam.pick
c ? p : P(0, 0)
-/
#guard_msgs in
solidity_import case11 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function returnConditional(uint256)

-- Returning the parameter as a tuple component.
/--
error: MemoryStructParam.sol:47:17: Identifier: [solidity-import:unsupported] returning a memory struct parameter (an alias) is outside this slice
closure: MemoryStructParam.returnTuple -> MemoryStructParam.pair
p
-/
#guard_msgs in
solidity_import case12 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function returnTuple(uint256)

-- Reading the parameter's members.
#guard_msgs in
solidity_import case13 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function readOnly(uint256)

-- Writing a struct built in the argument: the caller has no reference to it.
#guard_msgs in
solidity_import case14 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeTemporary(uint256)

-- Writing and returning the helper's own struct.
#guard_msgs in
solidity_import case15 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeOwnStruct(uint256)

-- Writing a struct solc copies from storage into memory for the call.
#guard_msgs in
solidity_import case16 from "Contracts/SolidityImportSmoke" entry "MemoryStructParam.sol"
  using memoryStruct
  contract MemoryStructParam
  function writeStorageCopy(uint256)

end SolidityImportSmoke.MemoryStructParamChecks
