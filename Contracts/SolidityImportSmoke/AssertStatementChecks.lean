import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
`assert(c)` and discarded expression statements (`AssertStatementSequence.sol`,
`AssertStatementRejections.sol`).

Both solc 0.8.34 pipelines evaluate the `assert` condition once and revert with
`Panic(0x01)` when it is false, and evaluate a discarded expression (`x;`, `a / b;`) for its
checks and effects. The forms below stay located rejections.
-/
namespace SolidityImportSmoke.AssertStatementChecks

solidity_profile assertStatements where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_profile assertStatementsLegacy where
  evmVersion := "osaka"
  viaIR := false
  optimizerRuns := some 466
  bytecodeHash := "none"

-- 0. The positive fixture also imports under the legacy pipeline (same semantics).
solidity_import legacyForm from "Contracts/SolidityImportSmoke"
  entry "AssertStatementSequence.sol"
  using assertStatementsLegacy
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()

-- 1. A conditional between two calls without return values.
/--
error: AssertStatementRejections.sol:13:9: Conditional: [solidity-import:unsupported] a conditional expression statement between calls without return values is unsupported
closure: VoidConditionalC.run
x > 0 ? left() : right()
-/
#guard_msgs in
solidity_import voidConditionalForm from "Contracts/SolidityImportSmoke"
  entry "AssertStatementRejections.sol"
  using assertStatements
  contract VoidConditionalC
  function run(uint256)

-- 2. A discarded struct constructor (a memory allocation).
/--
error: AssertStatementRejections.sol:24:9: FunctionCall: [solidity-import:unsupported] a structConstructorCall expression statement is unsupported
closure: StructConstructorC.run
Pair(x, 1)
-/
#guard_msgs in
solidity_import structConstructorForm from "Contracts/SolidityImportSmoke"
  entry "AssertStatementRejections.sol"
  using assertStatements
  contract StructConstructorC
  function run(uint256)

-- 3. A discarded inline array.
/--
error: AssertStatementRejections.sol:30:9: TupleExpression: [solidity-import:unsupported] a tuple or inline array expression statement is unsupported
closure: InlineArrayC.run
[x, 1]
-/
#guard_msgs in
solidity_import inlineArrayForm from "Contracts/SolidityImportSmoke"
  entry "AssertStatementRejections.sol"
  using assertStatements
  contract InlineArrayC
  function run(uint256)

-- 4. A discarded tuple.
/--
error: AssertStatementRejections.sol:36:9: TupleExpression: [solidity-import:unsupported] a tuple or inline array expression statement is unsupported
closure: TupleC.run
(x, 1)
-/
#guard_msgs in
solidity_import tupleForm from "Contracts/SolidityImportSmoke"
  entry "AssertStatementRejections.sol"
  using assertStatements
  contract TupleC
  function run(uint256)

-- 5. A type name as a statement: the kind is named.
/--
error: AssertStatementRejections.sol:42:9: ElementaryTypeNameExpression: [solidity-import:unsupported] ElementaryTypeNameExpression expression statements are unsupported
closure: TypeNameC.run
uint256
-/
#guard_msgs in
solidity_import typeNameForm from "Contracts/SolidityImportSmoke"
  entry "AssertStatementRejections.sol"
  using assertStatements
  contract TypeNameC
  function run(uint256)

end SolidityImportSmoke.AssertStatementChecks
