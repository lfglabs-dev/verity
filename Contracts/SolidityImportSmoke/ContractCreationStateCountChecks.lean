import Compiler.SolidityImport.Import

namespace SolidityImportSmoke.ContractCreationStateCountChecks

/-! Contract creation `new C(...)` rejects at the call in every contract (#2830).

Before this change a contract with more than one state variable lowered `new C(...)` to a
`uint256` staticcall to its own address: no account was created, the constructor never ran
and its revert was lost, while a one-slot contract rejected the same source. solc 0.8.34 runs
CREATE on both pipelines (Anvil: a fresh address with code, the constructor's `revert("zero")`
bubbled up). The pair below differs only by one unrelated state variable and one unused
function; each function must reject with the same located diagnostic in both contracts and
on both pipelines. `createdStatement` (`new C(a);` as a statement) is resolved as a call
target and rejects at the `NewExpression` in both contracts, as before. -/

/--
error: ContractCreationOneSlot.sol:34:26: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.created
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function created(uint256)

/--
error: ContractCreationOneSlot.sol:40:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.createdCode
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdCodeOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdCode(uint256)

/--
error: ContractCreationOneSlot.sol:45:40: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.createdNamed
new CreatedNamed("child")
-/
#guard_msgs in
solidity_import createdNamedOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdNamed(uint256)

/--
error: ContractCreationOneSlot.sol:30:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.createdInHelper -> ContractCreationOneSlot.build
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdInHelperOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdInHelper(uint256)

/--
error: ContractCreationOneSlot.sol:54:9: NewExpression: [solidity-import:unsupported] expression has no supported declaration reference
closure: ContractCreationOneSlot.createdStatement
new CreatedChild
-/
#guard_msgs in
solidity_import createdStatementOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdStatement(uint256)

/--
error: ContractCreationOneSlot.sol:34:26: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.created
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdOneSlotIr from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function created(uint256)

/--
error: ContractCreationOneSlot.sol:40:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.createdCode
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdCodeOneSlotIr from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdCode(uint256)

/--
error: ContractCreationOneSlot.sol:45:40: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.createdNamed
new CreatedNamed("child")
-/
#guard_msgs in
solidity_import createdNamedOneSlotIr from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdNamed(uint256)

/--
error: ContractCreationOneSlot.sol:30:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationOneSlot.createdInHelper -> ContractCreationOneSlot.build
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdInHelperOneSlotIr from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdInHelper(uint256)

/--
error: ContractCreationOneSlot.sol:54:9: NewExpression: [solidity-import:unsupported] expression has no supported declaration reference
closure: ContractCreationOneSlot.createdStatement
new CreatedChild
-/
#guard_msgs in
solidity_import createdStatementOneSlotIr from "Contracts/SolidityImportSmoke" entry "ContractCreationOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationOneSlot
  function createdStatement(uint256)

/--
error: ContractCreationTwoSlots.sol:38:26: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.created
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function created(uint256)

/--
error: ContractCreationTwoSlots.sol:44:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.createdCode
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdCodeTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdCode(uint256)

/--
error: ContractCreationTwoSlots.sol:49:40: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.createdNamed
new CreatedNamed("child")
-/
#guard_msgs in
solidity_import createdNamedTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdNamed(uint256)

/--
error: ContractCreationTwoSlots.sol:34:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.createdInHelper -> ContractCreationTwoSlots.build
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdInHelperTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdInHelper(uint256)

/--
error: ContractCreationTwoSlots.sol:58:9: NewExpression: [solidity-import:unsupported] expression has no supported declaration reference
closure: ContractCreationTwoSlots.createdStatement
new CreatedChild
-/
#guard_msgs in
solidity_import createdStatementTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdStatement(uint256)

/--
error: ContractCreationTwoSlots.sol:38:26: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.created
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function created(uint256)

/--
error: ContractCreationTwoSlots.sol:44:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.createdCode
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdCodeTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdCode(uint256)

/--
error: ContractCreationTwoSlots.sol:49:40: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.createdNamed
new CreatedNamed("child")
-/
#guard_msgs in
solidity_import createdNamedTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdNamed(uint256)

/--
error: ContractCreationTwoSlots.sol:34:24: FunctionCall: [solidity-import:unsupported] contract creation `new C(...)` requires CREATE semantics and is outside this slice
closure: ContractCreationTwoSlots.createdInHelper -> ContractCreationTwoSlots.build
new CreatedChild(a)
-/
#guard_msgs in
solidity_import createdInHelperTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdInHelper(uint256)

/--
error: ContractCreationTwoSlots.sol:58:9: NewExpression: [solidity-import:unsupported] expression has no supported declaration reference
closure: ContractCreationTwoSlots.createdStatement
new CreatedChild
-/
#guard_msgs in
solidity_import createdStatementTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "ContractCreationTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract ContractCreationTwoSlots
  function createdStatement(uint256)

end SolidityImportSmoke.ContractCreationStateCountChecks
