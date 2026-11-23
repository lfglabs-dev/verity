import Compiler.SolidityImport.Import

namespace SolidityImportSmoke.SelfTryCallStateCountChecks

/-! `try this.f(...)` rejects at the `try` in every contract (#2830).

Before this change a contract with more than one state variable lowered the self-call to the
success bit of an oracle call that ran none of `f` (its storage writes, return value and
revert data were not modelled) and treated `catch Error(string memory)` as a catch-all, while
a one-slot contract rejected the same source. solc 0.8.34 on Anvil, both pipelines:
`errorOnly(1)` reverts uncaught with no data, `returned(5)` decodes `6`, `revertData(0)`
binds 100 bytes of `Error("zero")`. The pair below differs only by one unrelated state variable
and one unused function; each function must reject with the same located diagnostic in both
contracts, on both pipelines, at the root and inside an inlined `void` helper. -/

/--
error: SelfTryCallOneSlot.sol:32:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.catchAll
try this.poke(a) { r = 1; } catch { r = 2; }
-/
#guard_msgs in
solidity_import catchAllOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function catchAll(uint256)

/--
error: SelfTryCallOneSlot.sol:36:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.errorOnly
try this.poke(a) { r = 1; } catch Error(string memory) { r = 3; }
-/
#guard_msgs in
solidity_import errorOnlyOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function errorOnly(uint256)

/--
error: SelfTryCallOneSlot.sol:40:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.returned
try this.target(a) returns (uint256 v) { r = v; } catch { r = 2; }
-/
#guard_msgs in
solidity_import returnedOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function returned(uint256)

/--
error: SelfTryCallOneSlot.sol:44:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.revertData
try this.poke(a) { r = 1; } catch (bytes memory d) { r = 100 + d.length; }
-/
#guard_msgs in
solidity_import revertDataOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function revertData(uint256)

/--
error: SelfTryCallOneSlot.sol:28:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.inHelper -> SelfTryCallOneSlot.guarded
try this.poke(a) { } catch { revert("caught"); }
-/
#guard_msgs in
solidity_import inHelperOneSlotLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function inHelper(uint256)

/--
error: SelfTryCallOneSlot.sol:32:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.catchAll
try this.poke(a) { r = 1; } catch { r = 2; }
-/
#guard_msgs in
solidity_import catchAllOneSlotIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function catchAll(uint256)

/--
error: SelfTryCallOneSlot.sol:36:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.errorOnly
try this.poke(a) { r = 1; } catch Error(string memory) { r = 3; }
-/
#guard_msgs in
solidity_import errorOnlyOneSlotIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function errorOnly(uint256)

/--
error: SelfTryCallOneSlot.sol:40:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.returned
try this.target(a) returns (uint256 v) { r = v; } catch { r = 2; }
-/
#guard_msgs in
solidity_import returnedOneSlotIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function returned(uint256)

/--
error: SelfTryCallOneSlot.sol:44:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.revertData
try this.poke(a) { r = 1; } catch (bytes memory d) { r = 100 + d.length; }
-/
#guard_msgs in
solidity_import revertDataOneSlotIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function revertData(uint256)

/--
error: SelfTryCallOneSlot.sol:28:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallOneSlot.inHelper -> SelfTryCallOneSlot.guarded
try this.poke(a) { } catch { revert("caught"); }
-/
#guard_msgs in
solidity_import inHelperOneSlotIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallOneSlot.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallOneSlot
  function inHelper(uint256)

/--
error: SelfTryCallTwoSlots.sol:36:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.catchAll
try this.poke(a) { r = 1; } catch { r = 2; }
-/
#guard_msgs in
solidity_import catchAllTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function catchAll(uint256)

/--
error: SelfTryCallTwoSlots.sol:40:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.errorOnly
try this.poke(a) { r = 1; } catch Error(string memory) { r = 3; }
-/
#guard_msgs in
solidity_import errorOnlyTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function errorOnly(uint256)

/--
error: SelfTryCallTwoSlots.sol:44:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.returned
try this.target(a) returns (uint256 v) { r = v; } catch { r = 2; }
-/
#guard_msgs in
solidity_import returnedTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function returned(uint256)

/--
error: SelfTryCallTwoSlots.sol:48:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.revertData
try this.poke(a) { r = 1; } catch (bytes memory d) { r = 100 + d.length; }
-/
#guard_msgs in
solidity_import revertDataTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function revertData(uint256)

/--
error: SelfTryCallTwoSlots.sol:32:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.inHelper -> SelfTryCallTwoSlots.guarded
try this.poke(a) { } catch { revert("caught"); }
-/
#guard_msgs in
solidity_import inHelperTwoSlotsLegacy from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function inHelper(uint256)

/--
error: SelfTryCallTwoSlots.sol:36:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.catchAll
try this.poke(a) { r = 1; } catch { r = 2; }
-/
#guard_msgs in
solidity_import catchAllTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function catchAll(uint256)

/--
error: SelfTryCallTwoSlots.sol:40:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.errorOnly
try this.poke(a) { r = 1; } catch Error(string memory) { r = 3; }
-/
#guard_msgs in
solidity_import errorOnlyTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function errorOnly(uint256)

/--
error: SelfTryCallTwoSlots.sol:44:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.returned
try this.target(a) returns (uint256 v) { r = v; } catch { r = 2; }
-/
#guard_msgs in
solidity_import returnedTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function returned(uint256)

/--
error: SelfTryCallTwoSlots.sol:48:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.revertData
try this.poke(a) { r = 1; } catch (bytes memory d) { r = 100 + d.length; }
-/
#guard_msgs in
solidity_import revertDataTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function revertData(uint256)

/--
error: SelfTryCallTwoSlots.sol:32:9: TryStatement: [solidity-import:unsupported] try/catch of an external self-call `this.f(...)` requires call semantics and is outside this slice
closure: SelfTryCallTwoSlots.inHelper -> SelfTryCallTwoSlots.guarded
try this.poke(a) { } catch { revert("caught"); }
-/
#guard_msgs in
solidity_import inHelperTwoSlotsIr from "Contracts/SolidityImportSmoke" entry "SelfTryCallTwoSlots.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SelfTryCallTwoSlots
  function inHelper(uint256)

end SolidityImportSmoke.SelfTryCallStateCountChecks
