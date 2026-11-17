import Compiler.SolidityImport.Import

/-!
A call to another contract's function that returns two words (`ExternalTupleCall.sol`).

There is no lowering for a two-word external call, so the importer rejects it with a located
error, whatever the number of state variables.

It used to import as two separate `staticcall`s that each decoded word 0 of the return data,
so the second result equalled the first, and without checking that the callee is `view`. That
path was gated on the compiled sources declaring more than one state variable in total, across
all contracts, so here it also fired for the one-variable contract.
-/
namespace SolidityImportSmoke.ExternalTupleCallChecks

solidity_profile tuple where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- A caller with two state variables.
/--
error: ExternalTupleCall.sol:17:34: MemberAccess: [solidity-import:unsupported] external contract calls are outside this slice
closure: ExternalTupleCall.change
ExternalTupleCall(address(this)).pair
-/
#guard_msgs in
solidity_import twoSlots from "Contracts/SolidityImportSmoke" entry "ExternalTupleCall.sol"
  using tuple
  contract ExternalTupleCall
  function change(uint256)

-- A caller with one state variable: rejected the same way.
/--
error: ExternalTupleCall.sol:32:34: MemberAccess: [solidity-import:unsupported] external contract calls are outside this slice
closure: ExternalTupleCallSingleSlot.change
ExternalTupleCallSingleSlot(address(this)).pair
-/
#guard_msgs in
solidity_import oneSlot from "Contracts/SolidityImportSmoke" entry "ExternalTupleCall.sol"
  using tuple
  contract ExternalTupleCallSingleSlot
  function change(uint256)

-- The functions without the external call still import.
solidity_import direct from "Contracts/SolidityImportSmoke" entry "ExternalTupleCall.sol"
  using tuple
  contract ExternalTupleCall
  function pair()
  function read()

example : Compiler.CompilationModel.CompilationModel := direct.model

end SolidityImportSmoke.ExternalTupleCallChecks
