import Compiler.SolidityImport.Import

/-!
`while (!cond)` (`WhileNegatedCondition.sol`).

The loop gives no iteration bound the importer can derive. It used to lower to a loop of at
most 256 iterations when the compiled sources declared more than one state variable, so
`countTo(300)` stored 256 where solc stores 300. It is now a located rejection in every
contract.
-/
namespace SolidityImportSmoke.WhileNegatedConditionChecks

solidity_profile whileNegated where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- A counting loop that runs `n` times.
/--
error: WhileNegatedCondition.sol:12:16: UnaryOperation: [solidity-import:unsupported] a while loop with a negated condition has no derivable iteration bound
closure: WhileNegatedCondition.countTo
!(i == n)
-/
#guard_msgs in
solidity_import countToForm from "Contracts/SolidityImportSmoke" entry "WhileNegatedCondition.sol"
  using whileNegated
  contract WhileNegatedCondition
  function countTo(uint256)

-- A subtracting loop that runs `n / 10` times.
/--
error: WhileNegatedCondition.sol:19:16: UnaryOperation: [solidity-import:unsupported] a while loop with a negated condition has no derivable iteration bound
closure: WhileNegatedCondition.countDown
!(i < 10)
-/
#guard_msgs in
solidity_import countDownForm from "Contracts/SolidityImportSmoke" entry "WhileNegatedCondition.sol"
  using whileNegated
  contract WhileNegatedCondition
  function countDown(uint256)

end SolidityImportSmoke.WhileNegatedConditionChecks
