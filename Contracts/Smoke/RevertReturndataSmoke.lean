import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

/-!
`revertReturndata` ends the call with a revert, in the executable EDSL as in the compiled code
(`returndatacopy` then `revert(0, returndatasize())`). The idiom `if ok == 0 then
revertReturndata` after a low-level call must stop there: nothing after it runs.
-/
verity_contract RevertReturndataSmoke where
  storage
    marker : Uint256 := slot 0

  -- `failed` stands for a failed call's success bit being 0
  function bubbleIf (failed : Bool) : Unit := do
    if failed then
      revertReturndata
    else
      pure ()
    setStorage marker 1

/-- When the bubbling branch is taken, the call reverts with the returndata bytes and the
write after it never happens. -/
theorem bubbleIf_reverts (s : ContractState) :
    (RevertReturndataSmoke.bubbleIf true).run s =
      .revert (.raw (s.rawReturndata.getD
        (Compiler.CompilationModel.Denote.returndataRevertBytes s.returndata))) s :=
  rfl

/-- Otherwise execution continues and writes `marker`. -/
theorem bubbleIf_continues (s : ContractState) :
    ∃ s', (RevertReturndataSmoke.bubbleIf false).run s = .success () s' ∧
      s'.storage 0 = 1 := by
  exact ⟨_, rfl, rfl⟩

end Contracts.Smoke
