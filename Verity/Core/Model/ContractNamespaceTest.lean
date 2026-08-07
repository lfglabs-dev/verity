import Verity.Core.Model.AllocationExtraction

namespace Verity.Core.Model.ContractNamespaceTest

open Compiler.CompilationModel
open AllocationExtraction

private def model (id : Nat) : CompilationModel :=
  { name := "namespace-test", contractId := id, fields := [], constructor := none,
    functions := [] }

/-- The same local slot in distinct positive contract worlds cannot alias. -/
example (slot : Nat) :
    canonicalSlot (model 1) 1 slot ≠ canonicalSlot (model 2) 2 slot := by
  simp [canonicalSlot]

example (slot : Nat) :
    canonicalSlot (model 2) 2 slot ≠ canonicalSlot (model 3) 3 slot := by
  simp [canonicalSlot]

/-- The legacy single-contract canonical slot remains unchanged. -/
example (slot : Nat) : canonicalSlot (model 0) 0 slot = slot := by
  simp [canonicalSlot]

/-- Legacy single-contract reads remain exactly the id-zero namespace. -/
example (state : Verity.ContractState) (slot : Nat) :
    state.readContractSlot 0 slot = state.readSlot slot := by
  exact Verity.ContractState.readContractSlot_zero state slot

/-- Legacy single-contract writes update the original storage field. -/
example (state : Verity.ContractState) (slot : Nat) (value : Verity.Uint256) :
    (state.writeContractSlot 0 slot value).readSlot slot = value := by
  simp [Verity.ContractState.writeContractSlot]

/-- A write in one contract world is invisible at the same slot in another. -/
example (state : Verity.ContractState) (slot : Nat) (value : Verity.Uint256) :
    (state.writeContractSlot 1 slot value).readContractSlot 2 slot =
      state.readContractSlot 2 slot := by
  apply Verity.ContractState.readContractSlot_writeContractSlot_other_contract
  omega

end Verity.Core.Model.ContractNamespaceTest
