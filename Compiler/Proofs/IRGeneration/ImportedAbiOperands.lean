import Compiler.Proofs.IRGeneration.ImportedPrefixFrames

namespace Compiler.Proofs.IRGeneration.ImportedAbiOperands
open Compiler.CompilationModel Compiler.CompilationModel.Denote

/-- The actual two final ABI loads preceding the isolated mapping write. -/
def loads : List Stmt := [
  .letVar "_verity_slice_tmp_1" (.calldataload (.literal 36)),
  .letVar "_verity_slice_tmp_2" (.calldataload (.literal 68))]

def loaded (state : DenoteState) : DenoteState :=
  { state with
    bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_1"
        (state.world.calldata.getD 1 0 % Compiler.Constants.evmModulus))
        "_verity_slice_tmp_2" (state.world.calldata.getD 2 0 % Compiler.Constants.evmModulus) }

/-- Symbolic calldata and state: no ABI execution is reduced in the kernel. -/
theorem execute_loads (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) :
    execStmtList oracle fields state loads = .continue (loaded state) := by
  rfl

theorem loaded_key (state : DenoteState) :
    lookupValue (loaded state).bindings "_verity_slice_tmp_1" =
      state.world.calldata.getD 1 0 % Compiler.Constants.evmModulus := by
  simp only [loaded]
  rw [SolidityImport.lookup_bind_other _ _ _ _ (by decide), SolidityImport.lookup_bind_same]

theorem loaded_value (state : DenoteState) :
    lookupValue (loaded state).bindings "_verity_slice_tmp_2" =
      state.world.calldata.getD 2 0 % Compiler.Constants.evmModulus := by
  exact SolidityImport.lookup_bind_same _ _ _

end Compiler.Proofs.IRGeneration.ImportedAbiOperands
