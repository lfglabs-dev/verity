import Compiler.SolidityImport.Transactions

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport

-- No assumption on the world, current memory, bindings or return-data buffer.
theorem emptyRevert_exact (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) :
    execStmt oracle fields state .revertEmpty = .revertWithData [] := rfl

theorem emptyRevert_frame (oracle : DenoteOracle) (fields : List Field)
    (initial : Verity.ContractState) (state : DenoteState) :
    Transactions.finishFrame initial (execStmt oracle fields state .revertEmpty) =
      .ok { success := false, data := [], world := initial } := rfl

#print axioms emptyRevert_exact
#print axioms emptyRevert_frame
