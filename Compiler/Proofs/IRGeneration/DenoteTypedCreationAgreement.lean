import Compiler.Proofs.IRGeneration.SourceTypedCompatibility
import Compiler.Proofs.IRGeneration.DenoteAgreement

/-! Agreement of the actual typed Source creation consumer with Denote at the
computed operand poststate. Actual opcode-entry context is still mandatory;
this step neither fabricates gas nor proves whole-function native agreement. -/
namespace Compiler.Proofs.IRGeneration.DenoteTypedCreationAgreement
open Compiler.CompilationModel
open SourceSemantics SourceTypedCompatibility

theorem create2_at_operand_poststate (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (initial : RuntimeState) (final : Denote.DenoteState)
    (destination : String) (offset size salt : Expr) (dst extent nonce : Nat)
    (trace : ArgumentTrace (SourceStatementEvaluation.execInternalStmts spec fields fuel)
      spec fields fuel initial [offset, size, salt] [dst, extent, nonce]
      (DenoteAgreement.toRuntimeState final)) :
    SourceStatementEvaluation.execStmt spec fields (fuel + 1) initial
      (.create2 destination offset size salt) =
      DenoteAgreement.toStmtResult (Denote.execCreation DenoteAgreement.sourceOracle fields final
        destination (.literal dst) (.literal extent) (.literal nonce)) := by
  rw [argumentTrace_create2 spec fields fuel initial _ destination offset size salt dst extent nonce trace]
  exact (DenoteAgreement.execCreation_eq fields final destination _ _ _).symm

end Compiler.Proofs.IRGeneration.DenoteTypedCreationAgreement
