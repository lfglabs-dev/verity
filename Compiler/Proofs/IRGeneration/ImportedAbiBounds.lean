import Compiler.Proofs.IRGeneration.ImportedAbiTupleHead

namespace Compiler.Proofs.IRGeneration.ImportedAbiBounds
open Compiler.CompilationModel Denote

theorem le_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (left right : Expr) (a b : Nat)
    (l : evalExpr oracle fields state left = some a) (r : evalExpr oracle fields state right = some b)
    (ordered : a ≤ b) : evalExpr oracle fields state (.le left right) = some 1 := by
  rw [evalExpr, l, r]
  simp [boolWord, ordered]

/-- Signed comparison is a natural comparison only after proving both signs. -/
theorem slt_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (left right : Expr) (a b : Nat)
    (l : evalExpr oracle fields state left = some a) (r : evalExpr oracle fields state right = some b)
    (smallA : a < Verity.Core.Int256.signBit) (smallB : b < Verity.Core.Int256.signBit)
    (ordered : a < b) : evalExpr oracle fields state (.slt left right) = some 1 := by
  rw [evalExpr, l, r]
  simp [ImportedAbiTupleHead.signed_small a smallA, ImportedAbiTupleHead.signed_small b smallB,
    boolWord, ordered]

/-- Actual multiplication, with all input and result truncation discharged. -/
theorem mul_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (left right : Expr) (a b : Nat)
    (l : evalExpr oracle fields state left = some a) (r : evalExpr oracle fields state right = some b)
    (smallA : a < Verity.Core.Uint256.modulus) (smallB : b < Verity.Core.Uint256.modulus)
    (product : a * b < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.mul left right) = some (a * b) := by
  rw [evalExpr, l, r]
  change some ((a % Verity.Core.Uint256.modulus * (b % Verity.Core.Uint256.modulus)) %
    Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt smallA, Nat.mod_eq_of_lt smallB, Nat.mod_eq_of_lt product]

/-- Successful allocation guards execute their real empty branch. -/
theorem allocation_cons (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (condition : Expr) (rest : List Stmt) (resolved : evalExpr oracle fields state condition = some 1) :
    execStmtList oracle fields state (.ite condition [] [.panicCode (.literal 0x41)] :: rest) =
      execStmtList oracle fields state rest := by
  simp [execStmtList, execStmt, resolved]

end Compiler.Proofs.IRGeneration.ImportedAbiBounds
