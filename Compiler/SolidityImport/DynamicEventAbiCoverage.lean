import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.DynamicEventAbi

namespace Compiler.CompilationModel.SolidityImport.DynamicEventAbi

/-!
Coverage entry for the dynamic-array event payload: whenever the importer's
operands are covered, every statement `encode` emits is in the executable
whitelist (`executableStmtListCovered`), so the payload runs only through
whitelisted Denote arms before the closed `SolidityLog` transport.
-/

/-- Every operand of an argument is a covered expression. -/
def Argument.covered : Argument → Bool
  | .word value => exprCovered value
  | .calldataArray data length _ => exprCovered data && exprCovered length

/-- Covered arguments, in order. -/
def argumentsCovered : List Argument → Bool
  | [] => true
  | argument :: rest => argument.covered && argumentsCovered rest

theorem executableStmtListCovered_append (xs ys : List Stmt) :
    executableStmtListCovered (xs ++ ys) =
      (executableStmtListCovered xs && executableStmtListCovered ys) := by
  induction xs with
  | nil => simp [executableStmtListCovered]
  | cons x rest ih => simp [executableStmtListCovered, ih, Bool.and_assoc]

theorem elementBody_covered (names : ArrayNames) (data : Expr) (kind : SolidityAbi.ScalarKind)
    (hData : exprCovered data = true) :
    executableStmtListCovered (elementBody names data kind) = true := by
  unfold elementBody
  split <;> simp [executableStmtListCovered, executableStmtCovered, stmtCovered,
    exprCovered, AbiLowering.guard, hData]

theorem arrayTail_covered (base position : Expr) (headIndex : Nat) (names : ArrayNames)
    (data length : Expr) (kind : SolidityAbi.ScalarKind) (hBase : exprCovered base = true)
    (hPosition : exprCovered position = true) (hData : exprCovered data = true)
    (hLength : exprCovered length = true) :
    executableStmtListCovered (arrayTail base headIndex position names data length kind) =
      true := by
  have hBody := elementBody_covered names data kind hData
  simp [arrayTail, executableStmtListCovered, executableStmtCovered, stmtCovered, exprCovered,
    hBase, hPosition, hLength, hBody]

theorem encodeFrom_covered (base : Expr) (hBase : exprCovered base = true) :
    ∀ (headIndex : Nat) (position : Expr) (names : List ArrayNames) (arguments : List Argument),
      exprCovered position = true → argumentsCovered arguments = true →
      executableStmtListCovered (encodeFrom base headIndex position names arguments).1 = true ∧
        exprCovered (encodeFrom base headIndex position names arguments).2 = true
  | _, position, _, [], hPosition, _ => by simp [encodeFrom, executableStmtListCovered, hPosition]
  | headIndex, position, names, .word value :: rest, hPosition, hArguments => by
      simp only [argumentsCovered, Argument.covered, Bool.and_eq_true] at hArguments
      have ih := encodeFrom_covered base hBase (headIndex + 1) position names rest hPosition
        hArguments.2
      simp [encodeFrom, executableStmtListCovered, executableStmtCovered, exprCovered, hBase,
        hArguments.1, ih]
  | headIndex, position, arrayNames :: names, .calldataArray data length kind :: rest,
      hPosition, hArguments => by
      simp only [argumentsCovered, Argument.covered, Bool.and_eq_true] at hArguments
      have hEnd : exprCovered (arrayEnd arrayNames length) = true := by
        simp [arrayEnd, exprCovered, hArguments.1.2]
      have ih := encodeFrom_covered base hBase (headIndex + 1) _ names rest hEnd hArguments.2
      have hTail := arrayTail_covered base position headIndex arrayNames data length kind hBase
        hPosition hArguments.1.1 hArguments.1.2
      simp [encodeFrom, executableStmtListCovered_append, hTail, ih]
  | _, position, [], .calldataArray .. :: _, hPosition, _ => by
      simp [encodeFrom, executableStmtListCovered, hPosition]

/-- The importer's coverage gate accepts every encoded payload over covered operands. -/
theorem encode_covered (pointer size : String) (names : List ArrayNames)
    (arguments : List Argument) (body : List Stmt)
    (hEncode : encode pointer size names arguments = some body)
    (hArguments : argumentsCovered arguments = true) :
    executableStmtListCovered body = true := by
  unfold encode at hEncode
  split at hEncode
  · cases hEncode
  · cases hEncode
    have h := encodeFrom_covered (.localVar pointer) rfl 0
      (.add (.localVar pointer) (.literal (32 * arguments.length))) names arguments rfl hArguments
    simp [executableStmtListCovered_append, executableStmtListCovered, executableStmtCovered,
      stmtCovered, exprCovered, h.1, h.2]

end Compiler.CompilationModel.SolidityImport.DynamicEventAbi
