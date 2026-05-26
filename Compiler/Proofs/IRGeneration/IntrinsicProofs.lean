import Compiler.CompilationModel.ExpressionCompile
import Compiler.Proofs.IRGeneration.ExprCore
import Verity.Core.Intrinsics

/-!
  Proven intrinsic plumbing.

  These lemmas cover the Verity-owned fragment of consumer intrinsics:
  fork-order checks, IR scope accounting, generic Yul lowering shape, and
  fail-closed verbatim arity checks. They deliberately do not prove any opcode
  semantics; that remains the consumer obligation until the backend semantics
  model knows the opcode.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Verity.Core.Intrinsics

namespace IntrinsicProofs

theorem hardFork_allows_eq_rank_decide (target required : HardFork) :
    HardFork.allows target required =
      decide (required.rank ≤ target.rank) := by
  cases target <;> cases required <;> rfl

theorem hardFork_allows_iff_rank_le (target required : HardFork) :
    HardFork.allows target required = true ↔ required.rank ≤ target.rank := by
  rw [hardFork_allows_eq_rank_decide]
  simp

@[simp] theorem exprBoundNames_intrinsic
    (name : String) (lowering : YulLowering) (args : List Expr) :
    FunctionBody.exprBoundNames (.intrinsic name lowering args) =
      FunctionBody.exprListBoundNames args := by
  simp [FunctionBody.exprBoundNames]

theorem intrinsic_boundNamesInScope_of_args
    {scope : List String} {name : String} {lowering : YulLowering} {args : List Expr}
    (hArgs : ∀ n, n ∈ FunctionBody.exprListBoundNames args → n ∈ scope) :
    FunctionBody.exprBoundNamesInScope (.intrinsic name lowering args) scope := by
  intro n hMem
  exact hArgs n (by simpa using hMem)

theorem verbatim_lowering_callName
    (inputs outputs : Nat) (opcodeHex : String) :
    YulLowering.callName (.verbatim inputs outputs opcodeHex) =
      s!"verbatim_{inputs}i_{outputs}o" := by
  rfl

theorem verbatim_lowering_hexLiteral
    (inputs outputs : Nat) (opcodeHex : String) :
    YulLowering.hexLiteral? (.verbatim inputs outputs opcodeHex) =
      some s!"hex\"{opcodeHex}\"" := by
  rfl

theorem compileExpr_intrinsic_verbatim_one_param
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name opcodeHex x : String) :
    compileExpr fields dynamicSource (.intrinsic name (.verbatim 1 1 opcodeHex) [.param x]) =
      .ok (YulExpr.call s!"verbatim_{1}i_{1}o"
        [YulExpr.ident s!"hex\"{opcodeHex}\"", YulExpr.ident x]) := by
  simp [compileExpr, compileExprList, YulLowering.callName, Pure.pure, Except.pure,
    bind, Except.bind]

theorem compileExpr_intrinsic_builtin_one_param
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name builtinName x : String) :
    compileExpr fields dynamicSource (.intrinsic name (.builtin builtinName) [.param x]) =
      .ok (YulExpr.call builtinName [YulExpr.ident x]) := by
  simp [compileExpr, compileExprList, Pure.pure, Except.pure, bind, Except.bind]

theorem compileExpr_intrinsic_verbatim_zero_output_error
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name opcodeHex x : String) :
    ∃ msg,
      compileExpr fields dynamicSource (.intrinsic name (.verbatim 1 0 opcodeHex) [.param x]) =
        .error msg := by
  refine ⟨toString "Compilation error: intrinsic " ++ toString name ++
    toString " must produce exactly 1 output, got " ++ toString 0 ++ toString "", ?_⟩
  simp [compileExpr, compileExprList, Pure.pure, Except.pure, bind, Except.bind]

theorem compileExpr_intrinsic_verbatim_wrong_arity_error
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name opcodeHex x y : String) :
    ∃ msg,
      compileExpr fields dynamicSource (.intrinsic name (.verbatim 1 1 opcodeHex)
        [.param x, .param y]) = .error msg := by
  refine ⟨toString "Compilation error: intrinsic " ++ toString name ++
    toString " expects " ++ toString 1 ++ toString " arg(s), got " ++
    toString 2 ++ toString "", ?_⟩
  simp [compileExpr, compileExprList, Pure.pure, Except.pure, bind, Except.bind]

end IntrinsicProofs

end Compiler.Proofs.IRGeneration
