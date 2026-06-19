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
    FunctionBody.exprBoundNames (.intrinsic name lowering minFork args) =
      FunctionBody.exprListBoundNames args := by
  simp [FunctionBody.exprBoundNames]

theorem intrinsic_boundNamesInScope_of_args
    {scope : List String} {name : String} {lowering : YulLowering} {args : List Expr}
    (hArgs : ∀ n, n ∈ FunctionBody.exprListBoundNames args → n ∈ scope) :
    FunctionBody.exprBoundNamesInScope (.intrinsic name lowering minFork args) scope := by
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

private theorem compileExprWithInternals_param
    (fields : List Field) (dynamicSource : DynamicDataSource) (x : String) :
    compileExprWithInternals fields dynamicSource [] (.param x) =
      .ok (YulExpr.ident x) := by
  unfold compileExprWithInternals
  rfl

private theorem compileExprListWithInternals_nil
    (fields : List Field) (dynamicSource : DynamicDataSource) :
    compileExprListWithInternals fields dynamicSource [] [] =
      .ok [] := by
  unfold compileExprListWithInternals
  rfl

private theorem compileExprListWithInternals_param_one
    (fields : List Field) (dynamicSource : DynamicDataSource) (x : String) :
    compileExprListWithInternals fields dynamicSource [] [.param x] =
      .ok [YulExpr.ident x] := by
  unfold compileExprListWithInternals
  rw [compileExprWithInternals_param, compileExprListWithInternals_nil]
  rfl

private theorem compileExprListWithInternals_param_two
    (fields : List Field) (dynamicSource : DynamicDataSource) (x y : String) :
    compileExprListWithInternals fields dynamicSource [] [.param x, .param y] =
      .ok [YulExpr.ident x, YulExpr.ident y] := by
  unfold compileExprListWithInternals
  rw [compileExprWithInternals_param, compileExprListWithInternals_param_one]
  rfl

theorem compileExpr_intrinsic_verbatim_one_param
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name opcodeHex x : String) :
  compileExpr fields dynamicSource (.intrinsic name (.verbatim 1 1 opcodeHex) .cancun [.param x]) =
      .ok (YulExpr.call s!"verbatim_{1}i_{1}o"
        [YulExpr.verbatimHex opcodeHex, YulExpr.ident x]) := by
  unfold compileExpr
  unfold compileExprWithInternals
  rw [compileExprListWithInternals_param_one]
  rfl

theorem compileExpr_intrinsic_builtin_one_param
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name x : String) :
  compileExpr fields dynamicSource (.intrinsic name (.builtin "not") .cancun [.param x]) =
      .ok (YulExpr.call "not" [YulExpr.ident x]) := by
  unfold compileExpr
  unfold compileExprWithInternals
  rw [compileExprListWithInternals_param_one]
  rfl

theorem compileExpr_intrinsic_verbatim_zero_output_error
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name opcodeHex x : String) :
    ∃ msg,
      compileExpr fields dynamicSource (.intrinsic name (.verbatim 1 0 opcodeHex) .cancun [.param x]) =
        .error msg := by
  refine ⟨toString "Compilation error: intrinsic " ++ toString name ++
    toString " must produce exactly 1 output, got " ++ toString 0 ++ toString "", ?_⟩
  unfold compileExpr
  unfold compileExprWithInternals
  rw [compileExprListWithInternals_param_one]
  rfl

theorem compileExpr_intrinsic_verbatim_wrong_arity_error
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (name opcodeHex x y : String) :
    ∃ msg,
      compileExpr fields dynamicSource (.intrinsic name (.verbatim 1 1 opcodeHex) .cancun
        [.param x, .param y]) = .error msg := by
  refine ⟨toString "Compilation error: intrinsic " ++ toString name ++
    toString " expects " ++ toString 1 ++ toString " arg(s), got " ++
    toString 2 ++ toString "", ?_⟩
  unfold compileExpr
  unfold compileExprWithInternals
  rw [compileExprListWithInternals_param_two]
  rfl

end IntrinsicProofs

end Compiler.Proofs.IRGeneration
