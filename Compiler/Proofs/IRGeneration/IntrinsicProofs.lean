import Compiler.CompilationModel.ExpressionCompile
import Compiler.Proofs.IRGeneration.ExprCore
import Verity.Core.Intrinsics

/-!
  Proven intrinsic plumbing.

  These lemmas cover the Verity-owned fragment of consumer intrinsics:
  fork-order checks, IR scope accounting, and the exact Yul shape emitted by the
  focused CLZ prototype. They deliberately do not prove EIP-7939 CLZ opcode
  semantics; that remains the consumer obligation until EVMYulLean models the
  opcode.
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

@[simp] theorem exprBoundNames_intrinsic (name : String) (args : List Expr) :
    FunctionBody.exprBoundNames (.intrinsic name args) =
      FunctionBody.exprListBoundNames args := by
  simp [FunctionBody.exprBoundNames]

theorem intrinsic_boundNamesInScope_of_args
    {scope : List String} {name : String} {args : List Expr}
    (hArgs : ∀ n, n ∈ FunctionBody.exprListBoundNames args → n ∈ scope) :
    FunctionBody.exprBoundNamesInScope (.intrinsic name args) scope := by
  intro n hMem
  exact hArgs n (by simpa using hMem)

/-- CLZ is a Fusaka-only intrinsic in the prototype fork model. -/
theorem clz_minFork_not_allowed_on_shanghai :
    HardFork.allows .shanghai .fusaka = false := by
  simp

/-- CLZ is accepted when the target fork is Fusaka. -/
theorem clz_minFork_allowed_on_fusaka :
    HardFork.allows .fusaka .fusaka = true := by
  simp

/-- The focused CLZ lowering has one input and one output. -/
theorem clz_lowering_arity :
    YulLowering.inputArity (.verbatim 1 1 "1e") = some 1 ∧
      YulLowering.outputArity (.verbatim 1 1 "1e") = some 1 := by
  simp [YulLowering.inputArity, YulLowering.outputArity]

/-- The focused CLZ lowering names Solidity's standalone-Yul verbatim builtin. -/
theorem clz_lowering_callName :
    YulLowering.callName (.verbatim 1 1 "1e") = "verbatim_1i_1o" := by
  rfl

/-- The focused CLZ lowering carries opcode byte `0x1e` as the verbatim hex literal. -/
theorem clz_lowering_hex :
    YulLowering.hexLiteral? (.verbatim 1 1 "1e") = some "hex\"1e\"" := by
  rfl

/-- A CLZ intrinsic over a parameter lowers to the exact verbatim call shape. -/
theorem compileExpr_clz_param
    (fields : List Field) (dynamicSource : DynamicDataSource) (x : String) :
    compileExpr fields dynamicSource (.intrinsic "clz" [.param x]) =
      .ok (YulExpr.call "verbatim_1i_1o"
        [YulExpr.ident "hex\"1e\"", YulExpr.ident x]) := by
  simp [compileExpr, compileExprList, Pure.pure, Except.pure, bind, Except.bind]

/-- A CLZ intrinsic over any successfully compiled argument lowers by wrapping
    that argument in `verbatim_1i_1o(hex"1e", ...)`. -/
theorem compileExpr_clz_of_arg_ok
    {fields : List Field} {dynamicSource : DynamicDataSource}
    {arg : Expr} {argY : YulExpr}
    (hArg : compileExpr fields dynamicSource arg = .ok argY) :
    compileExpr fields dynamicSource (.intrinsic "clz" [arg]) =
      .ok (YulExpr.call "verbatim_1i_1o" [YulExpr.ident "hex\"1e\"", argY]) := by
  simp [compileExpr, compileExprList, hArg, Pure.pure, Except.pure, bind, Except.bind]

/-- CLZ arity mismatch is fail-closed in expression lowering. -/
theorem compileExpr_clz_wrong_arity_error
    (fields : List Field) (dynamicSource : DynamicDataSource) (args : List Expr)
    (hLen : args.length ≠ 1) :
    ∃ msg, compileExpr fields dynamicSource (.intrinsic "clz" args) = .error msg := by
  cases args with
  | nil =>
      refine ⟨toString "Compilation error: intrinsic clz expects 1 arg, got " ++
        toString 0 ++ toString "", ?_⟩
      rfl
  | cons a rest =>
      cases rest with
      | nil =>
          exact False.elim (hLen rfl)
      | cons b rest' =>
          refine ⟨toString "Compilation error: intrinsic clz expects 1 arg, got " ++
            toString (rest'.length + 1 + 1) ++ toString "", ?_⟩
          rfl

end IntrinsicProofs

end Compiler.Proofs.IRGeneration
