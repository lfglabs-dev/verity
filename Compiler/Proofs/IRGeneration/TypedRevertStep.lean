import Compiler.Proofs.IRGeneration.GenericInduction.ErrorRevert
import Compiler.Proofs.IRGeneration.CustomErrorPayloadIR
import Compiler.CompilationModel.AbiEncoding

/-!
# Typed-error step lemmas with the revert observable discharged

`compiledStmtStep_requireError` and `compiledStmtStep_revertError` in
`GenericInduction.ErrorRevert` are proved modulo

    hrevertExec : ∀ state fuel, ∃ next, execIRStmts fuel state revertStmts = .revert next

`CustomErrorPayloadIR` provides the general machinery for that hypothesis
(`NonEscaping` / `RevertsAlways` / `execIRStmts_payloadBlock_revert`). This
module computes the payload shape `revertWithCustomError` emits for a
zero-parameter custom error, discharges `hrevertExec` for it, and joins the two
— giving the first `CompiledStmtStepWithHelpers` instances for typed errors and
therefore the first consumers of those two step lemmas.

The zero-parameter case is the one whose payload shape is already pinned down.
Errors *with* parameters emit the same statement vocabulary
(`let`/`assign`/`mstore`/`for`), all of which `CustomErrorPayloadIR` covers via
`NonEscaping`; what is still missing for them is the shape computation through
`attachOffsets` and `encodeStaticCustomErrorArg`, not any new semantic fact.

Note on namespacing: `bytesFromString`, `chunkBytes32` and `wordFromBytes` exist
in both `Compiler.ECM` and `Compiler.CompilationModel`. `CustomErrorPayloadIR`
opens the former (it is about the `Error(string)` payload); this module opens
only the latter, which is the one `revertWithCustomError` is defined against.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-! ## The zero-argument custom-error payload always reverts

`revertError E()` / `requireError c E()` compile through
`revertWithCustomError` to a single `block`: free-pointer load, the
signature-word `mstore`s, `keccak256`/`shl`/`shr` selector extraction, the
selector `mstore`, `let __err_tail = 0`, and the trailing `revert`. Every
statement before the `revert` is a `let` or an `mstore`, so the whole payload is
`RevertsAlways`. -/

/-- The zero-parameter payload prefix, as emitted by `revertWithCustomError`. -/
private def zeroArgErrorPrefix (errorDef : ErrorDef) : List YulStmt :=
  [YulStmt.let_ "__err_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])] ++
    ((chunkBytes32 (bytesFromString (errorSignature errorDef))).zipIdx.map
      (fun (chunk, idx) =>
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
          YulExpr.hex (wordFromBytes chunk)]))) ++
    [YulStmt.let_ "__err_hash"
        (YulExpr.call "keccak256" [YulExpr.ident "__err_ptr",
          YulExpr.lit (bytesFromString (errorSignature errorDef)).length]),
      YulStmt.let_ "__err_selector"
        (YulExpr.call "shl" [YulExpr.lit selectorShift,
          YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.ident "__err_hash"]]),
      YulStmt.exprStmt (YulExpr.call "mstore"
        [YulExpr.lit 0, YulExpr.ident "__err_selector"]),
      YulStmt.let_ "__err_tail" (YulExpr.lit 0)]

private theorem revertWithCustomError_zero_shape
    (dynamicSource : DynamicDataSource) (errorDef : ErrorDef)
    (hParams : errorDef.params = []) :
    revertWithCustomError dynamicSource errorDef [] [] = .ok
      [YulStmt.block (zeroArgErrorPrefix errorDef ++
        [YulStmt.exprStmt (YulExpr.call "revert"
          [YulExpr.lit 0,
            YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]])])] := by
  unfold revertWithCustomError zeroArgErrorPrefix
  simp [hParams]
  rfl

private theorem zeroArgErrorPrefix_nonEscaping (errorDef : ErrorDef) :
    ∀ stmt ∈ zeroArgErrorPrefix errorDef, NonEscaping stmt := by
  intro stmt hMem
  simp only [zeroArgErrorPrefix, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hMem
  rcases hMem with (rfl | ⟨chunkAndIdx, _, rfl⟩) | (rfl | rfl | rfl | rfl)
  · exact NonEscaping.let_ _ _
  · rcases chunkAndIdx with ⟨chunk, idx⟩
    exact NonEscaping.mstore _ _
  · exact NonEscaping.let_ _ _
  · exact NonEscaping.let_ _ _
  · exact NonEscaping.mstore _ _
  · exact NonEscaping.let_ _ _

/-- `hrevertExec` for a zero-argument custom error: the compiled payload reverts
from every state at every fuel value. -/
theorem execIRStmts_revertWithCustomError_zero_revert
    (dynamicSource : DynamicDataSource) (errorDef : ErrorDef)
    (hParams : errorDef.params = []) {out : List YulStmt}
    (hOk : revertWithCustomError dynamicSource errorDef [] [] = .ok out) :
    ∀ (state : IRState) (fuel : Nat),
      ∃ next, execIRStmts fuel state out = .revert next := by
  rw [revertWithCustomError_zero_shape dynamicSource errorDef hParams] at hOk
  injection hOk with hOk
  subst out
  exact execIRStmts_payloadBlock_revert _ _ (zeroArgErrorPrefix_nonEscaping errorDef)

/-! ## Step lemmas -/

/-- `revertError E()` for a zero-parameter custom error `E`, with the revert
observable discharged. -/
theorem compiledStmtStep_revertError_zeroArg
    {spec : CompilationModel} {fields : List Field} {scope : List String}
    {errorName : String} {errorDef : ErrorDef} {revertStmts : List YulStmt}
    (hparams : errorDef.params = [])
    (hpayload : revertWithCustomError .calldata errorDef [] [] = .ok revertStmts)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (.revertError errorName []) = Except.ok revertStmts) :
    CompiledStmtStepWithHelpers spec fields scope (.revertError errorName []) revertStmts :=
  compiledStmtStep_revertError hcompile
    (execIRStmts_revertWithCustomError_zero_revert .calldata errorDef hparams hpayload)

/-- `requireError cond E()` for a zero-parameter custom error `E`, with the
revert observable discharged. -/
theorem compiledStmtStep_requireError_zeroArg
    {spec : CompilationModel} {fields : List Field} {scope : List String} {cond : Expr}
    {errorName : String} {errorDef : ErrorDef} {failCond : YulExpr}
    {revertStmts : List YulStmt}
    (hcore : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hhelperSurface : exprTouchesUnsupportedHelperSurface cond = false)
    (hnextScopeIncl : FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (.requireError cond errorName [])) scope)
    (hfailCompile :
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
    (hparams : errorDef.params = [])
    (hpayload : revertWithCustomError .calldata errorDef [] [] = .ok revertStmts)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (.requireError cond errorName []) = Except.ok [YulStmt.if_ failCond revertStmts]) :
    CompiledStmtStepWithHelpers spec fields scope (.requireError cond errorName [])
      [YulStmt.if_ failCond revertStmts] :=
  compiledStmtStep_requireError hcore hinScope hhelperSurface hnextScopeIncl hfailCompile
    hcompile
    (execIRStmts_revertWithCustomError_zero_revert .calldata errorDef hparams hpayload)

end Compiler.Proofs.IRGeneration
