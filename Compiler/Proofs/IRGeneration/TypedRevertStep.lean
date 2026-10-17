import Compiler.Proofs.IRGeneration.GenericInduction.CustomErrorDomain
import Compiler.Proofs.IRGeneration.CustomErrorPayloadIR
import Compiler.CompilationModel.AbiEncoding

/-!
# Typed custom-error steps with exact observed payloads

The legacy NonEscaping/RevertsAlways laws below classify the statement shape;
they do not certify payload bytes or adequate fuel. Typed step consumers use
actual compiler/Source/physical execution laws, with explicit declaration,
canonical argument, scratch-frame, extent and fuel obligations. The declared
zero-error instance uses CustomErrorDomain; pointwise conditional/scalar laws
retain every computed-byte assertion while function-domain preservation is
being integrated. No arbitrary-runtime or exhausted-execution payload is assumed.
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

/-! ## The one-static-argument custom-error payload always reverts

The zero-parameter case above stops short of the only genuinely different
ingredient a parameterized error adds: the argument stores emitted between
`let __err_tail` and the trailing `revert`. For a single parameter of static
scalar type that store is one `mstore` at head offset `4`, so the payload is
still built entirely from `let`/`mstore` and stays `RevertsAlways`.

Types whose store goes through `compileUnindexedAbiEncode` (`bytes`, `string`,
`array`, dynamic `tuple`/`fixedArray`) are out of reach here for a structural
reason rather than a semantic one: that encoder is a `partial def`, so it has no
equation lemmas and its output shape cannot be computed in a proof. `adt` and
static composites are reachable in principle but emit a parameter-count-dependent
list of stores. -/

/-- Parameter types whose custom-error argument store is a single `mstore` of an
`encodeStaticCustomErrorArg` result. -/
private def customErrorStaticScalarParam : ParamType → Bool
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bool | .bytes32 => true
  | _ => false

/-- The single-static-argument payload prefix, as emitted by
`revertWithCustomError`. Identical to `zeroArgErrorPrefix` except that the ABI
tail cursor starts past the one-word head and the argument store follows. -/
private def oneStaticArgErrorPrefix (errorDef : ErrorDef) (encoded : YulExpr) :
    List YulStmt :=
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
      YulStmt.let_ "__err_tail" (YulExpr.lit (abiHeadSize errorDef.params)),
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, encoded])]

private theorem oneStaticArgErrorPrefix_nonEscaping (errorDef : ErrorDef)
    (encoded : YulExpr) :
    ∀ stmt ∈ oneStaticArgErrorPrefix errorDef encoded, NonEscaping stmt := by
  intro stmt hMem
  simp only [oneStaticArgErrorPrefix, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hMem
  rcases hMem with (rfl | ⟨chunkAndIdx, _, rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
  · exact NonEscaping.let_ _ _
  · rcases chunkAndIdx with ⟨chunk, idx⟩
    exact NonEscaping.mstore _ _
  · exact NonEscaping.let_ _ _
  · exact NonEscaping.let_ _ _
  · exact NonEscaping.mstore _ _
  · exact NonEscaping.let_ _ _
  · exact NonEscaping.mstore _ _

private theorem revertWithCustomError_oneStatic_shape
    (dynamicSource : DynamicDataSource) (errorDef : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (hParams : errorDef.params = [ty])
    (hStatic : customErrorStaticScalarParam ty = true)
    (hEncoded : encodeStaticCustomErrorArg errorDef.name ty argExpr = .ok encoded) :
    revertWithCustomError dynamicSource errorDef [srcExpr] [argExpr] = .ok
      [YulStmt.block (oneStaticArgErrorPrefix errorDef encoded ++
        [YulStmt.exprStmt (YulExpr.call "revert"
          [YulExpr.lit 0,
            YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]])])] := by
  unfold revertWithCustomError oneStaticArgErrorPrefix
  cases ty <;> simp_all [customErrorStaticScalarParam, revertWithCustomError.attachOffsets]

/-- `hrevertExec` for a custom error with one static scalar argument: the
compiled payload reverts from every state at every fuel value. -/
theorem execIRStmts_revertWithCustomError_oneStatic_revert
    (dynamicSource : DynamicDataSource) (errorDef : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (hParams : errorDef.params = [ty])
    (hStatic : customErrorStaticScalarParam ty = true)
    (hEncoded : encodeStaticCustomErrorArg errorDef.name ty argExpr = .ok encoded)
    {out : List YulStmt}
    (hOk : revertWithCustomError dynamicSource errorDef [srcExpr] [argExpr] = .ok out) :
    ∀ (state : IRState) (fuel : Nat),
      ∃ next, execIRStmts fuel state out = .revert next := by
  rw [revertWithCustomError_oneStatic_shape dynamicSource errorDef ty srcExpr argExpr encoded
    hParams hStatic hEncoded] at hOk
  injection hOk with hOk
  subst out
  exact execIRStmts_payloadBlock_revert _ _
    (oneStaticArgErrorPrefix_nonEscaping errorDef encoded)

/-! ## Exact typed step consumers -/

theorem compiledStmtStep_revertError_zeroArg
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (definition : ErrorDef) (out : List YulStmt)
    (params : definition.params = [])
    (compilerLookup : spec.errors.find? (·.name == definition.name) = some definition)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (compiled : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.revertError definition.name []) = .ok out) :
    CompiledErrorStepWithin spec fields scope (.revertError definition.name []) out
      ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + 5) :=
  compiledErrorStep_zero_within spec fields scope definition out params compilerLookup unique compiled

theorem compiledStmtStep_requireError_zeroArg
    (fields : List Field) (scope : List String) (errors : List ErrorDef)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (definition : ErrorDef) (cond : Expr) (failCond : YulExpr) (extra : Nat)
    (params : definition.params = [])
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (runtimeLookup : runtime.errors.filter (·.name == definition.name) = [definition])
    (condition : compileRequireFailCondWithInternals fields .calldata [] cond = .ok failCond)
    (sourceCond : SourceSemantics.evalExpr fields runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out data final,
      CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.requireError cond definition.name []) = .ok [.if_ failCond out] ∧
      SourceSemantics.execStmt fields runtime (.requireError cond definition.name []) =
        .revertWithData data ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 9)
        state [.if_ failCond out] = .revert final ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond definition.name []))
        (.revertWithData data) (.revert final) :=
  compiled_requireError_zero_failure_exact_bytes fields scope errors runtime state definition cond
    failCond extra params compilerLookup runtimeLookup condition sourceCond compiledCond extent

open PhysicalCustomErrorScalarExecution CustomErrorExpressionFrame

theorem compiledStmtStep_revertError_oneStaticArg (definition : ErrorDef) (fields : List Field)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (scope : List String) (errors : List ErrorDef)
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals fields .calldata [] [srcExpr] = .ok [argExpr])
    (params : definition.params = [ty]) (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (state : IRState) (value extra : Nat)
    (runtime : SourceSemantics.RuntimeState) (typeName : String)
    (evaluated : SourceSemantics.evalExprList fields runtime [srcExpr] = some [value])
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (supported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr state argExpr = some value)
    (supportedExpr : ScratchExpr argExpr) :
    ∃ out sourceResult irExec,
      CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.revertError definition.name [srcExpr]) = .ok out ∧
      SourceSemantics.execStmt fields runtime (.revertError definition.name [srcExpr]) = sourceResult ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 8) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.revertError definition.name [srcExpr]))
        sourceResult irExec :=
  compiled_revertError_scalar_exact_bytes definition fields ty srcExpr argExpr encoded scope errors
    compilerLookup compiledArgs params scalar encoding state value extra runtime typeName
    evaluated resolved canonical supported extent argument supportedExpr

theorem compiledStmtStep_requireError_oneStaticArg (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state final : IRState)
    (cond : Expr) (name : String) (args : List Expr) (failCond : YulExpr)
    (out : List YulStmt) (data : List UInt8) (fuel : Nat)
    (sourceCond : SourceSemantics.evalExpr fields runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1)
    (sourceError : SourceSemantics.execStmt fields runtime (.revertError name args) =
      .revertWithData data)
    (executed : execIRStmts fuel state out = .revert final)
    (payload : final.revertBytes = some data) :
    SourceSemantics.execStmt fields runtime (.requireError cond name args) = .revertWithData data ∧
    execIRStmts (fuel + 2) state [.if_ failCond out] = .revert final ∧
    stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond name args))
      (.revertWithData data) (.revert final) :=
  requireError_failure_exact_bytes fields scope runtime state final cond name args failCond out data fuel
    sourceCond compiledCond sourceError executed payload

end Compiler.Proofs.IRGeneration
