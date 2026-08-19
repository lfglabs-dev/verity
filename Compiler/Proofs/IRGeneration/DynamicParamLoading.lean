import Compiler.Proofs.IRGeneration.ParamLoading
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# IR execution of the generated `bytes` external-parameter loader

`Compiler.CompilationModel.genDynamicParamLoads` emits nine Yul statements for a
`bytes` external parameter: an offset load, two bounds checks, an absolute-offset
computation, a length load, tail arithmetic, a payload bounds check, and a data
pointer. This module proves that running those statements under the IR
interpreter produces exactly the six bindings that
`DynamicAbi.bindExternalParam` assigns to the same parameter, which is the
execution half of the refinement started in verity#2373.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace DynamicParamLoading

/-! ## Generated variable names are pairwise distinct -/

/-- Suffixes of different lengths cannot produce the same string under a shared
prefix — enough to separate every generated loader local, since the six suffixes
all have distinct lengths. -/
private theorem append_right_ne_of_length_ne {a b : String} (prefix_ : String)
    (h : a.length ≠ b.length) : prefix_ ++ a ≠ prefix_ ++ b := by
  intro heq
  apply h
  have hlen := congrArg String.length heq
  rw [String.length_append, String.length_append] at hlen
  omega

private theorem length_ne_tailHeadEnd (name : String) :
    s!"{name}_length" ≠ s!"{name}_tail_head_end" := by
  show name ++ "_length" ≠ name ++ "_tail_head_end"
  exact append_right_ne_of_length_ne name (by decide)

private theorem length_ne_tailRemaining (name : String) :
    s!"{name}_length" ≠ s!"{name}_tail_remaining" := by
  show name ++ "_length" ≠ name ++ "_tail_remaining"
  exact append_right_ne_of_length_ne name (by decide)

private theorem tailHeadEnd_ne_tailRemaining (name : String) :
    s!"{name}_tail_head_end" ≠ s!"{name}_tail_remaining" := by
  show name ++ "_tail_head_end" ≠ name ++ "_tail_remaining"
  exact append_right_ne_of_length_ne name (by decide)

/-! ## Local `IRState` variable lemmas -/

private theorem getVar_setVar_self (state : IRState) (name : String) (value : Nat) :
    (state.setVar name value).getVar name = some value := by
  simp [IRState.getVar, IRState.setVar]

private theorem getVar_setVar_of_ne (state : IRState) (bound query : String) (value : Nat)
    (hne : query ≠ bound) :
    (state.setVar bound value).getVar query = state.getVar query := by
  have hbound : (bound == query) = false := by
    simpa [beq_eq_false_iff_ne] using fun h => hne h.symm
  have hfilter : ∀ xs : List (String × Nat),
      (xs.filter (fun entry => entry.1 != bound)).find? (fun entry => entry.1 == query) =
        xs.find? (fun entry => entry.1 == query) := by
    intro xs
    induction xs with
    | nil => simp
    | cons entry rest ih =>
        by_cases hentry : entry.1 = bound
        · have hq : ¬ (entry.1 == query) = true := by
            simp only [beq_iff_eq, hentry]
            exact fun h => hne h.symm
          simp [List.filter, List.find?, hentry, hq, hbound, ih]
        · have hkeep : (entry.1 != bound) = true := by simpa [bne_iff_ne] using hentry
          simp [List.filter, List.find?, hkeep, ih]
  simp [IRState.getVar, IRState.setVar, List.find?, hbound, hfilter]

@[simp] private theorem setVar_calldata (state : IRState) (name : String) (value : Nat) :
    (state.setVar name value).calldata = state.calldata := rfl

@[simp] private theorem setVar_selector (state : IRState) (name : String) (value : Nat) :
    (state.setVar name value).selector = state.selector := rfl

private theorem execIRStmts_cons_continue
    (fuel : Nat) (state next : IRState) (stmt : YulStmt) (tail : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .continue next) :
    execIRStmts (fuel + 1) state (stmt :: tail) = execIRStmts fuel next tail := by
  simp [execIRStmts, hstmt]

/-! ## Statement shape emitted for a `bytes` parameter -/

/-- The revert guard a `bytes`/`string` loader puts on the payload length: the
payload must fit in the calldata remaining after the length word. -/
def bytesPayloadGuard (name : String) : YulStmt :=
  YulStmt.if_ (YulExpr.call "gt"
    [ YulExpr.ident s!"{name}_length", YulExpr.ident s!"{name}_tail_remaining" ])
    [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

/-- The revert guard a `T[]` loader puts on the element count: as many elements
as fit in the remaining calldata at one `dynamicArrayElementStrideWords` each. -/
def arrayPayloadGuard (name : String) (elemTy : ParamType) : YulStmt :=
  YulStmt.if_ (YulExpr.call "gt"
    [ YulExpr.ident s!"{name}_length"
    , YulExpr.call "div"
        [ YulExpr.ident s!"{name}_tail_remaining"
        , YulExpr.lit (32 * dynamicArrayElementStrideWords elemTy) ] ])
    [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

/-- The nine statements `genSingleParamLoad` emits for a length-prefixed dynamic
external parameter, at a non-zero ABI base offset (external dispatch uses `4`).
Only the eighth — the payload guard — depends on which length-prefixed type is
being loaded, so it is left abstract here and the execution refinement is proved
once (verity#2085). -/
def lengthPrefixedLoaderStmts (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat)
    (payloadGuard : YulStmt) : List YulStmt :=
  [ YulStmt.let_ s!"{name}_offset" (loadWord (YulExpr.lit headOffset))
  , YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident s!"{name}_offset", YulExpr.lit headSize])
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  , YulStmt.let_ s!"{name}_abs_offset"
      (YulExpr.call "add" [YulExpr.lit baseOffset, YulExpr.ident s!"{name}_offset"])
  , YulStmt.if_ (YulExpr.call "gt"
      [ YulExpr.ident s!"{name}_abs_offset"
      , YulExpr.call "sub" [sizeExpr, YulExpr.lit 32] ])
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  , YulStmt.let_ s!"{name}_length" (loadWord (YulExpr.ident s!"{name}_abs_offset"))
  , YulStmt.let_ s!"{name}_tail_head_end"
      (YulExpr.call "add" [YulExpr.ident s!"{name}_abs_offset", YulExpr.lit 32])
  , YulStmt.let_ s!"{name}_tail_remaining"
      (YulExpr.call "sub" [sizeExpr, YulExpr.ident s!"{name}_tail_head_end"])
  , payloadGuard
  , YulStmt.let_ s!"{name}_data_offset" (YulExpr.ident s!"{name}_tail_head_end") ]

/-- The nine statements `genSingleParamLoad` emits for a `bytes` external
parameter, at a non-zero ABI base offset (external dispatch uses `4`). -/
def bytesLoaderStmts (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat) : List YulStmt :=
  lengthPrefixedLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset
    (bytesPayloadGuard name)

/-- The nine statements `genSingleParamLoad` emits for a `T[]` external
parameter. Identical to the `bytes` loader except for the payload guard, which
divides the remaining tail by the element stride before comparing. -/
def arrayLoaderStmts (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (elemTy : ParamType) (headOffset : Nat) :
    List YulStmt :=
  lengthPrefixedLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset
    (arrayPayloadGuard name elemTy)

/-- The five statements `genSingleParamLoad` emits for a dynamic composite with
no length word — a `tuple` with a dynamic member, or a `fixedArray` of such. The
head word dereferences straight to the composite's own head area, so
`_data_offset` is just `_abs_offset` (verity#1839). -/
def dynamicCompositeLoaderStmts (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat) : List YulStmt :=
  [ YulStmt.let_ s!"{name}_offset" (loadWord (YulExpr.lit headOffset))
  , YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident s!"{name}_offset", YulExpr.lit headSize])
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  , YulStmt.let_ s!"{name}_abs_offset"
      (YulExpr.call "add" [YulExpr.lit baseOffset, YulExpr.ident s!"{name}_offset"])
  , YulStmt.if_ (YulExpr.call "gt"
      [ YulExpr.ident s!"{name}_abs_offset"
      , YulExpr.call "sub" [sizeExpr, YulExpr.lit 32] ])
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  , YulStmt.let_ s!"{name}_data_offset" (YulExpr.ident s!"{name}_abs_offset") ]

theorem genSingleParamLoad_bytes
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat)
    (hbase : ¬ (baseOffset == 0) = true) :
    genSingleParamLoad loadWord sizeExpr headSize baseOffset name ParamType.bytes headOffset =
      bytesLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset := by
  simp [genSingleParamLoad, genDynamicParamLoads, isLengthPrefixedDynamicShape,
    bytesLoaderStmts, lengthPrefixedLoaderStmts, bytesPayloadGuard, hbase]

/-- `string` is emitted through the very same loader as `bytes`: both are
length-prefixed dynamic shapes, and `genDynamicParamLoads` branches on the
shape, not on the type. -/
theorem genSingleParamLoad_string
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat)
    (hbase : ¬ (baseOffset == 0) = true) :
    genSingleParamLoad loadWord sizeExpr headSize baseOffset name ParamType.string headOffset =
      bytesLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset := by
  simp [genSingleParamLoad, genDynamicParamLoads, isLengthPrefixedDynamicShape,
    bytesLoaderStmts, lengthPrefixedLoaderStmts, bytesPayloadGuard, hbase]

theorem genSingleParamLoad_array
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (elemTy : ParamType) (headOffset : Nat)
    (hbase : ¬ (baseOffset == 0) = true) :
    genSingleParamLoad loadWord sizeExpr headSize baseOffset name (ParamType.array elemTy)
        headOffset =
      arrayLoaderStmts loadWord sizeExpr headSize baseOffset name elemTy headOffset := by
  simp [genSingleParamLoad, genDynamicParamLoads, isLengthPrefixedDynamicShape,
    arrayLoaderStmts, lengthPrefixedLoaderStmts, arrayPayloadGuard, hbase]

theorem genSingleParamLoad_dynamicTuple
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (elemTys : List ParamType) (headOffset : Nat)
    (hbase : ¬ (baseOffset == 0) = true)
    (hdynamic : isDynamicParamTypeList elemTys = true) :
    genSingleParamLoad loadWord sizeExpr headSize baseOffset name (ParamType.tuple elemTys)
        headOffset =
      dynamicCompositeLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset := by
  simp [genSingleParamLoad, genDynamicParamLoads, isLengthPrefixedDynamicShape,
    dynamicCompositeLoaderStmts, isDynamicParamType, hdynamic, hbase]

theorem genSingleParamLoad_dynamicFixedArray
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (elemTy : ParamType) (n headOffset : Nat)
    (hbase : ¬ (baseOffset == 0) = true)
    (hdynamic : isDynamicParamType elemTy = true) :
    genSingleParamLoad loadWord sizeExpr headSize baseOffset name
        (ParamType.fixedArray elemTy n) headOffset =
      dynamicCompositeLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset := by
  simp [genSingleParamLoad, genDynamicParamLoads, isLengthPrefixedDynamicShape,
    dynamicCompositeLoaderStmts, isDynamicParamType, hdynamic, hbase]

/-! ## Executing the generated `bytes` loader -/

private theorem calldataloadWord_eq (selector : Nat) (calldata : List Nat) (offset : Nat) :
    Compiler.Proofs.YulGeneration.calldataloadWord selector calldata offset =
      DynamicAbi.calldataloadWord selector calldata offset := rfl

private theorem externalWordAt?_eq_calldataloadWord
    {selector : Nat} {calldata : List Nat} {offset value : Nat}
    (h : DynamicAbi.externalWordAt? selector calldata offset = some value) :
    Compiler.Proofs.YulGeneration.calldataloadWord selector calldata offset = value := by
  rw [calldataloadWord_eq]
  by_cases hbounds :
      4 ≤ offset ∧ offset + 32 ≤ DynamicAbi.externalCalldataSize calldata
  · simpa [DynamicAbi.externalWordAt?, hbounds] using h
  · simp [DynamicAbi.externalWordAt?, hbounds] at h

/-- The bindings `DynamicAbi.bindExternalParam` produces for a `bytes` external
parameter, as an `IRState` update. Spelled out rather than routed through the
private `dynamicParamBindings` so it matches the statement of
`DynamicAbi.bindExternalParam_bytes_refines_dynamic_loader` verbatim. -/
def bytesParamBindings (name : String) (calldataSize baseOffset relativeOffset length : Nat) :
    List (String × Nat) :=
  [ (s!"{name}_offset", relativeOffset)
  , (s!"{name}_abs_offset", baseOffset + relativeOffset)
  , (s!"{name}_length", length)
  , (s!"{name}_tail_head_end", baseOffset + relativeOffset + 32)
  , (s!"{name}_tail_remaining", calldataSize - (baseOffset + relativeOffset + 32))
  , (s!"{name}_data_offset", baseOffset + relativeOffset + 32) ]

/-- The IR state a length-prefixed loader is in once its first seven statements
have run: the five locals bound before the payload guard. -/
def lengthPrefixedLoaderState (state : IRState) (name : String)
    (calldataSize baseOffset relativeOffset length : Nat) : IRState :=
  ((((state.setVar s!"{name}_offset" relativeOffset).setVar s!"{name}_abs_offset"
      (baseOffset + relativeOffset)).setVar s!"{name}_length" length).setVar
        s!"{name}_tail_head_end" (baseOffset + relativeOffset + 32)).setVar
          s!"{name}_tail_remaining" (calldataSize - (baseOffset + relativeOffset + 32))

/-- Executing the nine statements the compiler emits for a length-prefixed
dynamic external parameter binds exactly the six values the ABI model assigns to
it, and never reverts, whenever the calldata satisfies the model's decoding side
conditions and the type's own payload guard passes.

This is the execution half of the refinement opened by verity#2373. The guard is
abstract because the eight surrounding statements are the same for every
length-prefixed type; `bytes`/`string` and `T[]` differ only in what they
compare the length against (verity#2085). -/
theorem exec_lengthPrefixedLoaderStmts_then
    (state : IRState) (rest : List YulStmt) (name : String)
    (headSize baseOffset headOffset relativeOffset length extraFuel : Nat)
    (payloadGuard : YulStmt)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hhead : DynamicAbi.externalWordAt? state.selector state.calldata headOffset =
      some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound :
      baseOffset + relativeOffset + 32 ≤ DynamicAbi.externalCalldataSize state.calldata)
    (hlength :
      DynamicAbi.externalWordAt? state.selector state.calldata (baseOffset + relativeOffset) =
        some length)
    (hguard : ∀ f : Nat,
      execIRStmt (f + 1)
          (lengthPrefixedLoaderState state name
            (DynamicAbi.externalCalldataSize state.calldata) baseOffset relativeOffset length)
          payloadGuard =
        .continue (lengthPrefixedLoaderState state name
          (DynamicAbi.externalCalldataSize state.calldata) baseOffset relativeOffset length)) :
    execIRStmts (rest.length + extraFuel + 10) state
        (lengthPrefixedLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset name headOffset payloadGuard
          ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state
          (bytesParamBindings name (DynamicAbi.externalCalldataSize state.calldata)
            baseOffset relativeOffset length)) rest := by
  have hcsz : DynamicAbi.externalCalldataSize state.calldata =
      4 + state.calldata.length * 32 := by
    simp [DynamicAbi.externalCalldataSize, Nat.mul_comm]
  rw [hcsz] at hcalldataSize htailBound hguard ⊢
  simp only [lengthPrefixedLoaderState] at hguard
  have hro : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      headOffset = relativeOffset := externalWordAt?_eq_calldataloadWord hhead
  have hlenWord : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      (baseOffset + relativeOffset) = length := externalWordAt?_eq_calldataloadWord hlength
  have hEvm : (32 : Nat) < Compiler.Constants.evmModulus := by omega
  have hroLt : relativeOffset < Compiler.Constants.evmModulus := by omega
  have hHeadSizeLt : headSize < Compiler.Constants.evmModulus := by omega
  have hAbsLt : baseOffset + relativeOffset < Compiler.Constants.evmModulus := by omega
  have hTheLt : baseOffset + relativeOffset + 32 < Compiler.Constants.evmModulus := by omega
  have hSizeLt : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus := hcalldataSize
  -- `calldatasize() - 32` and `calldatasize() - {name}_tail_head_end` in EVM word arithmetic
  have hSub32 : (Compiler.Constants.evmModulus + (4 + state.calldata.length * 32) - 32) %
      Compiler.Constants.evmModulus = 4 + state.calldata.length * 32 - 32 := by
    have hrw : Compiler.Constants.evmModulus + (4 + state.calldata.length * 32) - 32 =
        Compiler.Constants.evmModulus + (4 + state.calldata.length * 32 - 32) := by omega
    rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hSubTail : (Compiler.Constants.evmModulus + (4 + state.calldata.length * 32) -
      (baseOffset + relativeOffset + 32)) % Compiler.Constants.evmModulus =
      4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32) := by
    have hrw : Compiler.Constants.evmModulus + (4 + state.calldata.length * 32) -
        (baseOffset + relativeOffset + 32) =
        Compiler.Constants.evmModulus +
          (4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32)) := by omega
    rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  -- Abbreviations for the six generated locals and the intermediate IR states.
  set nOffset := s!"{name}_offset" with hnOffset
  set nAbs := s!"{name}_abs_offset" with hnAbs
  set nLength := s!"{name}_length" with hnLength
  set nTailHeadEnd := s!"{name}_tail_head_end" with hnTailHeadEnd
  set nTailRemaining := s!"{name}_tail_remaining" with hnTailRemaining
  set nDataOffset := s!"{name}_data_offset" with hnDataOffset
  have hLenNeThe : nLength ≠ nTailHeadEnd := length_ne_tailHeadEnd name
  have hLenNeTr : nLength ≠ nTailRemaining := length_ne_tailRemaining name
  have hTheNeTr : nTailHeadEnd ≠ nTailRemaining := tailHeadEnd_ne_tailRemaining name
  -- Statement 1: `let {name}_offset := calldataload(headOffset)`
  have h1 : ∀ f : Nat, execIRStmt (f + 1) state
      (YulStmt.let_ nOffset (YulExpr.call "calldataload" [YulExpr.lit headOffset])) =
      .continue (state.setVar nOffset relativeOffset) := by
    intro f
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hro]
  -- Statement 2: `if lt({name}_offset, headSize) { revert }` — never taken
  have h2 : ∀ f : Nat, execIRStmt (f + 1) (state.setVar nOffset relativeOffset)
      (YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident nOffset, YulExpr.lit headSize])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue (state.setVar nOffset relativeOffset) := by
    intro f
    have hnot : ¬ relativeOffset % Compiler.Constants.evmModulus <
        headSize % Compiler.Constants.evmModulus := by
      rw [Nat.mod_eq_of_lt hroLt, Nat.mod_eq_of_lt hHeadSizeLt]; omega
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hnot]
  -- Statement 3: `let {name}_abs_offset := add(baseOffset, {name}_offset)`
  have h3 : ∀ f : Nat, execIRStmt (f + 1) (state.setVar nOffset relativeOffset)
      (YulStmt.let_ nAbs
        (YulExpr.call "add" [YulExpr.lit baseOffset, YulExpr.ident nOffset])) =
      .continue ((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)) := by
    intro f
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Nat.mod_eq_of_lt hAbsLt]
  -- Statement 4: `if gt({name}_abs_offset, sub(calldatasize(), 32)) { revert }` — never taken
  have h4 : ∀ f : Nat, execIRStmt (f + 1)
      ((state.setVar nOffset relativeOffset).setVar nAbs (baseOffset + relativeOffset))
      (YulStmt.if_ (YulExpr.call "gt"
        [ YulExpr.ident nAbs
        , YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.lit 32] ])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue ((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)) := by
    intro f
    have hnot : ¬ (4 + state.calldata.length * 32 - 32) % Compiler.Constants.evmModulus <
        (baseOffset + relativeOffset) % Compiler.Constants.evmModulus := by
      rw [Nat.mod_eq_of_lt (show 4 + state.calldata.length * 32 - 32 <
          Compiler.Constants.evmModulus by omega), Nat.mod_eq_of_lt hAbsLt]
      omega
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Nat.mod_eq_of_lt hSizeLt, Nat.mod_eq_of_lt hEvm, hSub32, hnot]
  -- Statement 5: `let {name}_length := calldataload({name}_abs_offset)`
  have h5 : ∀ f : Nat, execIRStmt (f + 1)
      ((state.setVar nOffset relativeOffset).setVar nAbs (baseOffset + relativeOffset))
      (YulStmt.let_ nLength (YulExpr.call "calldataload" [YulExpr.ident nAbs])) =
      .continue (((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length) := by
    intro f
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hlenWord]
  -- Statement 6: `let {name}_tail_head_end := add({name}_abs_offset, 32)`
  have h6 : ∀ f : Nat, execIRStmt (f + 1)
      (((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length)
      (YulStmt.let_ nTailHeadEnd
        (YulExpr.call "add" [YulExpr.ident nAbs, YulExpr.lit 32])) =
      .continue ((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)) := by
    intro f
    have hget : ((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length)).getVar nAbs =
        some (baseOffset + relativeOffset) := by
      rw [getVar_setVar_of_ne _ _ _ _ (by
        rw [hnAbs, hnLength]
        show name ++ "_abs_offset" ≠ name ++ "_length"
        exact append_right_ne_of_length_ne name (by decide)), getVar_setVar_self]
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hget,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Nat.mod_eq_of_lt hTheLt]
  -- Statement 7: `let {name}_tail_remaining := sub(calldatasize(), {name}_tail_head_end)`
  have h7 : ∀ f : Nat, execIRStmt (f + 1)
      ((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32))
      (YulStmt.let_ nTailRemaining
        (YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.ident nTailHeadEnd])) =
      .continue (((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)).setVar nTailRemaining
            (4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32))) := by
    intro f
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Nat.mod_eq_of_lt hSizeLt, Nat.mod_eq_of_lt hTheLt, hSubTail]
  -- Statement 8: the type-specific payload guard — never taken, by `hguard`.
  -- Statement 9: `let {name}_data_offset := {name}_tail_head_end`
  have h9 : ∀ f : Nat, execIRStmt (f + 1)
      (((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)).setVar nTailRemaining
            (4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32)))
      (YulStmt.let_ nDataOffset (YulExpr.ident nTailHeadEnd)) =
      .continue ((((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)).setVar nTailRemaining
            (4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32))).setVar
              nDataOffset (baseOffset + relativeOffset + 32)) := by
    intro f
    have hget : (((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)).setVar nTailRemaining
            (4 + state.calldata.length * 32 -
              (baseOffset + relativeOffset + 32))).getVar nTailHeadEnd =
        some (baseOffset + relativeOffset + 32) := by
      rw [getVar_setVar_of_ne _ _ _ _ hTheNeTr, getVar_setVar_self]
    simp [execIRStmt, evalIRExpr, hget]
  simp only [lengthPrefixedLoaderStmts, bytesParamBindings,
    ParamLoading.applyBindingsToIRState, List.cons_append, List.nil_append]
  rw [execIRStmts_cons_continue _ _ _ _ _ (h1 (rest.length + extraFuel + 8)),
    execIRStmts_cons_continue _ _ _ _ _ (h2 (rest.length + extraFuel + 7)),
    execIRStmts_cons_continue _ _ _ _ _ (h3 (rest.length + extraFuel + 6)),
    execIRStmts_cons_continue _ _ _ _ _ (h4 (rest.length + extraFuel + 5)),
    execIRStmts_cons_continue _ _ _ _ _ (h5 (rest.length + extraFuel + 4)),
    execIRStmts_cons_continue _ _ _ _ _ (h6 (rest.length + extraFuel + 3)),
    execIRStmts_cons_continue _ _ _ _ _ (h7 (rest.length + extraFuel + 2)),
    execIRStmts_cons_continue _ _ _ _ _ (hguard (rest.length + extraFuel + 1)),
    execIRStmts_cons_continue _ _ _ _ _ (h9 (rest.length + extraFuel))]

/-- The `bytes`/`string` payload guard never reverts when the model's payload
bound holds: the length word is at most the calldata remaining after it. -/
private theorem exec_bytesPayloadGuard_noop
    (state : IRState) (name : String)
    (baseOffset relativeOffset length : Nat)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hpayloadBound :
      length ≤
        DynamicAbi.externalCalldataSize state.calldata - (baseOffset + relativeOffset + 32))
    (f : Nat) :
    execIRStmt (f + 1)
        (lengthPrefixedLoaderState state name
          (DynamicAbi.externalCalldataSize state.calldata) baseOffset relativeOffset length)
        (bytesPayloadGuard name) =
      .continue (lengthPrefixedLoaderState state name
        (DynamicAbi.externalCalldataSize state.calldata) baseOffset relativeOffset length) := by
  set calldataSize := DynamicAbi.externalCalldataSize state.calldata with hsize
  have hLengthLt : length < Compiler.Constants.evmModulus := by omega
  have hTrLt :
      calldataSize - (baseOffset + relativeOffset + 32) < Compiler.Constants.evmModulus := by
    omega
  have hgetLength :
      (lengthPrefixedLoaderState state name calldataSize baseOffset relativeOffset
        length).getVar s!"{name}_length" = some length := by
    rw [lengthPrefixedLoaderState,
      getVar_setVar_of_ne _ _ _ _ (length_ne_tailRemaining name),
      getVar_setVar_of_ne _ _ _ _ (length_ne_tailHeadEnd name), getVar_setVar_self]
  simp only [lengthPrefixedLoaderState] at hgetLength
  have hnot : ¬ (calldataSize - (baseOffset + relativeOffset + 32)) %
      Compiler.Constants.evmModulus < length % Compiler.Constants.evmModulus := by
    rw [Nat.mod_eq_of_lt hLengthLt, Nat.mod_eq_of_lt hTrLt]; omega
  simp [bytesPayloadGuard, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hgetLength,
    lengthPrefixedLoaderState, getVar_setVar_self,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hnot]

/-- Executing the nine statements the compiler emits for a `bytes` external
parameter binds exactly the six values the ABI model assigns to it, and never
reverts, whenever the calldata satisfies the model's decoding side conditions. -/
theorem exec_bytesLoaderStmts_then
    (state : IRState) (rest : List YulStmt) (name : String)
    (headSize baseOffset headOffset relativeOffset length extraFuel : Nat)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hhead : DynamicAbi.externalWordAt? state.selector state.calldata headOffset =
      some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound :
      baseOffset + relativeOffset + 32 ≤ DynamicAbi.externalCalldataSize state.calldata)
    (hlength :
      DynamicAbi.externalWordAt? state.selector state.calldata (baseOffset + relativeOffset) =
        some length)
    (hpayloadBound :
      length ≤
        DynamicAbi.externalCalldataSize state.calldata - (baseOffset + relativeOffset + 32)) :
    execIRStmts (rest.length + extraFuel + 10) state
        (bytesLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset name headOffset ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state
          (bytesParamBindings name (DynamicAbi.externalCalldataSize state.calldata)
            baseOffset relativeOffset length)) rest :=
  exec_lengthPrefixedLoaderStmts_then state rest name headSize baseOffset headOffset
    relativeOffset length extraFuel (bytesPayloadGuard name) hcalldataSize hhead hheadBound
    htailBound hlength
    (exec_bytesPayloadGuard_noop state name baseOffset relativeOffset length hcalldataSize
      hpayloadBound)

/-- The `T[]` payload guard never reverts when the model's element-count bound
holds. The emitted `div` agrees with `Nat` division because the stride literal
is below `2 ^ 256` (`hstride`), which is exactly the side condition
`SupportedExternalParamType` carries for arrays. -/
private theorem exec_arrayPayloadGuard_noop
    (state : IRState) (name : String) (elemTy : ParamType)
    (baseOffset relativeOffset length : Nat)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hstride :
      32 * dynamicArrayElementStrideWords elemTy < Compiler.Constants.evmModulus)
    (hpayloadBound :
      length ≤
        (DynamicAbi.externalCalldataSize state.calldata - (baseOffset + relativeOffset + 32)) /
          (32 * dynamicArrayElementStrideWords elemTy))
    (f : Nat) :
    execIRStmt (f + 1)
        (lengthPrefixedLoaderState state name
          (DynamicAbi.externalCalldataSize state.calldata) baseOffset relativeOffset length)
        (arrayPayloadGuard name elemTy) =
      .continue (lengthPrefixedLoaderState state name
        (DynamicAbi.externalCalldataSize state.calldata) baseOffset relativeOffset length) := by
  set calldataSize := DynamicAbi.externalCalldataSize state.calldata with hsize
  have hstridePos : 0 < 32 * dynamicArrayElementStrideWords elemTy := by
    have := dynamicArrayElementStrideWords_pos elemTy
    omega
  have hTrLt :
      calldataSize - (baseOffset + relativeOffset + 32) < Compiler.Constants.evmModulus := by
    omega
  have hquotLe :
      (calldataSize - (baseOffset + relativeOffset + 32)) /
          (32 * dynamicArrayElementStrideWords elemTy) ≤
        calldataSize - (baseOffset + relativeOffset + 32) := Nat.div_le_self _ _
  have hLengthLt : length < Compiler.Constants.evmModulus := by omega
  have hgetLength :
      (lengthPrefixedLoaderState state name calldataSize baseOffset relativeOffset
        length).getVar s!"{name}_length" = some length := by
    rw [lengthPrefixedLoaderState,
      getVar_setVar_of_ne _ _ _ _ (length_ne_tailRemaining name),
      getVar_setVar_of_ne _ _ _ _ (length_ne_tailHeadEnd name), getVar_setVar_self]
  simp only [lengthPrefixedLoaderState] at hgetLength
  have hstrideMod : 32 * dynamicArrayElementStrideWords elemTy %
      Compiler.Constants.evmModulus = 32 * dynamicArrayElementStrideWords elemTy :=
    Nat.mod_eq_of_lt hstride
  have hstrideNe : ¬ 32 * dynamicArrayElementStrideWords elemTy %
      Compiler.Constants.evmModulus = 0 := by
    rw [hstrideMod]; omega
  have hquotLt :
      (calldataSize - (baseOffset + relativeOffset + 32)) /
        (32 * dynamicArrayElementStrideWords elemTy) < Compiler.Constants.evmModulus := by
    omega
  have hnot : ¬ ((calldataSize - (baseOffset + relativeOffset + 32)) %
      Compiler.Constants.evmModulus /
      (32 * dynamicArrayElementStrideWords elemTy % Compiler.Constants.evmModulus)) %
      Compiler.Constants.evmModulus < length % Compiler.Constants.evmModulus := by
    rw [hstrideMod, Nat.mod_eq_of_lt hTrLt, Nat.mod_eq_of_lt hquotLt,
      Nat.mod_eq_of_lt hLengthLt]
    omega
  simp [arrayPayloadGuard, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hgetLength,
    lengthPrefixedLoaderState, getVar_setVar_self,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    hstrideNe, hnot]

/-- Executing the nine statements the compiler emits for a `T[]` external
parameter binds exactly the six values the ABI model assigns to it, and never
reverts (verity#2085). -/
theorem exec_arrayLoaderStmts_then
    (state : IRState) (rest : List YulStmt) (name : String) (elemTy : ParamType)
    (headSize baseOffset headOffset relativeOffset length extraFuel : Nat)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hstride :
      32 * dynamicArrayElementStrideWords elemTy < Compiler.Constants.evmModulus)
    (hhead : DynamicAbi.externalWordAt? state.selector state.calldata headOffset =
      some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound :
      baseOffset + relativeOffset + 32 ≤ DynamicAbi.externalCalldataSize state.calldata)
    (hlength :
      DynamicAbi.externalWordAt? state.selector state.calldata (baseOffset + relativeOffset) =
        some length)
    (hpayloadBound :
      length ≤
        (DynamicAbi.externalCalldataSize state.calldata - (baseOffset + relativeOffset + 32)) /
          (32 * dynamicArrayElementStrideWords elemTy)) :
    execIRStmts (rest.length + extraFuel + 10) state
        (arrayLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset name elemTy headOffset ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state
          (bytesParamBindings name (DynamicAbi.externalCalldataSize state.calldata)
            baseOffset relativeOffset length)) rest :=
  exec_lengthPrefixedLoaderStmts_then state rest name headSize baseOffset headOffset
    relativeOffset length extraFuel (arrayPayloadGuard name elemTy) hcalldataSize hhead
    hheadBound htailBound hlength
    (exec_arrayPayloadGuard_noop state name elemTy baseOffset relativeOffset length
      hcalldataSize hstride hpayloadBound)

/-- The bindings `DynamicAbi.bindExternalParam` produces for a dynamic composite
with no length word, as an `IRState` update. -/
def dynamicCompositeParamBindings (name : String) (baseOffset relativeOffset : Nat) :
    List (String × Nat) :=
  [ (s!"{name}_offset", relativeOffset)
  , (s!"{name}_abs_offset", baseOffset + relativeOffset)
  , (s!"{name}_data_offset", baseOffset + relativeOffset) ]

/-- Executing the five statements the compiler emits for a dynamic composite
external parameter binds exactly the three values the ABI model assigns to it,
and never reverts. There is no length word to guard, so the only side conditions
are the two the offset itself must satisfy (verity#2085). -/
theorem exec_dynamicCompositeLoaderStmts_then
    (state : IRState) (rest : List YulStmt) (name : String)
    (headSize baseOffset headOffset relativeOffset extraFuel : Nat)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hhead : DynamicAbi.externalWordAt? state.selector state.calldata headOffset =
      some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound :
      baseOffset + relativeOffset + 32 ≤ DynamicAbi.externalCalldataSize state.calldata) :
    execIRStmts (rest.length + extraFuel + 6) state
        (dynamicCompositeLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset name headOffset ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state
          (dynamicCompositeParamBindings name baseOffset relativeOffset)) rest := by
  have hcsz : DynamicAbi.externalCalldataSize state.calldata =
      4 + state.calldata.length * 32 := by
    simp [DynamicAbi.externalCalldataSize, Nat.mul_comm]
  rw [hcsz] at hcalldataSize htailBound
  have hro : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      headOffset = relativeOffset := externalWordAt?_eq_calldataloadWord hhead
  have hEvm : (32 : Nat) < Compiler.Constants.evmModulus := by omega
  have hroLt : relativeOffset < Compiler.Constants.evmModulus := by omega
  have hHeadSizeLt : headSize < Compiler.Constants.evmModulus := by omega
  have hAbsLt : baseOffset + relativeOffset < Compiler.Constants.evmModulus := by omega
  have hSizeLt : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus := hcalldataSize
  have hSub32 : (Compiler.Constants.evmModulus + (4 + state.calldata.length * 32) - 32) %
      Compiler.Constants.evmModulus = 4 + state.calldata.length * 32 - 32 := by
    have hrw : Compiler.Constants.evmModulus + (4 + state.calldata.length * 32) - 32 =
        Compiler.Constants.evmModulus + (4 + state.calldata.length * 32 - 32) := by omega
    rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  set nOffset := s!"{name}_offset" with hnOffset
  set nAbs := s!"{name}_abs_offset" with hnAbs
  set nDataOffset := s!"{name}_data_offset" with hnDataOffset
  -- Statement 1: `let {name}_offset := calldataload(headOffset)`
  have h1 : ∀ f : Nat, execIRStmt (f + 1) state
      (YulStmt.let_ nOffset (YulExpr.call "calldataload" [YulExpr.lit headOffset])) =
      .continue (state.setVar nOffset relativeOffset) := by
    intro f
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hro]
  -- Statement 2: `if lt({name}_offset, headSize) { revert }` — never taken
  have h2 : ∀ f : Nat, execIRStmt (f + 1) (state.setVar nOffset relativeOffset)
      (YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident nOffset, YulExpr.lit headSize])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue (state.setVar nOffset relativeOffset) := by
    intro f
    have hnot : ¬ relativeOffset % Compiler.Constants.evmModulus <
        headSize % Compiler.Constants.evmModulus := by
      rw [Nat.mod_eq_of_lt hroLt, Nat.mod_eq_of_lt hHeadSizeLt]; omega
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hnot]
  -- Statement 3: `let {name}_abs_offset := add(baseOffset, {name}_offset)`
  have h3 : ∀ f : Nat, execIRStmt (f + 1) (state.setVar nOffset relativeOffset)
      (YulStmt.let_ nAbs
        (YulExpr.call "add" [YulExpr.lit baseOffset, YulExpr.ident nOffset])) =
      .continue ((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)) := by
    intro f
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Nat.mod_eq_of_lt hAbsLt]
  -- Statement 4: `if gt({name}_abs_offset, sub(calldatasize(), 32)) { revert }` — never taken
  have h4 : ∀ f : Nat, execIRStmt (f + 1)
      ((state.setVar nOffset relativeOffset).setVar nAbs (baseOffset + relativeOffset))
      (YulStmt.if_ (YulExpr.call "gt"
        [ YulExpr.ident nAbs
        , YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.lit 32] ])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue ((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)) := by
    intro f
    have hnot : ¬ (4 + state.calldata.length * 32 - 32) % Compiler.Constants.evmModulus <
        (baseOffset + relativeOffset) % Compiler.Constants.evmModulus := by
      rw [Nat.mod_eq_of_lt (show 4 + state.calldata.length * 32 - 32 <
          Compiler.Constants.evmModulus by omega), Nat.mod_eq_of_lt hAbsLt]
      omega
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Nat.mod_eq_of_lt hSizeLt, Nat.mod_eq_of_lt hEvm, hSub32, hnot]
  -- Statement 5: `let {name}_data_offset := {name}_abs_offset`
  have h5 : ∀ f : Nat, execIRStmt (f + 1)
      ((state.setVar nOffset relativeOffset).setVar nAbs (baseOffset + relativeOffset))
      (YulStmt.let_ nDataOffset (YulExpr.ident nAbs)) =
      .continue (((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nDataOffset (baseOffset + relativeOffset)) := by
    intro f
    simp [execIRStmt, evalIRExpr, getVar_setVar_self]
  simp only [dynamicCompositeLoaderStmts, dynamicCompositeParamBindings,
    ParamLoading.applyBindingsToIRState, List.cons_append, List.nil_append]
  rw [execIRStmts_cons_continue _ _ _ _ _ (h1 (rest.length + extraFuel + 4)),
    execIRStmts_cons_continue _ _ _ _ _ (h2 (rest.length + extraFuel + 3)),
    execIRStmts_cons_continue _ _ _ _ _ (h3 (rest.length + extraFuel + 2)),
    execIRStmts_cons_continue _ _ _ _ _ (h4 (rest.length + extraFuel + 1)),
    execIRStmts_cons_continue _ _ _ _ _ (h5 (rest.length + extraFuel))]

/-! ### Lifting the single-parameter refinement over parameter lists -/

private theorem scalar_cases {ty : ParamType} (h : SupportedExternalScalarParamType ty) :
    ty = .uint256 ∨ ty = .int256 ∨ ty = .uint8 ∨ ty = .uint16 ∨
      (∃ bits, ty = .uintN bits) ∨ (∃ bits, ty = .intN bits) ∨
      (∃ bytes, ty = .bytesN bytes) ∨
      ty = .address ∨ ty = .bytes32 ∨ ty = .bool := by
  cases ty <;> simp [SupportedExternalScalarParamType] at h ⊢

/-- Scalar parameters route through `genScalarLoad`; this is the compile-side
equation the list lift needs beside `genSingleParamLoad_bytes`. -/
theorem genSingleParamLoad_scalar
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (ty : ParamType) (headOffset : Nat)
    (hty : SupportedExternalScalarParamType ty) :
    genSingleParamLoad loadWord sizeExpr headSize baseOffset name ty headOffset =
      genScalarLoad loadWord name ty headOffset := by
  rcases scalar_cases hty with
    rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl | rfl | rfl <;> rfl

private theorem decode_total_of_scalar {ty : ParamType}
    (hty : SupportedExternalScalarParamType ty) (word : Nat) :
    ∃ value, DynamicAbi.decodeSupportedParamWord ty word = some value := by
  rcases scalar_cases hty with
    rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl | rfl | rfl <;>
    exact ⟨_, rfl⟩

/-- `decodeSupportedParamWord` already normalises its argument mod 2^256, so the
model's `calldataloadWord` (which is reduced) and the raw calldata word decode
alike. -/
private theorem decodeSupportedParamWord_mod (ty : ParamType) (word : Nat) :
    SourceSemantics.decodeSupportedParamWord ty (word % Compiler.Constants.evmModulus) =
      SourceSemantics.decodeSupportedParamWord ty word := by
  cases ty <;>
    simp [SourceSemantics.decodeSupportedParamWord, Nat.mod_mod]

theorem applyBindingsToIRState_append (state : IRState) (xs ys : List (String × Nat)) :
    ParamLoading.applyBindingsToIRState state (xs ++ ys) =
      ParamLoading.applyBindingsToIRState (ParamLoading.applyBindingsToIRState state xs) ys := by
  induction xs generalizing state with
  | nil => rfl
  | cons entry xs ih =>
      obtain ⟨name, value⟩ := entry
      simpa [ParamLoading.applyBindingsToIRState] using ih (state.setVar name value)

@[simp] theorem applyBindingsToIRState_calldata
    (state : IRState) (bs : List (String × Nat)) :
    (ParamLoading.applyBindingsToIRState state bs).calldata = state.calldata := by
  induction bs generalizing state with
  | nil => rfl
  | cons entry bs ih =>
      obtain ⟨name, value⟩ := entry
      simpa [ParamLoading.applyBindingsToIRState] using ih (state.setVar name value)

@[simp] theorem applyBindingsToIRState_selector
    (state : IRState) (bs : List (String × Nat)) :
    (ParamLoading.applyBindingsToIRState state bs).selector = state.selector := by
  induction bs generalizing state with
  | nil => rfl
  | cons entry bs ih =>
      obtain ⟨name, value⟩ := entry
      simpa [ParamLoading.applyBindingsToIRState] using ih (state.setVar name value)

@[simp] theorem bytesLoaderStmts_length
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat) :
    (bytesLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset).length = 9 := rfl

@[simp] theorem lengthPrefixedLoaderStmts_length
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat) (payloadGuard : YulStmt) :
    (lengthPrefixedLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset
      payloadGuard).length = 9 := rfl

@[simp] theorem dynamicCompositeLoaderStmts_length
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat) :
    (dynamicCompositeLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset).length =
      5 := rfl

/-- The bytes-like half of the per-parameter composition, phrased over the two
facts `bytes` and `string` share: the emitted block is the length-prefixed
loader, and the binder assigned it the `bytes` bindings. -/
private theorem exec_bytesLikeParamLoad_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (name : String) (ty : ParamType) (idx extraFuel : Nat) (here : List (String × Nat))
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hstmts : genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty (4 + 32 * idx) =
      bytesLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name (4 + 32 * idx))
    (hbind : DynamicAbi.bindExternalParam state.selector state.calldata headSize baseOffset
      (4 + 32 * idx) { name := name, ty := ParamType.bytes } = some here) :
    execIRStmts ((genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty
        (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
      (genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty
        (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state here) rest := by
  obtain ⟨relativeOffset, length, hhead, hheadBound, htailBound, hlength,
    hpayloadBound, hhere⟩ := DynamicAbi.bindExternalParam_bytes_eq_some_inv hbind
  subst hhere
  rw [hstmts]
  have hexec := exec_bytesLoaderStmts_then state rest name headSize baseOffset
    (4 + 32 * idx) relativeOffset length extraFuel hcalldataSize hhead hheadBound
    htailBound hlength hpayloadBound
  simpa [bytesParamBindings, bytesLoaderStmts, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hexec

/-- The `T[]` half of the per-parameter composition. -/
private theorem exec_arrayParamLoad_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (name : String) (ty elemTy : ParamType) (idx extraFuel : Nat) (here : List (String × Nat))
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hstride : 32 * dynamicArrayElementStrideWords elemTy < Compiler.Constants.evmModulus)
    (hstmts : genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty (4 + 32 * idx) =
      arrayLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name elemTy (4 + 32 * idx))
    (hbind : DynamicAbi.bindExternalParam state.selector state.calldata headSize baseOffset
      (4 + 32 * idx) { name := name, ty := ParamType.array elemTy } = some here) :
    execIRStmts ((genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty
        (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
      (genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty
        (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state here) rest := by
  obtain ⟨relativeOffset, length, hhead, hheadBound, htailBound, hlength,
    hpayloadBound, hhere⟩ := DynamicAbi.bindExternalParam_array_eq_some_inv hbind
  subst hhere
  rw [hstmts]
  have hexec := exec_arrayLoaderStmts_then state rest name elemTy headSize baseOffset
    (4 + 32 * idx) relativeOffset length extraFuel hcalldataSize hstride hhead hheadBound
    htailBound hlength hpayloadBound
  simpa [bytesParamBindings, arrayLoaderStmts, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hexec

/-- The dynamic-composite half of the per-parameter composition, shared by
`tuple`s with dynamic members and fixed-size arrays of such. -/
private theorem exec_dynamicCompositeParamLoad_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (name : String) (ty : ParamType) (idx extraFuel : Nat) (here : List (String × Nat))
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hdynamic : isDynamicParamType ty = true)
    (hnotLengthPrefixed : isLengthPrefixedDynamicShape ty = false)
    (hstmts : genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty (4 + 32 * idx) =
      dynamicCompositeLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name (4 + 32 * idx))
    (hbind : DynamicAbi.bindExternalParam state.selector state.calldata headSize baseOffset
      (4 + 32 * idx) { name := name, ty := ty } = some here) :
    execIRStmts ((genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty
        (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
      (genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset name ty
        (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state here) rest := by
  obtain ⟨relativeOffset, hhead, hheadBound, htailBound, hhere⟩ :=
    DynamicAbi.bindExternalParam_dynamicComposite_eq_some_inv hdynamic hnotLengthPrefixed hbind
  subst hhere
  rw [hstmts]
  have hexec := exec_dynamicCompositeLoaderStmts_then state rest name headSize baseOffset
    (4 + 32 * idx) relativeOffset extraFuel hcalldataSize hhead hheadBound htailBound
  simpa [dynamicCompositeParamBindings, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hexec

/-- Executing the statements emitted for one supported external parameter lands
on exactly the bindings `DynamicAbi.bindExternalParam` assigns to it. This is
the per-parameter composition: `bytes`, `string`, `T[]` and dynamic composites
go through the loader refinements, scalars through the existing single-word
lemma. -/
theorem exec_genSingleParamLoad_external_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (param : Param) (idx extraFuel : Nat) (here : List (String × Nat))
    (hbase : ¬ (baseOffset == 0) = true)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hsupported : SupportedExternalParamType param.ty)
    (hbind : DynamicAbi.bindExternalParam state.selector state.calldata headSize baseOffset
      (4 + 32 * idx) param = some here) :
    execIRStmts ((genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset param.name param.ty
        (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
      (genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset param.name param.ty
        (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState state here) rest := by
  rcases supportedExternalParamType_cases hsupported with
    hscalar | hbytes | hstring | ⟨elemTy, harray, hstride⟩ |
      ⟨elemTy, n, hfixed, hdynElem⟩ | ⟨elemTys, htuple, hdynList⟩
  · obtain ⟨word, value, hword, hdecode, hhere⟩ :=
      DynamicAbi.bindExternalParam_scalar_eq_some_inv (decode_total_of_scalar hscalar) hbind
    have hwordEq : word = state.calldata.getD idx 0 % Compiler.Constants.evmModulus := by
      have := externalWordAt?_eq_calldataloadWord hword
      rw [ParamLoading.calldataloadWord_aligned] at this
      exact this.symm
    have hdecode' :
        SourceSemantics.decodeSupportedParamWord param.ty (state.calldata.getD idx 0) =
          some value := by
      rw [← decodeSupportedParamWord_mod, ← hwordEq,
        SourceSemantics.decodeSupportedParamWord_eq_dynamicAbi]
      exact hdecode
    subst hhere
    rw [genSingleParamLoad_scalar _ _ _ _ _ _ _ hscalar]
    simpa [ParamLoading.applyBindingsToIRState] using
      ParamLoading.exec_genScalarLoad_supported_then state rest param.name param.ty idx value
        extraFuel hscalar hdecode'
  · have hparam : param = { name := param.name, ty := ParamType.bytes } := by
      cases param
      simp_all
    rw [hparam] at hbind
    exact exec_bytesLikeParamLoad_then state rest headSize baseOffset param.name param.ty idx
      extraFuel here hcalldataSize (by rw [hbytes]; exact genSingleParamLoad_bytes _ _ _ _ _ _ hbase)
      hbind
  · have hparam : param = { name := param.name, ty := ParamType.string } := by
      cases param
      simp_all
    rw [hparam, DynamicAbi.bindExternalParam_string_eq_bytes] at hbind
    exact exec_bytesLikeParamLoad_then state rest headSize baseOffset param.name param.ty idx
      extraFuel here hcalldataSize
      (by rw [hstring]; exact genSingleParamLoad_string _ _ _ _ _ _ hbase) hbind
  · have hparam : param = { name := param.name, ty := ParamType.array elemTy } := by
      cases param
      simp_all
    rw [hparam] at hbind
    exact exec_arrayParamLoad_then state rest headSize baseOffset param.name param.ty elemTy idx
      extraFuel here hcalldataSize hstride
      (by rw [harray]; exact genSingleParamLoad_array _ _ _ _ _ _ _ hbase) hbind
  · have hparam : param = { name := param.name, ty := param.ty } := rfl
    exact exec_dynamicCompositeParamLoad_then state rest headSize baseOffset param.name param.ty
      idx extraFuel here hcalldataSize (by rw [hfixed]; simpa [isDynamicParamType] using hdynElem)
      (by rw [hfixed]; rfl)
      (by rw [hfixed]; exact genSingleParamLoad_dynamicFixedArray _ _ _ _ _ _ _ _ hbase hdynElem)
      (by rw [← hparam]; exact hbind)
  · have hparam : param = { name := param.name, ty := param.ty } := rfl
    exact exec_dynamicCompositeParamLoad_then state rest headSize baseOffset param.name param.ty
      idx extraFuel here hcalldataSize (by rw [htuple]; simpa [isDynamicParamType] using hdynList)
      (by rw [htuple]; rfl)
      (by rw [htuple]; exact genSingleParamLoad_dynamicTuple _ _ _ _ _ _ _ hbase hdynList)
      (by rw [← hparam]; exact hbind)

/-- The parameter-list lift: the whole emitted calldata-decoding block executes
to exactly the bindings the dispatcher's external ABI binder computes, for any
mixture of supported scalars, `bytes` and `string`. -/
theorem exec_genParamLoadBodyFrom_external_then
    (headSize baseOffset : Nat) (hbase : ¬ (baseOffset == 0) = true)
    (params : List Param) :
    ∀ (state : IRState) (rest : List YulStmt) (idx extraFuel : Nat)
      (bindings : List (String × Nat)),
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus →
      (∀ param ∈ params, SupportedExternalParamType param.ty) →
      DynamicAbi.bindExternalParamsFrom state.selector state.calldata headSize baseOffset
        params (4 + 32 * idx) = some bindings →
      execIRStmts ((genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx)).length +
          rest.length + extraFuel + 1) state
        (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx) ++ rest) =
        execIRStmts (rest.length + extraFuel + 1)
          (ParamLoading.applyBindingsToIRState state bindings) rest := by
  induction params with
  | nil =>
      intro state rest idx extraFuel bindings _ _ hbind
      simp only [DynamicAbi.bindExternalParamsFrom, Option.some.injEq] at hbind
      subst hbind
      simp [Compiler.CompilationModel.genParamLoadBodyFrom,
        ParamLoading.applyBindingsToIRState]
  | cons param restParams ih =>
      intro state rest idx extraFuel bindings hcalldataSize hsupported hbind
      have hparamSupported : SupportedExternalParamType param.ty := hsupported param (by simp)
      have hrestSupported : ∀ next ∈ restParams, SupportedExternalParamType next.ty := by
        intro next hnext
        exact hsupported next (by simp [hnext])
      have hhead32 : paramHeadSize param.ty = 32 :=
        supportedExternalParamType_headSize_eq_32 hparamSupported
      have hoffset : 4 + 32 * idx + paramHeadSize param.ty = 4 + 32 * (idx + 1) := by
        rw [hhead32]; ring
      cases hhere : DynamicAbi.bindExternalParam state.selector state.calldata headSize
          baseOffset (4 + 32 * idx) param with
      | none =>
          rw [DynamicAbi.bindExternalParamsFrom, hhere] at hbind
          simp at hbind
      | some here =>
          cases hthere : DynamicAbi.bindExternalParamsFrom state.selector state.calldata
              headSize baseOffset restParams (4 + 32 * (idx + 1)) with
          | none =>
              rw [DynamicAbi.bindExternalParamsFrom, hhere, hoffset, hthere] at hbind
              simp at hbind
          | some there =>
              rw [DynamicAbi.bindExternalParamsFrom, hhere, hoffset, hthere] at hbind
              simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq] at hbind
              subst hbind
              set loadWordC : YulExpr → YulExpr :=
                fun pos => YulExpr.call "calldataload" [pos] with hloadWordC
              set sizeExprC : YulExpr := YulExpr.call "calldatasize" [] with hsizeExprC
              set single :=
                genSingleParamLoad loadWordC sizeExprC headSize baseOffset param.name
                  param.ty (4 + 32 * idx) with hsingle
              set genRest :=
                genParamLoadBodyFrom loadWordC sizeExprC headSize baseOffset restParams
                  (4 + 32 * (idx + 1)) with hgenRest
              have hgen :
                  genParamLoadBodyFrom loadWordC sizeExprC headSize baseOffset
                      (param :: restParams) (4 + 32 * idx) = single ++ genRest := by
                rw [Compiler.CompilationModel.genParamLoadBodyFrom, hsingle, hgenRest,
                  hoffset]
              have hstate' :
                  (ParamLoading.applyBindingsToIRState state here).calldata = state.calldata :=
                applyBindingsToIRState_calldata state here
              have hstate'sel :
                  (ParamLoading.applyBindingsToIRState state here).selector = state.selector :=
                applyBindingsToIRState_selector state here
              have hstep :=
                exec_genSingleParamLoad_external_then state (genRest ++ rest) headSize
                  baseOffset param idx extraFuel here hbase hcalldataSize hparamSupported hhere
              have hih :=
                ih (ParamLoading.applyBindingsToIRState state here) rest (idx + 1) extraFuel
                  there (by rw [hstate']; exact hcalldataSize) hrestSupported
                  (by rw [hstate', hstate'sel]; exact hthere)
              have hfuel :
                  (single ++ genRest).length + rest.length + extraFuel + 1 =
                    single.length + (genRest ++ rest).length + extraFuel + 1 := by
                simp [List.length_append]
                omega
              rw [hgen, List.append_assoc, hfuel, hstep, applyBindingsToIRState_append]
              rw [show (genRest ++ rest).length + extraFuel + 1 =
                  genRest.length + rest.length + extraFuel + 1 by
                simp [List.length_append]]
              exact hih

/-! ### End-to-end: the emitted entrypoint prologue implements `bindExternalParams` -/

private theorem headSizeFoldl_go (params : List Param) (init : Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) init =
      init + 32 * params.length := by
  induction params generalizing init with
  | nil => simp
  | cons param rest ih =>
      have hparam : SupportedExternalParamType param.ty := hsupported param (by simp)
      have hrest : ∀ next ∈ rest, SupportedExternalParamType next.ty := by
        intro next hnext
        exact hsupported next (by simp [hnext])
      have h32 : paramHeadSize param.ty = 32 :=
        supportedExternalParamType_headSize_eq_32 hparam
      rw [List.map_cons, List.foldl_cons, h32, ih (init + 32) hrest]
      simp only [List.length_cons]
      omega

private theorem headSizeFoldl_eq (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0 = 32 * params.length := by
  simpa using headSizeFoldl_go params 0 hsupported

private theorem paramHeadSizeList_eq (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    paramHeadSizeList (params.map (·.ty)) = 32 * params.length := by
  induction params with
  | nil => simp [paramHeadSizeList]
  | cons param rest ih =>
      have hparam : SupportedExternalParamType param.ty := hsupported param (by simp)
      have hrest : ∀ next ∈ rest, SupportedExternalParamType next.ty := by
        intro next hnext
        exact hsupported next (by simp [hnext])
      rw [List.map_cons, paramHeadSizeList,
        supportedExternalParamType_headSize_eq_32 hparam, ih hrest]
      simp only [List.length_cons]
      omega

private theorem exec_minInputSizeCheck_noop
    (fuel : Nat) (state : IRState) (headSize : Nat)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hfits : 4 + headSize ≤ 4 + state.calldata.length * 32) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.if_ (YulExpr.call "lt"
        [YulExpr.call "calldatasize" [], YulExpr.lit (4 + headSize)])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue state := by
  have hrhs : 4 + headSize < Compiler.Constants.evmModulus := by omega
  have hnotlt : ¬ 4 + state.calldata.length * 32 < 4 + headSize := by omega
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Nat.mod_eq_of_lt hcalldataSizeFits, Nat.mod_eq_of_lt hrhs, hnotlt]

private theorem scalar_of_decode {ty : ParamType} {word value : Nat}
    (h : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    SupportedExternalScalarParamType ty := by
  cases ty <;>
    simp [SourceSemantics.decodeSupportedParamWord, SupportedExternalScalarParamType] at h ⊢

private theorem scalars_of_bindSupportedParams :
    ∀ {params : List Param} {args : List Nat} {bindings : List (String × Nat)},
      SourceSemantics.bindSupportedParams params args = some bindings →
      ∀ param ∈ params, SupportedExternalScalarParamType param.ty := by
  intro params
  induction params with
  | nil => intro _ _ _ param hparam; cases hparam
  | cons param restParams ih =>
      intro args bindings hbind next hnext
      cases args with
      | nil => simp [SourceSemantics.bindSupportedParams] at hbind
      | cons arg restArgs =>
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg with
          | none => simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
          | some value =>
              cases hrest : SourceSemantics.bindSupportedParams restParams restArgs with
              | none =>
                  simp [SourceSemantics.bindSupportedParams, hdecode, hrest] at hbind
              | some restBindings =>
                  rcases List.mem_cons.1 hnext with rfl | hmem
                  · exact scalar_of_decode hdecode
                  · exact ih hrest next hmem

/-- End-to-end refinement for the generated entrypoint prologue: whatever
bindings the dispatcher's external ABI binder produces, executing the emitted
calldata-decoding block reaches exactly that variable environment — for any
mixture of supported scalars, `bytes` and `string` parameters (verity#2085).

Together with `interpretContract_correct_of_functions_generic_external` this is
the composition that admits `bytes` and `string` into external dispatch. -/
theorem exec_genParamLoads_external
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind :
      DynamicAbi.bindExternalParams state.selector params state.calldata = some bindings) :
    execIRStmts ((genParamLoads params).length + 1) state (genParamLoads params) =
      .continue (ParamLoading.applyBindingsToIRState state bindings) := by
  have hlen : params.length ≤ state.calldata.length := by
    by_contra hcon
    rw [DynamicAbi.bindExternalParams, if_neg hcon] at hbind
    cases hbind
  cases hsup : SourceSemantics.bindSupportedParams params state.calldata with
  | some scalarBindings =>
      have hscalarTys : ∀ param ∈ params, SupportedExternalScalarParamType param.ty :=
        scalars_of_bindSupportedParams hsup
      have heq : scalarBindings = bindings := by
        rw [DynamicAbi.bindExternalParams, if_pos hlen,
          ← SourceSemantics.bindSupportedParams_eq_dynamicAbi, hsup] at hbind
        exact Option.some.inj hbind
      subst heq
      exact ParamLoading.exec_genParamLoads_supported state params scalarBindings hscalarTys
        hcalldataSizeFits hsup
  | none =>
      have hfrom :
          DynamicAbi.bindExternalParamsFrom state.selector state.calldata
            (paramHeadSizeList (params.map (·.ty))) 4 params 4 = some bindings := by
        rw [DynamicAbi.bindExternalParams, if_pos hlen,
          ← SourceSemantics.bindSupportedParams_eq_dynamicAbi, hsup] at hbind
        exact hbind
      have hHeadSize : paramHeadSizeList (params.map (·.ty)) = 32 * params.length :=
        paramHeadSizeList_eq params hsupported
      have hFoldl : (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0 =
          32 * params.length := headSizeFoldl_eq params hsupported
      rw [hHeadSize] at hfrom
      set body :=
        genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4 with hbody
      have hbodyExec :
          execIRStmts (body.length + 1) state body =
            .continue (ParamLoading.applyBindingsToIRState state bindings) := by
        have := exec_genParamLoadBodyFrom_external_then (headSize := 32 * params.length)
          (baseOffset := 4) (by decide) params state [] 0 0 bindings
          (by simpa [DynamicAbi.externalCalldataSize, Nat.mul_comm] using hcalldataSizeFits)
          hsupported (by simpa using hfrom)
        simpa [hbody, execIRStmts] using this
      have hguard :
          execIRStmt (body.length + 1) state
            (YulStmt.if_ (YulExpr.call "lt"
              [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
              [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
            .continue state :=
        exec_minInputSizeCheck_noop body.length state (32 * params.length)
          hcalldataSizeFits (by omega)
      have hstep :
          execIRStmts (body.length + 2) state
            (YulStmt.if_ (YulExpr.call "lt"
              [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
              [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] ::
              body) =
            execIRStmts (body.length + 1) state body := by
        simp [execIRStmts, hguard]
      simpa [Compiler.CompilationModel.genParamLoads,
        Compiler.CompilationModel.genParamLoadsFrom, hFoldl, hbody] using
        hstep.trans hbodyExec

end DynamicParamLoading

end Compiler.Proofs.IRGeneration
