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

private theorem externalCalldataSize_eq (calldata : List Nat) :
    DynamicAbi.externalCalldataSize calldata = 4 + calldata.length * 32 := by
  simp [DynamicAbi.externalCalldataSize, Nat.mul_comm]

/-- EVM word subtraction `sub(b, a)` agrees with `Nat` subtraction when it does
not underflow. -/
private theorem evm_sub_mod_of_le {a b : Nat} (hab : a ≤ b)
    (hb : b < Compiler.Constants.evmModulus) :
    (Compiler.Constants.evmModulus + b - a) % Compiler.Constants.evmModulus = b - a := by
  have hrw : Compiler.Constants.evmModulus + b - a =
      Compiler.Constants.evmModulus + (b - a) := by omega
  rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

private theorem absOffset_ne_length (name : String) :
    s!"{name}_abs_offset" ≠ s!"{name}_length" := by
  show name ++ "_abs_offset" ≠ name ++ "_length"
  exact append_right_ne_of_length_ne name (by decide)

/-- `let n := calldataload(offset)` binds the calldata word at a literal offset. -/
private theorem exec_let_calldataload_lit (f : Nat) (state : IRState) (n : String)
    (offset value : Nat)
    (h : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata offset =
      value) :
    execIRStmt (f + 1) state
        (YulStmt.let_ n (YulExpr.call "calldataload" [YulExpr.lit offset])) =
      .continue (state.setVar n value) := by
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, h]

/-- `let n := calldataload(m)` binds the calldata word at the offset held in `m`. -/
private theorem exec_let_calldataload_ident (f : Nat) (state : IRState) (n m : String)
    (offset value : Nat) (hget : state.getVar m = some offset)
    (h : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata offset =
      value) :
    execIRStmt (f + 1) state
        (YulStmt.let_ n (YulExpr.call "calldataload" [YulExpr.ident m])) =
      .continue (state.setVar n value) := by
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hget,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, h]

/-- `if lt(n, bound) { revert }` is a no-op once `n` holds a word `≥ bound`. -/
private theorem exec_revertIfLtLit_noop (f : Nat) (state : IRState) (n : String)
    (value bound : Nat) (hget : state.getVar n = some value)
    (hvalue : value < Compiler.Constants.evmModulus) (hbound : bound ≤ value) :
    execIRStmt (f + 1) state
        (YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident n, YulExpr.lit bound])
          [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue state := by
  have hnot : ¬ value % Compiler.Constants.evmModulus <
      bound % Compiler.Constants.evmModulus := by
    rw [Nat.mod_eq_of_lt hvalue, Nat.mod_eq_of_lt (by omega)]; omega
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hget,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hnot]

/-- `let n := add(base, m)` binds `base + m` when the sum fits in a word. -/
private theorem exec_let_add_lit_ident (f : Nat) (state : IRState) (n m : String)
    (base value : Nat) (hget : state.getVar m = some value)
    (hlt : base + value < Compiler.Constants.evmModulus) :
    execIRStmt (f + 1) state
        (YulStmt.let_ n (YulExpr.call "add" [YulExpr.lit base, YulExpr.ident m])) =
      .continue (state.setVar n (base + value)) := by
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hget,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Nat.mod_eq_of_lt hlt]

/-- `let n := add(m, 32)` binds `m + 32` when the sum fits in a word. -/
private theorem exec_let_add_ident_32 (f : Nat) (state : IRState) (n m : String)
    (value : Nat) (hget : state.getVar m = some value)
    (hlt : value + 32 < Compiler.Constants.evmModulus) :
    execIRStmt (f + 1) state
        (YulStmt.let_ n (YulExpr.call "add" [YulExpr.ident m, YulExpr.lit 32])) =
      .continue (state.setVar n (value + 32)) := by
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hget,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Nat.mod_eq_of_lt hlt]

/-- `let n := m` copies the value held in `m`. -/
private theorem exec_let_ident (f : Nat) (state : IRState) (n m : String) (value : Nat)
    (hget : state.getVar m = some value) :
    execIRStmt (f + 1) state (YulStmt.let_ n (YulExpr.ident m)) =
      .continue (state.setVar n value) := by
  simp [execIRStmt, evalIRExpr, hget]

/-- `if gt(n, sub(calldatasize(), 32)) { revert }` is a no-op once `n` holds an
offset leaving room for one more word of calldata. -/
private theorem exec_revertIfGtSizeSub32_noop (f : Nat) (state : IRState) (n : String)
    (value : Nat) (hget : state.getVar n = some value)
    (hsize : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbound : value + 32 ≤ 4 + state.calldata.length * 32) :
    execIRStmt (f + 1) state
        (YulStmt.if_ (YulExpr.call "gt"
          [ YulExpr.ident n
          , YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.lit 32] ])
          [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue state := by
  have hEvm : (32 : Nat) < Compiler.Constants.evmModulus := by omega
  have hnot : ¬ (4 + state.calldata.length * 32 - 32) % Compiler.Constants.evmModulus <
      value % Compiler.Constants.evmModulus := by
    rw [Nat.mod_eq_of_lt (show 4 + state.calldata.length * 32 - 32 <
        Compiler.Constants.evmModulus by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hget,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Nat.mod_eq_of_lt hsize, Nat.mod_eq_of_lt hEvm, evm_sub_mod_of_le (a := 32) (by omega) hsize,
    hnot]

/-- `let n := sub(calldatasize(), m)` binds the calldata remaining after `m`. -/
private theorem exec_let_sub_calldatasize_ident (f : Nat) (state : IRState) (n m : String)
    (calldata : List Nat) (value : Nat) (hcd : state.calldata = calldata)
    (hget : state.getVar m = some value)
    (hsize : 4 + calldata.length * 32 < Compiler.Constants.evmModulus)
    (hle : value ≤ 4 + calldata.length * 32) :
    execIRStmt (f + 1) state
        (YulStmt.let_ n (YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.ident m])) =
      .continue (state.setVar n (4 + calldata.length * 32 - value)) := by
  have hlt : value < Compiler.Constants.evmModulus := by omega
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hget, hcd,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Nat.mod_eq_of_lt hsize, Nat.mod_eq_of_lt hlt, evm_sub_mod_of_le hle hsize]

/-- The first two loader statements: load the head word, then check that it
clears the head area. -/
private theorem exec_offsetLoad_then (state : IRState) (tail : List YulStmt) (name : String)
    (headSize headOffset relativeOffset k : Nat)
    (hro : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      headOffset = relativeOffset)
    (hroLt : relativeOffset < Compiler.Constants.evmModulus)
    (hheadBound : headSize ≤ relativeOffset) :
    execIRStmts (k + 3) state
        (YulStmt.let_ s!"{name}_offset" (YulExpr.call "calldataload" [YulExpr.lit headOffset]) ::
          YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident s!"{name}_offset", YulExpr.lit headSize])
            [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] :: tail) =
      execIRStmts (k + 1) (state.setVar s!"{name}_offset" relativeOffset) tail := by
  rw [execIRStmts_succ_cons_of_continue _ _ _ _ _
      (exec_let_calldataload_lit (k + 1) state _ _ _ hro),
    execIRStmts_succ_cons_of_continue _ _ _ _ _
      (exec_revertIfLtLit_noop k _ _ _ _ (getVar_setVar_self _ _ _) hroLt hheadBound)]

/-- The third and fourth loader statements: compute the absolute offset, then
check that one word of calldata remains past it. -/
private theorem exec_absOffset_then (state : IRState) (tail : List YulStmt) (name : String)
    (baseOffset relativeOffset k : Nat)
    (hget : state.getVar s!"{name}_offset" = some relativeOffset)
    (hsize : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (htailBound : baseOffset + relativeOffset + 32 ≤ 4 + state.calldata.length * 32) :
    execIRStmts (k + 3) state
        (YulStmt.let_ s!"{name}_abs_offset"
            (YulExpr.call "add" [YulExpr.lit baseOffset, YulExpr.ident s!"{name}_offset"]) ::
          YulStmt.if_ (YulExpr.call "gt"
            [ YulExpr.ident s!"{name}_abs_offset"
            , YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.lit 32] ])
            [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] :: tail) =
      execIRStmts (k + 1)
        (state.setVar s!"{name}_abs_offset" (baseOffset + relativeOffset)) tail := by
  rw [execIRStmts_succ_cons_of_continue _ _ _ _ _ (exec_let_add_lit_ident (k + 1) state
      s!"{name}_abs_offset" _ baseOffset _ hget (by omega)),
    execIRStmts_succ_cons_of_continue _ _ _ _ _ (exec_revertIfGtSizeSub32_noop k
      (state.setVar s!"{name}_abs_offset" (baseOffset + relativeOffset)) _ _
      (getVar_setVar_self _ _ _) hsize htailBound)]

/-- The fifth to seventh loader statements: load the length word, then bind the
tail start and the calldata remaining after it. -/
private theorem exec_lengthTail_then (state : IRState) (tail : List YulStmt) (name : String)
    (calldata : List Nat) (absOffset length k : Nat) (hcd : state.calldata = calldata)
    (hget : state.getVar s!"{name}_abs_offset" = some absOffset)
    (hsize : 4 + calldata.length * 32 < Compiler.Constants.evmModulus)
    (htailBound : absOffset + 32 ≤ 4 + calldata.length * 32)
    (hlenWord : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      absOffset = length) :
    execIRStmts (k + 4) state
        (YulStmt.let_ s!"{name}_length"
            (YulExpr.call "calldataload" [YulExpr.ident s!"{name}_abs_offset"]) ::
          YulStmt.let_ s!"{name}_tail_head_end"
            (YulExpr.call "add" [YulExpr.ident s!"{name}_abs_offset", YulExpr.lit 32]) ::
          YulStmt.let_ s!"{name}_tail_remaining" (YulExpr.call "sub"
            [YulExpr.call "calldatasize" [], YulExpr.ident s!"{name}_tail_head_end"]) :: tail) =
      execIRStmts (k + 1) (((state.setVar s!"{name}_length" length).setVar
        s!"{name}_tail_head_end" (absOffset + 32)).setVar s!"{name}_tail_remaining"
          (4 + calldata.length * 32 - (absOffset + 32))) tail := by
  have hget' : (state.setVar s!"{name}_length" length).getVar s!"{name}_abs_offset" =
      some absOffset := by rw [getVar_setVar_of_ne _ _ _ _ (absOffset_ne_length name), hget]
  rw [execIRStmts_succ_cons_of_continue _ _ _ _ _
      (exec_let_calldataload_ident (k + 2) state _ _ _ _ hget hlenWord),
    execIRStmts_succ_cons_of_continue _ _ _ _ _
      (exec_let_add_ident_32 (k + 1) _ s!"{name}_tail_head_end" _ _ hget' (by omega)),
    execIRStmts_succ_cons_of_continue _ _ _ _ _ (exec_let_sub_calldatasize_ident k
      ((state.setVar s!"{name}_length" length).setVar s!"{name}_tail_head_end" (absOffset + 32))
      s!"{name}_tail_remaining" _ calldata _ hcd (getVar_setVar_self _ _ _) hsize htailBound)]

/-- The first seven statements of a length-prefixed loader run straight through
to `lengthPrefixedLoaderState`, leaving the payload guard and the data pointer. -/
private theorem exec_lengthPrefixedLoaderStmts_prefix
    (state : IRState) (rest : List YulStmt) (name : String)
    (headSize baseOffset headOffset relativeOffset length k : Nat) (payloadGuard : YulStmt)
    (hsize : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hro : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      headOffset = relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound : baseOffset + relativeOffset + 32 ≤ 4 + state.calldata.length * 32)
    (hlenWord : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      (baseOffset + relativeOffset) = length) :
    execIRStmts (k + 8) state
        (lengthPrefixedLoaderStmts (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset name headOffset payloadGuard
          ++ rest) =
      execIRStmts (k + 1)
        (lengthPrefixedLoaderState state name (4 + state.calldata.length * 32) baseOffset
          relativeOffset length)
        (payloadGuard ::
          YulStmt.let_ s!"{name}_data_offset" (YulExpr.ident s!"{name}_tail_head_end") ::
            rest) := by
  simp only [lengthPrefixedLoaderStmts, lengthPrefixedLoaderState, List.cons_append,
    List.nil_append]
  rw [exec_offsetLoad_then state _ name headSize headOffset relativeOffset (k + 5) hro
      (by omega) hheadBound,
    exec_absOffset_then _ _ name baseOffset relativeOffset (k + 3) (getVar_setVar_self _ _ _)
      hsize htailBound, exec_lengthTail_then _ _ name state.calldata _ length k]
  all_goals first | rfl | assumption | exact getVar_setVar_self _ _ _

private theorem getVar_lengthPrefixedLoaderState_tailHeadEnd (state : IRState) (name : String)
    (calldataSize baseOffset relativeOffset length : Nat) :
    (lengthPrefixedLoaderState state name calldataSize baseOffset relativeOffset length).getVar
      s!"{name}_tail_head_end" = some (baseOffset + relativeOffset + 32) := by
  rw [lengthPrefixedLoaderState,
    getVar_setVar_of_ne _ _ _ _ (tailHeadEnd_ne_tailRemaining name), getVar_setVar_self]

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
    (headSize baseOffset headOffset relativeOffset length extraFuel : Nat) (payloadGuard : YulStmt)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hhead : DynamicAbi.externalWordAt? state.selector state.calldata headOffset =
      some relativeOffset) (hheadBound : headSize ≤ relativeOffset)
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
  rw [externalCalldataSize_eq] at hcalldataSize htailBound hguard ⊢
  rw [exec_lengthPrefixedLoaderStmts_prefix _ _ _ _ _ _ _ _ _ _ hcalldataSize
      (externalWordAt?_eq_calldataloadWord hhead) hheadBound htailBound
      (externalWordAt?_eq_calldataloadWord hlength),
    execIRStmts_succ_cons_of_continue _ _ _ _ _ (hguard _)]
  exact execIRStmts_succ_cons_of_continue _ _ _ _ _
    (exec_let_ident _ _ _ _ _ (getVar_lengthPrefixedLoaderState_tailHeadEnd _ _ _ _ _ _))

private theorem getVar_lengthPrefixedLoaderState_length (state : IRState) (name : String)
    (calldataSize baseOffset relativeOffset length : Nat) :
    (lengthPrefixedLoaderState state name calldataSize baseOffset relativeOffset length).getVar
      s!"{name}_length" = some length := by
  rw [lengthPrefixedLoaderState,
    getVar_setVar_of_ne _ _ _ _ (length_ne_tailRemaining name),
    getVar_setVar_of_ne _ _ _ _ (length_ne_tailHeadEnd name), getVar_setVar_self]

/-- `bytesPayloadGuard` is a no-op once the length fits in the remaining calldata. -/
private theorem exec_bytesPayloadGuard_noop_of_getVar (f : Nat) (state : IRState)
    (name : String) (length remaining : Nat)
    (hlen : state.getVar s!"{name}_length" = some length)
    (hrem : state.getVar s!"{name}_tail_remaining" = some remaining)
    (hremLt : remaining < Compiler.Constants.evmModulus) (hbound : length ≤ remaining) :
    execIRStmt (f + 1) state (bytesPayloadGuard name) = .continue state := by
  have hnot : ¬ remaining % Compiler.Constants.evmModulus <
      length % Compiler.Constants.evmModulus := by
    rw [Nat.mod_eq_of_lt (show length < Compiler.Constants.evmModulus by omega),
      Nat.mod_eq_of_lt hremLt]; omega
  simp [bytesPayloadGuard, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hlen, hrem,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hnot]

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
  exact exec_bytesPayloadGuard_noop_of_getVar f _ name length _
    (getVar_lengthPrefixedLoaderState_length _ _ _ _ _ _) (getVar_setVar_self _ _ _)
    (by omega) hpayloadBound

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
  exec_lengthPrefixedLoaderStmts_then state rest name headSize baseOffset headOffset _ _
    extraFuel _ hcalldataSize hhead hheadBound htailBound hlength
    (exec_bytesPayloadGuard_noop _ _ _ _ _ hcalldataSize hpayloadBound)

/-- The `div` comparison in `arrayPayloadGuard` never fires within the bound. -/
private theorem array_guard_not_lt {remaining stride length : Nat}
    (hstride : stride < Compiler.Constants.evmModulus)
    (hremLt : remaining < Compiler.Constants.evmModulus) (hbound : length ≤ remaining / stride) :
    ¬ (remaining % Compiler.Constants.evmModulus / (stride % Compiler.Constants.evmModulus)) %
      Compiler.Constants.evmModulus < length % Compiler.Constants.evmModulus := by
  have hquotLt : remaining / stride < Compiler.Constants.evmModulus :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hremLt
  rw [Nat.mod_eq_of_lt hstride, Nat.mod_eq_of_lt hremLt, Nat.mod_eq_of_lt hquotLt,
    Nat.mod_eq_of_lt (show length < Compiler.Constants.evmModulus by omega)]
  omega

/-- `arrayPayloadGuard` is a no-op once the element count fits in the remaining
calldata at one `dynamicArrayElementStrideWords` stride per element. -/
private theorem exec_arrayPayloadGuard_noop_of_getVar (f : Nat) (state : IRState)
    (name : String) (elemTy : ParamType) (length remaining : Nat)
    (hlen : state.getVar s!"{name}_length" = some length)
    (hrem : state.getVar s!"{name}_tail_remaining" = some remaining)
    (hstride : 32 * dynamicArrayElementStrideWords elemTy < Compiler.Constants.evmModulus)
    (hremLt : remaining < Compiler.Constants.evmModulus)
    (hbound : length ≤ remaining / (32 * dynamicArrayElementStrideWords elemTy)) :
    execIRStmt (f + 1) state (arrayPayloadGuard name elemTy) = .continue state := by
  have hstridePos : 0 < 32 * dynamicArrayElementStrideWords elemTy := by
    have := dynamicArrayElementStrideWords_pos elemTy
    omega
  have hstrideNe : ¬ 32 * dynamicArrayElementStrideWords elemTy %
      Compiler.Constants.evmModulus = 0 := by
    rw [Nat.mod_eq_of_lt hstride]; omega
  simp [arrayPayloadGuard, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hlen, hrem,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    hstrideNe, array_guard_not_lt hstride hremLt hbound]

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
  exact exec_arrayPayloadGuard_noop_of_getVar f _ name elemTy length _
    (getVar_lengthPrefixedLoaderState_length _ _ _ _ _ _) (getVar_setVar_self _ _ _) hstride
    (by omega) hpayloadBound

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
  exec_lengthPrefixedLoaderStmts_then state rest name headSize baseOffset headOffset _ _
    extraFuel _ hcalldataSize hhead hheadBound htailBound hlength
    (exec_arrayPayloadGuard_noop _ _ _ _ _ _ hcalldataSize hstride hpayloadBound)

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
  rw [externalCalldataSize_eq] at hcalldataSize htailBound
  simp only [dynamicCompositeLoaderStmts, dynamicCompositeParamBindings,
    ParamLoading.applyBindingsToIRState, List.cons_append, List.nil_append]
  rw [exec_offsetLoad_then state _ name headSize headOffset relativeOffset
      (rest.length + extraFuel + 3) (externalWordAt?_eq_calldataloadWord hhead) (by omega)
      hheadBound,
    exec_absOffset_then _ _ name baseOffset relativeOffset (rest.length + extraFuel + 1)
      (getVar_setVar_self _ _ _) hcalldataSize htailBound]
  exact execIRStmts_succ_cons_of_continue _ _ _ _ _
    (exec_let_ident _ _ _ _ _ (getVar_setVar_self _ _ _))

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

/-- Running the loader emitted for one external parameter `name : ty` at head
slot `idx` in front of `rest` reaches the state extended with `here`. -/
private def ExecSingleParamLoad (state : IRState) (rest : List YulStmt)
    (headSize baseOffset : Nat) (name : String) (ty : ParamType) (idx extraFuel : Nat)
    (here : List (String × Nat)) : Prop :=
  execIRStmts ((genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) headSize baseOffset name ty
      (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
    (genSingleParamLoad (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) headSize baseOffset name ty
      (4 + 32 * idx) ++ rest) =
    execIRStmts (rest.length + extraFuel + 1)
      (ParamLoading.applyBindingsToIRState state here) rest

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
    ExecSingleParamLoad state rest headSize baseOffset name ty idx extraFuel here := by
  obtain ⟨relativeOffset, length, hhead, hheadBound, htailBound, hlength,
    hpayloadBound, hhere⟩ := DynamicAbi.bindExternalParam_bytes_eq_some_inv hbind
  subst hhere
  rw [ExecSingleParamLoad, hstmts]
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
    ExecSingleParamLoad state rest headSize baseOffset name ty idx extraFuel here := by
  obtain ⟨relativeOffset, length, hhead, hheadBound, htailBound, hlength,
    hpayloadBound, hhere⟩ := DynamicAbi.bindExternalParam_array_eq_some_inv hbind
  subst hhere
  rw [ExecSingleParamLoad, hstmts]
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
    ExecSingleParamLoad state rest headSize baseOffset name ty idx extraFuel here := by
  obtain ⟨relativeOffset, hhead, hheadBound, htailBound, hhere⟩ :=
    DynamicAbi.bindExternalParam_dynamicComposite_eq_some_inv hdynamic hnotLengthPrefixed hbind
  subst hhere
  rw [ExecSingleParamLoad, hstmts]
  have hexec := exec_dynamicCompositeLoaderStmts_then state rest name headSize baseOffset
    (4 + 32 * idx) relativeOffset extraFuel hcalldataSize hhead hheadBound htailBound
  simpa [dynamicCompositeParamBindings, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hexec

/-- The non-scalar cases of the per-parameter composition: `bytes`, `string`,
`T[]`, and the two dynamic-composite shapes. -/
private theorem exec_dynamicParamLoad_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (name : String) (ty : ParamType) (idx extraFuel : Nat) (here : List (String × Nat))
    (hbase : ¬ (baseOffset == 0) = true)
    (hcalldataSize :
      DynamicAbi.externalCalldataSize state.calldata < Compiler.Constants.evmModulus)
    (hdyn : ty = ParamType.bytes ∨ ty = ParamType.string ∨
      (∃ elemTy, ty = ParamType.array elemTy ∧ ExternalArrayStrideFitsWord elemTy) ∨
      (∃ elemTy n, ty = ParamType.fixedArray elemTy n ∧ isDynamicParamType elemTy = true) ∨
      (∃ elemTys, ty = ParamType.tuple elemTys ∧ isDynamicParamTypeList elemTys = true))
    (hbind : DynamicAbi.bindExternalParam state.selector state.calldata headSize baseOffset
      (4 + 32 * idx) { name := name, ty := ty } = some here) :
    ExecSingleParamLoad state rest headSize baseOffset name ty idx extraFuel here := by
  rcases hdyn with rfl | rfl | ⟨elemTy, rfl, hstride⟩ | ⟨elemTy, n, rfl, hdynE⟩ | ⟨tys, rfl, hdynL⟩
  · exact exec_bytesLikeParamLoad_then state rest headSize baseOffset name _ idx extraFuel
      here hcalldataSize (genSingleParamLoad_bytes _ _ _ _ _ _ hbase) hbind
  · rw [DynamicAbi.bindExternalParam_string_eq_bytes] at hbind
    exact exec_bytesLikeParamLoad_then state rest headSize baseOffset name _ idx extraFuel
      here hcalldataSize (genSingleParamLoad_string _ _ _ _ _ _ hbase) hbind
  · exact exec_arrayParamLoad_then state rest headSize baseOffset name _ elemTy idx extraFuel
      here hcalldataSize hstride (genSingleParamLoad_array _ _ _ _ _ _ _ hbase) hbind
  · exact exec_dynamicCompositeParamLoad_then state rest headSize baseOffset name _ idx
      extraFuel here hcalldataSize (by simpa [isDynamicParamType] using hdynE) rfl
      (genSingleParamLoad_dynamicFixedArray _ _ _ _ _ _ _ _ hbase hdynE) hbind
  · exact exec_dynamicCompositeParamLoad_then state rest headSize baseOffset name _ idx
      extraFuel here hcalldataSize (by simpa [isDynamicParamType] using hdynL) rfl
      (genSingleParamLoad_dynamicTuple _ _ _ _ _ _ _ hbase hdynL) hbind

/-- The head word the external binder decodes is the scalar loader's aligned word. -/
private theorem decode_getD_of_externalWordAt {ty : ParamType} {selector idx word value : Nat}
    {calldata : List Nat}
    (hword : DynamicAbi.externalWordAt? selector calldata (4 + 32 * idx) = some word)
    (hdecode : DynamicAbi.decodeSupportedParamWord ty word = some value) :
    SourceSemantics.decodeSupportedParamWord ty (calldata.getD idx 0) = some value := by
  have hwordEq : word = calldata.getD idx 0 % Compiler.Constants.evmModulus := by
    have := externalWordAt?_eq_calldataloadWord hword
    rw [ParamLoading.calldataloadWord_aligned] at this
    exact this.symm
  rw [← decodeSupportedParamWord_mod, ← hwordEq,
    SourceSemantics.decodeSupportedParamWord_eq_dynamicAbi]
  exact hdecode

/-- The scalar case of the per-parameter composition. -/
private theorem exec_scalarParamLoad_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (param : Param) (idx extraFuel : Nat) (here : List (String × Nat))
    (hscalar : SupportedExternalScalarParamType param.ty)
    (hbind : DynamicAbi.bindExternalParam state.selector state.calldata headSize baseOffset
      (4 + 32 * idx) param = some here) :
    ExecSingleParamLoad state rest headSize baseOffset param.name param.ty idx extraFuel
      here := by
  obtain ⟨word, value, hword, hdecode, hhere⟩ :=
    DynamicAbi.bindExternalParam_scalar_eq_some_inv (SourceSemantics.scalarHeadParamType_of_supported hscalar) hbind
  subst hhere
  rw [ExecSingleParamLoad, genSingleParamLoad_scalar _ _ _ _ _ _ _ hscalar]
  simpa [ParamLoading.applyBindingsToIRState] using
    ParamLoading.exec_genScalarLoad_supported_then state rest param.name param.ty idx value
      extraFuel hscalar (decode_getD_of_externalWordAt hword hdecode)

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
  rcases supportedExternalParamType_cases hsupported with hscalar | hdyn
  · exact exec_scalarParamLoad_then state rest headSize baseOffset param idx extraFuel here
      hscalar hbind
  · exact exec_dynamicParamLoad_then state rest headSize baseOffset param.name param.ty idx
      extraFuel here hbase hcalldataSize hdyn hbind

/-- The statement of `exec_genParamLoadBodyFrom_external_then` for a fixed
parameter list, as the induction motive over that list. -/
private def ExecParamLoadBodyFrom (headSize baseOffset : Nat) (params : List Param) : Prop :=
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
        (ParamLoading.applyBindingsToIRState state bindings) rest

private theorem exec_paramLoadBodyFrom_nil (headSize baseOffset : Nat) :
    ExecParamLoadBodyFrom headSize baseOffset [] := by
  intro state rest idx extraFuel bindings _ _ hbind
  simp only [DynamicAbi.bindExternalParamsFrom, Option.some.injEq] at hbind
  subst hbind
  simp [Compiler.CompilationModel.genParamLoadBodyFrom, ParamLoading.applyBindingsToIRState]

/-- A supported parameter occupies exactly one head word. -/
private theorem headOffset_succ_of_supported {ty : ParamType}
    (hsupported : SupportedExternalParamType ty) (idx : Nat) :
    4 + 32 * idx + paramHeadSize ty = 4 + 32 * (idx + 1) := by
  rw [supportedExternalParamType_headSize_eq_32 hsupported]; ring

/-- Inverting a successful binder run over a non-empty parameter list. -/
private theorem bindExternalParamsFrom_cons_eq_some {selector headSize baseOffset idx : Nat}
    {calldata : List Nat} {param : Param} {params : List Param}
    {bindings : List (String × Nat)}
    (hoffset : 4 + 32 * idx + paramHeadSize param.ty = 4 + 32 * (idx + 1))
    (hbind : DynamicAbi.bindExternalParamsFrom selector calldata headSize baseOffset
      (param :: params) (4 + 32 * idx) = some bindings) :
    ∃ here there, DynamicAbi.bindExternalParam selector calldata headSize baseOffset
        (4 + 32 * idx) param = some here ∧
      DynamicAbi.bindExternalParamsFrom selector calldata headSize baseOffset params
        (4 + 32 * (idx + 1)) = some there ∧ bindings = here ++ there := by
  cases hhere : DynamicAbi.bindExternalParam selector calldata headSize baseOffset
      (4 + 32 * idx) param with
  | none =>
      rw [DynamicAbi.bindExternalParamsFrom, hhere] at hbind
      simp at hbind
  | some here =>
      cases hthere : DynamicAbi.bindExternalParamsFrom selector calldata headSize baseOffset
          params (4 + 32 * (idx + 1)) with
      | none =>
          rw [DynamicAbi.bindExternalParamsFrom, hhere, hoffset, hthere] at hbind
          simp at hbind
      | some there =>
          rw [DynamicAbi.bindExternalParamsFrom, hhere, hoffset, hthere] at hbind
          simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq] at hbind
          exact ⟨here, there, rfl, rfl, hbind.symm⟩

/-- Sequencing two blocks whose fuel budgets are each phrased over their own
length and the code that follows them. -/
private theorem execIRStmts_append_trans (first second rest : List YulStmt) (extraFuel : Nat)
    (state mid : IRState) (result : IRExecResult)
    (hfirst : execIRStmts (first.length + (second ++ rest).length + extraFuel + 1) state
        (first ++ (second ++ rest)) =
      execIRStmts ((second ++ rest).length + extraFuel + 1) mid (second ++ rest))
    (hsecond : execIRStmts (second.length + rest.length + extraFuel + 1) mid
        (second ++ rest) = result) :
    execIRStmts ((first ++ second).length + rest.length + extraFuel + 1) state
        (first ++ second ++ rest) = result := by
  have hfuel : (first ++ second).length + rest.length + extraFuel + 1 =
      first.length + (second ++ rest).length + extraFuel + 1 := by
    simp only [List.length_append]; omega
  rw [hfuel, List.append_assoc, hfirst]
  simpa only [List.length_append, Nat.add_assoc] using hsecond

private theorem exec_paramLoadBodyFrom_cons (headSize baseOffset : Nat)
    (hbase : ¬ (baseOffset == 0) = true) (param : Param) (restParams : List Param)
    (ih : ExecParamLoadBodyFrom headSize baseOffset restParams) :
    ExecParamLoadBodyFrom headSize baseOffset (param :: restParams) := by
  intro state rest idx extraFuel bindings hcalldataSize hsupported hbind
  have hparam : SupportedExternalParamType param.ty := hsupported param (by simp)
  obtain ⟨here, there, hhere, hthere, rfl⟩ :=
    bindExternalParamsFrom_cons_eq_some (headOffset_succ_of_supported hparam idx) hbind
  rw [Compiler.CompilationModel.genParamLoadBodyFrom, headOffset_succ_of_supported hparam idx,
    applyBindingsToIRState_append]
  exact execIRStmts_append_trans _ _ _ _ _ _ _
    (exec_genSingleParamLoad_external_then state _ headSize baseOffset param idx extraFuel
      here hbase hcalldataSize hparam hhere)
    (ih _ rest (idx + 1) extraFuel there (by simpa using hcalldataSize)
      (fun next hnext => hsupported next (by simp [hnext])) (by simpa using hthere))

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
  | nil => exact exec_paramLoadBodyFrom_nil headSize baseOffset
  | cons param restParams ih =>
      exact exec_paramLoadBodyFrom_cons headSize baseOffset hbase param restParams ih

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

/-- The emitted parameter-list body, run on its own, reaches the bindings the
external binder computes from the head offset `4`. -/
private theorem exec_paramLoadBody_of_bindFrom (state : IRState) (params : List Param)
    (bindings : List (String × Nat))
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hfrom : DynamicAbi.bindExternalParamsFrom state.selector state.calldata
      (32 * params.length) 4 params 4 = some bindings) :
    execIRStmts ((genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4).length + 1) state
      (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4) =
      .continue (ParamLoading.applyBindingsToIRState state bindings) := by
  have := exec_genParamLoadBodyFrom_external_then (headSize := 32 * params.length)
    (baseOffset := 4) (by decide) params state [] 0 0 bindings
    (by simpa [DynamicAbi.externalCalldataSize, Nat.mul_comm] using hcalldataSizeFits)
    hsupported (by simpa using hfrom)
  simpa [execIRStmts] using this

/-- The dynamic branch of `exec_genParamLoads_external`: the binder fell
through to the external ABI decoder, so the minimum-size guard is followed by
the full parameter-list lift. -/
private theorem exec_genParamLoads_external_of_bindFrom
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hlen : params.length ≤ state.calldata.length)
    (hfrom : DynamicAbi.bindExternalParamsFrom state.selector state.calldata
      (paramHeadSizeList (params.map (·.ty))) 4 params 4 = some bindings) :
    execIRStmts ((genParamLoads params).length + 1) state (genParamLoads params) =
      .continue (ParamLoading.applyBindingsToIRState state bindings) := by
  rw [paramHeadSizeList_eq params hsupported] at hfrom
  have hbodyExec :=
    exec_paramLoadBody_of_bindFrom state params bindings hsupported hcalldataSizeFits hfrom
  set body :=
    genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4 with hbody
  have hstep := execIRStmts_succ_cons_of_continue _ _ _ _ body
    (exec_minInputSizeCheck_noop body.length state (32 * params.length) hcalldataSizeFits
      (by omega))
  simpa [Compiler.CompilationModel.genParamLoads, Compiler.CompilationModel.genParamLoadsFrom,
    headSizeFoldl_eq params hsupported, hbody] using hstep.trans hbodyExec

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
  rw [DynamicAbi.bindExternalParams, if_pos hlen,
    ← SourceSemantics.bindSupportedParams_eq_dynamicAbi] at hbind
  cases hsup : SourceSemantics.bindSupportedParams params state.calldata with
  | some scalarBindings =>
      rw [hsup] at hbind
      cases Option.some.inj hbind
      exact ParamLoading.exec_genParamLoads_supported state params _
        (scalars_of_bindSupportedParams hsup) hcalldataSizeFits hsup
  | none =>
      rw [hsup] at hbind
      exact exec_genParamLoads_external_of_bindFrom state params bindings hsupported
        hcalldataSizeFits hlen hbind

end DynamicParamLoading

end Compiler.Proofs.IRGeneration
