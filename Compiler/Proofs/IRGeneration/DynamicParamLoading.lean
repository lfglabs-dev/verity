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

private theorem append_right_ne_of_ne {a b : String} (prefix_ : String) (h : a ≠ b) :
    prefix_ ++ a ≠ prefix_ ++ b := by
  intro heq
  apply h
  have hdata : (prefix_ ++ a).data = (prefix_ ++ b).data := by rw [heq]
  simp only [String.data_append, List.append_cancel_left_eq] at hdata
  exact String.ext hdata

private theorem length_ne_tailHeadEnd (name : String) :
    s!"{name}_length" ≠ s!"{name}_tail_head_end" := by
  simpa using append_right_ne_of_ne (prefix_ := name) (a := "_length")
    (b := "_tail_head_end") (by decide)

private theorem length_ne_tailRemaining (name : String) :
    s!"{name}_length" ≠ s!"{name}_tail_remaining" := by
  simpa using append_right_ne_of_ne (prefix_ := name) (a := "_length")
    (b := "_tail_remaining") (by decide)

private theorem tailHeadEnd_ne_tailRemaining (name : String) :
    s!"{name}_tail_head_end" ≠ s!"{name}_tail_remaining" := by
  simpa using append_right_ne_of_ne (prefix_ := name) (a := "_tail_head_end")
    (b := "_tail_remaining") (by decide)

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
          simp [List.filter, List.find?, hentry, hq, ih]
        · simp [List.filter, List.find?, hentry, ih]
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

/-- The nine statements `genSingleParamLoad` emits for a `bytes` external
parameter, at a non-zero ABI base offset (external dispatch uses `4`). -/
def bytesLoaderStmts (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
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
  , YulStmt.let_ s!"{name}_length" (loadWord (YulExpr.ident s!"{name}_abs_offset"))
  , YulStmt.let_ s!"{name}_tail_head_end"
      (YulExpr.call "add" [YulExpr.ident s!"{name}_abs_offset", YulExpr.lit 32])
  , YulStmt.let_ s!"{name}_tail_remaining"
      (YulExpr.call "sub" [sizeExpr, YulExpr.ident s!"{name}_tail_head_end"])
  , YulStmt.if_ (YulExpr.call "gt"
      [ YulExpr.ident s!"{name}_length", YulExpr.ident s!"{name}_tail_remaining" ])
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  , YulStmt.let_ s!"{name}_data_offset" (YulExpr.ident s!"{name}_tail_head_end") ]

theorem genSingleParamLoad_bytes
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (headOffset : Nat)
    (hbase : ¬ (baseOffset == 0) = true) :
    genSingleParamLoad loadWord sizeExpr headSize baseOffset name ParamType.bytes headOffset =
      bytesLoaderStmts loadWord sizeExpr headSize baseOffset name headOffset := by
  simp [genSingleParamLoad, genDynamicParamLoads, isLengthPrefixedDynamicShape,
    bytesLoaderStmts, hbase]

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
  · simpa [DynamicAbi.externalWordAt?, hbounds] using h.symm
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

/-- Executing the nine statements the compiler emits for a `bytes` external
parameter binds exactly the six values the ABI model assigns to it, and never
reverts, whenever the calldata satisfies the model's decoding side conditions.

This is the execution half of the refinement opened by verity#2373: combined
with `DynamicAbi.bindExternalParam_bytes_refines_dynamic_loader` it says the
generated loader implements `bindExternalParam` for `bytes`. -/
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
            baseOffset relativeOffset length)) rest := by
  have hcsz : DynamicAbi.externalCalldataSize state.calldata =
      4 + state.calldata.length * 32 := by
    simp [DynamicAbi.externalCalldataSize, Nat.mul_comm]
  rw [hcsz] at hcalldataSize htailBound hpayloadBound ⊢
  have hro : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      headOffset = relativeOffset := externalWordAt?_eq_calldataloadWord hhead
  have hlenWord : Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.calldata
      (baseOffset + relativeOffset) = length := externalWordAt?_eq_calldataloadWord hlength
  have hEvm : (32 : Nat) < Compiler.Constants.evmModulus := by omega
  have hroLt : relativeOffset < Compiler.Constants.evmModulus := by omega
  have hHeadSizeLt : headSize < Compiler.Constants.evmModulus := by omega
  have hAbsLt : baseOffset + relativeOffset < Compiler.Constants.evmModulus := by omega
  have hTheLt : baseOffset + relativeOffset + 32 < Compiler.Constants.evmModulus := by omega
  have hLengthLt : length < Compiler.Constants.evmModulus := by omega
  have hTrLt : 4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32) <
      Compiler.Constants.evmModulus := by omega
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
        simpa [hnAbs, hnLength] using
          (append_right_ne_of_ne (prefix_ := name) (a := "_abs_offset") (b := "_length")
            (by decide))), getVar_setVar_self]
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
  -- Statement 8: `if gt({name}_length, {name}_tail_remaining) { revert }` — never taken
  have h8 : ∀ f : Nat, execIRStmt (f + 1)
      (((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)).setVar nTailRemaining
            (4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32)))
      (YulStmt.if_ (YulExpr.call "gt"
        [YulExpr.ident nLength, YulExpr.ident nTailRemaining])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue (((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)).setVar nTailRemaining
            (4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32))) := by
    intro f
    have hgetLength : (((((state.setVar nOffset relativeOffset).setVar nAbs
        (baseOffset + relativeOffset)).setVar nLength length).setVar nTailHeadEnd
          (baseOffset + relativeOffset + 32)).setVar nTailRemaining
            (4 + state.calldata.length * 32 -
              (baseOffset + relativeOffset + 32))).getVar nLength = some length := by
      rw [getVar_setVar_of_ne _ _ _ _ hLenNeTr, getVar_setVar_of_ne _ _ _ _ hLenNeThe,
        getVar_setVar_self]
    have hnot : ¬ length % Compiler.Constants.evmModulus <
        (4 + state.calldata.length * 32 - (baseOffset + relativeOffset + 32)) %
          Compiler.Constants.evmModulus := by
      rw [Nat.mod_eq_of_lt hLengthLt, Nat.mod_eq_of_lt hTrLt]
      omega
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, getVar_setVar_self, hgetLength,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hnot]
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
  simp only [bytesLoaderStmts, bytesParamBindings, ParamLoading.applyBindingsToIRState,
    List.cons_append, List.nil_append]
  rw [execIRStmts_cons_continue _ _ _ _ _ (h1 (rest.length + extraFuel + 8)),
    execIRStmts_cons_continue _ _ _ _ _ (h2 (rest.length + extraFuel + 7)),
    execIRStmts_cons_continue _ _ _ _ _ (h3 (rest.length + extraFuel + 6)),
    execIRStmts_cons_continue _ _ _ _ _ (h4 (rest.length + extraFuel + 5)),
    execIRStmts_cons_continue _ _ _ _ _ (h5 (rest.length + extraFuel + 4)),
    execIRStmts_cons_continue _ _ _ _ _ (h6 (rest.length + extraFuel + 3)),
    execIRStmts_cons_continue _ _ _ _ _ (h7 (rest.length + extraFuel + 2)),
    execIRStmts_cons_continue _ _ _ _ _ (h8 (rest.length + extraFuel + 1)),
    execIRStmts_cons_continue _ _ _ _ _ (h9 (rest.length + extraFuel))]

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

/-- Executing the statements emitted for one supported external parameter lands
on exactly the bindings `DynamicAbi.bindExternalParam` assigns to it. This is
the per-parameter composition: `bytes` goes through the loader refinement,
scalars through the existing single-word lemma. -/
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
  rcases supportedExternalParamType_scalar_or_bytes hsupported with hscalar | hbytes
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
    obtain ⟨relativeOffset, length, hhead, hheadBound, htailBound, hlength,
      hpayloadBound, hhere⟩ := DynamicAbi.bindExternalParam_bytes_eq_some_inv hbind
    subst hhere
    rw [hbytes, genSingleParamLoad_bytes _ _ _ _ _ _ hbase]
    have hexec := exec_bytesLoaderStmts_then state rest param.name headSize baseOffset
      (4 + 32 * idx) relativeOffset length extraFuel hcalldataSize hhead hheadBound
      htailBound hlength hpayloadBound
    simpa [bytesParamBindings, bytesLoaderStmts, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hexec

/-- The parameter-list lift: the whole emitted calldata-decoding block executes
to exactly the bindings the dispatcher's external ABI binder computes, for any
mixture of supported scalars and `bytes`. -/
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
              simp only [Option.bind_eq_bind, Option.some_bind, Option.some.injEq] at hbind
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
                simp [List.length_append]; omega]
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
mixture of supported scalars and `bytes` parameters (verity#2085).

Together with `interpretContract_correct_of_functions_generic_external` this is
the composition that admits `bytes` into external dispatch. -/
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
