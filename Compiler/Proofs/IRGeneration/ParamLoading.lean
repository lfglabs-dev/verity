import Compiler.CompilationModel.ParamLoading
import Compiler.Proofs.IRGeneration.SourceSemantics

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace ParamLoading

def applyBindingsToIRState (state : IRState) : List (String × Nat) → IRState
  | [] => state
  | (name, value) :: rest =>
      applyBindingsToIRState (state.setVar name value) rest

@[simp] theorem uint256_modulus_eq_evm :
    Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := by
  rfl

@[simp] theorem wordNormalize_eq_mod (n : Nat) :
    SourceSemantics.wordNormalize n = n % Compiler.Constants.evmModulus := by
  change n % Verity.Core.UINT256_MODULUS = n % Compiler.Constants.evmModulus
  rfl

private theorem foldl_add_eq (xs : List Nat) (init : Nat) :
    xs.foldl (· + ·) init = xs.foldl (· + ·) 0 + init := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x rest ih =>
      calc
        (x :: rest).foldl (· + ·) init
            = rest.foldl (· + ·) (init + x) := by simp [List.foldl]
        _ = rest.foldl (· + ·) 0 + (init + x) := ih (init + x)
        _ = rest.foldl (· + ·) 0 + x + init := by omega
        _ = rest.foldl (· + ·) x + init := by
              rw [ih x]
        _ = (x :: rest).foldl (· + ·) 0 + init := by simp [List.foldl]

theorem bindSupportedParams_some_length
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    params.length ≤ args.length := by
  induction params generalizing args bindings with
  | nil =>
      exact Nat.zero_le _
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [SourceSemantics.bindSupportedParams] at hbind
      | cons arg restArgs =>
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
              simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
          case some value =>
            cases hrest : SourceSemantics.bindSupportedParams rest restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              exact Nat.succ_le_succ (ih hrest)

theorem supportedParamHeadSize_eq_32
    {ty : ParamType} (hsupported : SupportedExternalScalarParamType ty) :
    paramHeadSize ty = 32 := by
  cases ty <;> simp [SupportedExternalScalarParamType] at hsupported <;>
    simp [paramHeadSize]

theorem supportedScalarHeadSize_eq
    (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty) :
    (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0 = 32 * params.length := by
  induction params with
  | nil =>
      simp
  | cons param rest ih =>
      have hparam : SupportedExternalScalarParamType param.ty := hsupported param (by simp)
      have hrest : ∀ next ∈ rest, SupportedExternalScalarParamType next.ty := by
        intro next hnext
        exact hsupported next (by simp [hnext])
      calc
        (List.map (fun p => paramHeadSize p.ty) (param :: rest)).foldl (· + ·) 0
            = paramHeadSize param.ty + (List.map (fun p => paramHeadSize p.ty) rest).foldl (· + ·) 0 := by
                simpa [Nat.add_comm] using
                  (foldl_add_eq (List.map (fun p => paramHeadSize p.ty) rest) (paramHeadSize param.ty))
        _ = 32 + (List.map (fun p => paramHeadSize p.ty) rest).foldl (· + ·) 0 := by
              rw [supportedParamHeadSize_eq_32 hparam]
        _ = 32 + 32 * rest.length := by
              rw [ih hrest]
        _ = 32 * (rest.length + 1) := by
              omega
        _ = 32 * (param :: rest).length := by
              simp

@[simp] theorem calldataloadWord_aligned
    (selector : Nat) (calldata : List Nat) (idx : Nat) :
    Compiler.Proofs.YulGeneration.calldataloadWord selector calldata (4 + 32 * idx) =
      calldata.getD idx 0 % Compiler.Constants.evmModulus := by
  have hlt : ¬ 4 + 32 * idx < 4 := by omega
  simp [Compiler.Proofs.YulGeneration.calldataloadWord, hlt]

private theorem getD_eq_of_drop_eq_cons
    {xs : List Nat} {idx arg : Nat} {rest : List Nat}
    (hdrop : xs.drop idx = arg :: rest) :
    xs.getD idx 0 = arg := by
  have hlookup : xs[idx]? = some arg := by
    simpa [hdrop, Nat.zero_add] using
      (List.getElem?_drop (xs := xs) (i := idx) (j := 0)).symm
  simp [List.getD, hlookup]

private theorem drop_succ_eq_of_drop_eq_cons
    {xs : List Nat} {idx arg : Nat} {rest : List Nat}
    (hdrop : xs.drop idx = arg :: rest) :
    xs.drop (idx + 1) = rest := by
  calc
    xs.drop (idx + 1) = (xs.drop idx).drop 1 := by
      simpa [Nat.add_comm] using
        (List.drop_drop (i := 1) (j := idx) (l := xs)).symm
    _ = rest := by simp [hdrop]

private theorem supportedExternalParamType_cases
    {ty : ParamType} (hsupported : SupportedExternalScalarParamType ty) :
    ty = .uint256 ∨ ty = .int256 ∨ ty = .uint8 ∨ ty = .uint16 ∨
      (∃ bits, ty = .uintN bits) ∨ (∃ bits, ty = .intN bits) ∨
      (∃ bytes, ty = .bytesN bytes) ∨
      ty = .address ∨ ty = .bytes32 ∨ ty = .bool := by
  cases ty <;> simp [SupportedExternalScalarParamType] at hsupported ⊢

private theorem execIRStmts_cons_of_execIRStmt_continue
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .continue next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      execIRStmts (rest.length + 1) next rest := by
  simp [execIRStmts, hstmt]

theorem execIRStmts_cons_of_execIRStmt_continue_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .continue next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      execIRStmts (rest.length + extraFuel + 1) next rest := by
  simp [execIRStmts, hstmt]

private theorem land_mod_evm_right (a b : Nat) :
    (a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus) =
      (a % Compiler.Constants.evmModulus) &&& b := by
  rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
  rw [← Nat.and_two_pow_sub_one_eq_mod b 256, ← Nat.land_assoc,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by
    rw [Nat.land_comm]
    exact Nat.and_lt_two_pow b (Nat.mod_lt a (by positivity)))

private theorem exec_genScalarLoad_supported_then_word_passthrough
    (state : IRState) (rest : List YulStmt) (name : String) (ty : ParamType) (idx value extraFuel : Nat)
    (hpassthrough : ty = .uint256 ∨ ty = .int256 ∨ ty = .bytes32)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx)).length +
        rest.length + extraFuel + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + extraFuel + 1) (state.setVar name value) rest := by
  rcases hpassthrough with rfl | rfl | rfl <;> (
    have hstmt :
        execIRStmt (rest.length + extraFuel + 1) state
          (YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)])) =
          .continue (state.setVar name value) := by
        have hvalue : value = state.calldata.getD idx 0 % Compiler.Constants.evmModulus := by
          simpa [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
            Verity.Core.UINT256_MODULUS, uint256_modulus_eq_evm] using hdecode.symm
        cases hvalue
        simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
          Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
          Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, calldataloadWord_aligned]
    simpa [genScalarLoad, genScalarCleanLoad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state (state.setVar name value)
        (YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)])) rest hstmt
  )

/-- A one-statement `revert(0, 0)` block reverts at any fuel. -/
private theorem execIRStmts_revert_zero (fuel : Nat) (state : IRState) :
    execIRStmts fuel state
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] =
      .revert state := by
  rcases fuel with _ | _ | fuel <;> simp [execIRStmts, execIRStmt]

/-- An `if cond { revert(0, 0) }` guard continues when `cond` is zero and
reverts otherwise. -/
private theorem execIRStmt_revert_guard (fuel : Nat) (state : IRState) (cond : YulExpr)
    (c : Nat) (hcond : evalIRExpr state cond = some c) :
    execIRStmt (fuel + 1) state (YulStmt.if_ cond
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      if c = 0 then .continue state else .revert state := by
  by_cases hc : c = 0 <;> simp [execIRStmt, hcond, hc, execIRStmts_revert_zero]

/-- Whatever its condition, an `if cond { revert(0, 0) }` guard either continues
on the same state or reverts. -/
private theorem execIRStmt_revert_guard_cases (fuel : Nat) (state : IRState) (cond : YulExpr) :
    execIRStmt (fuel + 1) state (YulStmt.if_ cond
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue state ∨
    execIRStmt (fuel + 1) state (YulStmt.if_ cond
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .revert state := by
  cases hcond : evalIRExpr state cond with
  | none => exact Or.inr (by simp [execIRStmt, hcond])
  | some c =>
      rw [execIRStmt_revert_guard fuel state cond c hcond]
      by_cases hc : c = 0 <;> simp [hc]

/-- The validator condition `iszero(eq(name, calldataload(4 + 32 * idx)))`
is zero exactly when `name` holds the raw head word. -/
private theorem evalIRExpr_scalarValidationCond
    (state : IRState) (name : String) (idx clean : Nat)
    (hclean : clean < Compiler.Constants.evmModulus) :
    evalIRExpr (state.setVar name clean)
      (YulExpr.call "iszero" [YulExpr.call "eq" [YulExpr.ident name,
        YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)]]]) =
      some (if clean = state.calldata.getD idx 0 % Compiler.Constants.evmModulus
        then 0 else 1) := by
  have hsize : EvmYul.UInt256.size = Compiler.Constants.evmModulus := rfl
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : clean = state.calldata[idx]?.getD 0 % Compiler.Constants.evmModulus <;>
    simp [evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Compiler.Proofs.YulGeneration.Backends.evalPureBuiltinViaEvmYulLean,
      calldataloadWord_aligned, hsize, h, Nat.mod_eq_of_lt hclean]

/-- A validated scalar load binds the cleaned word, then continues past its
guard when the word was clean and reverts otherwise. -/
private theorem exec_validatedScalarLoad
    (state : IRState) (rest : List YulStmt) (name : String) (cleanExpr : YulExpr)
    (idx clean fuel : Nat)
    (hlet : ∀ fuel, execIRStmt (fuel + 1) state (YulStmt.let_ name cleanExpr) =
      .continue (state.setVar name clean))
    (hclean : clean < Compiler.Constants.evmModulus) :
    execIRStmts (fuel + 3) state (YulStmt.let_ name cleanExpr ::
        scalarValidationGuard name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)]) ::
        rest) =
      if clean = state.calldata.getD idx 0 % Compiler.Constants.evmModulus then
        execIRStmts (fuel + 1) (state.setVar name clean) rest
      else .revert (state.setVar name clean) := by
  have hguard := execIRStmt_revert_guard fuel (state.setVar name clean) _ _
    (evalIRExpr_scalarValidationCond state name idx clean hclean)
  have hlet' := hlet (fuel + 1)
  by_cases h : clean = state.calldata.getD idx 0 % Compiler.Constants.evmModulus <;>
    simp_all [execIRStmts, scalarValidationGuard]

/-- The shape of a validated scalar load: `genScalarLoad` binds `clean`, the
type's cleanup of the head word, then guards it against the raw word; the
source decoder accepts exactly when the cleanup is the identity. -/
private def ValidatedScalarLoad (state : IRState) (name : String) (ty : ParamType)
    (idx : Nat) : Prop :=
  ∃ cleanExpr clean,
    genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx) =
      [YulStmt.let_ name cleanExpr,
        scalarValidationGuard name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)])] ∧
    (∀ fuel, execIRStmt (fuel + 1) state (YulStmt.let_ name cleanExpr) =
      .continue (state.setVar name clean)) ∧
    clean < Compiler.Constants.evmModulus ∧
    SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) =
      DynamicAbi.validatedWord clean (state.calldata.getD idx 0 % Compiler.Constants.evmModulus)

private theorem and_mod_evm_lt (a b : Nat) :
    a % Compiler.Constants.evmModulus &&& b < Compiler.Constants.evmModulus :=
  Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt a (by unfold Compiler.Constants.evmModulus; positivity))

private theorem validatedScalarLoad_uint8 (state : IRState) (name : String) (idx : Nat) :
    ValidatedScalarLoad state name .uint8 idx := by
  refine ⟨_, state.calldata.getD idx 0 % Compiler.Constants.evmModulus &&& 255, rfl,
    fun fuel => ?_, and_mod_evm_lt _ _, ?_⟩
  · have h255 : (255 : Nat) % Compiler.Constants.evmModulus = 255 := by
      norm_num [Compiler.Constants.evmModulus]
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      calldataloadWord_aligned, h255]
  · simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.uint8Modulus]

private theorem validatedScalarLoad_uint16 (state : IRState) (name : String) (idx : Nat) :
    ValidatedScalarLoad state name .uint16 idx := by
  refine ⟨_, state.calldata.getD idx 0 % Compiler.Constants.evmModulus &&& 65535, rfl,
    fun fuel => ?_, and_mod_evm_lt _ _, ?_⟩
  · have h65535 : (65535 : Nat) % Compiler.Constants.evmModulus = 65535 := by
      norm_num [Compiler.Constants.evmModulus]
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      calldataloadWord_aligned, h65535]
  · simp [SourceSemantics.decodeSupportedParamWord]

private theorem validatedScalarLoad_uintN (state : IRState) (name : String) (bits idx : Nat) :
    ValidatedScalarLoad state name (.uintN bits) idx := by
  refine ⟨_, state.calldata.getD idx 0 % Compiler.Constants.evmModulus &&& (2 ^ bits - 1), rfl,
    fun fuel => ?_, and_mod_evm_lt _ _, ?_⟩
  · simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      calldataloadWord_aligned, land_mod_evm_right]
  · simp [SourceSemantics.decodeSupportedParamWord]

private theorem validatedScalarLoad_bytesN (state : IRState) (name : String) (bytes idx : Nat) :
    ValidatedScalarLoad state name (.bytesN bytes) idx := by
  refine ⟨_, state.calldata.getD idx 0 % Compiler.Constants.evmModulus &&&
      ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))), rfl,
    fun fuel => ?_, and_mod_evm_lt _ _, ?_⟩
  · simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      calldataloadWord_aligned, land_mod_evm_right]
  · simp [SourceSemantics.decodeSupportedParamWord]

private theorem validatedScalarLoad_address (state : IRState) (name : String) (idx : Nat) :
    ValidatedScalarLoad state name .address idx := by
  refine ⟨_, state.calldata.getD idx 0 % Compiler.Constants.evmModulus &&&
      Compiler.Constants.addressMask, rfl, fun fuel => ?_, and_mod_evm_lt _ _, ?_⟩
  · have hmask : Compiler.Constants.addressMask % Compiler.Constants.evmModulus =
        Compiler.Constants.addressMask :=
      Nat.mod_eq_of_lt (by dsimp [Compiler.Constants.addressMask, Compiler.Constants.evmModulus]; omega)
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      calldataloadWord_aligned, hmask]
  · simp [SourceSemantics.decodeSupportedParamWord]

private theorem validatedScalarLoad_intN (state : IRState) (name : String) (bits idx : Nat) :
    ValidatedScalarLoad state name (.intN bits) idx := by
  refine ⟨_, (Verity.Core.Uint256.signextend (Verity.Core.Uint256.ofNat (bits / 8 - 1))
      (Verity.Core.Uint256.ofNat (state.calldata.getD idx 0 %
        Compiler.Constants.evmModulus))).val, rfl, fun fuel => ?_, Verity.Core.Uint256.isLt _, ?_⟩
  · have hbyteIdx :
        Verity.Core.Uint256.ofNat ((bits / 8 - 1) % Compiler.Constants.evmModulus) =
          Verity.Core.Uint256.ofNat (bits / 8 - 1) := by
      apply Verity.Core.Uint256.ext
      simp [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS, Nat.mod_mod]
    simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      calldataloadWord_aligned, hbyteIdx]
  · simp [SourceSemantics.decodeSupportedParamWord]

private theorem validatedScalarLoad_bool (state : IRState) (name : String) (idx : Nat) :
    ValidatedScalarLoad state name .bool idx := by
  refine ⟨_, if state.calldata.getD idx 0 % Compiler.Constants.evmModulus = 0 then 0 else 1, rfl,
    fun fuel => ?_, by split <;> decide, ?_⟩
  · simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, calldataloadWord_aligned]
    split <;> simp_all
  · simp [SourceSemantics.decodeSupportedParamWord]

/-- Every supported scalar type narrower than a full word is loaded by a
validated scalar load. -/
private theorem validatedScalarLoad_of_supported
    (state : IRState) (name : String) (ty : ParamType) (idx : Nat)
    (hsupported : SupportedExternalScalarParamType ty)
    (hnarrow : ¬ (ty = .uint256 ∨ ty = .int256 ∨ ty = .bytes32)) :
    ValidatedScalarLoad state name ty idx := by
  rcases supportedExternalParamType_cases hsupported with
    rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl | rfl | rfl <;>
    simp at hnarrow
  · exact validatedScalarLoad_uint8 state name idx
  · exact validatedScalarLoad_uint16 state name idx
  · exact validatedScalarLoad_uintN state name _ idx
  · exact validatedScalarLoad_intN state name _ idx
  · exact validatedScalarLoad_bytesN state name _ idx
  · exact validatedScalarLoad_address state name idx
  · exact validatedScalarLoad_bool state name idx

private theorem exec_validatedScalarLoad_then
    (state : IRState) (rest : List YulStmt) (name : String) (ty : ParamType)
    (idx value extraFuel : Nat) (hload : ValidatedScalarLoad state name ty idx)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) =
      some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty
        (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx) ++
        rest) =
      execIRStmts (rest.length + extraFuel + 1) (state.setVar name value) rest := by
  obtain ⟨cleanExpr, clean, hshape, hlet, hlt, hdec⟩ := hload
  rw [hdec, DynamicAbi.validatedWord_eq_some_iff] at hdecode
  obtain ⟨hclean, rfl⟩ := hdecode
  have hexec := exec_validatedScalarLoad state rest name cleanExpr idx clean
    (rest.length + extraFuel) hlet hlt
  rw [if_pos hclean] at hexec
  rw [hshape]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hexec

private theorem exec_validatedScalarLoad_revert
    (state : IRState) (rest : List YulStmt) (name : String) (ty : ParamType)
    (idx extraFuel : Nat) (hload : ValidatedScalarLoad state name ty idx)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) = none) :
    ∃ reverted, execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty
        (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx) ++
        rest) = .revert reverted := by
  obtain ⟨cleanExpr, clean, hshape, hlet, hlt, hdec⟩ := hload
  rw [hdec, DynamicAbi.validatedWord_eq_none_iff] at hdecode
  have hexec := exec_validatedScalarLoad state rest name cleanExpr idx clean
    (rest.length + extraFuel) hlet hlt
  rw [if_neg hdecode] at hexec
  rw [hshape]
  exact ⟨_, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hexec⟩

theorem exec_genScalarLoad_supported_then
    (state : IRState) (rest : List YulStmt) (name : String) (ty : ParamType) (idx value extraFuel : Nat)
    (hsupported : SupportedExternalScalarParamType ty)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx)).length +
        rest.length + extraFuel + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + extraFuel + 1) (state.setVar name value) rest := by
  by_cases hwide : ty = .uint256 ∨ ty = .int256 ∨ ty = .bytes32
  · exact exec_genScalarLoad_supported_then_word_passthrough state rest name ty idx value
      extraFuel hwide hdecode
  · exact exec_validatedScalarLoad_then state rest name ty idx value extraFuel
      (validatedScalarLoad_of_supported state name ty idx hsupported hwide) hdecode

/-- A scalar head word the source decoder rejects (a dirty encoding of a narrow
type) makes the generated load revert. -/
theorem exec_genScalarLoad_supported_revert
    (state : IRState) (rest : List YulStmt) (name : String) (ty : ParamType)
    (idx extraFuel : Nat) (hsupported : SupportedExternalScalarParamType ty)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) = none) :
    ∃ reverted, execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty
        (4 + 32 * idx)).length + rest.length + extraFuel + 1) state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx) ++
        rest) = .revert reverted := by
  by_cases hwide : ty = .uint256 ∨ ty = .int256 ∨ ty = .bytes32
  · rcases hwide with rfl | rfl | rfl <;>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  · exact exec_validatedScalarLoad_revert state rest name ty idx extraFuel
      (validatedScalarLoad_of_supported state name ty idx hsupported hwide) hdecode

theorem bindSupportedParams_names
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    bindings.map Prod.fst = params.map Param.name := by
  induction params generalizing args bindings with
  | nil =>
      simp [SourceSemantics.bindSupportedParams] at hbind
      cases hbind
      rfl
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [SourceSemantics.bindSupportedParams] at hbind
      | cons arg restArgs =>
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
              simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
          case some value =>
            cases hrest : SourceSemantics.bindSupportedParams rest restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              simp [ih hrest]

theorem bindSupportedParams_names_nodup
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hparams : (params.map Param.name).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    (bindings.map Prod.fst).Nodup := by
  rw [bindSupportedParams_names hbind]
  exact hparams

private theorem exec_minInputSizeCheck_supported_noop
    (fuel : Nat) (state : IRState) (params : List Param)
    (_hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hlen : params.length ≤ state.calldata.length) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.if_ (YulExpr.call "lt"
        [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue state := by
  have hrhs_lt_modulus : 4 + 32 * params.length < Compiler.Constants.evmModulus := by
    omega
  have hnotlt : ¬ 4 + state.calldata.length * 32 < 4 + 32 * params.length := by
    omega
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Nat.mod_eq_of_lt hcalldataSizeFits, Nat.mod_eq_of_lt hrhs_lt_modulus, hnotlt]

private theorem exec_genParamLoadBodyFrom_supported_then_bind_cons
    {param : Param} {restParams : List Param} {calldata : List Nat} {idx : Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams (param :: restParams) (calldata.drop idx) =
      some bindings) :
    ∃ value restBindings, bindings = (param.name, value) :: restBindings ∧
      SourceSemantics.decodeSupportedParamWord param.ty (calldata.getD idx 0) = some value ∧
      SourceSemantics.bindSupportedParams restParams (calldata.drop (idx + 1)) =
        some restBindings := by
  cases hdrop : calldata.drop idx with
  | nil => simp [SourceSemantics.bindSupportedParams, hdrop] at hbind
  | cons arg restArgs =>
      cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
          simp [SourceSemantics.bindSupportedParams, hdrop, hdecode] at hbind
      case some value =>
        cases hrest : SourceSemantics.bindSupportedParams restParams restArgs <;>
            simp [hrest] at hbind
        case some restBindings =>
          subst hbind
          refine ⟨value, restBindings, rfl, ?_, ?_⟩
          · rw [getD_eq_of_drop_eq_cons hdrop]
            exact hdecode
          · rw [drop_succ_eq_of_drop_eq_cons hdrop]
            exact hrest

private theorem exec_genParamLoadBodyFrom_supported_then_cons_eq
    (headSize baseOffset idx : Nat) (param : Param) (restParams : List Param)
    (hparam : SupportedExternalScalarParamType param.ty) :
    genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset (param :: restParams) (4 + 32 * idx) =
      genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) param.name param.ty
          (4 + 32 * idx) ++
        genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) headSize baseOffset restParams
          (4 + 32 * (idx + 1)) := by
  have hoff : 4 + 32 * idx + 32 = 4 + 32 * (idx + 1) := by omega
  rcases supportedExternalParamType_cases hparam with
    hty | hty | hty | hty | ⟨_, hty⟩ | ⟨_, hty⟩ | ⟨_, hty⟩ | hty | hty | hty <;>
  simp [Compiler.CompilationModel.genParamLoadBodyFrom,
    Compiler.CompilationModel.genSingleParamLoad, paramHeadSize, hty, hoff]

theorem exec_genParamLoadBodyFrom_supported_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (params : List Param) (idx : Nat)
    (bindings : List (String × Nat)) (extraFuel : Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hbind : SourceSemantics.bindSupportedParams params (state.calldata.drop idx) = some bindings) :
    execIRStmts ((genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx)).length +
        rest.length + extraFuel + 1)
      state
      (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + extraFuel + 1) (applyBindingsToIRState state bindings) rest := by
  induction params generalizing state idx bindings rest headSize baseOffset with
  | nil =>
      cases (by simpa [SourceSemantics.bindSupportedParams] using hbind : [] = bindings)
      simp [Compiler.CompilationModel.genParamLoadBodyFrom, applyBindingsToIRState]
  | cons param restParams ih =>
      obtain ⟨value, restBindings, rfl, hdecode, hrest⟩ :=
        exec_genParamLoadBodyFrom_supported_then_bind_cons hbind
      have hparam := hsupported param (by simp)
      have hih := ih (state.setVar param.name value) rest headSize baseOffset (idx + 1)
        restBindings (fun next hnext => hsupported next (by simp [hnext]))
        (by simpa [IRState.setVar] using hrest)
      rw [← List.length_append] at hih
      rw [exec_genParamLoadBodyFrom_supported_then_cons_eq _ _ _ _ _ hparam]
      simpa only [List.length_append, List.append_assoc, Nat.add_assoc, applyBindingsToIRState]
        using (exec_genScalarLoad_supported_then state _ param.name param.ty idx value
          extraFuel hparam hdecode).trans hih

theorem exec_genParamLoads_supported
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    execIRStmts ((genParamLoads params).length + 1) state (genParamLoads params) =
      .continue (applyBindingsToIRState state bindings) := by
  have hlen : params.length ≤ state.calldata.length := bindSupportedParams_some_length hbind
  let body :=
    genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4
  have hguard :
      execIRStmt (body.length + 1) state
        (YulStmt.if_ (YulExpr.call "lt"
          [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
          [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
        .continue state :=
    exec_minInputSizeCheck_supported_noop (fuel := body.length) state params hsupported
      hcalldataSizeFits hlen
  have hbody :=
    exec_genParamLoadBodyFrom_supported_then (state := state) (rest := []) (headSize := 32 * params.length)
      (baseOffset := 4) (params := params) (idx := 0) (bindings := bindings) (extraFuel := 0) hsupported
      (by simpa using hbind)
  have hstep :=
    execIRStmts_cons_of_execIRStmt_continue state state
      (YulStmt.if_ (YulExpr.call "lt"
        [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])])
      body hguard
  have hbody' :
      execIRStmts (body.length + 1) state body =
        .continue (applyBindingsToIRState state bindings) := by
    simpa [body, execIRStmts] using hbody
  simpa [Compiler.CompilationModel.genParamLoads, Compiler.CompilationModel.genParamLoadsFrom,
    body, supportedScalarHeadSize_eq params hsupported] using hstep.trans hbody'

private theorem exec_genParamLoads_supported_then_extraFuel_guard
    (state : IRState) (params : List Param) (rest : List YulStmt) (extraFuel : Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hlen : params.length ≤ state.calldata.length) :
    execIRStmts ((genParamLoads params).length + rest.length + extraFuel + 1) state
      (genParamLoads params ++ rest) =
      execIRStmts ((genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4 ++ rest).length +
          extraFuel + 1) state
        (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
          (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4 ++ rest) := by
  let body :=
    genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4
  have hguard := exec_minInputSizeCheck_supported_noop
    (fuel := body.length + rest.length + extraFuel) state params hsupported hcalldataSizeFits hlen
  have hstep :=
    execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state
      (YulStmt.if_ (YulExpr.call "lt"
        [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
        [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])])
      (body ++ rest) (by simpa [body] using hguard)
  have hfuel' : extraFuel + (rest.length + (2 + body.length)) =
      extraFuel + (rest.length + (1 + (1 + body.length))) := by omega
  simpa [Compiler.CompilationModel.genParamLoads, Compiler.CompilationModel.genParamLoadsFrom,
    body, List.length_append, supportedScalarHeadSize_eq params hsupported,
    hfuel', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

theorem exec_genParamLoads_supported_then_extraFuel
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (rest : List YulStmt) (extraFuel : Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    execIRStmts ((genParamLoads params).length + rest.length + extraFuel + 1) state
      (genParamLoads params ++ rest) =
      execIRStmts (rest.length + extraFuel + 1) (applyBindingsToIRState state bindings) rest := by
  have hbody :=
    exec_genParamLoadBodyFrom_supported_then (state := state) (rest := rest)
      (headSize := 32 * params.length) (baseOffset := 4) (params := params) (idx := 0)
      (bindings := bindings) (extraFuel := extraFuel) hsupported (by simpa using hbind)
  rw [← List.length_append] at hbody
  exact (exec_genParamLoads_supported_then_extraFuel_guard state params rest extraFuel hsupported
    hcalldataSizeFits (bindSupportedParams_some_length hbind)).trans (by simpa using hbody)

theorem exec_genParamLoads_supported_then
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (rest : List YulStmt)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    execIRStmts ((genParamLoads params).length + rest.length + 1) state (genParamLoads params ++ rest) =
      execIRStmts (rest.length + 1) (applyBindingsToIRState state bindings) rest := by
  simpa using exec_genParamLoads_supported_then_extraFuel
    (state := state) (params := params) (bindings := bindings) (rest := rest)
    (extraFuel := 0) hsupported hcalldataSizeFits hbind

/-- Where scalar binding fails with enough arguments, it fails at the head
word or, after a clean head, in the tail. -/
private theorem bindSupportedParams_cons_none
    {param : Param} {restParams : List Param} {calldata : List Nat} {idx : Nat}
    (hlen : idx + (param :: restParams).length ≤ calldata.length)
    (hnone : SourceSemantics.bindSupportedParams (param :: restParams) (calldata.drop idx) =
      none) :
    SourceSemantics.decodeSupportedParamWord param.ty (calldata.getD idx 0) = none ∨
      ∃ value, SourceSemantics.decodeSupportedParamWord param.ty (calldata.getD idx 0) =
          some value ∧
        SourceSemantics.bindSupportedParams restParams (calldata.drop (idx + 1)) = none := by
  cases hdrop : calldata.drop idx with
  | nil =>
      have := congrArg List.length hdrop
      simp at this hlen
      omega
  | cons arg restArgs =>
      rw [getD_eq_of_drop_eq_cons hdrop, drop_succ_eq_of_drop_eq_cons hdrop]
      rw [hdrop] at hnone
      cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg with
      | none => exact Or.inl rfl
      | some value =>
          refine Or.inr ⟨value, rfl, ?_⟩
          cases hrest : SourceSemantics.bindSupportedParams restParams restArgs <;>
            simp_all [SourceSemantics.bindSupportedParams]

/-- When the source binder rejects the arguments (a dirty head word), the
generated parameter-load body reverts. -/
theorem exec_genParamLoadBodyFrom_supported_revert
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (params : List Param) (idx extraFuel : Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hlen : idx + params.length ≤ state.calldata.length)
    (hnone : SourceSemantics.bindSupportedParams params (state.calldata.drop idx) = none) :
    ∃ reverted, execIRStmts ((genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx)).length +
        rest.length + extraFuel + 1) state
      (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx) ++ rest) =
      .revert reverted := by
  induction params generalizing state idx rest with
  | nil => simp [SourceSemantics.bindSupportedParams] at hnone
  | cons param restParams ih =>
      have hparam := hsupported param (by simp)
      rw [exec_genParamLoadBodyFrom_supported_then_cons_eq _ _ _ _ _ hparam]
      rcases bindSupportedParams_cons_none hlen hnone with hdecode | ⟨value, hdecode, hrest⟩
      · simpa only [List.length_append, List.append_assoc, Nat.add_assoc] using
          exec_genScalarLoad_supported_revert state (_ ++ rest) param.name param.ty idx
            extraFuel hparam hdecode
      · obtain ⟨reverted, hih⟩ := ih (state.setVar param.name value) rest (idx + 1)
          (fun next hnext => hsupported next (by simp [hnext]))
          (by simp at hlen ⊢; omega) (by simpa using hrest)
        rw [← List.length_append] at hih
        exact ⟨reverted, by simpa only [List.length_append, List.append_assoc, Nat.add_assoc] using
          (exec_genScalarLoad_supported_then state _ param.name param.ty idx value
            extraFuel hparam hdecode).trans hih⟩

private theorem execIRStmts_cons_of_execIRStmt_revert_extraFuel
    (extraFuel : Nat) (state reverted : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .revert reverted) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) = .revert reverted := by
  simp [execIRStmts, hstmt]

/-- When the source binder rejects arguments that cover every parameter, the
generated parameter loads revert (the dirty word's validator, or the input-size
guard, fires first). -/
theorem exec_genParamLoads_supported_revert
    (state : IRState) (params : List Param) (rest : List YulStmt) (extraFuel : Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hlen : params.length ≤ state.calldata.length)
    (hnone : SourceSemantics.bindSupportedParams params state.calldata = none) :
    ∃ reverted, execIRStmts ((genParamLoads params).length + rest.length + extraFuel + 1) state
      (genParamLoads params ++ rest) = .revert reverted := by
  let body := genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
    (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4
  have hshape : genParamLoads params = YulStmt.if_ (YulExpr.call "lt"
      [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] :: body := by
    simp [genParamLoads, genParamLoadsFrom, body, supportedScalarHeadSize_eq params hsupported]
  rw [hshape, show ∀ guard : YulStmt, (guard :: body).length + rest.length + extraFuel + 1 =
    (body ++ rest).length + extraFuel + 2 from fun _ => by simp; omega, List.cons_append]
  rcases execIRStmt_revert_guard_cases ((body ++ rest).length + extraFuel) state
      (YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
    with hguard | hguard
  · obtain ⟨reverted, hbody⟩ := exec_genParamLoadBodyFrom_supported_revert state rest
      (32 * params.length) 4 params 0 extraFuel hsupported (by simpa using hlen)
      (by simpa using hnone)
    refine ⟨reverted, ?_⟩
    rw [execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state _ _ hguard]
    simpa [body, List.length_append, Nat.add_assoc] using hbody
  · exact ⟨state, execIRStmts_cons_of_execIRStmt_revert_extraFuel extraFuel state state _ _ hguard⟩

end ParamLoading

end Compiler.Proofs.IRGeneration
