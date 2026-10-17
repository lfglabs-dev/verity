import Compiler.Proofs.IRGeneration.PhysicalCustomErrorScalarExecution

namespace Compiler.Proofs.IRGeneration.CustomErrorScalarEncoding
open Compiler.Yul Compiler.CompilationModel

theorem evaluate_mask (state : IRState) (expr : YulExpr) (value bits : Nat)
    (evaluated : evalIRExpr state expr = some value) (width : bits ≤ 256)
    (canonical : value < 2^bits) :
    evalIRExpr state (.call "and" [expr, .lit (2^bits - 1)]) = some value := by
  have power : 2^bits ≤ Compiler.Constants.evmModulus := by
    change 2^bits ≤ 2^256
    exact Nat.pow_le_pow_right (by decide) width
  have valueBound : value < Compiler.Constants.evmModulus := lt_of_lt_of_le canonical power
  have maskBound : 2^bits - 1 < Compiler.Constants.evmModulus := by
    have positive : 0 < 2^bits := Nat.pow_pos (by decide)
    omega
  have result := FunctionBody.evalIRExpr_and_of_eval (state := state)
    (lhs := expr) (rhs := .lit (2^bits - 1)) (a := value) (b := 2^bits - 1)
    evaluated (by simp [evalIRExpr])
  simpa only [Nat.mod_eq_of_lt valueBound, Nat.mod_eq_of_lt maskBound,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt canonical] using result

theorem evaluate_bool (state : IRState) (expr : YulExpr) (value : Nat)
    (evaluated : evalIRExpr state expr = some value) (canonical : value ≤ 1) :
    evalIRExpr state (yulToBool expr) = some value := by
  have one : 1 % Compiler.Constants.evmModulus = 1 := by decide
  have bounded : value < Compiler.Constants.evmModulus := by
    have bound : 1 < Compiler.Constants.evmModulus := by decide
    omega
  have cases : value = 0 ∨ value = 1 := by omega
  rcases cases with rfl | rfl <;>
    simp [yulToBool, evalIRExpr, evalIRCall, evalIRExprs, evaluated, one,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

/-- Supported canonical Source scalar values survive the actual compiler
encoder, rather than assuming an encoded-value oracle. -/
theorem evaluate_encoding (state : IRState) (name : String) (ty : ParamType)
    (expr encoded : YulExpr) (value : Nat) (typeName : String)
    (supported : Denote.errorScalarType ty = some typeName)
    (canonical : Denote.errorScalarValueValid ty value = true)
    (evaluated : evalIRExpr state expr = some value)
    (encoding : encodeStaticCustomErrorArg name ty expr = .ok encoded) :
    evalIRExpr state encoded = some value := by
  cases ty <;> simp_all [Denote.errorScalarType, Denote.errorScalarValueValid,
    encodeStaticCustomErrorArg, pure, Except.pure]
  all_goals subst encoded
  · simpa using evaluate_mask state expr value 8 evaluated (by omega) canonical
  · simpa using evaluate_mask state expr value 16 evaluated (by omega) canonical
  · exact evaluate_mask state expr value _ evaluated (by omega) canonical
  · simpa [Compiler.Constants.addressMask, evalIRExpr, evalIRCall, evalIRExprs] using
      evaluate_mask state expr value 160 evaluated (by omega) canonical
  · exact evaluate_bool state expr value evaluated canonical

/-- Atomic IR arguments whose referenced variable is outside the compiler's
custom-error scratch bindings. Compound expressions need the recursive frame law. -/
def ScratchIndependent (expr : YulExpr) : Prop :=
  (∃ value, expr = .lit value) ∨ (∃ value, expr = .hex value) ∨
  (∃ name, expr = .ident name ∧ name ≠ "__err_ptr" ∧ name ≠ "__err_hash" ∧
    name ≠ "__err_selector" ∧ name ≠ "__err_tail") ∨
  (∃ func, expr = .call func [])

private theorem stores_vars (state : IRState) (writes : List (Nat × Nat)) :
    (PhysicalRevertWrites.applyStores state writes).vars = state.vars := by
  induction writes generalizing state with
  | nil => rfl
  | cons pair tail ih => exact ih _

private theorem scratch_nullary (state : IRState) (writes : List (Nat × Nat))
    (func : String) :
    evalIRCall (PhysicalRevertWrites.applyStores state writes) func [] =
      evalIRCall state func [] := by
  induction writes generalizing state with
  | nil => rfl
  | cons pair tail ih =>
      rw [PhysicalRevertWrites.applyStores, ih]
      simp [evalIRCall, evalIRExprs, IRState.writePhysicalMemoryValue,
        IRState.installPhysicalMemory]

private theorem getVar_write (state : IRState) (offset value : Nat) (name : String) :
    (state.writePhysicalMemoryValue offset value).getVar name = state.getVar name := rfl

private theorem getVar_stores (state : IRState) (writes : List (Nat × Nat)) (name : String) :
    (PhysicalRevertWrites.applyStores state writes).getVar name = state.getVar name := by
  unfold IRState.getVar
  rw [stores_vars]

private theorem nullary_setVar (state : IRState) (name : String) (value : Nat) (func : String) :
    evalIRCall (state.setVar name value) func [] = evalIRCall state func [] := by
  simp [evalIRCall, evalIRExprs, IRState.setVar]

private theorem nullary_write (state : IRState) (offset value : Nat) (func : String) :
    evalIRCall (state.writePhysicalMemoryValue offset value) func [] = evalIRCall state func [] := by
  simp [evalIRCall, evalIRExprs, IRState.writePhysicalMemoryValue, IRState.installPhysicalMemory]

theorem argument_frame (state : IRState) (bytes : List UInt8) (expr : YulExpr)
    (independent : ScratchIndependent expr) :
    evalIRExpr
      (PhysicalCustomErrorScalarExecution.argumentState
        (PhysicalCustomErrorExecution.hashedState state bytes)
        (SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length)) expr =
      evalIRExpr state expr := by
  rcases independent with ⟨value, rfl⟩ | ⟨value, rfl⟩ |
    ⟨name, rfl, ptr, hash, selector, tail⟩ | ⟨func, rfl⟩
  · simp [evalIRExpr]
  · simp [evalIRExpr]
  · simp only [evalIRExpr, PhysicalCustomErrorScalarExecution.argumentState,
      PhysicalCustomErrorExecution.hashedState]
    rw [FunctionBody.getVar_setVar_ne _ _ _ _ tail, getVar_write,
      FunctionBody.getVar_setVar_ne _ _ _ _ selector,
      FunctionBody.getVar_setVar_ne _ _ _ _ hash, getVar_stores,
      FunctionBody.getVar_setVar_ne _ _ _ _ ptr]
  · simp only [evalIRExpr, PhysicalCustomErrorScalarExecution.argumentState,
      PhysicalCustomErrorExecution.hashedState]
    rw [nullary_setVar, nullary_write, nullary_setVar, nullary_setVar,
      scratch_nullary, nullary_setVar]

open PhysicalCustomErrorScalarExecution PhysicalCustomErrorExecution

theorem compiled_atomic_source_bytes (source : DynamicDataSource) (definition : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (params : definition.params = [ty]) (scalar : staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (state : IRState) (value extra : Nat)
    (fields : List Field) (runtime : SourceSemantics.RuntimeState) (typeName : String)
    (evaluated : SourceSemantics.evalExprList fields runtime [srcExpr] = some [value])
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (supported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr state argExpr = some value)
    (independent : ScratchIndependent argExpr) :
    ∃ out final data, revertWithCustomError source definition [srcExpr] [argExpr] = .ok out ∧
      execIRStmts ((signaturePrefix (bytesFromString (errorSignature definition))).length + extra + 8)
        state out = .revert final ∧ final.revertBytes = some data ∧
      SourceSemantics.typedErrorRevertResult fields runtime definition.name [srcExpr] =
        .revertWithData data := by
  apply compiled_scalar_source_bytes source definition ty srcExpr argExpr encoded params scalar
    encoding state value extra fields runtime typeName evaluated resolved canonical supported extent
  apply evaluate_encoding _ definition.name ty argExpr encoded value typeName supported canonical
  · rw [argument_frame state (bytesFromString (errorSignature definition)) argExpr independent]
    exact argument
  · exact encoding

end Compiler.Proofs.IRGeneration.CustomErrorScalarEncoding
