import Compiler.Proofs.IRGeneration.ImportedAbiWordBinding
import Compiler.SolidityImport.AbiRootLowering

namespace Compiler.Proofs.IRGeneration.ImportedAbiTupleHead
open Compiler.CompilationModel Denote

/-- Below the sign bit, the signed interpretation is the original natural. -/
theorem signed_small (value : Nat) (small : value < Verity.Core.Int256.signBit) :
    (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat value) : Int) = (value : Int) := by
  have bound : value < Verity.Core.Uint256.modulus :=
    lt_trans small Verity.Core.Int256.signBit_lt_modulus
  change Verity.Core.Int256.toInt _ = _
  simp [Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt bound, small]

/-- Actual signed remaining-length guard, derived from natural input bounds. -/
theorem remaining_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (pointer : Expr) (base required : Nat)
    (resolved : evalExpr oracle fields state pointer = some base)
    (available : base + required ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit) :
    evalExpr oracle fields state
      (.logicalNot (.slt (.sub .calldatasize pointer) (.literal required))) = some 1 := by
  have baseLe : base ≤ state.world.calldataSize.val := by omega
  have wordBound : state.world.calldataSize.val < Verity.Core.Uint256.modulus :=
    lt_trans sizeBound Verity.Core.Int256.signBit_lt_modulus
  have difference : state.world.calldataSize.val - base < Verity.Core.Int256.signBit := by omega
  have requiredBound : required < Verity.Core.Int256.signBit := by omega
  have subtract := SolidityImport.sub_word wordBound baseLe
  have requiredWord : required < Verity.Core.Uint256.modulus :=
    lt_trans requiredBound Verity.Core.Int256.signBit_lt_modulus
  simp [evalExpr, resolved, wordNormalize, Nat.mod_eq_of_lt requiredWord, subtract,
    signed_small _ difference, signed_small _ requiredBound, boolWord]
  omega

/-- A successful real ABI guard preserves the complete state before its tail. -/
theorem guard_cons (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (condition : Expr) (rest : List Stmt)
    (resolved : evalExpr oracle fields state condition = some 1) :
    execStmtList oracle fields state (SolidityImport.AbiLowering.guard condition :: rest) =
      execStmtList oracle fields state rest := by
  simp [SolidityImport.AbiLowering.guard, execStmtList, execStmt, resolved]

def rawOffset (state : DenoteState) (parameterIndex : Nat) : Nat :=
  calldataloadWord state.selector state.world.calldata (wordNormalize (4 + 32 * parameterIndex))

def decoded (state : DenoteState) (binding : String) (parameterIndex : Nat) : DenoteState :=
  { state with bindings := bindValue state.bindings binding (4 + rawOffset state parameterIndex) }

/-- Run all actual root-head checks and bind the decoded pointer from ORIGINAL
calldata. No desired postworld, evaluated-condition or offset-binding premise. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (binding : String) (rootWords parameterIndex tupleWords : Nat)
    (headAvailable : 4 + 32 * rootWords ≤ state.world.calldataSize.val)
    (offsetBound : rawOffset state parameterIndex ≤ 2^64 - 1)
    (tupleAvailable : 4 + rawOffset state parameterIndex + 32 * tupleWords ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit) :
    execStmtList oracle fields state
      (SolidityImport.AbiLowering.tupleHead binding rootWords parameterIndex tupleWords) =
      .continue (decoded state binding parameterIndex) := by
  have first := remaining_evaluated oracle fields state (.literal 4) 4 (32 * rootWords)
    (by rfl) headAvailable sizeBound
  have offset : evalExpr oracle fields state (.calldataload (.literal (4 + 32 * parameterIndex))) =
      some (rawOffset state parameterIndex) := by rfl
  have boundGuard : evalExpr oracle fields state
      (.le (.calldataload (.literal (4 + 32 * parameterIndex))) (.literal (2^64 - 1))) = some 1 := by
    change some (boolWord (decide (rawOffset state parameterIndex ≤ wordNormalize (2^64 - 1)))) = _
    have normalized : wordNormalize (2^64 - 1) = 2^64 - 1 := by rfl
    simp only [normalized, offsetBound, decide_true, boolWord, ite_true]
  have pointer := ImportedAbiWordBinding.add_evaluated oracle fields state
    (.literal 4) (.calldataload (.literal (4 + 32 * parameterIndex))) 4
    (rawOffset state parameterIndex) (by rfl) offset (by
      have : 2^64 - 1 + 4 < Verity.Core.Uint256.modulus := by decide
      omega)
  have last := remaining_evaluated oracle fields (decoded state binding parameterIndex)
    (.localVar binding) (4 + rawOffset state parameterIndex) (32 * tupleWords)
    (by simp [evalExpr, decoded]) tupleAvailable sizeBound
  unfold SolidityImport.AbiLowering.tupleHead
  rw [guard_cons oracle fields state _ _ first, guard_cons oracle fields state _ _ boundGuard,
    SolidityImport.exec_let_cons, pointer]
  change execStmtList oracle fields (decoded state binding parameterIndex)
    [SolidityImport.AbiLowering.guard _] = _
  rw [guard_cons oracle fields _ _ [] last]
  rfl

end Compiler.Proofs.IRGeneration.ImportedAbiTupleHead
