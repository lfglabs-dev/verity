import Compiler.SolidityImport.Import
import TranslationValidationArithmetic

open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.Denote
open Verity.Core

namespace SolidityTranslationValidation

solidity_profile capturedBuild where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import captured from "experiments/solidity-translation-validation/sources"
  entry "MulDivDown.sol" using capturedBuild
  contract MulDivDown
  function mulDivDown(uint256, uint256, uint256)

#print captured.sourceDigest

private theorem word_roundtrip (x : Uint256) : Uint256.ofNat x.val = x := by
  apply Uint256.ext
  exact Nat.mod_eq_of_lt x.isLt

/-- Successful execution of the actual imported wrapper for every oracle and
world. This does not assert equivalence of either panic path or Yul execution. -/
theorem captured_success (oracle : DenoteOracle) (world : Verity.ContractState)
    (x y d : Uint256) (hfit : x.val * y.val < Uint256.modulus) (hd : d.val ≠ 0) :
    captured.mulDivDown oracle world x y d =
      some (Uint256.ofNat (x.val * y.val / d.val)) := by
  have hp : (x * y).val = x.val * y.val := by
    change (Uint256.mul x y).val = _
    exact Nat.mod_eq_of_lt hfit
  have hguard : x.val = 0 ∨ ((x * y) / x).val = y.val := by
    simpa only [word_roundtrip] using
      (denote_word_mul_overflow_guard_iff x.val y.val x.isLt y.isLt).mpr hfit
  have hquot : ((x * y) / d).val = x.val * y.val / d.val := by
    simpa only [word_roundtrip] using
      denote_mul_div_success x.val y.val d.val x.isLt y.isLt d.isLt hfit hd
  have hproductRoundtrip : Uint256.ofNat (x.val * y.val) = x * y := by
    rw [← hp, word_roundtrip]
  have hqbound : x.val * y.val / d.val < Uint256.modulus :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hfit
  rcases hguard with hzero | hdiv
  all_goals
    simp [captured.mulDivDown, runFunction, functionBody, functionBody.go,
      captured.model, execStmtList, execStmt, evalExpr, evalExprList,
      lookupValue, bindValue, Word.toWord, Word.ofWord, boolWord, wordNormalize,
      word_roundtrip, Nat.mod_eq_of_lt hqbound, *]

#print axioms captured_success

/-- The imported wrapper's successful result agrees with native EVMYulLean
multiply/divide builtin composition. This is intentionally not an execution
theorem for the captured Yul dispatcher or its error/ABI paths. -/
theorem captured_success_matches_native_arithmetic
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (x y d : Uint256) (hfit : x.val * y.val < Uint256.modulus) (hd : d.val ≠ 0) :
    (captured.mulDivDown oracle world x y d).map Uint256.val =
      (Compiler.Proofs.YulGeneration.Backends.evalPureBuiltinViaEvmYulLean
        "mul" [x.val, y.val]).bind
        (fun product => Compiler.Proofs.YulGeneration.Backends.evalPureBuiltinViaEvmYulLean
          "div" [product, d.val]) := by
  rw [captured_success oracle world x y d hfit hd,
    native_mul_div_success x.val y.val d.val hfit d.isLt hd]
  simp only [Option.map_some, Uint256.ofNat]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hfit)]

#print axioms captured_success_matches_native_arithmetic

end SolidityTranslationValidation
