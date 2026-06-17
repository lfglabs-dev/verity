import Compiler.CompilationModel
import Contracts.Common
import Verity.Macro.Translate
import Verity.Stdlib.Math

namespace Compiler.ImmutableCheckedArithmeticObligationTest

open Compiler
open Compiler.CompilationModel
open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract ExplicitImmutableCheckedArithmetic where
  storage

  constants
    offset : Uint256 := 2

  immutables
    seededSupply : Uint256 := requireSomeUint (safeAdd seed offset) "seed overflow"

  constructor (seed : Uint256) := do
    pure ()

verity_contract ImplicitImmutableCheckedArithmetic where
  storage

  immutables
    feeScale : Uint256 := requireSomeUint (safeAdd 9999 1) "fee overflow"

def explicitConstructorSurfacesImmutableCheckedArithmeticObligation : Bool :=
  match ExplicitImmutableCheckedArithmetic.spec.«constructor» with
  | some { localObligations :=
      [{ name := "checked_arithmetic_constructor_1_add_no_overflow"
         obligation :=
           "Prove `Verity.Proofs.Stdlib.Math.CheckedArithmetic.AddNoOverflow (seed) (offset)` for the checked arithmetic operation emitted at this entrypoint."
         proofStatus := .assumed }], .. } => true
  | _ => false

example : explicitConstructorSurfacesImmutableCheckedArithmeticObligation = true := by rfl

def implicitConstructorSurfacesImmutableCheckedArithmeticObligation : Bool :=
  match ImplicitImmutableCheckedArithmetic.spec.«constructor» with
  | some { localObligations :=
      [{ name := "checked_arithmetic_constructor_1_add_no_overflow"
         obligation :=
           "Prove `Verity.Proofs.Stdlib.Math.CheckedArithmetic.AddNoOverflow (9999) (1)` for the checked arithmetic operation emitted at this entrypoint."
         proofStatus := .assumed }], .. } => true
  | _ => false

example : implicitConstructorSurfacesImmutableCheckedArithmeticObligation = true := by rfl

end Compiler.ImmutableCheckedArithmeticObligationTest
