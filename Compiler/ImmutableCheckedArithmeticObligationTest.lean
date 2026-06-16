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

verity_contract ExplicitImmutableCheckedArithmetic where
  storage

  constants
    offset : Uint256 := 2

  immutables
    seededSupply : Uint256 := (addPanic seed offset)

  constructor (seed : Uint256) := do
    pure ()

verity_contract ImplicitImmutableCheckedArithmetic where
  storage

  immutables
    feeScale : Uint256 := (addPanic 9999 1)

private def explicitConstructorSurfacesImmutableCheckedArithmeticObligation : Bool :=
  match ExplicitImmutableCheckedArithmetic.spec.constructor with
  | some { localObligations :=
      [{ name := "checked_arithmetic_constructor_1_add_no_overflow"
         obligation :=
           "Prove `Verity.Proofs.Stdlib.Math.CheckedArithmetic.AddNoOverflow (seed) (offset)` for the checked arithmetic operation emitted at this entrypoint."
         proofStatus := .assumed }], .. } => true
  | _ => false

private def implicitConstructorSurfacesImmutableCheckedArithmeticObligation : Bool :=
  match ImplicitImmutableCheckedArithmetic.spec.constructor with
  | some { localObligations :=
      [{ name := "checked_arithmetic_constructor_1_add_no_overflow"
         obligation :=
           "Prove `Verity.Proofs.Stdlib.Math.CheckedArithmetic.AddNoOverflow (9999) (1)` for the checked arithmetic operation emitted at this entrypoint."
         proofStatus := .assumed }], .. } => true
  | _ => false

private def checkedArithmeticInitializerObligationSmoke : Bool :=
  explicitConstructorSurfacesImmutableCheckedArithmeticObligation &&
    implicitConstructorSurfacesImmutableCheckedArithmeticObligation

#eval show IO Unit from do
  if checkedArithmeticInitializerObligationSmoke then
    IO.println "ok: immutable initializer checked arithmetic obligations surfaced"
  else
    throw <| IO.userError "immutable initializer checked arithmetic obligations were not surfaced"

end Compiler.ImmutableCheckedArithmeticObligationTest
