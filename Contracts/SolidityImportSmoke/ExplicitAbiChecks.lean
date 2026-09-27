import Compiler.SolidityImport.AbiLowering
import Verity.Core.Model.Denote

namespace SolidityImportSmoke.ExplicitAbiChecks
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport.AbiLowering

def function : FunctionSpec :=
  { name := "read"
    params := [{ name := "market", ty := .tuple [.uint256, .array .uint256] }]
    returnType := some .uint256
    abiDecoding := .explicitPrelude
    body := tupleHead "market_pointer" 1 0 2 ++
      [.return (.calldataload (.localVar "market_pointer"))]
    localObligations := [{
      name := "solidity_explicit_abi"
      obligation := "Source-compatible tuple-head guards and raw loads; decoder equivalence remains unchecked."
      proofStatus := .unchecked }] }

def model : CompilationModel :=
  { name := "ExplicitAbi", fields := [], constructor := none, functions := [function] }
def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩

theorem declared_signature_retained :
    function.params = [{ name := "market", ty := .tuple [.uint256, .array .uint256] }] := by rfl

theorem explicit_loader_has_no_automatic_bindings : function.bindingParams = [] := by rfl

theorem public_denote_accepts_overlap :
    (denoteFunction oracle model function
      { sender := 1, functionSelector := 0, args := [0, 64, 0] } Verity.defaultState).returnValue =
      some 0 := by decide +kernel

theorem standard_loader_still_rejects_overlap :
    (denoteFunction oracle model { function with abiDecoding := .standard }
      { sender := 1, functionSelector := 0, args := [0, 64, 0] } Verity.defaultState).success =
      false := by decide +kernel

def checkBoundary : IO Unit := do
  unless (validateFunctionSpec function).isOk do
    throw (IO.userError "valid explicit ABI entry rejected")
  unless (compileFunctionSpec [] [] [] [] 0 function).isOk do
    throw (IO.userError "explicit ABI function did not compile")
  for bad in [
    { function with localObligations := [] },
    { function with localObligations := [{ name := "unrelated", obligation := "not the ABI boundary", proofStatus := .unchecked }] },
    { function with isInternal := true },
    { function with nonReentrantLock := some "lock" },
    { function with body := [.return (.param "market")] },
    { function with body := [.return (.paramDynamicHeadWord "market" 0)] },
    { function with body := [.return (.localVar "unbound")] }] do
    if (validateFunctionSpec bad).isOk then
      throw (IO.userError "invalid explicit ABI entry accepted")

end SolidityImportSmoke.ExplicitAbiChecks

def main : IO Unit := SolidityImportSmoke.ExplicitAbiChecks.checkBoundary
