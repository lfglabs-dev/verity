import Compiler.CompilationModel.Validation

namespace SolidityImportSmoke.RequirePayloadValidationChecks
open Compiler.CompilationModel

def messages : List String :=
  ["", "é🙂", "constant message"] ++
    [31, 32, 63, 64, 65].map (fun count => String.ofList (List.replicate count 'x'))

def body (message : String) : List Stmt :=
  [.ite (.literal 1) [.forEach "i" (.literal 1) [.require (.literal 1) message]] []]

def runChecks : IO Unit := do
  for message in messages do
    unless requirePayloadFitsWord message do
      throw (IO.userError "finite ABI message incorrectly exceeds the EVM address space")
    unless (validateRequirePayloads "nested" (body message)).isOk do
      throw (IO.userError "canonical nested payload traversal rejected a finite message")
    let fn : FunctionSpec := { name := "payload", params := [], returnType := none, body := body message }
    unless (validateFunctionSpec fn).isOk do
      throw (IO.userError "production function wrapper rejected a finite message")
    let ctor : ConstructorSpec := { params := [], body := body message }
    unless (validateConstructorSpec (some ctor)).isOk do
      throw (IO.userError "production constructor wrapper rejected a finite message")
  unless (validateConstructorSpec none).isOk do
    throw (IO.userError "absent constructor validation changed")
  let invalid : FunctionSpec := { name := "invalid", params := [], returnType := none, body := [], isPure := true, isPayable := true }
  if (validateFunctionSpec invalid).isOk then
    throw (IO.userError "payload wrapper bypassed pre-existing function checks")
  let invalidCtor : ConstructorSpec := { params := [], body := [.return (.literal 0)] }
  if (validateConstructorSpec (some invalidCtor)).isOk then
    throw (IO.userError "payload wrapper bypassed pre-existing constructor checks")
  IO.println "Require payload extent and preserved production validation checks passed"

end SolidityImportSmoke.RequirePayloadValidationChecks

def main : IO Unit := SolidityImportSmoke.RequirePayloadValidationChecks.runChecks
