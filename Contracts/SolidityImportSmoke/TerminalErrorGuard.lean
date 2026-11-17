import Compiler.SolidityImport.Import
import Compiler.CompilationModel
import Verity.Core.Model.DenoteErrorGuard

/-! A declared-return root that always reverts must compile. The controls below
retain the same imported prefix and change only the terminal statement, so an
unrelated importer error cannot masquerade as the expected compiler rejection. -/

namespace SolidityImportSmoke.TerminalErrorGuard
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "TerminalErrorGuard.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract TerminalErrorGuard
  function fail(uint256)

private def returnPathError : String :=
  "Compilation error: function 'fail' declares return values but not all " ++
  "control-flow paths end in return/revert (Issue #738 (exhaustive return-path analysis))"

/-- Check source import, compilation, and the exact boundary of terminal guards. -/
def runChecks : IO Unit := do
  let [fn] := imported.model.functions
    | throw (IO.userError "expected exactly one imported root")
  unless (← IO.ofExcept (functionReturns fn)) == [.uint256] do
    throw (IO.userError "the reproducer must retain its declared return value")
  let some guard@(.requireError (.literal 0) name args) := fn.body.getLast?
    | throw (IO.userError "expected an imported literal-zero custom-error guard")
  let checks : List (String × List Stmt × Bool) := [
    ("literal zero", [guard], true),
    ("literal one", [.requireError (.literal 1) name args], false),
    ("unknown condition", [.requireError (.param "supplied") name args], false),
    ("nonliteral zero", [.requireError (.sub (.literal 1) (.literal 1)) name args], false),
    ("raw stop", [.stop], false),
    ("fallthrough branch", [.ite (.param "supplied") [guard] []], false),
    ("both branches revert", [.ite (.param "supplied") [guard] [.revertEmpty]], true),
    ("unreachable stop", [guard, .stop], true)]
  for (label, tail, terminal) in checks do
    let active := { imported.model with
      functions := [{ fn with body := fn.body.dropLast ++ tail }] }
    match compile active [0] .osaka with
    | .ok _ =>
        unless terminal do throw (IO.userError s!"{label}: expected return-path rejection")
    | .error reason =>
        if terminal then throw (IO.userError s!"{label}: unexpected rejection: {reason}")
        unless reason == returnPathError do
          throw (IO.userError s!"{label}: wrong rejection: {reason}")
  -- Terminality must not bypass error-declaration validation.
  let invalid := { imported.model with
    functions := [{ fn with body := fn.body.dropLast ++
      [.requireError (.literal 0) "Missing" args] }] }
  match compile invalid [0] .osaka with
  | .ok _ => throw (IO.userError "terminal guard bypassed custom-error validation")
  | .error reason =>
      unless (reason.splitOn "unknown custom error 'Missing'").length > 1 do
        throw (IO.userError s!"wrong custom-error rejection: {reason}")

end SolidityImportSmoke.TerminalErrorGuard

def main : IO Unit := SolidityImportSmoke.TerminalErrorGuard.runChecks
