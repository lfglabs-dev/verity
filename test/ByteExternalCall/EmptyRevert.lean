import Compiler.SolidityImport.Transactions
import Compiler.SolidityImport.TransactionAccess
import Compiler.SolidityImport.Coverage

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport

private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩

def main : IO UInt32 := do
  let initial := Verity.defaultState
  let state : DenoteState :=
    { world := { initial with returndata := [Verity.Core.Uint256.ofNat 42] }
      bindings := []
      rawReturndata := some [0xff, 0x01, 0x00] }
  let traced ← IO.ofExcept (Transactions.traceStraightLine oracle [] state [.revertEmpty])
  let frame ← IO.ofExcept (Transactions.finishFrame initial traced.outcome)
  unless !frame.success && frame.data.isEmpty do
    throw (IO.userError "empty revert propagated stale return bytes")
  unless traced.touched.isEmpty do throw (IO.userError "empty revert accessed storage")
  unless executableStmtCovered .revertEmpty do
    throw (IO.userError "empty revert missing executable coverage")
  unless Stmt.controlFlow .revertEmpty == .reverts do
    throw (IO.userError "empty revert control flow differs")
  IO.println "empty revert boundary checks passed"
  return 0

