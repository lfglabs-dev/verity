import Compiler.Proofs.GeneratedTransition

namespace Compiler.Proofs.GeneratedTransitionTest

open Compiler.CompilationModel
open Compiler.Proofs.GeneratedTransition

private def assert (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"GeneratedTransition test failed: {label}")
  IO.println s!"ok: {label}"

#eval! do
  let summary := extract
    [ Stmt.require (Expr.gt (Expr.storage "totalUnits") (Expr.literal 0)) "nonzero"
    , Stmt.setMapping "position" (Expr.param "borrower") (Expr.storage "totalUnits")
    , Stmt.emit "Take" [Expr.param "borrower", Expr.storage "totalUnits"] ]
  assert "extracts reads" (summary.reads.contains "totalUnits")
  assert "extracts writes" (summary.writes.contains "position")
  assert "extracts guards" (summary.guards.contains "nonzero")
  assert "extracts events" (summary.events.contains "Take")
  assert "non-empty summary can feed later Midnight RCF/totalUnits" (enoughForMidnightRcfTotalUnits summary)

end Compiler.Proofs.GeneratedTransitionTest
