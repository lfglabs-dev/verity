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
    [ Stmt.require (Expr.gt (Expr.storage "totalSupply") (Expr.literal 0)) "nonzero"
    , Stmt.setMapping "balances" (Expr.param "account") (Expr.storage "totalSupply")
    , Stmt.emit "Transfer" [Expr.param "account", Expr.storage "totalSupply"] ]
  assert "extracts reads" (summary.reads.contains "totalSupply")
  assert "extracts writes" (summary.writes.contains "balances")
  assert "extracts guards" (summary.guards.contains "nonzero")
  assert "extracts events" (summary.events.contains "Transfer")
  assert "non-empty summary reports isNonEmpty" summary.isNonEmpty
  assert "empty summary is not isNonEmpty" (!(extract []).isNonEmpty)
  let failingRequireError := extract
    [Stmt.requireError (Expr.literal 0) "InsufficientBalance" [Expr.storage "balance"]]
  assert "failing requireError includes payload storage reads"
    (failingRequireError.reads.contains "balance")
  let literalRequireError := extract
    [Stmt.requireError (Expr.literal 0) "InsufficientBalance" [Expr.literal 1]]
  assert "literal requireError payload remains read-free" literalRequireError.reads.isEmpty

end Compiler.Proofs.GeneratedTransitionTest
