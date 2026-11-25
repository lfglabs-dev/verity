import Compiler.CompilationModel

/-!
# `Stmt.forEachWhile` smoke model (#2916)

Early-exit bounded loops written directly in the CompilationModel. The executable
semantics (`Compiler/Proofs/IRGeneration/SourceSemanticsFeatureTest.lean`) and the
compiled bytecode (`test/ForEachWhileSmoke.t.sol`, against a Solidity reference that
uses `break`) check the same values. The reference's gas behaviour is the point: once
the loop exits it runs no further iteration, so a large count with an early exit
succeeds and a large count without one runs out of gas on both sides.

Every function returns `hit * 2^255 + found * 2^128 + iterations`, where `iterations`
counts the bodies that ran.
-/

namespace Contracts.Smoke.ForEachWhileSmoke

open Compiler.CompilationModel

private def lv (name : String) : Expr := Expr.localVar name

/-- `hit * 2^255 + found * 2^128 + iters`. -/
def packedResult : Expr :=
  Expr.add (Expr.mul (lv "hit") (Expr.literal (2 ^ 255)))
    (Expr.add (Expr.mul (lv "found") (Expr.literal (2 ^ 128))) (lv "iters"))

/-- The match test of one iteration: record the index and raise the exit flag. -/
def matchStep : List Stmt :=
  [ Stmt.assignVar "iters" (Expr.add (lv "iters") (Expr.literal 1))
  , Stmt.ite (Expr.eq (lv "i") (Expr.param "target"))
      [ Stmt.assignVar "found" (lv "i")
      , Stmt.assignVar "hit" (Expr.literal 1)
      , Stmt.assignVar "flag" (Expr.literal 2) ]
      [] ]

/-- The importer's exit-flag loop body: every iteration is guarded by `flag < 2`. -/
def flagGuardedBody : List Stmt :=
  [ Stmt.ite (Expr.lt (lv "flag") (Expr.literal 2))
      (Stmt.assignVar "flag" (Expr.literal 0) :: matchStep)
      [] ]

def resultLocals : List Stmt :=
  [ Stmt.letVar "flag" (Expr.literal 0)
  , Stmt.letVar "hit" (Expr.literal 0)
  , Stmt.letVar "found" (Expr.literal 0)
  , Stmt.letVar "iters" (Expr.literal 0) ]

/-- First index equal to `target` in `0 … n-1`, as an early-exit loop. -/
def firstMatchBody : List Stmt :=
  resultLocals ++
    [ Stmt.forEachWhile "i" (Expr.param "n") (Expr.lt (lv "flag") (Expr.literal 2))
        flagGuardedBody
    , Stmt.return packedResult ]

/-- The same flag loop on plain `forEach`: functionally equal, but it runs every
remaining (empty) iteration after the match. -/
def firstMatchForEachBody : List Stmt :=
  resultLocals ++
    [ Stmt.forEach "i" (Expr.param "n") flagGuardedBody
    , Stmt.return packedResult ]

/-- A guard that reads the loop variable. The guard sees the variable's value before
the iteration binds it: `0` before the first iteration, then the last index. -/
def countWhileBelowBody : List Stmt :=
  resultLocals ++
    [ Stmt.forEachWhile "i" (Expr.param "n") (Expr.lt (lv "i") (Expr.param "limit"))
        [ Stmt.assignVar "iters" (Expr.add (lv "iters") (Expr.literal 1))
        , Stmt.assignVar "found" (lv "i") ]
    , Stmt.return packedResult ]

/-- An empty body under a constant-true guard: `n` iterations, nothing else. -/
def emptyLoopBody : List Stmt :=
  [ Stmt.forEachWhile "i" (Expr.param "n") (Expr.literal 1) []
  , Stmt.return (Expr.literal 7) ]

/-- A guard that evaluates to an even nonzero word (`2` while `i < limit`, `0` otherwise),
exercising `iszero(iszero(guard))` normalization where raw bitwise `and(1, 2)` would be `0`. -/
def evenWordGuardBody : List Stmt :=
  resultLocals ++
    [ Stmt.forEachWhile "i" (Expr.param "n")
        (Expr.mul (Expr.lt (lv "i") (Expr.param "limit")) (Expr.literal 2))
        [ Stmt.assignVar "iters" (Expr.add (lv "iters") (Expr.literal 1))
        , Stmt.assignVar "found" (lv "i") ]
    , Stmt.return packedResult ]

def spec : CompilationModel := {
  name := "ForEachWhileSmoke"
  fields := []
  constructor := none
  functions := [
    { name := "firstMatch"
      params := [{ name := "n", ty := ParamType.uint256 },
        { name := "target", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := firstMatchBody }
  , { name := "firstMatchForEach"
      params := [{ name := "n", ty := ParamType.uint256 },
        { name := "target", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := firstMatchForEachBody }
  , { name := "countWhileBelow"
      params := [{ name := "n", ty := ParamType.uint256 },
        { name := "limit", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := countWhileBelowBody }
  , { name := "emptyLoop"
      params := [{ name := "n", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := emptyLoopBody }
  , { name := "evenWordGuard"
      params := [{ name := "n", ty := ParamType.uint256 },
        { name := "limit", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := evenWordGuardBody }
  ]
}

end Contracts.Smoke.ForEachWhileSmoke
