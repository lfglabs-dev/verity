import Compiler.Yul.Ast
import Verity.Core.Model.Types

namespace Compiler.Yul.StatementRegions

open Compiler.CompilationModel (UnsafeYulFragment)

def ecmBeginMarker : String := "__verity_ecm_begin"
def ecmEndMarker : String := "__verity_ecm_end"

private def childBlocks : YulStmt → List (List YulStmt)
  | .if_ _ body | .block body | .funcDef _ _ _ body => [body]
  | .for_ init _ post body => [init, post, body]
  | .switch _ cases default => cases.map Prod.snd ++ default.toList
  | _ => []

private def allStatementListsFuel (p : List YulStmt → Bool) : Nat → List YulStmt → Bool
  | 0, _ => false
  | fuel + 1, stmts =>
      p stmts && stmts.all fun stmt =>
        (childBlocks stmt).all (allStatementListsFuel p fuel)

/-- Check every lexical statement list, failing closed if traversal fuel runs out. -/
def allStatementLists (p : List YulStmt → Bool) (stmts : List YulStmt) : Bool :=
  allStatementListsFuel p ((toString (repr stmts)).length + 1) stmts

def containsEcmMarker (stmts : List YulStmt) : Bool :=
  !allStatementLists (fun body => body.all fun
    | .comment text => text != ecmBeginMarker && text != ecmEndMarker
    | _ => true) stmts

-- Each list must balance its own markers: regions cannot span lexical scopes.
-- The stack stores the expected closing comment, distinguishing ECM/unsafe Yul.
private def balancedMarkers : List String → List YulStmt → Bool
  | stack, [] => stack.isEmpty
  | stack, .comment text :: rest =>
      if text == ecmBeginMarker then
        balancedMarkers (ecmEndMarker :: stack) rest
      else if text == UnsafeYulFragment.beginMarker then
        balancedMarkers (UnsafeYulFragment.endMarker :: stack) rest
      else if text == ecmEndMarker || text == UnsafeYulFragment.endMarker then
        match stack with
        | expected :: tail => text == expected && balancedMarkers tail rest
        | [] => false
      else balancedMarkers stack rest
  | stack, _ :: rest => balancedMarkers stack rest

def wellFormed (stmts : List YulStmt) : Bool :=
  allStatementLists (balancedMarkers []) stmts

end Compiler.Yul.StatementRegions
