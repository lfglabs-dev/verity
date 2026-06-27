namespace Compiler.Yul

inductive YulExpr
  | lit (n : Nat)
  | hex (n : Nat)
  | str (s : String)
  | ident (name : String)
  | call (func : String) (args : List YulExpr)
  deriving Repr, BEq

namespace YulExpr

private def verbatimHexPrefix : String := "__verity_verbatim_hex:"

def verbatimHex (opcodeHex : String) : YulExpr :=
  .str (verbatimHexPrefix ++ opcodeHex)

def verbatimHex? : YulExpr → Option String
  | .str s => (s.dropPrefix? verbatimHexPrefix).map (·.toString)
  | _ => none

end YulExpr

inductive YulStmt
  | comment (text : String)
  | let_ (name : String) (value : YulExpr)
  | letMany (names : List String) (value : YulExpr)
  | assign (name : String) (value : YulExpr)
  | exprStmt (e : YulExpr)
  | leave
  | if_ (cond : YulExpr) (body : List YulStmt)
  | for_ (init : List YulStmt) (cond : YulExpr) (post : List YulStmt) (body : List YulStmt)
  | switch (expr : YulExpr) (cases : List (Nat × List YulStmt)) (default : Option (List YulStmt))
  | block (stmts : List YulStmt)
  | funcDef (name : String) (params : List String) (rets : List String) (body : List YulStmt)
  deriving Repr, BEq

structure YulObject where
  name : String
  deployCode : List YulStmt
  runtimeCode : List YulStmt
  deriving Repr

end Compiler.Yul
