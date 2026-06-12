import Compiler.CompilationModel.Types
import Compiler.CompilationModel.IssueRefs

/-!
Call-like-operand purity analysis, expressed over the canonical `Expr.children`
/ `Stmt.childLists` traversal surface: each predicate is a node-local
classifier lifted with `anyDeep`, so new AST constructors fail to compile in
the canonical traversal instead of silently falling through a bespoke walk.
-/

namespace Compiler.CompilationModel

/-- Node-local classifier: is this expression itself a call-like node?
    `externalCall` to the compiler-synthesized exponentiation builtin is pure
    (its lowering is a loop, not a CALL), so only its operands matter. -/
def exprIsCallLikeNode : Expr → Bool
  | Expr.call _ _ _ _ _ _ _ => true
  | Expr.staticcall _ _ _ _ _ _ => true
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.internalCall _ _ => true
  | Expr.externalCall name _ => name != builtinExpName
  | _ => false

/-- Does the expression contain a call-like node anywhere? -/
def exprContainsCallLike (expr : Expr) : Bool :=
  expr.anyDeep exprIsCallLikeNode

def exprListContainsCallLike (exprs : List Expr) : Bool :=
  exprs.any exprContainsCallLike

def validateLogicalOperandPurity (context : String) (a b : Expr) : Except String Unit := do
  if exprContainsCallLike a || exprContainsCallLike b then
    throw s!"Compilation error: {context} uses Expr.logicalAnd/Expr.logicalOr with call-like operand(s), which are eagerly evaluated ({issue748Ref}). Move call-like expressions into Stmt.letVar/Stmt.ite before combining booleans."

def validateArithDuplicatedOperandPurity (context : String) (duplicated : List Expr) : Except String Unit := do
  if duplicated.any exprContainsCallLike then
    throw s!"Compilation error: {context} uses an arithmetic helper (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before using them in arithmetic helpers."

/-- Node-local classifier for the operand-duplication hazard: expression forms
    whose Yul lowering duplicates (or eagerly evaluates) specific operands, so
    a call-like expression in those positions would execute more than once or
    unconditionally. `mulDiv512Up`/`mulDiv512Down` lower to a single helper
    call where each operand is evaluated once, so they are safe (verity#1761). -/
def exprIsUnsafeLogicalNode : Expr → Bool
  | Expr.logicalAnd a b | Expr.logicalOr a b
  | Expr.min a b | Expr.max a b =>
      exprContainsCallLike a || exprContainsCallLike b
  | Expr.mulDivUp _ _ c => exprContainsCallLike c
  | Expr.wDivUp _ b => exprContainsCallLike b
  | Expr.ite cond thenVal elseVal =>
      exprContainsCallLike cond || exprContainsCallLike thenVal ||
        exprContainsCallLike elseVal
  | _ => false

/-- Does the expression contain a duplication-hazardous node anywhere? -/
def exprContainsUnsafeLogicalCallLike (expr : Expr) : Bool :=
  expr.anyDeep exprIsUnsafeLogicalNode

def exprListAnyUnsafeLogicalCallLike (exprs : List Expr) : Bool :=
  exprs.any exprContainsUnsafeLogicalCallLike

/-- Statement-level lift: scans every statement-local expression (via the
    canonical `directMetadata.subexpressions`) and recurses through nested
    statement bodies. Raw `unsafeYul` fragments are emitted verbatim — the
    expression compiler never duplicates their operands — so they contribute
    no subexpressions here by construction. -/
def stmtContainsUnsafeLogicalCallLike (stmt : Stmt) : Bool :=
  stmt.anyDeep fun s =>
    s.directMetadata.subexpressions.any exprContainsUnsafeLogicalCallLike

def stmtListAnyUnsafeLogicalCallLike (stmts : List Stmt) : Bool :=
  stmts.any stmtContainsUnsafeLogicalCallLike

def matchBranchesAnyUnsafeLogicalCallLike
    (branches : List (String × List String × List Stmt)) : Bool :=
  branches.any fun (_, _, body) => stmtListAnyUnsafeLogicalCallLike body

end Compiler.CompilationModel
