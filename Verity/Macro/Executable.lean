import Lean
import Verity.Core.Intrinsics
import Verity.Macro.Types

namespace Verity.Macro

open Lean
open Lean.Elab.Command

/-! Minimal session-local registry for intrinsics declared via `verity_intrinsic`.
   Sufficient for same-module declaration-before-use.
   Cross-module requires attribute-based collection (future). -/
private initialize intrinsicDeclRegistry : IO.Ref (Array Verity.Core.Intrinsics.IntrinsicDecl) ← IO.mkRef #[]

def getRegisteredIntrinsics : IO (Array Verity.Core.Intrinsics.IntrinsicDecl) :=
  intrinsicDeclRegistry.get

def registerIntrinsic (d : Verity.Core.Intrinsics.IntrinsicDecl) : IO Unit :=
  intrinsicDeclRegistry.modify (·.push d)

def hardForkTermFromParsed (fork : Verity.Core.Intrinsics.HardFork) : CommandElabM Term := do
  match fork with
  | .cancun => `(Verity.Core.Intrinsics.HardFork.cancun)
  | .prague => `(Verity.Core.Intrinsics.HardFork.prague)
  | .osaka => `(Verity.Core.Intrinsics.HardFork.osaka)

def hardForkTermFromIdent (fork : TSyntax `ident) : CommandElabM Term := do
  match Verity.Core.Intrinsics.HardFork.parse? (toString fork.getId) with
  | some parsed => hardForkTermFromParsed parsed
  | none =>
      throwErrorAt fork
        s!"unknown fork '{toString fork.getId}' (expected cancun, prague, osaka, or fusaka alias)"

partial def yulExprTerm : Compiler.Yul.YulExpr → CommandElabM Term
  | .lit n => `(Compiler.Yul.YulExpr.lit $(natTerm n))
  | .hex n => `(Compiler.Yul.YulExpr.hex $(natTerm n))
  | .str s => `(Compiler.Yul.YulExpr.str $(strTerm s))
  | .ident name => `(Compiler.Yul.YulExpr.ident $(strTerm name))
  | .call func args => do
      let argTerms ← args.mapM yulExprTerm
      `(Compiler.Yul.YulExpr.call $(strTerm func) [ $[$argTerms.toArray],* ])

partial def yulStmtTerm : Compiler.Yul.YulStmt → CommandElabM Term
  | .comment text => `(Compiler.Yul.YulStmt.comment $(strTerm text))
  | .let_ name value => do
      let valueTerm ← yulExprTerm value
      `(Compiler.Yul.YulStmt.let_ $(strTerm name) $valueTerm)
  | .letMany names value => do
      let nameTerms := names.map strTerm
      let valueTerm ← yulExprTerm value
      `(Compiler.Yul.YulStmt.letMany [ $[$nameTerms.toArray],* ] $valueTerm)
  | .assign name value => do
      let valueTerm ← yulExprTerm value
      `(Compiler.Yul.YulStmt.assign $(strTerm name) $valueTerm)
  | .exprStmt expr => do
      let exprTerm ← yulExprTerm expr
      `(Compiler.Yul.YulStmt.exprStmt $exprTerm)
  | .leave => `(Compiler.Yul.YulStmt.leave)
  | .if_ cond body => do
      let condTerm ← yulExprTerm cond
      let bodyTerms ← body.mapM yulStmtTerm
      `(Compiler.Yul.YulStmt.if_ $condTerm [ $[$bodyTerms.toArray],* ])
  | .for_ init cond post body => do
      let initTerms ← init.mapM yulStmtTerm
      let condTerm ← yulExprTerm cond
      let postTerms ← post.mapM yulStmtTerm
      let bodyTerms ← body.mapM yulStmtTerm
      `(Compiler.Yul.YulStmt.for_
          [ $[$initTerms.toArray],* ]
          $condTerm
          [ $[$postTerms.toArray],* ]
          [ $[$bodyTerms.toArray],* ])
  | .switch expr cases default => do
      let exprTerm ← yulExprTerm expr
      let caseTerms ← cases.mapM fun (tag, body) => do
        let bodyTerms ← body.mapM yulStmtTerm
        `(($(natTerm tag), [ $[$bodyTerms.toArray],* ]))
      let defaultTerm ←
        match default with
        | none => `(none)
        | some body => do
            let bodyTerms ← body.mapM yulStmtTerm
            `(some [ $[$bodyTerms.toArray],* ])
      `(Compiler.Yul.YulStmt.switch
          $exprTerm
          [ $[$caseTerms.toArray],* ]
          $defaultTerm)
  | .block stmts => do
      let stmtTerms ← stmts.mapM yulStmtTerm
      `(Compiler.Yul.YulStmt.block [ $[$stmtTerms.toArray],* ])
  | .funcDef name params rets body => do
      let paramTerms := params.map strTerm
      let retTerms := rets.map strTerm
      let bodyTerms ← body.mapM yulStmtTerm
      `(Compiler.Yul.YulStmt.funcDef
          $(strTerm name)
          [ $[$paramTerms.toArray],* ]
          [ $[$retTerms.toArray],* ]
          [ $[$bodyTerms.toArray],* ])

def yulLoweringTerm (lowering : Verity.Core.Intrinsics.YulLowering) : CommandElabM Term := do
  match lowering with
  | .verbatim inArity outArity opcodeHex =>
      `(Verity.Core.Intrinsics.YulLowering.verbatim
          $(natTerm inArity) $(natTerm outArity) $(strTerm opcodeHex))
  | .builtin name =>
      `(Verity.Core.Intrinsics.YulLowering.builtin $(strTerm name))
  | .template params output body obligations => do
      let paramTerms := params.map strTerm
      let bodyTerms ← body.mapM yulStmtTerm
      let obligationTerms ← obligations.mapM fun (name, status, message) =>
        `(( $(strTerm name), $(strTerm status), $(strTerm message) ))
      `(Verity.Core.Intrinsics.YulLowering.template
          [ $[$paramTerms.toArray],* ]
          $(strTerm output)
          [ $[$bodyTerms.toArray],* ]
          [ $[$obligationTerms.toArray],* ])

end Verity.Macro
