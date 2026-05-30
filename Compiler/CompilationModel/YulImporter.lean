import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

open Compiler.Yul

/-- Source location supplied by an external Solidity/Yul AST importer. -/
structure YulSourceSpan where
  sourceName : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, BEq, Inhabited

namespace YulSourceSpan

def toReportString (span : YulSourceSpan) : String :=
  s!"{span.sourceName}:{span.startLine}:{span.startColumn}-{span.endLine}:{span.endColumn}"

end YulSourceSpan

/-- Provenance for Yul entering the compilation model from outside Verity. -/
inductive ImportedYulDialect where
  | solidityInlineAssembly
  | yul
  | generatedYul
  deriving Repr, BEq, Inhabited

namespace ImportedYulDialect

def toReportString : ImportedYulDialect → String
  | .solidityInlineAssembly => "Solidity inline assembly"
  | .yul => "Yul"
  | .generatedYul => "generated Yul"

end ImportedYulDialect

/-- Typed boundary for importing already-parsed Solidity inline assembly/Yul AST.
    Parsing remains outside this module; this boundary converts `Compiler.Yul.YulStmt`
    into the localized unsafe-Yul statement surface with derived metadata. -/
structure ImportedYulBlock where
  label : String
  dialect : ImportedYulDialect := .solidityInlineAssembly
  sourceSpan : Option YulSourceSpan := none
  stmts : List YulStmt
  obligation : Option String := none
  proofStatus : Compiler.ProofStatus := .assumed
  extraMechanics : List LowLevelMechanic := []
  extraContracts : List UnsafeYulContract := []
  termination : StmtTermination := .mayTerminate
  controlFlow : ControlFlowSummary := .unknown
  deriving Repr

namespace YulImporter

private def uniqueMechanics (xs : List LowLevelMechanic) : List LowLevelMechanic :=
  xs.eraseDups

private partial def mechanicsOfExpr : YulExpr → List LowLevelMechanic
  | .call name args =>
      let here :=
        match name with
        | "call" => [.call]
        | "staticcall" => [.staticcall]
        | "delegatecall" => [.delegatecall]
        | "returndatasize" => [.returndataSize]
        | "returndatacopy" => [.returndataCopy]
        | "revert" => [.rawRevert]
        | "mload" => [.mload]
        | "mstore" => [.mstore]
        | "calldataload" => [.calldataload]
        | "calldatacopy" => [.calldatacopy]
        | "extcodesize" => [.extcodesize]
        | "tload" => [.tload]
        | "tstore" => [.tstore, .storageWrite]
        | "sstore" => [.storageWrite]
        | "log0" | "log1" | "log2" | "log3" | "log4" => [.rawLog]
        | "address" => [.contractAddress]
        | "chainid" => [.chainid]
        | "selfbalance" => [.selfBalance]
        | "number" => [.blockNumber]
        | _ => []
      here ++ args.flatMap mechanicsOfExpr
  | _ => []

mutual
private partial def mechanicsOfStmt : YulStmt → List LowLevelMechanic
  | .comment _ | .leave => []
  | .let_ _ value | .letMany _ value | .assign _ value | .expr value =>
      mechanicsOfExpr value
  | .if_ cond body =>
      mechanicsOfExpr cond ++ mechanicsOfStmts body
  | .for_ init cond post body =>
      mechanicsOfStmts init ++ mechanicsOfExpr cond ++ mechanicsOfStmts post ++ mechanicsOfStmts body
  | .switch expr cases default =>
      mechanicsOfExpr expr ++
        cases.flatMap (fun (_, body) => mechanicsOfStmts body) ++
        default.toList.flatMap mechanicsOfStmts
  | .block stmts =>
      mechanicsOfStmts stmts
  | .funcDef _ _ _ body =>
      mechanicsOfStmts body

private partial def mechanicsOfStmts : List YulStmt → List LowLevelMechanic
  | [] => []
  | stmt :: rest => mechanicsOfStmt stmt ++ mechanicsOfStmts rest
end

private def controlFlowOfExpr : YulExpr → ControlFlowSummary
  | .call "revert" _ => .reverts
  | .call "return" _ => .returns
  | .call "stop" _ => .stops
  | _ => .fallsThrough

mutual
private partial def controlFlowOfStmt : YulStmt → ControlFlowSummary
  | .comment _ | .let_ _ _ | .letMany _ _ | .assign _ _ | .funcDef _ _ _ _ =>
      .fallsThrough
  | .leave =>
      .returns
  | .expr expr =>
      controlFlowOfExpr expr
  | .if_ cond body =>
      (controlFlowOfExpr cond).union { (controlFlowOfStmts body) with mayFallThrough := true }
  | .for_ _ _ _ _ | .switch _ _ _ =>
      .unknown
  | .block stmts =>
      controlFlowOfStmts stmts

private partial def controlFlowOfStmts : List YulStmt → ControlFlowSummary
  | [] => .fallsThrough
  | stmt :: rest =>
      (controlFlowOfStmt stmt).seq (controlFlowOfStmts rest)
end

private def defaultObligationText (block : ImportedYulBlock) : String :=
  let source :=
    match block.sourceSpan with
    | none => block.dialect.toReportString
    | some span => s!"{block.dialect.toReportString} at {span.toReportString}"
  s!"Imported {source} block '{block.label}' must refine the declared Verity state transition."

/-- Convert imported Solidity inline assembly/Yul AST into a localized unsafe-Yul statement. -/
def importBlock (block : ImportedYulBlock) : Stmt :=
  let obligationText := block.obligation.getD (defaultObligationText block)
  let obligation : LocalObligation :=
    { name := block.label
      obligation := obligationText
      proofStatus := block.proofStatus }
  Stmt.unsafeYul {
    label := block.label
    stmts := block.stmts
    obligations := [obligation]
    contracts := block.extraContracts
    mechanics := uniqueMechanics (mechanicsOfStmts block.stmts ++ block.extraMechanics)
    scopeEffects := yulStmtListScopeEffects block.stmts
    termination := block.termination
    controlFlow :=
      if block.controlFlow == .unknown then
        controlFlowOfStmts block.stmts
      else
        block.controlFlow
  }

end YulImporter

end Compiler.CompilationModel
