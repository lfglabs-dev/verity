import Compiler.Yul.Ast
import Lean

namespace Compiler.Yul

/-- Phase at which a patch rule runs. -/
inductive PatchPhase
  | postCodegen
  deriving Repr, DecidableEq

/-- Scope in which a patch rule is allowed to run. -/
inductive RewriteScope
  | runtime
  | deploy
  | object
  deriving Repr, DecidableEq

/-- Typed rewrite execution context carried through one pass iteration. -/
structure RewriteCtx where
  scope : RewriteScope
  passPhase : PatchPhase
  iteration : Nat
  packId : String := ""
  deriving Repr

/-- Audit metadata + executable rewrite for one expression patch rule. -/
structure ExprPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyExpr : RewriteCtx → YulExpr → Option YulExpr

/-- Audit metadata + executable rewrite for one statement patch rule. -/
structure StmtPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyStmt : RewriteCtx → YulStmt → Option YulStmt

/-- Audit metadata + executable rewrite for one block patch rule. -/
structure BlockPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyBlock : RewriteCtx → List YulStmt → Option (List YulStmt)

/-- Audit metadata + executable rewrite for one object-level patch rule. -/
structure ObjectPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyObject : RewriteCtx → YulObject → Option YulObject

/-- Deterministic patch pass settings. -/
structure PatchPassConfig where
  enabled : Bool := true
  maxIterations : Nat := 2
  passPhase : PatchPhase := .postCodegen
  packId : String := ""
  /-- Selected rewrite bundle ID (e.g., `foundation`). -/
  rewriteBundleId : String := "foundation"
  /-- Optional activation-time proof registry for fail-closed rule filtering.
      When non-empty, only rules whose `proofId` appears in this list can run. -/
  requiredProofRefs : List Lean.Name := []

/-- Per-rule usage entry emitted by the patch pass. -/
structure PatchManifestEntry where
  patchName : String
  matchCount : Nat
  changedNodes : Nat
  proofRef : String
  deriving Repr

/-- Result of running a patch pass over Yul statements. -/
structure PatchPassReport where
  patched : List YulStmt
  iterations : Nat
  manifest : List PatchManifestEntry
  deriving Repr

/-- Result of running a patch pass over a full Yul object. -/
structure ObjectPatchPassReport where
  patched : YulObject
  iterations : Nat
  manifest : List PatchManifestEntry
  deriving Repr

private structure PatchRuleMeta where
  patchName : String
  proofRef : Lean.Name

private class PatchRuleLike (α : Type) where
  patchName : α → String
  proofId : α → Lean.Name
  sideConditions : α → List String
  packAllowlist : α → List String
  scope : α → RewriteScope
  passPhase : α → PatchPhase
  priority : α → Nat

private def proofRefPresent (proofRef : Lean.Name) : Bool :=
  proofRef != .anonymous

/-- Parse a dotted declaration name into `Lean.Name` metadata without requiring the
    declaration to be imported at the call site. -/
def proofRefName (ref : String) : Lean.Name :=
  ref.splitOn "." |>.foldl Lean.Name.str .anonymous

private def isRuleAuditable [PatchRuleLike α] (r : α) : Bool :=
  !(PatchRuleLike.patchName r).isEmpty &&
    proofRefPresent (PatchRuleLike.proofId r) &&
    !(PatchRuleLike.sideConditions r).isEmpty

private instance : PatchRuleLike ExprPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private instance : PatchRuleLike StmtPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private instance : PatchRuleLike BlockPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private instance : PatchRuleLike ObjectPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private def ruleAllowsPack [PatchRuleLike α] (rule : α) (packId : String) : Bool :=
  let allowlist := PatchRuleLike.packAllowlist rule
  allowlist.isEmpty || allowlist.any (fun allowed => allowed = packId)

private def ruleActiveInCtx [PatchRuleLike α] (rule : α) (ctx : RewriteCtx) : Bool :=
  PatchRuleLike.scope rule == ctx.scope &&
    PatchRuleLike.passPhase rule == ctx.passPhase &&
    ruleAllowsPack rule ctx.packId

private def ruleHasRegisteredProof [PatchRuleLike α] (config : PatchPassConfig) (rule : α) : Bool :=
  config.requiredProofRefs.isEmpty ||
    config.requiredProofRefs.any (fun proofRef => proofRef = PatchRuleLike.proofId rule)

/-- Fail-closed metadata guard: a runnable rule must carry audit/proof linkage. -/
def ExprPatchRule.isAuditable (rule : ExprPatchRule) : Bool :=
  isRuleAuditable rule

/-- Fail-closed metadata guard: a runnable statement rule must carry audit/proof linkage. -/
def StmtPatchRule.isAuditable (rule : StmtPatchRule) : Bool :=
  isRuleAuditable rule

/-- Fail-closed metadata guard: a runnable block rule must carry audit/proof linkage. -/
def BlockPatchRule.isAuditable (rule : BlockPatchRule) : Bool :=
  isRuleAuditable rule

/-- Fail-closed metadata guard: a runnable object rule must carry audit/proof linkage. -/
def ObjectPatchRule.isAuditable (rule : ObjectPatchRule) : Bool :=
  isRuleAuditable rule

private def insertByPriority [PatchRuleLike α] (r : α) : List α → List α
  | [] => [r]
  | head :: tail =>
      if PatchRuleLike.priority r > PatchRuleLike.priority head then
        r :: head :: tail
      else
        head :: insertByPriority r tail

private def orderByPriority [PatchRuleLike α] (rules : List α) : List α :=
  rules.foldl (fun acc r => insertByPriority r acc) []

private def applyFirstPatchRule [PatchRuleLike α]
    (orderedRules : List α)
    (applyRule : α → RewriteCtx → target → Option target)
    (ctx : RewriteCtx)
    (targetNode : target) : Option (target × String) :=
  let rec go : List α → Option (target × String)
    | [] => none
    | r :: rest =>
        if !(ruleActiveInCtx r ctx) then
          go rest
        else
          match applyRule r ctx targetNode with
          | some rewritten => some (rewritten, PatchRuleLike.patchName r)
          | none => go rest
  go orderedRules

/-- Stable, deterministic ordering: priority descending, declaration order as tie-break. -/
def orderRulesByPriority (rules : List ExprPatchRule) : List ExprPatchRule :=
  orderByPriority rules

/-- Stable, deterministic ordering for statement rules. -/
def orderStmtRulesByPriority (rules : List StmtPatchRule) : List StmtPatchRule :=
  orderByPriority rules

/-- Stable, deterministic ordering for block rules. -/
def orderBlockRulesByPriority (rules : List BlockPatchRule) : List BlockPatchRule :=
  orderByPriority rules

/-- Stable, deterministic ordering for object rules. -/
def orderObjectRulesByPriority (rules : List ObjectPatchRule) : List ObjectPatchRule :=
  orderByPriority rules

private def applyFirstRule
    (orderedRules : List ExprPatchRule)
    (ctx : RewriteCtx)
    (expr : YulExpr) : Option (YulExpr × String) :=
  applyFirstPatchRule orderedRules (fun rule ruleCtx node => rule.applyExpr ruleCtx node) ctx expr

private def applyFirstStmtRule
    (orderedRules : List StmtPatchRule)
    (ctx : RewriteCtx)
    (stmt : YulStmt) : Option (YulStmt × String) :=
  applyFirstPatchRule orderedRules (fun rule ruleCtx node => rule.applyStmt ruleCtx node) ctx stmt

private def applyFirstBlockRule
    (orderedRules : List BlockPatchRule)
    (ctx : RewriteCtx)
    (block : List YulStmt) : Option (List YulStmt × String) :=
  applyFirstPatchRule orderedRules (fun rule ruleCtx node => rule.applyBlock ruleCtx node) ctx block

private def applyAllObjectRulesOnce
    (orderedRules : List ObjectPatchRule)
    (ctx : RewriteCtx)
    (obj : YulObject) : YulObject × List String :=
  orderedRules.foldl
    (fun (state : YulObject × List String) rule =>
      let (currentObj, hits) := state
      if ¬ruleActiveInCtx rule ctx then
        (currentObj, hits)
      else
        match rule.applyObject ctx currentObj with
        | some rewritten => (rewritten, hits ++ [rule.patchName])
        | none => (currentObj, hits))
    (obj, [])

mutual

private def rewriteExprOnce
    (orderedRules : List ExprPatchRule)
    (ctx : RewriteCtx) : YulExpr → (YulExpr × List String)
  | .call func args =>
      let (rewrittenArgs, argHits) := rewriteExprListOnce orderedRules ctx args
      let candidate := YulExpr.call func rewrittenArgs
      match applyFirstRule orderedRules ctx candidate with
      | some (rewritten, patchName) => (rewritten, patchName :: argHits)
      | none => (candidate, argHits)
  | expr =>
      match applyFirstRule orderedRules ctx expr with
      | some (rewritten, patchName) => (rewritten, [patchName])
      | none => (expr, [])

private def rewriteExprListOnce
    (orderedRules : List ExprPatchRule)
    (ctx : RewriteCtx) : List YulExpr → (List YulExpr × List String)
  | [] => ([], [])
  | expr :: rest =>
      let (expr', hitsHead) := rewriteExprOnce orderedRules ctx expr
      let (rest', hitsTail) := rewriteExprListOnce orderedRules ctx rest
      (expr' :: rest', hitsHead ++ hitsTail)

end

private def applyStmtRulesToCandidate
    (orderedStmtRules : List StmtPatchRule)
    (ctx : RewriteCtx)
    (candidate : YulStmt)
    (hits : List String) : YulStmt × List String :=
  match applyFirstStmtRule orderedStmtRules ctx candidate with
  | some (rewritten, patchName) => (rewritten, hits ++ [patchName])
  | none => (candidate, hits)

mutual

private def rewriteStmtOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : YulStmt → (YulStmt × List String)
  | .comment txt =>
      applyStmtRulesToCandidate orderedStmtRules ctx (.comment txt) []
  | .let_ name value =>
      let (value', hits) := rewriteExprOnce orderedExprRules ctx value
      applyStmtRulesToCandidate orderedStmtRules ctx (.let_ name value') hits
  | .letMany names value =>
      let (value', hits) := rewriteExprOnce orderedExprRules ctx value
      applyStmtRulesToCandidate orderedStmtRules ctx (.letMany names value') hits
  | .assign name value =>
      let (value', hits) := rewriteExprOnce orderedExprRules ctx value
      applyStmtRulesToCandidate orderedStmtRules ctx (.assign name value') hits
  | .exprStmt expr =>
      let (expr', hits) := rewriteExprOnce orderedExprRules ctx expr
      applyStmtRulesToCandidate orderedStmtRules ctx (.exprStmt expr') hits
  | .leave =>
      applyStmtRulesToCandidate orderedStmtRules ctx .leave []
  | .if_ cond body =>
      let (cond', condHits) := rewriteExprOnce orderedExprRules ctx cond
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      applyStmtRulesToCandidate orderedStmtRules ctx (.if_ cond' body') (condHits ++ bodyHits)
  | .for_ init cond post body =>
      let (init', initHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx init
      let (cond', condHits) := rewriteExprOnce orderedExprRules ctx cond
      let (post', postHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx post
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      applyStmtRulesToCandidate
        orderedStmtRules
        ctx
        (.for_ init' cond' post' body')
        (initHits ++ condHits ++ postHits ++ bodyHits)
  | .switch expr cases default =>
      let (expr', exprHits) := rewriteExprOnce orderedExprRules ctx expr
      let (cases', caseHits) := rewriteSwitchCasesOnce orderedExprRules orderedStmtRules orderedBlockRules ctx cases
      let (default', defaultHits) := rewriteOptionalStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx default
      applyStmtRulesToCandidate orderedStmtRules ctx (.switch expr' cases' default') (exprHits ++ caseHits ++ defaultHits)
  | .block stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx stmts
      applyStmtRulesToCandidate orderedStmtRules ctx (.block stmts') hits
  | .funcDef name params rets body =>
      let (body', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      applyStmtRulesToCandidate orderedStmtRules ctx (.funcDef name params rets body') hits

private def rewriteStmtListOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : List YulStmt → (List YulStmt × List String)
  | [] => ([], [])
  | stmt :: rest =>
      let (stmt', headHits) := rewriteStmtOnce orderedExprRules orderedStmtRules orderedBlockRules ctx stmt
      let (rest', tailHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx rest
      let candidate := stmt' :: rest'
      let hits := headHits ++ tailHits
      match applyFirstBlockRule orderedBlockRules ctx candidate with
      | some (rewritten, patchName) => (rewritten, hits ++ [patchName])
      | none => (candidate, hits)

private def rewriteOptionalStmtListOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : Option (List YulStmt) → (Option (List YulStmt) × List String)
  | none => (none, [])
  | some stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx stmts
      (some stmts', hits)

private def rewriteSwitchCasesOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : List (Nat × List YulStmt) → (List (Nat × List YulStmt) × List String)
  | [] => ([], [])
  | (tag, body) :: rest =>
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      let (rest', restHits) := rewriteSwitchCasesOnce orderedExprRules orderedStmtRules orderedBlockRules ctx rest
      ((tag, body') :: rest', bodyHits ++ restHits)

end

private def countHitsForPatch (patchName : String) (hits : List String) : Nat :=
  hits.foldl (fun acc hit => if hit = patchName then acc + 1 else acc) 0

private def metaListFromRules
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (objectRules : List ObjectPatchRule) : List PatchRuleMeta :=
  let exprMeta := exprRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let stmtMeta := stmtRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let blockMeta := blockRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let objectMeta := objectRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let allMeta := exprMeta ++ stmtMeta ++ blockMeta ++ objectMeta
  allMeta.foldl
    (fun acc m =>
      if acc.any (fun seen => seen.patchName = m.patchName) then acc else acc ++ [m])
    []

private def manifestFromHits (ruleMeta : List PatchRuleMeta) (hits : List String) : List PatchManifestEntry :=
  (ruleMeta.foldr (fun m acc =>
    let hitCount := countHitsForPatch m.patchName hits
    if hitCount = 0 then
      acc
    else
      { patchName := m.patchName
        matchCount := hitCount
        changedNodes := hitCount
        proofRef := toString m.proofRef } :: acc) [])

private def runPatchPassLoop
    (config : PatchPassConfig)
    (scope : RewriteScope)
    (fuel : Nat)
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (current : List YulStmt)
    (iterations : Nat)
    (allHits : List String) : List YulStmt × Nat × List String :=
  match fuel with
  | 0 => (current, iterations, allHits)
  | Nat.succ fuel' =>
      let loopCtx : RewriteCtx :=
        { scope := scope
          passPhase := config.passPhase
          iteration := iterations
          packId := config.packId }
      let (next, stepHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules loopCtx current
      if stepHits.isEmpty then
        (current, iterations, allHits)
      else
        runPatchPassLoop config scope fuel' orderedExprRules orderedStmtRules orderedBlockRules next (iterations + 1) (allHits ++ stepHits)

private def rewriteObjectOnce
    (config : PatchPassConfig)
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (orderedObjectRules : List ObjectPatchRule)
    (iteration : Nat)
    (obj : YulObject) : YulObject × List String :=
  let deployCtx : RewriteCtx :=
    { scope := .deploy
      passPhase := config.passPhase
      iteration := iteration
      packId := config.packId }
  let runtimeCtx : RewriteCtx :=
    { scope := .runtime
      passPhase := config.passPhase
      iteration := iteration
      packId := config.packId }
  let objectCtx : RewriteCtx :=
    { scope := .object
      passPhase := config.passPhase
      iteration := iteration
      packId := config.packId }
  let (deployCode', deployHits) :=
    rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules deployCtx obj.deployCode
  let (runtimeCode', runtimeHits) :=
    rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules runtimeCtx obj.runtimeCode
  let candidate := { obj with deployCode := deployCode', runtimeCode := runtimeCode' }
  let (afterObjectRules, objectHits) := applyAllObjectRulesOnce orderedObjectRules objectCtx candidate
  (afterObjectRules, deployHits ++ runtimeHits ++ objectHits)

private def runObjectPatchPassLoop
    (config : PatchPassConfig)
    (fuel : Nat)
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (orderedObjectRules : List ObjectPatchRule)
    (current : YulObject)
    (iterations : Nat)
    (allHits : List String) : YulObject × Nat × List String :=
  match fuel with
  | 0 => (current, iterations, allHits)
  | Nat.succ fuel' =>
      let (next, stepHits) :=
        rewriteObjectOnce config orderedExprRules orderedStmtRules orderedBlockRules orderedObjectRules iterations current
      if stepHits.isEmpty then
        (current, iterations, allHits)
      else
        runObjectPatchPassLoop
          config
          fuel'
          orderedExprRules
          orderedStmtRules
          orderedBlockRules
          orderedObjectRules
          next
          (iterations + 1)
          (allHits ++ stepHits)

/-- Run one deterministic patch pass over expression/statement/block rules with bounded fixpoint iterations.
    The pass defaults to runtime scope but can target deploy scope explicitly. -/
def runPatchPassWithBlocks
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (stmts : List YulStmt)
    (scope : RewriteScope := .runtime) : PatchPassReport :=
  if ¬config.enabled then
    { patched := stmts, iterations := 0, manifest := [] }
  else
    let orderedExprRules :=
      orderRulesByPriority
        (exprRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedStmtRules :=
      orderStmtRulesByPriority
        (stmtRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedBlockRules :=
      orderBlockRulesByPriority
        (blockRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let ruleMeta := metaListFromRules orderedExprRules orderedStmtRules orderedBlockRules []
    let (patched, iterations, hits) :=
      runPatchPassLoop config scope config.maxIterations orderedExprRules orderedStmtRules orderedBlockRules stmts 0 []
    { patched := patched
      iterations := iterations
      manifest := manifestFromHits ruleMeta hits }

/-- Run one deterministic patch pass over a full Yul object with bounded fixpoint iterations. -/
def runPatchPassWithObjects
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (objectRules : List ObjectPatchRule)
    (obj : YulObject) : ObjectPatchPassReport :=
  if ¬config.enabled then
    { patched := obj, iterations := 0, manifest := [] }
  else
    let orderedExprRules :=
      orderRulesByPriority
        (exprRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedStmtRules :=
      orderStmtRulesByPriority
        (stmtRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedBlockRules :=
      orderBlockRulesByPriority
        (blockRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedObjectRules :=
      orderObjectRulesByPriority
        (objectRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let ruleMeta := metaListFromRules orderedExprRules orderedStmtRules orderedBlockRules orderedObjectRules
    let (patched, iterations, hits) :=
      runObjectPatchPassLoop
        config
        config.maxIterations
        orderedExprRules
        orderedStmtRules
        orderedBlockRules
        orderedObjectRules
        obj
        0
        []
    { patched := patched
      iterations := iterations
      manifest := manifestFromHits ruleMeta hits }

/-- Run one deterministic patch pass over expression and statement rules with bounded fixpoint iterations.
    Defaults to runtime scope. -/
def runPatchPass
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (stmts : List YulStmt)
    (scope : RewriteScope := .runtime) : PatchPassReport :=
  runPatchPassWithBlocks config exprRules stmtRules [] stmts scope

/-- Run one deterministic expression patch pass on statements with bounded fixpoint iterations.
    Defaults to runtime scope. -/
def runExprPatchPass
    (config : PatchPassConfig)
    (rules : List ExprPatchRule)
    (stmts : List YulStmt)
    (scope : RewriteScope := .runtime) : PatchPassReport :=
  runPatchPassWithBlocks config rules [] [] stmts scope

/-- Run one deterministic patch pass over a full Yul object with expression/statement/block rules. -/
def runPatchPassOnObject
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (obj : YulObject) : ObjectPatchPassReport :=
  runPatchPassWithObjects config exprRules stmtRules blockRules [] obj

open Lean (Name)

/-- Unified Yul patch rule sum type spanning expression, statement, block, and object rewrites. -/
inductive PatchRule where
  | expr (rule : ExprPatchRule)
  | stmt (rule : StmtPatchRule)
  | block (rule : BlockPatchRule)
  | object (rule : ObjectPatchRule)

instance : Coe ExprPatchRule PatchRule := ⟨PatchRule.expr⟩
instance : Coe StmtPatchRule PatchRule := ⟨PatchRule.stmt⟩
instance : Coe BlockPatchRule PatchRule := ⟨PatchRule.block⟩
instance : Coe ObjectPatchRule PatchRule := ⟨PatchRule.object⟩

/-- Underlying patch name of a unified `PatchRule`. -/
def PatchRule.patchName : PatchRule → String
  | .expr r => r.patchName
  | .stmt r => r.patchName
  | .block r => r.patchName
  | .object r => r.patchName

/-- Underlying kernel proof reference of a unified `PatchRule`. -/
def PatchRule.proofId : PatchRule → Name
  | .expr r => r.proofId
  | .stmt r => r.proofId
  | .block r => r.proofId
  | .object r => r.proofId

/-- Fail-closed auditability check for a unified `PatchRule`. -/
def PatchRule.isAuditable : PatchRule → Bool
  | .expr r => r.isAuditable
  | .stmt r => r.isAuditable
  | .block r => r.isAuditable
  | .object r => r.isAuditable

/-- Lightweight descriptor coupling a `ShimArena`-certified compiler runtime shim
with its kernel proof reference, verified per-call gas savings, and executable
`PatchRule` for direct registration as a `PatchPass` in the Yul pipeline. -/
structure VerifiedShimPatchDescriptor where
  shimName : String
  proofRef : Name
  gasSavedPerCall : Nat
  rule : PatchRule

/-- Fail-closed check ensuring a `VerifiedShimPatchDescriptor` has a non-empty name,
a non-anonymous proof reference matching its underlying rule, and an auditable rule. -/
def VerifiedShimPatchDescriptor.isAuditable (d : VerifiedShimPatchDescriptor) : Bool :=
  !d.shimName.isEmpty &&
    proofRefPresent d.proofRef &&
    d.rule.isAuditable &&
    d.rule.proofId == d.proofRef

/-- Partition a list of unified `PatchRule`s into typed rule lists for pass execution. -/
def partitionPatchRules
    (rules : List PatchRule) :
    List ExprPatchRule × List StmtPatchRule × List BlockPatchRule × List ObjectPatchRule :=
  rules.foldr
    (fun rule (exprs, stmts, blocks, objs) =>
      match rule with
      | .expr r => (r :: exprs, stmts, blocks, objs)
      | .stmt r => (exprs, r :: stmts, blocks, objs)
      | .block r => (exprs, stmts, r :: blocks, objs)
      | .object r => (exprs, stmts, blocks, r :: objs))
    ([], [], [], [])

/-- Register verified shim descriptors into a `PatchPassConfig`'s proof allowlist. -/
def registerVerifiedShimDescriptors
    (config : PatchPassConfig)
    (descriptors : List VerifiedShimPatchDescriptor) : PatchPassConfig :=
  let validRefs :=
    (descriptors.filter VerifiedShimPatchDescriptor.isAuditable).map (·.proofRef)
  let mergedRefs :=
    validRefs.foldl
      (fun acc ref => if acc.any (· = ref) then acc else acc ++ [ref])
      config.requiredProofRefs
  { config with requiredProofRefs := mergedRefs }

/-- Execute a deterministic Yul `PatchPass` over statements using `ShimArena`-certified
`VerifiedShimPatchDescriptor`s. -/
def runVerifiedShimPatchPass
    (config : PatchPassConfig)
    (descriptors : List VerifiedShimPatchDescriptor)
    (stmts : List YulStmt)
    (scope : RewriteScope := .runtime) : PatchPassReport :=
  let auditable := descriptors.filter VerifiedShimPatchDescriptor.isAuditable
  let (exprRules, stmtRules, blockRules, _) := partitionPatchRules (auditable.map (·.rule))
  let config' := registerVerifiedShimDescriptors config auditable
  runPatchPassWithBlocks config' exprRules stmtRules blockRules stmts scope

/-- Execute a deterministic Yul `PatchPass` over a full `YulObject` using `ShimArena`-certified
`VerifiedShimPatchDescriptor`s. -/
def runVerifiedShimObjectPatchPass
    (config : PatchPassConfig)
    (descriptors : List VerifiedShimPatchDescriptor)
    (obj : YulObject) : ObjectPatchPassReport :=
  let auditable := descriptors.filter VerifiedShimPatchDescriptor.isAuditable
  let (exprRules, stmtRules, blockRules, objectRules) :=
    partitionPatchRules (auditable.map (·.rule))
  let config' := registerVerifiedShimDescriptors config auditable
  runPatchPassWithObjects config' exprRules stmtRules blockRules objectRules obj

/-! ## Unified Parametric Certified Patch Rule Framework -/

/-- Typeclass for AST node types that support single-step rewrite traversal. -/
class Rewritable (α : Type) where
  /-- Apply a counted rewrite step `(α → α × Nat)` across immediate child nodes. -/
  rewriteChildren : (α → α × Nat) → α → α × Nat

instance : Rewritable YulExpr where
  rewriteChildren step
    | .call func args =>
        let (args', count) :=
          args.foldr
            (fun arg (accArgs, accCount) =>
              let (arg', c) := step arg
              (arg' :: accArgs, accCount + c))
            ([], 0)
        (.call func args', count)
    | expr => (expr, 0)

instance : Rewritable YulStmt where
  rewriteChildren step
    | .block stmts =>
        let (stmts', count) :=
          stmts.foldr
            (fun s (accStmts, accCount) =>
              let (s', c) := step s
              (s' :: accStmts, accCount + c))
            ([], 0)
        (.block stmts', count)
    | stmt => (stmt, 0)

instance : Rewritable (List YulStmt) where
  rewriteChildren step stmts :=
    match stmts with
    | [] => ([], 0)
    | hd :: tl =>
        let (tl', count) := step tl
        (hd :: tl', count)

instance : Rewritable YulObject where
  rewriteChildren step obj := step obj

/-- Parametric certified patch rule bundling an executable rewrite on AST node type `α`,
its proven static gas delta (`≤ 0` for gas-reducing optimizations), a semantic denotation
`denote : α → Sem`, and a proof that every successful rewrite preserves `denote`. -/
structure CertifiedPatchRule (α : Type) (Sem : Type) where
  patchName : String
  proofId : Name
  rewrite : α → Option α
  gasDelta : Int
  denote : α → Sem
  sound : ∀ (x x' : α), rewrite x = some x' → denote x' = denote x

/-- Apply a certified patch rule when `enabled = true`, returning the (possibly rewritten)
node together with the match count (`0` or `1`). -/
def CertifiedPatchRule.apply {α Sem : Type}
    (r : CertifiedPatchRule α Sem) (enabled : Bool) (x : α) : α × Nat :=
  if enabled then
    match r.rewrite x with
    | some x' => (x', 1)
    | none => (x, 0)
  else
    (x, 0)

/-- Applying a `CertifiedPatchRule` preserves its semantic denotation for any `enabled` flag
and input node `x`. -/
theorem CertifiedPatchRule.apply_sound {α Sem : Type}
    (r : CertifiedPatchRule α Sem) (enabled : Bool) (x : α) :
    r.denote (r.apply enabled x).1 = r.denote x := by
  unfold CertifiedPatchRule.apply
  cases enabled with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    cases h : r.rewrite x with
    | none => rfl
    | some x' => exact r.sound x x' h

/-- Applying a single `CertifiedPatchRule` produces a match count of at most `1`. -/
theorem CertifiedPatchRule.apply_matchCount_le_one {α Sem : Type}
    (r : CertifiedPatchRule α Sem) (enabled : Bool) (x : α) :
    (r.apply enabled x).2 ≤ 1 := by
  unfold CertifiedPatchRule.apply
  cases enabled with
  | false => exact Nat.zero_le 1
  | true =>
    simp only [↓reduceIte]
    cases r.rewrite x with
    | none => exact Nat.zero_le 1
    | some _ => exact Nat.le_refl 1

/-- Fold a list of certified patch rules sequentially over an AST node `x`,
accumulating total match counts starting from `initMatches`. -/
def CertifiedPatchRule.applyList {α Sem : Type}
    (rules : List (CertifiedPatchRule α Sem)) (enabled : Bool) (x : α)
    (initMatches : Nat := 0) : α × Nat :=
  rules.foldl
    (fun (acc : α × Nat) r =>
      let res := r.apply enabled acc.1
      (res.1, acc.2 + res.2))
    (x, initMatches)

/-- Folding a list of `CertifiedPatchRule`s sharing semantic denotation `denote`
preserves `denote` by induction on the rule list. -/
theorem CertifiedPatchRule.applyList_sound {α Sem : Type} (denote : α → Sem)
    (rules : List <| CertifiedPatchRule α Sem) (enabled : Bool) (x : α) (initMatches : Nat)
    (hDenote : ∀ r ∈ rules, r.denote = denote) :
    denote (CertifiedPatchRule.applyList rules enabled x initMatches).1 = denote x := by
  induction rules generalizing x initMatches with
  | nil => rfl
  | cons r rs ih =>
    simp only [CertifiedPatchRule.applyList, List.foldl_cons]
    have hrDenote : r.denote = denote := hDenote r (List.mem_cons_self ..)
    have hrsDenote : ∀ r' ∈ rs, r'.denote = denote := by
      intro r' hr'
      exact hDenote r' (List.mem_cons_of_mem r hr')
    have hStep := ih (r.apply enabled x).1 (initMatches + (r.apply enabled x).2) hrsDenote
    unfold CertifiedPatchRule.applyList at hStep
    rw [hStep, ← hrDenote]
    exact r.apply_sound enabled x

/-- Embed an `ExprPatchRule` at a given `RewriteCtx` into `CertifiedPatchRule YulExpr Sem`. -/
def ExprPatchRule.toCertified {Sem : Type}
    (r : ExprPatchRule)
    (ctx : RewriteCtx)
    (denote : YulExpr → Sem)
    (sound : ∀ (x x' : YulExpr), r.applyExpr ctx x = some x' → denote x' = denote x)
    (gasDelta : Int := 0) : CertifiedPatchRule YulExpr Sem where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.applyExpr ctx
  gasDelta := gasDelta
  denote := denote
  sound := sound

/-- Embed a `StmtPatchRule` at a given `RewriteCtx` into `CertifiedPatchRule YulStmt Sem`. -/
def StmtPatchRule.toCertified {Sem : Type}
    (r : StmtPatchRule)
    (ctx : RewriteCtx)
    (denote : YulStmt → Sem)
    (sound : ∀ (x x' : YulStmt), r.applyStmt ctx x = some x' → denote x' = denote x)
    (gasDelta : Int := 0) : CertifiedPatchRule YulStmt Sem where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.applyStmt ctx
  gasDelta := gasDelta
  denote := denote
  sound := sound

/-- Embed a `BlockPatchRule` at a given `RewriteCtx` into `CertifiedPatchRule (List YulStmt) Sem`. -/
def BlockPatchRule.toCertified {Sem : Type}
    (r : BlockPatchRule)
    (ctx : RewriteCtx)
    (denote : List YulStmt → Sem)
    (sound : ∀ (x x' : List YulStmt), r.applyBlock ctx x = some x' → denote x' = denote x)
    (gasDelta : Int := 0) : CertifiedPatchRule (List YulStmt) Sem where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.applyBlock ctx
  gasDelta := gasDelta
  denote := denote
  sound := sound

/-- Embed an `ObjectPatchRule` at a given `RewriteCtx` into `CertifiedPatchRule YulObject Sem`. -/
def ObjectPatchRule.toCertified {Sem : Type}
    (r : ObjectPatchRule)
    (ctx : RewriteCtx)
    (denote : YulObject → Sem)
    (sound : ∀ (x x' : YulObject), r.applyObject ctx x = some x' → denote x' = denote x)
    (gasDelta : Int := 0) : CertifiedPatchRule YulObject Sem where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.applyObject ctx
  gasDelta := gasDelta
  denote := denote
  sound := sound

/-- Bridge soundness for `ExprPatchRule.toCertified`: applying the embedded rule preserves `denote`. -/
theorem ExprPatchRule.toCertified_apply_sound {Sem : Type}
    (r : ExprPatchRule) (ctx : RewriteCtx) (denote : YulExpr → Sem)
    (sound : ∀ (x x' : YulExpr), r.applyExpr ctx x = some x' → denote x' = denote x)
    (gasDelta : Int) (enabled : Bool) (x : YulExpr) :
    denote ((r.toCertified ctx denote sound gasDelta).apply enabled x).1 = denote x :=
  (r.toCertified ctx denote sound gasDelta).apply_sound enabled x

/-- Bridge soundness for `StmtPatchRule.toCertified`: applying the embedded rule preserves `denote`. -/
theorem StmtPatchRule.toCertified_apply_sound {Sem : Type}
    (r : StmtPatchRule) (ctx : RewriteCtx) (denote : YulStmt → Sem)
    (sound : ∀ (x x' : YulStmt), r.applyStmt ctx x = some x' → denote x' = denote x)
    (gasDelta : Int) (enabled : Bool) (x : YulStmt) :
    denote ((r.toCertified ctx denote sound gasDelta).apply enabled x).1 = denote x :=
  (r.toCertified ctx denote sound gasDelta).apply_sound enabled x

/-- Bridge soundness for `BlockPatchRule.toCertified`: applying the embedded rule preserves `denote`. -/
theorem BlockPatchRule.toCertified_apply_sound {Sem : Type}
    (r : BlockPatchRule) (ctx : RewriteCtx) (denote : List YulStmt → Sem)
    (sound : ∀ x x', r.applyBlock ctx x = some x' → denote x' = denote x)
    (gasDelta : Int) (enabled : Bool) (x : List YulStmt) :
    denote ((r.toCertified ctx denote sound gasDelta).apply enabled x).1 = denote x :=
  (r.toCertified ctx denote sound gasDelta).apply_sound enabled x

/-- Bridge soundness for `ObjectPatchRule.toCertified`: applying the embedded rule preserves `denote`. -/
theorem ObjectPatchRule.toCertified_apply_sound {Sem : Type}
    (r : ObjectPatchRule) (ctx : RewriteCtx) (denote : YulObject → Sem)
    (sound : ∀ x x', r.applyObject ctx x = some x' → denote x' = denote x)
    (gasDelta : Int) (enabled : Bool) (x : YulObject) :
    denote ((r.toCertified ctx denote sound gasDelta).apply enabled x).1 = denote x :=
  (r.toCertified ctx denote sound gasDelta).apply_sound enabled x

/-! ## Denotation-Indexed Certified Rules, Sequential Packs, and Lifted List Passes -/

/-- Certified patch rule indexed by a fixed semantic denotation `denote : α → Sem`,
enabling direct composition of rules and rule packs without side-conditions on denotation equality. -/
structure CertifiedRuleOn {α Sem : Type} (denote : α → Sem) where
  patchName : String
  proofId : Name
  rewrite : α → Option α
  gasDelta : Int
  sound : ∀ (x x' : α), rewrite x = some x' → denote x' = denote x

/-- Embed a `CertifiedPatchRule α Sem` into `CertifiedRuleOn denote` when its denotation matches `denote`. -/
def CertifiedRuleOn.ofRule {α Sem : Type} {denote : α → Sem}
    (r : CertifiedPatchRule α Sem) (hDenote : r.denote = denote := by rfl) :
    CertifiedRuleOn denote where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.rewrite
  gasDelta := r.gasDelta
  sound := by
    intro x x' h
    rw [← hDenote]
    exact r.sound x x' h

/-- Forget the index and project a `CertifiedRuleOn denote` to `CertifiedPatchRule α Sem`. -/
def CertifiedRuleOn.toRule {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) : CertifiedPatchRule α Sem where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.rewrite
  gasDelta := r.gasDelta
  denote := denote
  sound := r.sound

/-- Apply a `CertifiedRuleOn denote` when `enabled = true`, returning the (possibly rewritten)
node together with the match count (`0` or `1`). -/
def CertifiedRuleOn.apply {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (enabled : Bool) (x : α) : α × Nat :=
  if enabled then
    match r.rewrite x with
    | some x' => (x', 1)
    | none => (x, 0)
  else
    (x, 0)

/-- Applying a `CertifiedRuleOn denote` preserves `denote` for any `enabled` flag and input `x`. -/
theorem CertifiedRuleOn.apply_sound {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (enabled : Bool) (x : α) :
    denote (r.apply enabled x).1 = denote x := by
  unfold CertifiedRuleOn.apply
  cases enabled with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    cases h : r.rewrite x with
    | none => rfl
    | some x' => exact r.sound x x' h

/-- When disabled (`enabled = false`), `CertifiedRuleOn.apply` returns the input term unchanged. -/
theorem CertifiedRuleOn.apply_disabled_fst {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (x : α) :
    (r.apply false x).1 = x := by
  rfl

/-- When disabled (`enabled = false`), `CertifiedRuleOn.apply` reports zero matches. -/
theorem CertifiedRuleOn.apply_disabled_matches {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (x : α) :
    (r.apply false x).2 = 0 := by
  rfl

/-- Sequential composition of two `CertifiedRuleOn denote` rules over the same semantic denotation:
applies `r₁` if it matches (and then optionally `r₂` on the result), or falls back to `r₂`. -/
def CertifiedRuleOn.seq {α Sem : Type} {denote : α → Sem}
    (r₁ r₂ : CertifiedRuleOn denote) : CertifiedRuleOn denote where
  patchName := r₁.patchName ++ "_seq_" ++ r₂.patchName
  proofId := r₁.proofId
  rewrite := fun x =>
    match r₁.rewrite x with
    | some x₁ =>
        match r₂.rewrite x₁ with
        | some x₂ => some x₂
        | none => some x₁
    | none => r₂.rewrite x
  gasDelta := r₁.gasDelta + r₂.gasDelta
  sound := by
    intro x x' h
    cases h₁ : r₁.rewrite x with
    | none =>
      rw [h₁] at h
      exact r₂.sound x x' h
    | some x₁ =>
      cases h₂ : r₂.rewrite x₁ with
      | none =>
        simp only [h₁, h₂] at h
        injection h with hEq
        rw [← hEq]
        exact r₁.sound x x₁ h₁
      | some x₂ =>
        simp only [h₁, h₂] at h
        injection h with hEq
        rw [← hEq]
        rw [r₂.sound x₁ x₂ h₂]
        exact r₁.sound x x₁ h₁

/-- Applying a sequentially composed rule `r₁.seq r₂` preserves `denote`. -/
theorem CertifiedRuleOn.seq_apply_sound {α Sem : Type} {denote : α → Sem}
    (r₁ r₂ : CertifiedRuleOn denote) (enabled : Bool) (x : α) :
    denote ((r₁.seq r₂).apply enabled x).1 = denote x :=
  (r₁.seq r₂).apply_sound enabled x

/-- A sequential pack of `CertifiedRuleOn denote` rules sharing a fixed denotation `denote : α → Sem`. -/
abbrev CertifiedRuleOnPack {α Sem : Type} (denote : α → Sem) :=
  List (CertifiedRuleOn denote)

/-- Execute a `CertifiedRuleOnPack` sequentially on `x`, returning the rewritten term,
cumulative match count, and cumulative static gas delta across all matched rules. -/
def applyPack {α Sem : Type} {denote : α → Sem}
    (enabled : Bool) (pack : List <| CertifiedRuleOn denote) (x : α) : α × Nat × Int :=
  match pack with
  | [] => (x, 0, 0)
  | r :: rs =>
      let res₁ := r.apply enabled x
      let g₁ : Int := if res₁.2 == 0 then 0 else r.gasDelta
      let res₂ := applyPack enabled rs res₁.1
      (res₂.1, res₁.2 + res₂.2.1, g₁ + res₂.2.2)

/-- Applying an empty `CertifiedRuleOnPack` returns `(x, 0, 0)`. -/
theorem applyPack_nil {α Sem : Type} {denote : α → Sem}
    (enabled : Bool) (x : α) :
    applyPack (denote := denote) enabled [] x = (x, 0, 0) := by
  rfl

/-- Unfolding lemma for `applyPack` on a non-empty rule pack `r :: rs`. -/
theorem applyPack_cons {α Sem : Type} {denote : α → Sem}
    (enabled : Bool) (r : CertifiedRuleOn denote) (rs : List <| CertifiedRuleOn denote) (x : α) :
    applyPack enabled (r :: rs) x =
      let res₁ := r.apply enabled x
      let g₁ : Int := if res₁.2 == 0 then 0 else r.gasDelta
      let res₂ := applyPack enabled rs res₁.1
      (res₂.1, res₁.2 + res₂.2.1, g₁ + res₂.2.2) := by
  rfl

/-- When disabled (`enabled = false`), `applyPack` leaves the input term `x` unchanged. -/
theorem applyPack_disabled_fst {α Sem : Type} {denote : α → Sem}
    (pack : List <| CertifiedRuleOn denote) (x : α) :
    (applyPack false pack x).1 = x := by
  induction pack generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [applyPack, CertifiedRuleOn.apply_disabled_fst]
    exact ih x

/-- Applying any `CertifiedRuleOnPack` preserves the shared semantic denotation `denote`. -/
theorem applyPack_sound {α Sem : Type} {denote : α → Sem}
    (enabled : Bool) (pack : List <| CertifiedRuleOn denote) (x : α) :
    denote (applyPack enabled pack x).1 = denote x := by
  induction pack generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [applyPack]
    rw [ih (r.apply enabled x).1]
    exact r.apply_sound enabled x

/-- The rewritten term produced by `applyPack` over `p₁ ++ p₂` equals running `p₁` then `p₂`. -/
theorem applyPack_append_fst {α Sem : Type} {denote : α → Sem}
    (enabled : Bool) (p₁ p₂ : List <| CertifiedRuleOn denote) (x : α) :
    (applyPack enabled (p₁ ++ p₂) x).1 =
      (applyPack enabled p₂ (applyPack enabled p₁ x).1).1 := by
  induction p₁ generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.cons_append, applyPack]
    exact ih (r.apply enabled x).1

/-- Apply a `CertifiedRuleOn denote` elementwise across `xs : List α`,
accumulating total match counts across all list elements. -/
def CertifiedRuleOn.applyList {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (enabled : Bool) (xs : List α) : List α × Nat :=
  match xs with
  | [] => ([], 0)
  | x :: rest =>
      let (x', m₁) := r.apply enabled x
      let (rest', m₂) := r.applyList enabled rest
      (x' :: rest', m₁ + m₂)

/-- Elementwise application `CertifiedRuleOn.applyList` preserves `List.map denote`. -/
theorem CertifiedRuleOn.applyList_map_denote_eq {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (enabled : Bool) (xs : List α) :
    List.map denote (r.applyList enabled xs).1 = List.map denote xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [CertifiedRuleOn.applyList, List.map_cons]
    rw [r.apply_sound enabled x, ih]

/-- When disabled (`enabled = false`), `CertifiedRuleOn.applyList` returns the list unchanged. -/
theorem CertifiedRuleOn.applyList_disabled_fst {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (xs : List α) :
    (r.applyList false xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [CertifiedRuleOn.applyList, CertifiedRuleOn.apply_disabled_fst, ih]

/-- Lift a node-level `CertifiedRuleOn denote` to a list-level `CertifiedRuleOn (List.map denote)`
that rewrites `List α` elementwise. -/
def CertifiedRuleOn.liftList {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) : CertifiedRuleOn (List.map denote) where
  patchName := r.patchName ++ "_list"
  proofId := r.proofId
  rewrite := fun xs => some (r.applyList true xs).1
  gasDelta := r.gasDelta
  sound := by
    intro xs xs' h
    injection h with hEq
    rw [← hEq]
    exact r.applyList_map_denote_eq true xs

/-- Applying a lifted list rule `r.liftList` preserves `List.map denote`. -/
theorem CertifiedRuleOn.liftList_apply_sound {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleOn denote) (enabled : Bool) (xs : List α) :
    List.map denote ((r.liftList).apply enabled xs).1 = List.map denote xs :=
  (r.liftList).apply_sound enabled xs

/-! ## Algebraic Composition and Certified Patch Packs (`CertifiedRuleFor` / `CertifiedPatchPack`) -/

/-- When `enabled = false`, applying a `CertifiedPatchRule` returns the original node and `0` matches. -/
theorem CertifiedPatchRule.apply_disabled {α Sem : Type}
    (r : CertifiedPatchRule α Sem) (x : α) :
    r.apply false x = (x, 0) := by
  unfold CertifiedPatchRule.apply
  rfl

/-- Sequential composition of two `CertifiedPatchRule`s sharing the same semantic denotation
(`hDenote : r₂.denote = r₁.denote`), summing their static `gasDelta`s. -/
def CertifiedPatchRule.comp {α Sem : Type}
    (r₁ r₂ : CertifiedPatchRule α Sem)
    (hDenote : r₂.denote = r₁.denote) : CertifiedPatchRule α Sem where
  patchName := r₁.patchName ++ "+" ++ r₂.patchName
  proofId := r₁.proofId ++ r₂.proofId
  rewrite := fun x =>
    match r₁.rewrite x with
    | some x₁ =>
      match r₂.rewrite x₁ with
      | some x₂ => some x₂
      | none => some x₁
    | none => r₂.rewrite x
  gasDelta := r₁.gasDelta + r₂.gasDelta
  denote := r₁.denote
  sound := by
    intro x x' hRewrite
    cases h₁ : r₁.rewrite x with
    | some x₁ =>
      rw [h₁] at hRewrite
      dsimp only at hRewrite
      cases h₂ : r₂.rewrite x₁ with
      | some x₂ =>
        rw [h₂] at hRewrite
        injection hRewrite with hEq
        subst hEq
        have hs₁ : r₁.denote x₁ = r₁.denote x := r₁.sound x x₁ h₁
        have hs₂ : r₂.denote x₂ = r₂.denote x₁ := r₂.sound x₁ x₂ h₂
        rw [hDenote] at hs₂
        rw [hs₂, hs₁]
      | none =>
        rw [h₂] at hRewrite
        injection hRewrite with hEq
        subst hEq
        exact r₁.sound x x₁ h₁
    | none =>
      rw [h₁] at hRewrite
      have hs₂ : r₂.denote x' = r₂.denote x := r₂.sound x x' hRewrite
      rw [hDenote] at hs₂
      exact hs₂

/-- Applying the sequential composition `r₁.comp r₂ hDenote` preserves `r₁.denote`. -/
theorem CertifiedPatchRule.comp_apply_sound {α Sem : Type}
    (r₁ r₂ : CertifiedPatchRule α Sem)
    (hDenote : r₂.denote = r₁.denote)
    (enabled : Bool) (x : α) :
    r₁.denote ((r₁.comp r₂ hDenote).apply enabled x).1 = r₁.denote x :=
  (r₁.comp r₂ hDenote).apply_sound enabled x

/-- When disabled (`enabled = false`), a composed `CertifiedPatchRule` returns `(x, 0)`. -/
theorem CertifiedPatchRule.comp_disabled {α Sem : Type}
    (r₁ r₂ : CertifiedPatchRule α Sem)
    (hDenote : r₂.denote = r₁.denote) (x : α) :
    (r₁.comp r₂ hDenote).apply false x = (x, 0) :=
  (r₁.comp r₂ hDenote).apply_disabled x

/-- Certified patch rule parameterized directly by a fixed semantic denotation `denote : α → Sem`,
so all rules in a pack share the same denotation by construction. -/
structure CertifiedRuleFor {α Sem : Type} (denote : α → Sem) where
  patchName : String
  proofId : Name
  rewrite : α → Option α
  gasDelta : Int
  sound : ∀ (x x' : α), rewrite x = some x' → denote x' = denote x

/-- Project a `CertifiedPatchRule α Sem` into `CertifiedRuleFor r.denote`. -/
def CertifiedPatchRule.toCertifiedRuleFor {α Sem : Type}
    (r : CertifiedPatchRule α Sem) : CertifiedRuleFor r.denote where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.rewrite
  gasDelta := r.gasDelta
  sound := r.sound

/-- Embed a `CertifiedRuleFor denote` into `CertifiedPatchRule α Sem`. -/
def CertifiedRuleFor.toCertifiedPatchRule {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleFor denote) : CertifiedPatchRule α Sem where
  patchName := r.patchName
  proofId := r.proofId
  rewrite := r.rewrite
  gasDelta := r.gasDelta
  denote := denote
  sound := r.sound

/-- Apply a `CertifiedRuleFor denote` when `enabled = true`, returning the (possibly rewritten)
node together with the match count (`0` or `1`). -/
def CertifiedRuleFor.apply {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleFor denote) (enabled : Bool) (x : α) : α × Nat :=
  if enabled then
    match r.rewrite x with
    | some x' => (x', 1)
    | none => (x, 0)
  else
    (x, 0)

/-- Applying a `CertifiedRuleFor denote` preserves `denote` for any `enabled` flag and node `x`. -/
theorem CertifiedRuleFor.apply_sound {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleFor denote) (enabled : Bool) (x : α) :
    denote (r.apply enabled x).1 = denote x := by
  unfold CertifiedRuleFor.apply
  cases enabled with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    cases h : r.rewrite x with
    | none => rfl
    | some x' => exact r.sound x x' h

/-- When `enabled = false`, applying a `CertifiedRuleFor denote` returns `(x, 0)`. -/
theorem CertifiedRuleFor.apply_disabled {α Sem : Type} {denote : α → Sem}
    (r : CertifiedRuleFor denote) (x : α) :
    r.apply false x = (x, 0) := by
  unfold CertifiedRuleFor.apply
  rfl

/-- Sequential composition of two `CertifiedRuleFor denote` rules sharing `denote` by construction. -/
def CertifiedRuleFor.comp {α Sem : Type} {denote : α → Sem}
    (r₁ r₂ : CertifiedRuleFor denote) : CertifiedRuleFor denote where
  patchName := r₁.patchName ++ "+" ++ r₂.patchName
  proofId := r₁.proofId ++ r₂.proofId
  rewrite := fun x =>
    match r₁.rewrite x with
    | some x₁ =>
      match r₂.rewrite x₁ with
      | some x₂ => some x₂
      | none => some x₁
    | none => r₂.rewrite x
  gasDelta := r₁.gasDelta + r₂.gasDelta
  sound := by
    intro x x' hRewrite
    cases h₁ : r₁.rewrite x with
    | some x₁ =>
      rw [h₁] at hRewrite
      dsimp only at hRewrite
      cases h₂ : r₂.rewrite x₁ with
      | some x₂ =>
        rw [h₂] at hRewrite
        injection hRewrite with hEq
        subst hEq
        rw [r₂.sound x₁ x₂ h₂, r₁.sound x x₁ h₁]
      | none =>
        rw [h₂] at hRewrite
        injection hRewrite with hEq
        subst hEq
        exact r₁.sound x x₁ h₁
    | none =>
      rw [h₁] at hRewrite
      exact r₂.sound x x' hRewrite

/-- Composing two `CertifiedRuleFor denote` rules and applying the composite rule preserves `denote`. -/
theorem CertifiedRuleFor.comp_sound {α Sem : Type} {denote : α → Sem}
    (r₁ r₂ : CertifiedRuleFor denote) (enabled : Bool) (x : α) :
    denote ((r₁.comp r₂).apply enabled x).1 = denote x :=
  (r₁.comp r₂).apply_sound enabled x

/-- Sequential execution of a list of `CertifiedRuleFor denote` rules over `x`,
accumulating the match counts across the rule sequence. -/
def CertifiedRuleFor.applyRules {α Sem : Type} {denote : α → Sem}
    (enabled : Bool) : List (CertifiedRuleFor denote) → α → α × Nat
  | [], x => (x, 0)
  | r :: rs, x =>
      let step := r.apply enabled x
      let rest := CertifiedRuleFor.applyRules enabled rs step.1
      (rest.1, step.2 + rest.2)

/-- Pack of certified patch rules sharing a fixed semantic denotation `denote : α → Sem`. -/
structure CertifiedPatchPack {α Sem : Type} (denote : α → Sem) where
  packName : String
  rules : List (CertifiedRuleFor denote)

/-- Execute all rules in a `CertifiedPatchPack` sequentially on `x`. -/
def CertifiedPatchPack.apply {α Sem : Type} {denote : α → Sem}
    (pack : CertifiedPatchPack denote) (enabled : Bool) (x : α) : α × Nat :=
  CertifiedRuleFor.applyRules enabled pack.rules x

/-- Concatenate two `CertifiedPatchPack`s sharing the same semantic denotation `denote`. -/
def CertifiedPatchPack.append {α Sem : Type} {denote : α → Sem}
    (p₁ p₂ : CertifiedPatchPack denote) : CertifiedPatchPack denote where
  packName := p₁.packName ++ "+" ++ p₂.packName
  rules := p₁.rules ++ p₂.rules

instance {α Sem : Type} {denote : α → Sem} : Append (CertifiedPatchPack denote) where
  append := CertifiedPatchPack.append

/-- Applying an empty `CertifiedPatchPack` leaves the AST node unchanged with `0` matches. -/
theorem CertifiedPatchPack.apply_nil {α Sem : Type} {denote : α → Sem}
    (packName : String) (enabled : Bool) (x : α) :
    ({ packName := packName, rules := [] } : CertifiedPatchPack denote).apply enabled x = (x, 0) := by
  rfl

/-- Applying a `r :: rs` pack steps `r` first and then runs the remaining `rs` pack on the resulting node. -/
theorem CertifiedPatchPack.apply_cons {α Sem : Type} {denote : α → Sem}
    (packName : String) (r : CertifiedRuleFor denote) (rs : List <| CertifiedRuleFor denote)
    (enabled : Bool) (x : α) :
    ({ packName := packName, rules := r :: rs } : CertifiedPatchPack denote).apply enabled x =
      let step := r.apply enabled x
      let rest := ({ packName := packName, rules := rs } : CertifiedPatchPack denote).apply enabled step.1
      (rest.1, step.2 + rest.2) := by
  rfl

/-- Helper: running `CertifiedRuleFor.applyRules` with `enabled = false` returns `(x, 0)`. -/
theorem CertifiedRuleFor.applyRules_disabled {α Sem : Type} {denote : α → Sem}
    (rules : List <| CertifiedRuleFor denote) (x : α) :
    CertifiedRuleFor.applyRules false rules x = (x, 0) := by
  induction rules generalizing x with
  | nil =>
    unfold CertifiedRuleFor.applyRules
    rfl
  | cons r rs ih =>
    unfold CertifiedRuleFor.applyRules
    rw [r.apply_disabled x]
    dsimp only
    rw [ih x]
    rfl

/-- When disabled (`enabled = false`), applying any `CertifiedPatchPack` returns `(x, 0)`. -/
theorem CertifiedPatchPack.apply_disabled {α Sem : Type} {denote : α → Sem}
    (pack : CertifiedPatchPack denote) (x : α) :
    pack.apply false x = (x, 0) :=
  CertifiedRuleFor.applyRules_disabled pack.rules x

/-- Helper: `CertifiedRuleFor.applyRules` preserves `denote` across any list of certified rules. -/
theorem CertifiedRuleFor.applyRules_sound {α Sem : Type} {denote : α → Sem}
    (rules : List <| CertifiedRuleFor denote) (enabled : Bool) (x : α) :
    denote (CertifiedRuleFor.applyRules enabled rules x).1 = denote x := by
  induction rules generalizing x with
  | nil =>
    unfold CertifiedRuleFor.applyRules
    rfl
  | cons r rs ih =>
    unfold CertifiedRuleFor.applyRules
    dsimp only
    rw [ih (r.apply enabled x).1]
    exact r.apply_sound enabled x

/-- Applying any `CertifiedPatchPack` preserves its semantic denotation `denote`. -/
theorem CertifiedPatchPack.apply_sound {α Sem : Type} {denote : α → Sem}
    (pack : CertifiedPatchPack denote) (enabled : Bool) (x : α) :
    denote (pack.apply enabled x).1 = denote x :=
  CertifiedRuleFor.applyRules_sound pack.rules enabled x

/-- Helper: running `applyRules` over `rs₁ ++ rs₂` equals running `rs₁` and then `rs₂` on the result,
accumulating the match counts. -/
theorem CertifiedRuleFor.applyRules_append {α Sem : Type} {denote : α → Sem}
    (rs₁ rs₂ : List <| CertifiedRuleFor denote) (enabled : Bool) (x : α) :
    CertifiedRuleFor.applyRules enabled (rs₁ ++ rs₂) x =
      let step₁ := CertifiedRuleFor.applyRules enabled rs₁ x
      let step₂ := CertifiedRuleFor.applyRules enabled rs₂ step₁.1
      (step₂.1, step₁.2 + step₂.2) := by
  induction rs₁ generalizing x with
  | nil =>
    simp only [List.nil_append, CertifiedRuleFor.applyRules, Nat.zero_add]
  | cons r rs ih =>
    simp only [List.cons_append, CertifiedRuleFor.applyRules]
    rw [ih (r.apply enabled x).1]
    dsimp only
    rw [Nat.add_assoc]

/-- Running an appended pack `p₁ ++ p₂` equals running `p₁` and then `p₂` on the resulting AST node,
summing their match counts. -/
theorem CertifiedPatchPack.append_apply_eq {α Sem : Type} {denote : α → Sem}
    (p₁ p₂ : CertifiedPatchPack denote) (enabled : Bool) (x : α) :
    (p₁ ++ p₂).apply enabled x =
      let step₁ := p₁.apply enabled x
      let step₂ := p₂.apply enabled step₁.1
      (step₂.1, step₁.2 + step₂.2) :=
  CertifiedRuleFor.applyRules_append p₁.rules p₂.rules enabled x

end Compiler.Yul
