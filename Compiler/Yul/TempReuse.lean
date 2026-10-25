import Compiler.Yul.Ast
import Verity.Core.Model.Types

namespace Compiler.Yul.TempReuse

open Compiler.Yul
open Compiler.CompilationModel (UnsafeYulFragment)

/-- Default maximum number of Yul `let` bindings in a single lexical block before
    dead-temporary reuse and scratch-memory spilling activate. -/
def defaultMaxStackLocals : Nat := 12

/-- Dedicated scratch memory base offset (`0x1000`) used when spilling excess live
    temporaries above Verity's low scratch memory region (`0x00..0x200`). -/
def defaultSpillBase : Nat := 4096

/-- Count top-level `let` bindings in a single Yul lexical statement list. -/
def countLetBindings : List YulStmt → Nat
  | [] => 0
  | .let_ _ _ :: rest => 1 + countLetBindings rest
  | _ :: rest => countLetBindings rest

mutual
/-- Check whether an identifier `target` occurs in `YulExpr`. -/
def exprUsesIdent (target : String) : YulExpr → Bool
  | .lit _ | .hex _ | .str _ => false
  | .ident name => name == target
  | .call _ args => exprsUseIdent target args

/-- Check whether an identifier `target` occurs in a list of `YulExpr`. -/
def exprsUseIdent (target : String) : List YulExpr → Bool
  | [] => false
  | e :: es => exprUsesIdent target e || exprsUseIdent target es
end

mutual
/-- Check whether an identifier `target` is read anywhere in a `YulStmt`. -/
def stmtUsesIdent (target : String) : YulStmt → Bool
  | .comment _ | .leave => false
  | .let_ _ value | .letMany _ value | .assign _ value | .exprStmt value =>
      exprUsesIdent target value
  | .if_ cond body =>
      exprUsesIdent target cond || stmtsUseIdent target body
  | .for_ init cond post body =>
      stmtsUseIdent target init || exprUsesIdent target cond ||
        stmtsUseIdent target post || stmtsUseIdent target body
  | .switch expr cases default =>
      exprUsesIdent target expr ||
        casesUsesIdent target cases ||
        match default with
        | none => false
        | some body => stmtsUseIdent target body
  | .block stmts => stmtsUseIdent target stmts
  | .funcDef _ _ _ body => stmtsUseIdent target body

/-- Check whether an identifier `target` is read anywhere in a list of `YulStmt`. -/
def stmtsUseIdent (target : String) : List YulStmt → Bool
  | [] => false
  | s :: ss => stmtUsesIdent target s || stmtsUseIdent target ss

/-- Check whether an identifier `target` is read in switch cases. -/
def casesUsesIdent (target : String) : List (Nat × List YulStmt) → Bool
  | [] => false
  | (_, body) :: rest => stmtsUseIdent target body || casesUsesIdent target rest
end

mutual
/-- Check whether `target` is assigned or redeclared in a `YulStmt`. -/
def stmtAssignsIdent (target : String) : YulStmt → Bool
  | .comment _ | .exprStmt _ | .leave => false
  | .let_ name _ | .assign name _ => name == target
  | .letMany names _ => names.contains target
  | .if_ _ body | .block body => stmtsAssignIdent target body
  | .for_ init _ post body =>
      stmtsAssignIdent target init || stmtsAssignIdent target post || stmtsAssignIdent target body
  | .switch _ cases default =>
      casesAssignIdent target cases ||
        match default with
        | none => false
        | some body => stmtsAssignIdent target body
  | .funcDef _ params rets body =>
      params.contains target || rets.contains target || stmtsAssignIdent target body

/-- Check whether `target` is assigned or redeclared in a list of `YulStmt`. -/
def stmtsAssignIdent (target : String) : List YulStmt → Bool
  | [] => false
  | s :: ss => stmtAssignsIdent target s || stmtsAssignIdent target ss

/-- Check whether `target` is assigned or redeclared in switch cases. -/
def casesAssignIdent (target : String) : List (Nat × List YulStmt) → Bool
  | [] => false
  | (_, body) :: rest => stmtsAssignIdent target body || casesAssignIdent target rest
end

mutual
/-- Check whether `target` appears inside any nested `funcDef` in `YulStmt`. -/
def stmtFuncDefUsesIdent (target : String) : YulStmt → Bool
  | .comment _ | .let_ _ _ | .letMany _ _ | .assign _ _ | .exprStmt _ | .leave => false
  | .if_ _ body | .block body => stmtsFuncDefUsesIdent target body
  | .for_ init _ post body =>
      stmtsFuncDefUsesIdent target init || stmtsFuncDefUsesIdent target post ||
        stmtsFuncDefUsesIdent target body
  | .switch _ cases default =>
      casesFuncDefUsesIdent target cases ||
        match default with
        | none => false
        | some body => stmtsFuncDefUsesIdent target body
  | .funcDef _ params rets body =>
      params.contains target || rets.contains target ||
        stmtsUseIdent target body || stmtsAssignIdent target body

/-- Check whether `target` appears inside any nested `funcDef` in a list of `YulStmt`. -/
def stmtsFuncDefUsesIdent (target : String) : List YulStmt → Bool
  | [] => false
  | s :: ss => stmtFuncDefUsesIdent target s || stmtsFuncDefUsesIdent target ss

/-- Check whether `target` appears inside any nested `funcDef` in switch cases. -/
def casesFuncDefUsesIdent (target : String) : List (Nat × List YulStmt) → Bool
  | [] => false
  | (_, body) :: rest => stmtsFuncDefUsesIdent target body || casesFuncDefUsesIdent target rest
end

mutual
/-- Check whether `mload(slot)` occurs in a `YulExpr`. -/
def exprContainsMloadSlot (slot : Nat) : YulExpr → Bool
  | .lit _ | .hex _ | .str _ | .ident _ => false
  | .call func args =>
      (func == "mload" && args == [.lit slot]) || exprsContainMloadSlot slot args

/-- Check whether `mload(slot)` occurs in a list of `YulExpr`. -/
def exprsContainMloadSlot (slot : Nat) : List YulExpr → Bool
  | [] => false
  | e :: es => exprContainsMloadSlot slot e || exprsContainMloadSlot slot es
end

mutual
/-- Check whether `mload(slot)` occurs in a `YulStmt`. -/
def stmtContainsMloadSlot (slot : Nat) : YulStmt → Bool
  | .comment _ | .leave => false
  | .let_ _ value | .letMany _ value | .assign _ value | .exprStmt value =>
      exprContainsMloadSlot slot value
  | .if_ cond body =>
      exprContainsMloadSlot slot cond || stmtsContainMloadSlot slot body
  | .for_ init cond post body =>
      stmtsContainMloadSlot slot init || exprContainsMloadSlot slot cond ||
        stmtsContainMloadSlot slot post || stmtsContainMloadSlot slot body
  | .switch expr cases default =>
      exprContainsMloadSlot slot expr ||
        casesContainMloadSlot slot cases ||
        match default with
        | none => false
        | some body => stmtsContainMloadSlot slot body
  | .block stmts => stmtsContainMloadSlot slot stmts
  | .funcDef _ _ _ body => stmtsContainMloadSlot slot body

/-- Check whether `mload(slot)` occurs in a list of `YulStmt`. -/
def stmtsContainMloadSlot (slot : Nat) : List YulStmt → Bool
  | [] => false
  | s :: ss => stmtContainsMloadSlot slot s || stmtsContainMloadSlot slot ss

/-- Check whether `mload(slot)` occurs in switch cases. -/
def casesContainMloadSlot (slot : Nat) : List (Nat × List YulStmt) → Bool
  | [] => false
  | (_, body) :: rest => stmtsContainMloadSlot slot body || casesContainMloadSlot slot rest
end

mutual
/-- Substitute `replacement` for every `.ident oldName` in a `YulExpr`. -/
def replaceIdentInExpr (oldName : String) (replacement : YulExpr) : YulExpr → YulExpr
  | .lit n => .lit n
  | .hex n => .hex n
  | .str s => .str s
  | .ident name => if name == oldName then replacement else .ident name
  | .call func args => .call func (replaceIdentInExprs oldName replacement args)

/-- Substitute `replacement` for every `.ident oldName` in a list of `YulExpr`. -/
def replaceIdentInExprs (oldName : String) (replacement : YulExpr) : List YulExpr → List YulExpr
  | [] => []
  | e :: es => replaceIdentInExpr oldName replacement e :: replaceIdentInExprs oldName replacement es
end

mutual
/-- Substitute `replacement` for every `.ident oldName` in a `YulStmt`. -/
def replaceIdentInStmt (oldName : String) (replacement : YulExpr) : YulStmt → YulStmt
  | .comment text => .comment text
  | .let_ name value => .let_ name (replaceIdentInExpr oldName replacement value)
  | .letMany names value => .letMany names (replaceIdentInExpr oldName replacement value)
  | .assign name value => .assign name (replaceIdentInExpr oldName replacement value)
  | .exprStmt value => .exprStmt (replaceIdentInExpr oldName replacement value)
  | .leave => .leave
  | .if_ cond body =>
      .if_ (replaceIdentInExpr oldName replacement cond) (replaceIdentInStmts oldName replacement body)
  | .for_ init cond post body =>
      .for_
        (replaceIdentInStmts oldName replacement init)
        (replaceIdentInExpr oldName replacement cond)
        (replaceIdentInStmts oldName replacement post)
        (replaceIdentInStmts oldName replacement body)
  | .switch expr cases default =>
      .switch
        (replaceIdentInExpr oldName replacement expr)
        (replaceIdentInCases oldName replacement cases)
        (match default with
         | none => none
         | some body => some (replaceIdentInStmts oldName replacement body))
  | .block stmts => .block (replaceIdentInStmts oldName replacement stmts)
  | .funcDef name params rets body =>
      if params.contains oldName || rets.contains oldName then
        .funcDef name params rets body
      else
        .funcDef name params rets (replaceIdentInStmts oldName replacement body)

/-- Substitute `replacement` for every `.ident oldName` in a list of `YulStmt`. -/
def replaceIdentInStmts (oldName : String) (replacement : YulExpr) : List YulStmt → List YulStmt
  | [] => []
  | s :: ss => replaceIdentInStmt oldName replacement s :: replaceIdentInStmts oldName replacement ss

/-- Substitute `replacement` for every `.ident oldName` in switch cases. -/
def replaceIdentInCases (oldName : String) (replacement : YulExpr) :
    List (Nat × List YulStmt) → List (Nat × List YulStmt)
  | [] => []
  | (tag, body) :: rest =>
      (tag, replaceIdentInStmts oldName replacement body) ::
        replaceIdentInCases oldName replacement rest
end

/-- Rename occurrences of `.ident oldName` to `.ident newName` across `stmts`. -/
def renameIdentInStmts (oldName newName : String) (stmts : List YulStmt) : List YulStmt :=
  replaceIdentInStmts oldName (.ident newName) stmts

/-- Replace occurrences of `.ident oldName` with `mload(slot)` across `stmts`. -/
def spillIdentInStmts (oldName : String) (slot : Nat) (stmts : List YulStmt) : List YulStmt :=
  replaceIdentInStmts oldName (.call "mload" [.lit slot]) stmts

/-- Single-step dead-temporary slot reuse: rewrite `let oldName := rhs; rest`
    into `newName := rhs; rest[oldName := newName]`. -/
def reuseDeadLetStep (oldName newName : String) (rhs : YulExpr) (rest : List YulStmt) : List YulStmt :=
  .assign newName rhs :: renameIdentInStmts oldName newName rest

/-- Single-step scratch-memory spill: rewrite `let oldName := rhs; rest`
    into `mstore(slot, rhs); rest[oldName := mload(slot)]`. -/
def spillLetStep (oldName : String) (slot : Nat) (rhs : YulExpr) (rest : List YulStmt) : List YulStmt :=
  .exprStmt (.call "mstore" [.lit slot, rhs]) :: spillIdentInStmts oldName slot rest

/-- Count how many top-level `let_` statements in `rest` precede the last use of `target`. -/
def letSpanInStmts (target : String) : List YulStmt → Nat
  | [] => 0
  | stmt :: rest =>
      if stmtsUseIdent target rest then
        (match stmt with | .let_ _ _ => 1 | _ => 0) + letSpanInStmts target rest
      else
        0

/-- Check whether `let v := rhs` is eligible for slot reuse or scratch-memory spilling. -/
def canRewriteLet (protectedNames : List String) (v : String) (rhs : YulExpr)
    (rest : List YulStmt) : Bool :=
  !(v.startsWith "__") &&
    !protectedNames.contains v &&
    !exprUsesIdent v rhs &&
    !stmtsAssignIdent v rest &&
    !stmtsFuncDefUsesIdent v rest

/-- Find the first declared stack temporary `t ∈ stackVars` that is dead in `rhs` and `rest`. -/
def findDeadStackVar (protectedNames : List String) (rhs : YulExpr) (rest : List YulStmt) :
    List String → Option String
  | [] => none
  | t :: ts =>
      if !protectedNames.contains t &&
         !exprUsesIdent t rhs &&
         !stmtsUseIdent t rest &&
         !stmtsAssignIdent t rest &&
         !stmtsFuncDefUsesIdent t rest then
        some t
      else
        findDeadStackVar protectedNames rhs rest ts

/-- Find the first allocated scratch-memory slot whose value is no longer read in `rest`. -/
def findFreeSpillSlot (rest : List YulStmt) : List Nat → Option Nat
  | [] => none
  | slot :: slots =>
      if !stmtsContainMloadSlot slot rest then
        some slot
      else
        findFreeSpillSlot rest slots

/-- Fuel-bounded pass over a single lexical statement list when `countLetBindings > maxStackLocals`. -/
def reuseBlockTempsLoop
    (stackCap : Nat)
    (spillBase : Nat)
    (protectedNames : List String) :
    Nat → List String → List Nat → Bool → List YulStmt → List YulStmt
  | 0, _, _, _, stmts => stmts
  | _ + 1, _, _, _, [] => []
  | fuel + 1, stackVars, spillSlots, inUnsafe, stmt :: rest =>
      match stmt with
      | .comment text =>
          let nextUnsafe :=
            if text == UnsafeYulFragment.beginMarker then true
            else if text == UnsafeYulFragment.endMarker then false
            else inUnsafe
          stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames fuel stackVars spillSlots nextUnsafe rest
      | .let_ v rhs =>
          if inUnsafe || !canRewriteLet protectedNames v rhs rest then
            stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames fuel (stackVars ++ [v]) spillSlots inUnsafe rest
          else
            let span := letSpanInStmts v rest
            if stackVars.length < stackCap && (span ≤ 2 || stackVars.length < 4) then
              stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames fuel (stackVars ++ [v]) spillSlots inUnsafe rest
            else
              match if span ≤ 2 then findDeadStackVar protectedNames rhs rest stackVars else none with
              | some deadVar =>
                  let rest' := renameIdentInStmts v deadVar rest
                  .assign deadVar rhs ::
                    reuseBlockTempsLoop stackCap spillBase protectedNames fuel stackVars spillSlots inUnsafe rest'
              | none =>
                  let (slot, spillSlots') :=
                    match findFreeSpillSlot rest spillSlots with
                    | some existingSlot => (existingSlot, spillSlots)
                    | none =>
                        let newSlot := spillBase + 32 * spillSlots.length
                        (newSlot, spillSlots ++ [newSlot])
                  let rest' := spillIdentInStmts v slot rest
                  .exprStmt (.call "mstore" [.lit slot, rhs]) ::
                    reuseBlockTempsLoop stackCap spillBase protectedNames fuel stackVars spillSlots' inUnsafe rest'
      | _ =>
          stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames fuel stackVars spillSlots inUnsafe rest

/-- Rewrite a single lexical block: fast-path identity when `countLetBindings stmts ≤ maxStackLocals`. -/
def reuseBlockTemps
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (protectedNames : List String := [])
    (stmts : List YulStmt) : List YulStmt :=
  if countLetBindings stmts ≤ maxStackLocals then
    stmts
  else
    let stackCap := Nat.max 1 (maxStackLocals / 2 + 1)
    reuseBlockTempsLoop stackCap defaultSpillBase protectedNames stmts.length [] [] false stmts

/-- Rewrite a single lexical block using an explicit dynamic scratch-memory `spillBase`:
    fast-path identity when `countLetBindings stmts ≤ maxStackLocals`. -/
def reuseBlockTempsWithSpillBase
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (spillBase : Nat := defaultSpillBase)
    (protectedNames : List String := [])
    (stmts : List YulStmt) : List YulStmt :=
  if countLetBindings stmts ≤ maxStackLocals then
    stmts
  else
    let stackCap := Nat.max 1 (maxStackLocals / 2 + 1)
    reuseBlockTempsLoop stackCap spillBase protectedNames stmts.length [] [] false stmts

mutual
/-- Recursively apply temporary reuse and spilling across a `YulStmt`. -/
def reuseAndSpillTempsInStmt
    (maxStackLocals : Nat)
    (protectedNames : List String) : YulStmt → YulStmt
  | .comment text => .comment text
  | .let_ name value => .let_ name value
  | .letMany names value => .letMany names value
  | .assign name value => .assign name value
  | .exprStmt value => .exprStmt value
  | .leave => .leave
  | .if_ cond body =>
      .if_ cond (reuseAndSpillTemps maxStackLocals protectedNames body)
  | .for_ init cond post body =>
      .for_
        (reuseAndSpillTemps maxStackLocals protectedNames init)
        cond
        (reuseAndSpillTemps maxStackLocals protectedNames post)
        (reuseAndSpillTemps maxStackLocals protectedNames body)
  | .switch expr cases default =>
      .switch
        expr
        (reuseAndSpillTempsInCases maxStackLocals protectedNames cases)
        (match default with
         | none => none
         | some body => some (reuseAndSpillTemps maxStackLocals protectedNames body))
  | .block stmts =>
      .block (reuseAndSpillTemps maxStackLocals protectedNames stmts)
  | .funcDef name params rets body =>
      .funcDef name params rets (reuseAndSpillTemps maxStackLocals (params ++ rets) body)

/-- Recursively apply temporary reuse and spilling across a list of `YulStmt`. -/
def reuseAndSpillTempsChildren
    (maxStackLocals : Nat)
    (protectedNames : List String) : List YulStmt → List YulStmt
  | [] => []
  | s :: ss =>
      reuseAndSpillTempsInStmt maxStackLocals protectedNames s ::
        reuseAndSpillTempsChildren maxStackLocals protectedNames ss

/-- Recursively apply temporary reuse and spilling across switch cases. -/
def reuseAndSpillTempsInCases
    (maxStackLocals : Nat)
    (protectedNames : List String) : List (Nat × List YulStmt) → List (Nat × List YulStmt)
  | [] => []
  | (tag, body) :: rest =>
      (tag, reuseAndSpillTemps maxStackLocals protectedNames body) ::
        reuseAndSpillTempsInCases maxStackLocals protectedNames rest

/-- Apply temporary reuse and scratch-memory spilling to a statement list and all nested blocks. -/
def reuseAndSpillTemps
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (protectedNames : List String := [])
    (stmts : List YulStmt) : List YulStmt :=
  reuseBlockTemps maxStackLocals protectedNames
    (reuseAndSpillTempsChildren maxStackLocals protectedNames stmts)
end

/-- Apply temporary reuse and scratch-memory spilling to a full `YulObject`. -/
def reuseAndSpillTempsObject
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (obj : YulObject) : YulObject :=
  { obj with
    deployCode := reuseAndSpillTemps maxStackLocals [] obj.deployCode
    runtimeCode := reuseAndSpillTemps maxStackLocals [] obj.runtimeCode }

end Compiler.Yul.TempReuse
