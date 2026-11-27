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

mutual
/-- One past the highest spill slot (`mload`/`mstore` at a literal address at or above
`defaultSpillBase`) used in an expression, or 0 if none. -/
def spillHighWaterExpr : YulExpr → Nat
  | .call func args =>
      let here := match func, args with
        | "mload", [.lit slot] | "mstore", .lit slot :: _ =>
            if defaultSpillBase ≤ slot then slot + 32 else 0
        | _, _ => 0
      max here (spillHighWaterExprs args)
  | _ => 0

/-- `spillHighWaterExpr` over a list of expressions. -/
def spillHighWaterExprs : List YulExpr → Nat
  | [] => 0
  | e :: es => max (spillHighWaterExpr e) (spillHighWaterExprs es)
end

mutual
/-- One past the highest spill slot used anywhere in a statement (including nested blocks
and function bodies), or 0 if none. -/
def spillHighWaterStmt : YulStmt → Nat
  | .comment _ | .leave => 0
  | .let_ _ value | .letMany _ value | .assign _ value | .exprStmt value =>
      spillHighWaterExpr value
  | .if_ cond body => max (spillHighWaterExpr cond) (spillHighWaterStmts body)
  | .for_ init cond post body =>
      max (max (spillHighWaterStmts init) (spillHighWaterExpr cond))
        (max (spillHighWaterStmts post) (spillHighWaterStmts body))
  | .switch expr cases default =>
      max (spillHighWaterExpr expr)
        (max (spillHighWaterCases cases)
          (match default with
           | none => 0
           | some body => spillHighWaterStmts body))
  | .block stmts => spillHighWaterStmts stmts
  | .funcDef _ _ _ body => spillHighWaterStmts body

/-- `spillHighWaterStmt` over a statement list. -/
def spillHighWaterStmts : List YulStmt → Nat
  | [] => 0
  | s :: ss => max (spillHighWaterStmt s) (spillHighWaterStmts ss)

/-- `spillHighWaterStmt` over switch cases. -/
def spillHighWaterCases : List (Nat × List YulStmt) → Nat
  | [] => 0
  | (_, body) :: rest => max (spillHighWaterStmts body) (spillHighWaterCases rest)
end

/-- Fuel-bounded pass over a single lexical statement list when `countLetBindings > maxStackLocals`.
With `allowSpill = false` a `let` with no dead stack temporary to reuse stays a `let` (no
scratch-memory spill): used where fixed spill slots would be shared by live frames. -/
def reuseBlockTempsLoop
    (stackCap : Nat)
    (spillBase : Nat)
    (protectedNames : List String)
    (allowSpill : Bool := true) :
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
          stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames allowSpill fuel stackVars spillSlots nextUnsafe rest
      | .let_ v rhs =>
          if inUnsafe || !canRewriteLet protectedNames v rhs rest then
            stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames allowSpill fuel (stackVars ++ [v]) spillSlots inUnsafe rest
          else
            let span := letSpanInStmts v rest
            if stackVars.length < stackCap && (span ≤ 2 || stackVars.length < 4) then
              stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames allowSpill fuel (stackVars ++ [v]) spillSlots inUnsafe rest
            else
              match if span ≤ 2 then findDeadStackVar protectedNames rhs rest stackVars else none with
              | some deadVar =>
                  let rest' := renameIdentInStmts v deadVar rest
                  .assign deadVar rhs ::
                    reuseBlockTempsLoop stackCap spillBase protectedNames allowSpill fuel stackVars spillSlots inUnsafe rest'
              | none =>
                  if !allowSpill then
                    stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames allowSpill fuel
                      (stackVars ++ [v]) spillSlots inUnsafe rest
                  else
                    let (slot, spillSlots') :=
                      match findFreeSpillSlot rest spillSlots with
                      | some existingSlot => (existingSlot, spillSlots)
                      | none =>
                          let newSlot := spillBase + 32 * spillSlots.length
                          (newSlot, spillSlots ++ [newSlot])
                    let rest' := spillIdentInStmts v slot rest
                    .exprStmt (.call "mstore" [.lit slot, rhs]) ::
                      reuseBlockTempsLoop stackCap spillBase protectedNames allowSpill fuel
                        stackVars spillSlots' inUnsafe rest'
      | _ =>
          stmt :: reuseBlockTempsLoop stackCap spillBase protectedNames allowSpill fuel stackVars spillSlots inUnsafe rest

/-- Rewrite a single lexical block: fast-path identity when `countLetBindings stmts ≤ maxStackLocals`.
New spill slots start above any spill slot already used inside `stmts`. Not used by any compile
path (`writeContract` uses `reuseAndSpillTempsStaticObject`; `Compiler.emitYulSpilled` uses
`reuseAndSpillTempsDispatchedObject`). -/
def reuseBlockTemps
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (protectedNames : List String := [])
    (stmts : List YulStmt) : List YulStmt :=
  if countLetBindings stmts ≤ maxStackLocals then
    stmts
  else
    let stackCap := Nat.max 1 (maxStackLocals / 2 + 1)
    reuseBlockTempsLoop stackCap (max defaultSpillBase (spillHighWaterStmts stmts)) protectedNames true
      stmts.length [] [] false stmts

/-- Rewrite a single lexical block using an explicit dynamic scratch-memory `spillBase`:
    fast-path identity when `countLetBindings stmts ≤ maxStackLocals`. Not used by any compile
    path (`writeContract` uses `reuseAndSpillTempsStaticObject`; `Compiler.emitYulSpilled` uses
    `reuseAndSpillTempsDispatchedObject`). -/
def reuseBlockTempsWithSpillBase
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (spillBase : Nat := defaultSpillBase)
    (protectedNames : List String := [])
    (stmts : List YulStmt) : List YulStmt :=
  if countLetBindings stmts ≤ maxStackLocals then
    stmts
  else
    let stackCap := Nat.max 1 (maxStackLocals / 2 + 1)
    reuseBlockTempsLoop stackCap (max spillBase (spillHighWaterStmts stmts)) protectedNames true
      stmts.length [] [] false stmts

/-- Rewrite one lexical block for `reuseAndSpillTemps`. New spill slots start above every
slot the (already rewritten) nested blocks of `stmts` use: a nested block runs while this
block's spilled locals are live, so the two must never share a slot. With
`allowSpill = false` only dead stack temporaries are reused. -/
def reuseBlockTempsNested
    (maxStackLocals : Nat)
    (protectedNames : List String)
    (allowSpill : Bool)
    (stmts : List YulStmt) : List YulStmt :=
  if countLetBindings stmts ≤ maxStackLocals then
    stmts
  else
    let stackCap := Nat.max 1 (maxStackLocals / 2 + 1)
    reuseBlockTempsLoop stackCap (max defaultSpillBase (spillHighWaterStmts stmts))
      protectedNames allowSpill stmts.length [] [] false stmts

/-- Names declared by the top-level `let`s of a statement list. -/
def stmtsLetNames : List YulStmt → List String
  | [] => []
  | .let_ name _ :: rest => name :: stmtsLetNames rest
  | .letMany names _ :: rest => names ++ stmtsLetNames rest
  | _ :: rest => stmtsLetNames rest

mutual
/-- Recursively apply temporary reuse and spilling across a `YulStmt`.

Spill slots are fixed memory words, so spilling is only sound where no other live frame can
touch the same words. A function body never spills: it runs while its caller's spilled locals
are live and may recurse into itself, and its slots would not be disjoint from either. A `for`
initialiser never spills: its variables stay live while the body and post blocks run. Both
still reuse dead stack temporaries; a body that remains too deep fails closed in solc
(StackTooDeep) instead of aliasing memory. The initialiser's own variables are protected:
liveness is judged on the rest of the initialiser only, so reusing one of them as a dead
temporary would clobber a value the condition, body or post block still reads. -/
def reuseAndSpillTempsInStmt
    (maxStackLocals : Nat)
    (protectedNames : List String)
    (allowSpill : Bool) : YulStmt → YulStmt
  | .comment text => .comment text
  | .let_ name value => .let_ name value
  | .letMany names value => .letMany names value
  | .assign name value => .assign name value
  | .exprStmt value => .exprStmt value
  | .leave => .leave
  | .if_ cond body =>
      .if_ cond (reuseAndSpillTemps maxStackLocals protectedNames allowSpill body)
  | .for_ init cond post body =>
      .for_
        (reuseAndSpillTemps maxStackLocals (protectedNames ++ stmtsLetNames init) false init)
        cond
        (reuseAndSpillTemps maxStackLocals protectedNames allowSpill post)
        (reuseAndSpillTemps maxStackLocals protectedNames allowSpill body)
  | .switch expr cases default =>
      .switch
        expr
        (reuseAndSpillTempsInCases maxStackLocals protectedNames allowSpill cases)
        (match default with
         | none => none
         | some body => some (reuseAndSpillTemps maxStackLocals protectedNames allowSpill body))
  | .block stmts =>
      .block (reuseAndSpillTemps maxStackLocals protectedNames allowSpill stmts)
  | .funcDef name params rets body =>
      .funcDef name params rets (reuseAndSpillTemps maxStackLocals (params ++ rets) false body)

/-- Recursively apply temporary reuse and spilling across a list of `YulStmt`. -/
def reuseAndSpillTempsChildren
    (maxStackLocals : Nat)
    (protectedNames : List String)
    (allowSpill : Bool) : List YulStmt → List YulStmt
  | [] => []
  | s :: ss =>
      reuseAndSpillTempsInStmt maxStackLocals protectedNames allowSpill s ::
        reuseAndSpillTempsChildren maxStackLocals protectedNames allowSpill ss

/-- Recursively apply temporary reuse and spilling across switch cases. -/
def reuseAndSpillTempsInCases
    (maxStackLocals : Nat)
    (protectedNames : List String)
    (allowSpill : Bool) : List (Nat × List YulStmt) → List (Nat × List YulStmt)
  | [] => []
  | (tag, body) :: rest =>
      (tag, reuseAndSpillTemps maxStackLocals protectedNames allowSpill body) ::
        reuseAndSpillTempsInCases maxStackLocals protectedNames allowSpill rest

/-- Apply temporary reuse and scratch-memory spilling to a statement list and all nested blocks
(`allowSpill = false`: dead-stack-temporary reuse only). -/
def reuseAndSpillTemps
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (protectedNames : List String := [])
    (allowSpill : Bool := true)
    (stmts : List YulStmt) : List YulStmt :=
  reuseBlockTempsNested maxStackLocals protectedNames allowSpill
    (reuseAndSpillTempsChildren maxStackLocals protectedNames allowSpill stmts)
end


/-- Raise the free-memory-pointer initialisation `mstore(64, 128)` (top level of a code
section) to `minFree` when that is higher.

No compile path uses this any more. Raising a literal `mstore(64, 128)` inside a section or case
body can corrupt user data written to byte 64 and does not protect spill words from memory
written at fixed low addresses with a runtime size. Instead, `writeContract` uses
`reuseAndSpillTempsStaticObject`, and `Compiler.emitYulSpilled` uses
`reuseAndSpillTempsDispatchedObject` (which prepends `mstore(64, highWater)` only at dispatch
case entry behind `caseMemoryFreePtrSafe` and never rewrites `mstore(64, ...)` inside a case). -/
def raiseFreePointerInit (minFree : Nat) : List YulStmt → List YulStmt
  | [] => []
  | (.exprStmt (.call "mstore" [.lit 64, .lit init])) :: rest =>
      .exprStmt (.call "mstore" [.lit 64, .lit (max init minFree)]) :: raiseFreePointerInit minFree rest
  | s :: rest => s :: raiseFreePointerInit minFree rest

/-- Literal byte range `[offset, offset + len)` ends at or below `bound`; a non-literal offset or
length is never accepted. A zero-length range touches no memory. -/
def literalRangeBelow (bound : Nat) : YulExpr → YulExpr → Bool
  | .lit _, .lit 0 => true
  | .lit offset, .lit len => offset + len ≤ bound
  | _, _ => false

/-- The memory byte ranges `(offset, length)` a builtin call touches, by argument position, or
`none` when the call does not touch memory. `msize` reads the memory size, so it is reported
as touching an unknown range. -/
def builtinMemoryRanges : String → List YulExpr → Option (List (YulExpr × YulExpr))
  | "mload", [p] => some [(p, .lit 32)]
  | "mstore", [p, _] => some [(p, .lit 32)]
  | "mstore8", [p, _] => some [(p, .lit 1)]
  | "keccak256", [p, n] | "return", [p, n] | "revert", [p, n] => some [(p, n)]
  | "log0", p :: n :: _ | "log1", p :: n :: _ | "log2", p :: n :: _
  | "log3", p :: n :: _ | "log4", p :: n :: _ => some [(p, n)]
  | "calldatacopy", [d, _, n] | "codecopy", [d, _, n] | "returndatacopy", [d, _, n]
  | "datacopy", [d, _, n] => some [(d, n)]
  | "extcodecopy", [_, d, _, n] => some [(d, n)]
  | "mcopy", [d, s, n] => some [(d, n), (s, n)]
  | "call", [_, _, _, i, iLen, o, oLen] | "callcode", [_, _, _, i, iLen, o, oLen] =>
      some [(i, iLen), (o, oLen)]
  | "delegatecall", [_, _, i, iLen, o, oLen] | "staticcall", [_, _, i, iLen, o, oLen] =>
      some [(i, iLen), (o, oLen)]
  | "create", [_, p, n] | "create2", [_, p, n, _] => some [(p, n)]
  | "msize", _ => some [(.ident "msize", .ident "msize")]
  | _, _ => none

/-- EVM builtins that read or write no memory. -/
def memoryFreeBuiltins : List String :=
  [ "stop", "add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp", "not", "lt", "gt", "slt",
    "sgt", "eq", "iszero", "and", "or", "xor", "byte", "shl", "shr", "sar", "addmod", "mulmod",
    "signextend", "pop", "sload", "sstore", "tload", "tstore", "calldataload", "calldatasize",
    "callvalue", "caller", "origin", "address", "balance", "selfbalance", "gas", "gasprice",
    "chainid", "coinbase", "timestamp", "number", "difficulty", "prevrandao", "gaslimit",
    "basefee", "blobbasefee", "blobhash", "blockhash", "codesize", "extcodesize", "extcodehash",
    "returndatasize", "datasize", "dataoffset", "loadimmutable", "clz", "invalid", "selfdestruct" ]

mutual
/-- Every memory access in an expression has a literal address and length ending at or below
`bound`, the expression does not use `msize`, and every other call is a memory-free builtin
or a function named in `fns` (whose body is checked separately). -/
def exprMemoryStaticBelow (bound : Nat) (fns : List String) : YulExpr → Bool
  | .call func args =>
      (match builtinMemoryRanges func args with
       | some ranges => ranges.all fun (offset, len) => literalRangeBelow bound offset len
       | none => memoryFreeBuiltins.contains func || fns.contains func) &&
        exprsMemoryStaticBelow bound fns args
  | _ => true

/-- `exprMemoryStaticBelow` over a list of expressions. -/
def exprsMemoryStaticBelow (bound : Nat) (fns : List String) : List YulExpr → Bool
  | [] => true
  | e :: es => exprMemoryStaticBelow bound fns e && exprsMemoryStaticBelow bound fns es
end

mutual
/-- `exprMemoryStaticBelow` over every expression of a statement, nested blocks and function
bodies included. -/
def stmtMemoryStaticBelow (bound : Nat) (fns : List String) : YulStmt → Bool
  | .comment _ | .leave => true
  | .let_ _ value | .letMany _ value | .assign _ value | .exprStmt value =>
      exprMemoryStaticBelow bound fns value
  | .if_ cond body =>
      exprMemoryStaticBelow bound fns cond && stmtsMemoryStaticBelow bound fns body
  | .for_ init cond post body =>
      stmtsMemoryStaticBelow bound fns init && exprMemoryStaticBelow bound fns cond &&
        stmtsMemoryStaticBelow bound fns post && stmtsMemoryStaticBelow bound fns body
  | .switch expr cases default =>
      exprMemoryStaticBelow bound fns expr && casesMemoryStaticBelow bound fns cases &&
        match default with
        | none => true
        | some body => stmtsMemoryStaticBelow bound fns body
  | .block stmts => stmtsMemoryStaticBelow bound fns stmts
  | .funcDef _ _ _ body => stmtsMemoryStaticBelow bound fns body

/-- `stmtMemoryStaticBelow` over a statement list. -/
def stmtsMemoryStaticBelow (bound : Nat) (fns : List String) : List YulStmt → Bool
  | [] => true
  | s :: ss => stmtMemoryStaticBelow bound fns s && stmtsMemoryStaticBelow bound fns ss

/-- `stmtMemoryStaticBelow` over switch cases. -/
def casesMemoryStaticBelow (bound : Nat) (fns : List String) :
    List (Nat × List YulStmt) → Bool
  | [] => true
  | (_, body) :: rest =>
      stmtsMemoryStaticBelow bound fns body && casesMemoryStaticBelow bound fns rest
end

mutual
/-- Names of the functions defined anywhere in a statement. -/
def stmtFuncDefNames : YulStmt → List String
  | .if_ _ body | .block body => stmtsFuncDefNames body
  | .for_ init _ post body =>
      stmtsFuncDefNames init ++ stmtsFuncDefNames post ++ stmtsFuncDefNames body
  | .switch _ cases default =>
      casesFuncDefNames cases ++
        match default with
        | none => []
        | some body => stmtsFuncDefNames body
  | .funcDef name _ _ body => name :: stmtsFuncDefNames body
  | _ => []

/-- `stmtFuncDefNames` over a statement list. -/
def stmtsFuncDefNames : List YulStmt → List String
  | [] => []
  | s :: ss => stmtFuncDefNames s ++ stmtsFuncDefNames ss

/-- `stmtFuncDefNames` over switch cases. -/
def casesFuncDefNames : List (Nat × List YulStmt) → List String
  | [] => []
  | (_, body) :: rest => stmtsFuncDefNames body ++ casesFuncDefNames rest
end

/-- Every memory access in a code section (all its functions included) has a literal address
and length ending at or below `bound`, `msize` is unused, and no call leaves the section
except to a memory-free builtin. -/
def sectionMemoryStaticBelow (bound : Nat) (code : List YulStmt) : Bool :=
  stmtsMemoryStaticBelow bound (stmtsFuncDefNames code) code

/-- Spill a code section only when the spill words are statically checked to be disjoint from
every other memory access: each access in `code` has a literal address and length below
`defaultSpillBase`, `msize` is unused, and every call stays inside the section or is a
memory-free builtin. The free-memory pointer is left untouched, so the
memory layout (and every allocation bound) stays exactly as emitted. Any other section is
returned unchanged: if it is too deep for the stack, solc rejects it (StackTooDeep) instead of
the spill words aliasing runtime-allocated memory or shifting the allocation bounds. -/
def reuseAndSpillTempsStaticSection (maxStackLocals : Nat) (code : List YulStmt) :
    List YulStmt :=
  if sectionMemoryStaticBelow defaultSpillBase code then
    reuseAndSpillTemps maxStackLocals [] true code
  else
    code

/-- `reuseAndSpillTempsStaticSection` on the deploy and runtime code of a `YulObject`. This is
the spill entry point of the CLI compile path (`writeContract`). It is a trusted,
tested-only pass (`docs/TRUST_ASSUMPTIONS.md`, "Yul Stack Spill Pass"). -/
def reuseAndSpillTempsStaticObject
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (obj : YulObject) : YulObject :=
  { obj with
    deployCode := reuseAndSpillTempsStaticSection maxStackLocals obj.deployCode
    runtimeCode := reuseAndSpillTempsStaticSection maxStackLocals obj.runtimeCode }

private def uint256Modulus : Nat := 2 ^ 256

private def maxU64 : Nat := 2 ^ 64 - 1

private def defaultInitialFreePtr : Nat := 128

private def maxSpillHighWater : Nat := 2 ^ 32

private def reservedBuiltins : List String :=
  [ "mload", "mstore", "mstore8", "keccak256", "return", "revert",
    "log0", "log1", "log2", "log3", "log4",
    "calldatacopy", "codecopy", "returndatacopy", "datacopy", "extcodecopy", "mcopy",
    "call", "callcode", "delegatecall", "staticcall",
    "create", "create2", "msize", "setimmutable",
    "break", "continue", "leave" ] ++ memoryFreeBuiltins

mutual
/-- Every `funcDef` body anywhere in a statement satisfies `stmtsMemoryStaticBelow bound fns`. -/
private def stmtFuncDefsMemoryStaticBelow (bound : Nat) (fns : List String) : YulStmt → Bool
  | .if_ _ body | .block body => stmtsFuncDefsMemoryStaticBelow bound fns body
  | .for_ init _ post body =>
      stmtsFuncDefsMemoryStaticBelow bound fns init &&
        stmtsFuncDefsMemoryStaticBelow bound fns post &&
        stmtsFuncDefsMemoryStaticBelow bound fns body
  | .switch _ cases default =>
      casesFuncDefsMemoryStaticBelow bound fns cases &&
        match default with
        | none => true
        | some body => stmtsFuncDefsMemoryStaticBelow bound fns body
  | .funcDef _ _ _ body =>
      stmtsMemoryStaticBelow bound fns body && stmtsFuncDefsMemoryStaticBelow bound fns body
  | _ => true

/-- `stmtFuncDefsMemoryStaticBelow` over a statement list. -/
private def stmtsFuncDefsMemoryStaticBelow (bound : Nat) (fns : List String) :
    List YulStmt → Bool
  | [] => true
  | s :: ss =>
      stmtFuncDefsMemoryStaticBelow bound fns s &&
        stmtsFuncDefsMemoryStaticBelow bound fns ss

/-- `stmtFuncDefsMemoryStaticBelow` over switch cases. -/
private def casesFuncDefsMemoryStaticBelow (bound : Nat) (fns : List String) :
    List (Nat × List YulStmt) → Bool
  | [] => true
  | (_, body) :: rest =>
      stmtsFuncDefsMemoryStaticBelow bound fns body &&
        casesFuncDefsMemoryStaticBelow bound fns rest
end

private def lookupNatAssoc (name : String) : List (String × Nat) → Option Nat
  | [] => none
  | (k, v) :: rest => if k == name then some v else lookupNatAssoc name rest

/-- Evaluate simple 256-bit constant expressions (`lit`, `hex`, immutable literal `let`s, `add`). -/
private def litConstExpr (litVars : List (String × Nat)) : YulExpr → Option Nat
  | .lit n | .hex n => some (n % uint256Modulus)
  | .ident name => lookupNatAssoc name litVars
  | .call "add" [a, b] =>
      match litConstExpr litVars a, litConstExpr litVars b with
      | some va, some vb => some ((va + vb) % uint256Modulus)
      | _, _ => none
  | _ => none

/-- Constant byte range `[offset, offset + len)` ends at or below `bound` (zero length touches
nothing). -/
private def constRangeBelow (bound : Nat) (litVars : List (String × Nat))
    (offset len : YulExpr) : Bool :=
  match litConstExpr litVars offset, litConstExpr litVars len with
  | some _, some 0 => true
  | some off, some sz => off + sz ≤ bound
  | _, _ => false

/-- Constant byte range `[offset, offset + len)` ends at or below `bound` and is disjoint from
`[64, 96)`. -/
private def constRangeDisjointFromFp (bound : Nat) (litVars : List (String × Nat))
    (offset len : YulExpr) : Bool :=
  match litConstExpr litVars offset, litConstExpr litVars len with
  | some _, some 0 => true
  | some off, some sz => off + sz ≤ bound && (off + sz ≤ 64 || 96 ≤ off)
  | _, _ => false

/-- Constant non-empty byte range `[offset, offset + len)` completely covers `[64, 96)` and ends
at or below `bound`. -/
private def constRangeCoversFp (bound : Nat) (litVars : List (String × Nat))
    (offset len : YulExpr) : Bool :=
  match litConstExpr litVars offset, litConstExpr litVars len with
  | some off, some sz => 0 < sz && off ≤ 64 && 96 ≤ off + sz && off + sz ≤ bound
  | _, _ => false

/-- Static read (or partial-write) byte range safety: disjoint from `[64, 96)` unless `[64, 96)`
has been completely overwritten on every path reaching this point. -/
private def constRangeSafeForRead (bound : Nat) (litVars : List (String × Nat))
    (fpOverwritten : Bool) (offset len : YulExpr) : Bool :=
  if fpOverwritten then
    constRangeBelow bound litVars offset len
  else
    constRangeDisjointFromFp bound litVars offset len

/-- Sound upper bound `< 2^64` on a non-negative 256-bit Yul expression. -/
private def exprUpperBound (litVars u64Bounds : List (String × Nat)) : YulExpr → Option Nat
  | .lit n | .hex n =>
      let v := n % uint256Modulus
      if v < 2 ^ 64 then some v else none
  | .ident name =>
      match lookupNatAssoc name litVars with
      | some v => if v < 2 ^ 64 then some v else none
      | none => lookupNatAssoc name u64Bounds
  | .call "and" [a, b] =>
      match exprUpperBound litVars u64Bounds a, exprUpperBound litVars u64Bounds b with
      | some ua, some ub => some (min ua ub)
      | some ua, none => some ua
      | none, some ub => some ub
      | none, none => none
  | .call "mod" [_, b] =>
      match litConstExpr litVars b with
      | some vb => if 0 < vb && vb ≤ 2 ^ 64 then some (vb - 1) else none
      | none => none
  | .call "shr" [shift, _] =>
      match litConstExpr litVars shift with
      | some s =>
          if s == 192 then some maxU64
          else if 192 < s && s ≤ 256 then some (2 ^ (256 - s) - 1)
          else none
      | none => none
  | .call "add" [a, b] =>
      match exprUpperBound litVars u64Bounds a, exprUpperBound litVars u64Bounds b with
      | some ua, some ub => if ua + ub < 2 ^ 64 then some (ua + ub) else none
      | _, _ => none
  | .call "mul" [a, b] =>
      match exprUpperBound litVars u64Bounds a, exprUpperBound litVars u64Bounds b with
      | some ua, some ub => if ua * ub < 2 ^ 64 then some (ua * ub) else none
      | _, _ => none
  | _ => none

/-- Cumulative non-negative offset bound `< 2^64` added onto an immutable free-pointer variable
`p ∈ fpVars`. Since `highWater ≤ p ≤ 2^64 - 1`, `p + offset < 2^65 < 2^256` never wraps. -/
private def fpAddrOffsetBound (fpVars : List String)
    (litVars u64Bounds : List (String × Nat)) : YulExpr → Option Nat
  | .ident name => if fpVars.contains name then some 0 else none
  | .call "add" [a, b] =>
      match fpAddrOffsetBound fpVars litVars u64Bounds a,
            exprUpperBound litVars u64Bounds b with
      | some oa, some ob => if oa + ob < 2 ^ 64 then some (oa + ob) else none
      | _, _ =>
          match exprUpperBound litVars u64Bounds a,
                fpAddrOffsetBound fpVars litVars u64Bounds b with
          | some oa, some ob => if oa + ob < 2 ^ 64 then some (oa + ob) else none
          | _, _ => none
  | _ => none

/-- Heap range `(offset, len)` starting at an `fpVars`-derived address with `< 2^64` length,
guaranteeing `[offset, offset + len) ⊆ [highWater, 2^66)` with no 256-bit wraparound. -/
private def fpHeapRange (fpVars : List String) (litVars u64Bounds : List (String × Nat))
    (offset len : YulExpr) : Bool :=
  (fpAddrOffsetBound fpVars litVars u64Bounds offset).isSome &&
    (exprUpperBound litVars u64Bounds len).isSome

mutual
/-- Whether a non-halting control-flow exit (`.leave` or any non-call `.exprStmt` such as
`.ident "break"`, `.ident "continue"`, or `.ident "leave"`) occurs anywhere in `stmt` outside
nested `funcDef`s. -/
private def stmtMayLeave : YulStmt → Bool
  | .leave => true
  | .exprStmt (.call _ _) => false
  | .exprStmt _ => true
  | .if_ _ body | .block body => stmtsMayLeave body
  | .for_ init _ post body =>
      stmtsMayLeave init || stmtsMayLeave post || stmtsMayLeave body
  | .switch _ cases default =>
      casesMayLeave cases ||
        match default with
        | none => false
        | some dbody => stmtsMayLeave dbody
  | .funcDef _ _ _ _ => false
  | _ => false

private def stmtsMayLeave : List YulStmt → Bool
  | [] => false
  | s :: ss => stmtMayLeave s || stmtsMayLeave ss

private def casesMayLeave : List (Nat × List YulStmt) → Bool
  | [] => false
  | (_, body) :: rest => stmtsMayLeave body || casesMayLeave rest
end

mutual
/-- Conservative check that executing `stmt` unconditionally halts the current EVM call frame. -/
private def stmtAlwaysTerminates : YulStmt → Bool
  | .exprStmt (.call "revert" [_, _]) | .exprStmt (.call "return" [_, _]) => true
  | .exprStmt (.call "stop" []) | .exprStmt (.call "invalid" []) => true
  | .exprStmt (.call "selfdestruct" [_]) => true
  | .block stmts => stmtsAlwaysTerminate stmts
  | .if_ (.lit n) body | .if_ (.hex n) body =>
      n % uint256Modulus != 0 && stmtsAlwaysTerminate body
  | .if_ (.call "iszero" [.lit 0]) body | .if_ (.call "iszero" [.hex 0]) body =>
      stmtsAlwaysTerminate body
  | .switch _ cases (some dbody) =>
      stmtsAlwaysTerminate dbody && casesAlwaysTerminate cases
  | _ => false

/-- `stmtAlwaysTerminates` over a statement list. -/
private def stmtsAlwaysTerminate : List YulStmt → Bool
  | [] => false
  | .leave :: _ => false
  | .exprStmt (.ident _) :: _ | .exprStmt (.lit _) :: _
  | .exprStmt (.hex _) :: _ | .exprStmt (.str _) :: _ => false
  | .if_ (.ident v) b1 :: .if_ (.call "iszero" [.ident v']) b2 :: rest =>
      if v == v' && !stmtsAssignIdent v b1 && !stmtsMayLeave b1 &&
         stmtsAlwaysTerminate b1 && stmtsAlwaysTerminate b2 then
        true
      else if stmtMayLeave (.if_ (.ident v) b1) then
        false
      else
        stmtsAlwaysTerminate (.if_ (.call "iszero" [.ident v']) b2 :: rest)
  | s :: ss =>
      if stmtAlwaysTerminates s then true
      else if stmtMayLeave s then false
      else stmtsAlwaysTerminate ss

private def casesAlwaysTerminate : List (Nat × List YulStmt) → Bool
  | [] => true
  | (_, body) :: rest => stmtsAlwaysTerminate body && casesAlwaysTerminate rest
end

/-- Flow-sensitive state of `[64, 96)` and the free-pointer ceiling in a dispatch case:
- `fpClean`: `[64, 96)` holds the aligned free-memory pointer in `[highWater, maxFp]`.
- `fpOverwritten`: all 32 bytes `[64, 96)` have been overwritten with program data on every path
  since the last free-pointer store, making static reads of `[64, 96)` unobservable.
- `maxFp`: sound upper bound (`≤ 2^64 - 1`) on the free-memory pointer across all paths reaching
  this point when spilled (`mem[64]` initialized to `highWater ≤ maxSpillHighWater`), ensuring the
  checked-allocation `2^64 - 1` overflow guard never fires in spilled code when unspilled code
  (`mem[64]` initialized to `128`) would succeed. -/
private structure FpState where
  fpClean : Bool
  fpOverwritten : Bool
  maxFp : Nat
  deriving DecidableEq

/-- Lexical environment of immutable locals tracked by the per-case gate. -/
private structure FreePtrEnv where
  fpVars : List String := []
  immVars : List String := []
  litVars : List (String × Nat) := []
  u64Bounds : List (String × Nat) := []

private def envHasTrackedVar (env : FreePtrEnv) (name : String) : Bool :=
  env.fpVars.contains name ||
    env.immVars.contains name ||
    (lookupNatAssoc name env.litVars).isSome ||
    (lookupNatAssoc name env.u64Bounds).isSome

private def isFreshImmutable (env : FreePtrEnv) (name : String) (rest : List YulStmt) : Bool :=
  !envHasTrackedVar env name &&
    !stmtsAssignIdent name rest &&
    !stmtsFuncDefUsesIdent name rest

private def envAddFp (env : FreePtrEnv) (name : String) : FreePtrEnv :=
  { env with fpVars := name :: env.fpVars, immVars := name :: env.immVars }

private def envAddU64 (env : FreePtrEnv) (name : String) (ub : Nat) : FreePtrEnv :=
  let nextBounds :=
    match lookupNatAssoc name env.u64Bounds with
    | some prev => (name, min prev ub) :: env.u64Bounds
    | none => (name, ub) :: env.u64Bounds
  { env with u64Bounds := nextBounds }

private def isMload64 (litVars : List (String × Nat)) : YulExpr → Bool
  | .call "mload" [arg] => litConstExpr litVars arg == some 64
  | _ => false

private def readRangeFreePtrSafe (bound : Nat) (env : FreePtrEnv) (state : FpState)
    (offset len : YulExpr) : Bool :=
  constRangeSafeForRead bound env.litVars state.fpOverwritten offset len ||
    fpHeapRange env.fpVars env.litVars env.u64Bounds offset len

mutual
/-- Check a Yul expression under `FpState`. With `allowFpAddr = false` (value position), `fpVars`
and unoverwritten `[64, 96)` reads are rejected everywhere so pointers can never be stored,
returned, logged, or compared. With `allowFpAddr = true` (memory-address operand), `p ∈ fpVars`
is permitted as a base with `exprFreePtrSafe ... false` addends when `fpAddrOffsetBound` holds. -/
private def exprFreePtrSafe (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (state : FpState) : Bool → YulExpr → Bool
  | _, .lit _ | _, .hex _ | _, .str _ => true
  | allowFpAddr, .ident name =>
      if allowFpAddr then true else !env.fpVars.contains name
  | allowFpAddr, .call "add" [a, b] =>
      if allowFpAddr &&
         (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds (.call "add" [a, b])).isSome
      then
        if (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds a).isSome &&
           (exprUpperBound env.litVars env.u64Bounds b).isSome then
          exprFreePtrSafe bound fns env state true a &&
            exprFreePtrSafe bound fns env state false b
        else
          exprFreePtrSafe bound fns env state false a &&
            exprFreePtrSafe bound fns env state true b
      else
        exprFreePtrSafe bound fns env state false a &&
          exprFreePtrSafe bound fns env state false b
  | _, .call "mload" [p] =>
      let pIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds p).isSome
      readRangeFreePtrSafe bound env state p (.lit 32) &&
        exprFreePtrSafe bound fns env state pIsFp p
  | _, .call "keccak256" [p, n] =>
      let pIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds p).isSome
      readRangeFreePtrSafe bound env state p n &&
        exprFreePtrSafe bound fns env state pIsFp p &&
        exprFreePtrSafe bound fns env state false n
  | _, .call "create" [v, p, n] =>
      let pIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds p).isSome
      readRangeFreePtrSafe bound env state p n &&
        exprFreePtrSafe bound fns env state false v &&
        exprFreePtrSafe bound fns env state pIsFp p &&
        exprFreePtrSafe bound fns env state false n
  | _, .call "create2" [v, p, n, salt] =>
      let pIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds p).isSome
      readRangeFreePtrSafe bound env state p n &&
        exprFreePtrSafe bound fns env state false v &&
        exprFreePtrSafe bound fns env state pIsFp p &&
        exprFreePtrSafe bound fns env state false n &&
        exprFreePtrSafe bound fns env state false salt
  | _, .call "call" [g, a, v, i, iLen, o, oLen]
  | _, .call "callcode" [g, a, v, i, iLen, o, oLen] =>
      let iIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds i).isSome
      let oIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds o).isSome
      readRangeFreePtrSafe bound env state i iLen &&
        readRangeFreePtrSafe bound env state o oLen &&
        exprFreePtrSafe bound fns env state iIsFp i &&
        exprFreePtrSafe bound fns env state oIsFp o &&
        exprFreePtrSafe bound fns env state false g &&
        exprFreePtrSafe bound fns env state false a &&
        exprFreePtrSafe bound fns env state false v &&
        exprFreePtrSafe bound fns env state false iLen &&
        exprFreePtrSafe bound fns env state false oLen
  | _, .call "delegatecall" [g, a, i, iLen, o, oLen]
  | _, .call "staticcall" [g, a, i, iLen, o, oLen] =>
      let iIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds i).isSome
      let oIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds o).isSome
      readRangeFreePtrSafe bound env state i iLen &&
        readRangeFreePtrSafe bound env state o oLen &&
        exprFreePtrSafe bound fns env state iIsFp i &&
        exprFreePtrSafe bound fns env state oIsFp o &&
        exprFreePtrSafe bound fns env state false g &&
        exprFreePtrSafe bound fns env state false a &&
        exprFreePtrSafe bound fns env state false iLen &&
        exprFreePtrSafe bound fns env state false oLen
  | _, .call "msize" _ => false
  | _, .call func args =>
      if reservedBuiltins.contains func then
        memoryFreeBuiltins.contains func && exprsValueFreePtrSafe bound fns env state args
      else
        fns.contains func && exprsValueFreePtrSafe bound fns env state args

private def exprsValueFreePtrSafe (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (state : FpState) : List YulExpr → Bool
  | [] => true
  | e :: es =>
      exprFreePtrSafe bound fns env state false e &&
        exprsValueFreePtrSafe bound fns env state es
end

private def exprValueFreePtrSafe (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (state : FpState) (e : YulExpr) : Bool :=
  exprFreePtrSafe bound fns env state false e

private def exprAddrArgSafe (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (state : FpState) (addr : YulExpr) : Bool :=
  let addrIsFp := (fpAddrOffsetBound env.fpVars env.litVars env.u64Bounds addr).isSome
  exprFreePtrSafe bound fns env state addrIsFp addr

/-- Update `FpState` across a full-range memory write `(offset, len)` (`mstore`, `mstore8`,
`*copy`). Literal writes overlapping `[64, 96)` set `fpClean := false`, and set
`fpOverwritten := true` only when all 32 bytes `[64, 96)` are overwritten. -/
private def writeRangeFreePtrStep (bound : Nat) (env : FreePtrEnv) (state : FpState)
    (offset len : YulExpr) : Option FpState :=
  if constRangeDisjointFromFp bound env.litVars offset len ||
     fpHeapRange env.fpVars env.litVars env.u64Bounds offset len then
    some state
  else if constRangeCoversFp bound env.litVars offset len then
    some { state with fpClean := false, fpOverwritten := true }
  else if constRangeBelow bound env.litVars offset len then
    some { state with fpClean := false, fpOverwritten := false }
  else
    none

private def joinFpStates (a b : FpState) : FpState :=
  { fpClean := a.fpClean && b.fpClean
    fpOverwritten := a.fpOverwritten && b.fpOverwritten
    maxFp := max a.maxFp b.maxFp }

/-- Extract `(varName, upperBound)` when `stmt` unconditionally reverts if `varName > upperBound`
for an immutable scalar `varName ∈ env.immVars` (not in `fpVars`) with `upperBound < 2^64`. -/
private def dominatingU64GuardBound? (env : FreePtrEnv) : YulStmt → Option (String × Nat × List YulStmt)
  | .if_ (.call "gt" [.ident v, boundExpr]) rev =>
      if !env.fpVars.contains v && env.immVars.contains v && stmtsAlwaysTerminate rev then
        match exprUpperBound env.litVars env.u64Bounds boundExpr with
        | some ub => some (v, ub, rev)
        | none => none
      else
        none
  | .if_ (.call "iszero" [.call "lt" [.ident v, boundExpr]]) rev =>
      if !env.fpVars.contains v && env.immVars.contains v && stmtsAlwaysTerminate rev then
        match litConstExpr env.litVars boundExpr with
        | some b => if 0 < b && b ≤ 2 ^ 64 then some (v, b - 1, rev) else none
        | none => none
      else
        none
  | .block [ .let_ c (.call "iszero" [.call "gt" [.ident v, boundExpr]]),
             .if_ (.ident c1) [],
             .if_ (.call "iszero" [.ident c2]) rev ] =>
      if c == c1 && c == c2 && c != v && !envHasTrackedVar env c &&
         !env.fpVars.contains v && env.immVars.contains v && stmtsAlwaysTerminate rev then
        match exprUpperBound env.litVars env.u64Bounds boundExpr with
        | some ub => some (v, ub, rev)
        | none => none
      else
        none
  | .block [ .let_ c (.call "lt" [.ident v, boundExpr]),
             .if_ (.ident c1) [],
             .if_ (.call "iszero" [.ident c2]) rev ] =>
      if c == c1 && c == c2 && c != v && !envHasTrackedVar env c &&
         !env.fpVars.contains v && env.immVars.contains v && stmtsAlwaysTerminate rev then
        match litConstExpr env.litVars boundExpr with
        | some b => if 0 < b && b ≤ 2 ^ 64 then some (v, b - 1, rev) else none
        | none => none
      else
        none
  | _ => none

/-- Match the `next ≤ 2^64 - 1` guard of the compiler's checked-allocation idiom, returning its
revert branch statements for recursive checking. -/
private def allocU64GuardRev? (env : FreePtrEnv) (base next : String) :
    YulStmt → Option (List YulStmt)
  | .if_ (.call "gt" [.ident n, boundExpr]) rev =>
      if n == next && litConstExpr env.litVars boundExpr == some maxU64 &&
         stmtsAlwaysTerminate rev then
        some rev
      else
        none
  | .block [ .let_ c (.call "iszero" [.call "gt" [.ident n, boundExpr]]),
             .if_ (.ident c1) [],
             .if_ (.call "iszero" [.ident c2]) rev ] =>
      if n == next && c == c1 && c == c2 && c != base && c != next &&
         !envHasTrackedVar env c &&
         litConstExpr env.litVars boundExpr == some maxU64 &&
         stmtsAlwaysTerminate rev then
        some rev
      else
        none
  | _ => none

/-- Match the `next ≥ base` no-wraparound guard of the compiler's checked-allocation idiom,
returning its revert branch statements for recursive checking. -/
private def allocGeGuardRev? (env : FreePtrEnv) (base next : String) :
    YulStmt → Option (List YulStmt)
  | .if_ (.call "lt" [.ident n, .ident b]) rev =>
      if n == next && b == base && stmtsAlwaysTerminate rev then some rev else none
  | .block [ .let_ c (.call "iszero" [.call "lt" [.ident n, .ident b]]),
             .if_ (.ident c1) [],
             .if_ (.call "iszero" [.ident c2]) rev ] =>
      if n == next && b == base && c == c1 && c == c2 && c != base && c != next &&
         !envHasTrackedVar env c && stmtsAlwaysTerminate rev then
        some rev
      else
        none
  | _ => none

/-- Match a combined `if or(gt(next, 2^64 - 1), lt(next, base)) { revert }` guard. -/
private def allocCombinedGuardRev? (env : FreePtrEnv) (base next : String) :
    YulStmt → Option (List YulStmt)
  | .if_ (.call "or" [.call "gt" [.ident n1, boundExpr], .call "lt" [.ident n2, .ident b]]) rev
  | .if_ (.call "or" [.call "lt" [.ident n2, .ident b], .call "gt" [.ident n1, boundExpr]]) rev =>
      if n1 == next && n2 == next && b == base &&
         litConstExpr env.litVars boundExpr == some maxU64 &&
         stmtsAlwaysTerminate rev then
        some rev
      else
        none
  | _ => none

mutual
/-- Check a single statement under the per-case free-pointer static memory gate. -/
private def stmtFreePtrStep (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (allowAlloc allowFpBind : Bool) (state : FpState) : Nat → YulStmt → Option FpState
  | 0, _ => none
  | _ + 1, .comment _ => some state
  | _ + 1, .leave => none
  | _ + 1, .let_ name value =>
      if envHasTrackedVar env name then
        none
      else if exprValueFreePtrSafe bound fns env state value then
        some state
      else
        none
  | _ + 1, .letMany names value =>
      if names.any (envHasTrackedVar env) then
        none
      else if exprValueFreePtrSafe bound fns env state value then
        some state
      else
        none
  | _ + 1, .assign name value =>
      if envHasTrackedVar env name then
        none
      else if exprValueFreePtrSafe bound fns env state value then
        some state
      else
        none
  | _ + 1, .exprStmt (.call "mstore" [p, val]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprValueFreePtrSafe bound fns env state val then
        writeRangeFreePtrStep bound env state p (.lit 32)
      else
        none
  | _ + 1, .exprStmt (.call "mstore8" [p, val]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprValueFreePtrSafe bound fns env state val then
        writeRangeFreePtrStep bound env state p (.lit 1)
      else
        none
  | _ + 1, .exprStmt (.call "calldatacopy" [d, s, n])
  | _ + 1, .exprStmt (.call "codecopy" [d, s, n])
  | _ + 1, .exprStmt (.call "returndatacopy" [d, s, n])
  | _ + 1, .exprStmt (.call "datacopy" [d, s, n]) =>
      if exprAddrArgSafe bound fns env state d &&
         exprsValueFreePtrSafe bound fns env state [s, n] then
        writeRangeFreePtrStep bound env state d n
      else
        none
  | _ + 1, .exprStmt (.call "extcodecopy" [a, d, s, n]) =>
      if exprAddrArgSafe bound fns env state d &&
         exprsValueFreePtrSafe bound fns env state [a, s, n] then
        writeRangeFreePtrStep bound env state d n
      else
        none
  | _ + 1, .exprStmt (.call "mcopy" [d, s, n]) =>
      if exprAddrArgSafe bound fns env state d &&
         exprAddrArgSafe bound fns env state s &&
         exprValueFreePtrSafe bound fns env state n &&
         readRangeFreePtrSafe bound env state s n then
        writeRangeFreePtrStep bound env state d n
      else
        none
  | _ + 1, .exprStmt (.call "return" [p, n])
  | _ + 1, .exprStmt (.call "revert" [p, n]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprValueFreePtrSafe bound fns env state n &&
         readRangeFreePtrSafe bound env state p n then
        some state
      else
        none
  | _ + 1, .exprStmt (.call "log0" [p, n]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprValueFreePtrSafe bound fns env state n &&
         readRangeFreePtrSafe bound env state p n then
        some state
      else
        none
  | _ + 1, .exprStmt (.call "log1" [p, n, t1]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprsValueFreePtrSafe bound fns env state [n, t1] &&
         readRangeFreePtrSafe bound env state p n then
        some state
      else
        none
  | _ + 1, .exprStmt (.call "log2" [p, n, t1, t2]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprsValueFreePtrSafe bound fns env state [n, t1, t2] &&
         readRangeFreePtrSafe bound env state p n then
        some state
      else
        none
  | _ + 1, .exprStmt (.call "log3" [p, n, t1, t2, t3]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprsValueFreePtrSafe bound fns env state [n, t1, t2, t3] &&
         readRangeFreePtrSafe bound env state p n then
        some state
      else
        none
  | _ + 1, .exprStmt (.call "log4" [p, n, t1, t2, t3, t4]) =>
      if exprAddrArgSafe bound fns env state p &&
         exprsValueFreePtrSafe bound fns env state [n, t1, t2, t3, t4] &&
         readRangeFreePtrSafe bound env state p n then
        some state
      else
        none
  | _ + 1, .exprStmt (.call func args) =>
      if exprValueFreePtrSafe bound fns env state (.call func args) then some state else none
  | _ + 1, .exprStmt _ => none
  | fuel + 1, .if_ cond body =>
      if !exprValueFreePtrSafe bound fns env state cond then
        none
      else
        match stmtsFreePtrStep bound fns env allowAlloc allowFpBind state [] fuel body with
        | none => none
        | some (stateAfter, _) =>
            some (if stmtsAlwaysTerminate body then state else joinFpStates state stateAfter)
  | fuel + 1, .for_ init cond post body =>
      match stmtsFreePtrStep bound fns env false false state (post ++ body) fuel init with
      | none => none
      | some (stateInit, envInit) =>
          if !exprValueFreePtrSafe bound fns envInit stateInit cond then
            none
          else
            let envBody :=
              match cond with
              | .call "lt" [.ident idx, countExpr] =>
                  if !envInit.fpVars.contains idx &&
                     !stmtsAssignIdent idx body then
                    match exprUpperBound envInit.litVars envInit.u64Bounds countExpr with
                    | some ub => if 0 < ub then envAddU64 envInit idx (ub - 1) else envInit
                    | none => envInit
                  else
                    envInit
              | _ => envInit
            match stmtsFreePtrStep bound fns envBody false false stateInit [] fuel body with
            | none => none
            | some (stateBody, _) =>
                match stmtsFreePtrStep bound fns envInit false false stateBody [] fuel post with
                | none => none
                | some (statePost, _) =>
                    if stmtsAlwaysTerminate body then
                      some stateInit
                    else if stateBody == stateInit && statePost == stateInit then
                      some stateInit
                    else
                      none
  | fuel + 1, .switch expr cases default =>
      if !exprValueFreePtrSafe bound fns env state expr then
        none
      else
        match casesFreePtrStep bound fns env allowAlloc allowFpBind state fuel cases with
        | none => none
        | some maybeCasesState =>
            match default with
            | none =>
                some (match maybeCasesState with
                      | none => state
                      | some cs => joinFpStates state cs)
            | some dbody =>
                match stmtsFreePtrStep bound fns env allowAlloc allowFpBind state [] fuel dbody with
                | none => none
                | some (dState, _) =>
                    if stmtsAlwaysTerminate dbody then
                      some (maybeCasesState.getD dState)
                    else
                      some (match maybeCasesState with
                            | none => dState
                            | some cs => joinFpStates cs dState)
  | fuel + 1, .block stmts =>
      match stmtsFreePtrStep bound fns env allowAlloc allowFpBind state [] fuel stmts with
      | none => none
      | some (stateAfter, _) => some stateAfter
  | _ + 1, .funcDef _ _ _ _ => none

/-- Check a statement list sequentially under the per-case free-pointer static memory gate.
`scopeTail` holds statements in enclosing constructs (such as `for` `post ++ body`) where
bindings introduced in this list remain in scope. -/
private def stmtsFreePtrStep (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (allowAlloc allowFpBind : Bool) (state : FpState) (scopeTail : List YulStmt) :
    Nat → List YulStmt → Option (FpState × FreePtrEnv)
  | 0, _ => none
  | _ + 1, [] => some (state, env)
  | _ + 1,
    [ .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, .ident sz]),
      .exprStmt (.call "revert" [.lit 0, .ident sz']) ] =>
      if scopeTail.isEmpty && sz == sz' && sz.startsWith "__" && !env.fpVars.contains sz then
        some ({ state with fpClean := false, fpOverwritten := false }, env)
      else
        none
  | fuel + 1,
    (.let_ base rhsBase) :: (.let_ next (.call "add" [a, b])) :: s3 :: s4 ::
      (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest =>
      let fullAfterBase :=
        (.let_ next (.call "add" [a, b])) :: s3 :: s4 ::
          (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest ++ scopeTail
      let fullAfterNext :=
        s3 :: s4 :: (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest ++ scopeTail
      let sizeExpr? :=
        if a == .ident base then some b
        else if b == .ident base then some a
        else none
      let guardRevs? :=
        match allocU64GuardRev? env base next s3, allocGeGuardRev? env base next s4 with
        | some r1, some r2 => some (r1, r2)
        | _, _ =>
            match allocGeGuardRev? env base next s3, allocU64GuardRev? env base next s4 with
            | some r1, some r2 => some (r1, r2)
            | _, _ => none
      match sizeExpr?, guardRevs? with
      | some sizeExpr, some (rev1, rev2) =>
          let envAfterBase := envAddFp env base
          let envWithAlloc := envAddFp envAfterBase next
          match exprUpperBound env.litVars env.u64Bounds sizeExpr with
          | some sizeUb =>
              if allowAlloc && allowFpBind && state.fpClean &&
                 state.maxFp + sizeUb ≤ maxU64 &&
                 isMload64 env.litVars rhsBase &&
                 base != next && next == nextUse &&
                 litConstExpr env.litVars slot64 == some 64 &&
                 isFreshImmutable env base fullAfterBase &&
                 isFreshImmutable envAfterBase next fullAfterNext &&
                 exprValueFreePtrSafe bound fns envAfterBase state sizeExpr &&
                 (stmtsFreePtrStep bound fns envWithAlloc false false state [] fuel rev1).isSome &&
                 (stmtsFreePtrStep bound fns envWithAlloc false false state [] fuel rev2).isSome then
                let nextState : FpState :=
                  { fpClean := true, fpOverwritten := false, maxFp := state.maxFp + sizeUb }
                stmtsFreePtrStep bound fns envWithAlloc allowAlloc allowFpBind nextState
                  scopeTail fuel rest
              else
                none
          | none => none
      | _, _ =>
          stmtsFreePtrStepSingle bound fns env allowAlloc allowFpBind state scopeTail fuel
            (.let_ base rhsBase)
            ((.let_ next (.call "add" [a, b])) :: s3 :: s4 ::
              (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest)
  | fuel + 1,
    (.let_ base rhsBase) :: (.let_ next (.call "add" [a, b])) :: s3 ::
      (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest =>
      let fullAfterBase :=
        (.let_ next (.call "add" [a, b])) :: s3 ::
          (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest ++ scopeTail
      let fullAfterNext :=
        s3 :: (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest ++ scopeTail
      let sizeExpr? :=
        if a == .ident base then some b
        else if b == .ident base then some a
        else none
      match sizeExpr?, allocCombinedGuardRev? env base next s3 with
      | some sizeExpr, some rev =>
          let envAfterBase := envAddFp env base
          let envWithAlloc := envAddFp envAfterBase next
          match exprUpperBound env.litVars env.u64Bounds sizeExpr with
          | some sizeUb =>
              if allowAlloc && allowFpBind && state.fpClean &&
                 state.maxFp + sizeUb ≤ maxU64 &&
                 isMload64 env.litVars rhsBase &&
                 base != next && next == nextUse &&
                 litConstExpr env.litVars slot64 == some 64 &&
                 isFreshImmutable env base fullAfterBase &&
                 isFreshImmutable envAfterBase next fullAfterNext &&
                 exprValueFreePtrSafe bound fns envAfterBase state sizeExpr &&
                 (stmtsFreePtrStep bound fns envWithAlloc false false state [] fuel rev).isSome then
                let nextState : FpState :=
                  { fpClean := true, fpOverwritten := false, maxFp := state.maxFp + sizeUb }
                stmtsFreePtrStep bound fns envWithAlloc allowAlloc allowFpBind nextState
                  scopeTail fuel rest
              else
                none
          | none => none
      | _, _ =>
          stmtsFreePtrStepSingle bound fns env allowAlloc allowFpBind state scopeTail fuel
            (.let_ base rhsBase)
            ((.let_ next (.call "add" [a, b])) :: s3 ::
              (.exprStmt (.call "mstore" [slot64, .ident nextUse])) :: rest)
  | fuel + 1, s :: ss =>
      stmtsFreePtrStepSingle bound fns env allowAlloc allowFpBind state scopeTail fuel s ss

/-- Single-statement step helper for `stmtsFreePtrStep`. -/
private def stmtsFreePtrStepSingle (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (allowAlloc allowFpBind : Bool) (state : FpState) (scopeTail : List YulStmt) :
    Nat → YulStmt → List YulStmt → Option (FpState × FreePtrEnv)
  | 0, _, _ => none
  | fuel + 1, s, ss =>
      let fullRest := ss ++ scopeTail
      match s with
      | .let_ v rhs =>
          if state.fpClean && isMload64 env.litVars rhs then
            if allowFpBind && isFreshImmutable env v fullRest then
              stmtsFreePtrStep bound fns (envAddFp env v) allowAlloc allowFpBind state
                scopeTail fuel ss
            else
              none
          else
            match stmtFreePtrStep bound fns env allowAlloc allowFpBind state fuel s with
            | none => none
            | some stateNext =>
                let env' :=
                  if isFreshImmutable env v fullRest then
                    let env1 := { env with immVars := v :: env.immVars }
                    let env2 :=
                      match litConstExpr env.litVars rhs with
                      | some n => { env1 with litVars := (v, n) :: env1.litVars }
                      | none => env1
                    match exprUpperBound env.litVars env.u64Bounds rhs with
                    | some ub => envAddU64 env2 v ub
                    | none => env2
                  else
                    env
                stmtsFreePtrStep bound fns env' allowAlloc allowFpBind stateNext scopeTail fuel ss
      | _ =>
          match stmtFreePtrStep bound fns env allowAlloc allowFpBind state fuel s with
          | none => none
          | some stateNext =>
              if stmtAlwaysTerminates s then
                match stmtsFreePtrStep bound fns env allowAlloc allowFpBind stateNext scopeTail
                    fuel ss with
                | none => none
                | some _ => some (stateNext, env)
              else
                let env' :=
                  match dominatingU64GuardBound? env s with
                  | some (v, ub, _) => envAddU64 env v ub
                  | none => env
                stmtsFreePtrStep bound fns env' allowAlloc allowFpBind stateNext scopeTail fuel ss

/-- `stmtFreePtrStep` across switch cases; returns `none` on gate failure, `some none` when all
cases terminate, or `some (some joinedState)` over non-terminating cases. -/
private def casesFreePtrStep (bound : Nat) (fns : List String) (env : FreePtrEnv)
    (allowAlloc allowFpBind : Bool) (state : FpState) :
    Nat → List (Nat × List YulStmt) → Option (Option FpState)
  | 0, _ => none
  | _ + 1, [] => some none
  | fuel + 1, (_, body) :: rest =>
      match stmtsFreePtrStep bound fns env allowAlloc allowFpBind state [] fuel body,
            casesFreePtrStep bound fns env allowAlloc allowFpBind state fuel rest with
      | some (bodyState, _), some restState =>
          if stmtsAlwaysTerminate body then
            some restState
          else
            some (some (match restState with
                        | none => bodyState
                        | some rs => joinFpStates bodyState rs))
      | _, _ => none
end

mutual
private def stmtAstNodes : YulStmt → Nat
  | .if_ _ body | .block body | .funcDef _ _ _ body => 1 + stmtsAstNodes body
  | .for_ init _ post body =>
      1 + stmtsAstNodes init + stmtsAstNodes post + stmtsAstNodes body
  | .switch _ cases default =>
      1 + casesAstNodes cases +
        match default with
        | none => 0
        | some dbody => stmtsAstNodes dbody
  | _ => 1

private def stmtsAstNodes : List YulStmt → Nat
  | [] => 1
  | s :: ss => 1 + stmtAstNodes s + stmtsAstNodes ss

private def casesAstNodes : List (Nat × List YulStmt) → Nat
  | [] => 1
  | (_, body) :: rest => 1 + stmtsAstNodes body + casesAstNodes rest
end

/-- Check whether a single dispatch `case` body can safely place spill words at
`[defaultSpillBase, H)` by initializing `mstore(64, H)` at case entry. Static accesses must end at
or below `bound` (`128`, the unspilled initial free pointer) so moving the heap from `128` to `H`
cannot change aliasing between static accesses and heap allocations.
Precondition: every function named in `fns` satisfies `stmtsMemoryStaticBelow 64 fns`. -/
private def caseMemoryFreePtrSafe (bound : Nat) (fns : List String)
    (caseBody : List YulStmt) : Bool :=
  let fuel := 4 * stmtsAstNodes caseBody + 16
  let initState : FpState :=
    { fpClean := true, fpOverwritten := false, maxFp := maxSpillHighWater }
  (stmtsFreePtrStep bound fns {} true true initState [] fuel caseBody).isSome

/-- Rewrite one dispatch `case` arm when `stmtsAlwaysTerminate caseBody` holds:
1. If `stmtsMemoryStaticBelow defaultSpillBase fns caseBody`, spill directly at `defaultSpillBase`
   (leaving `mem[64]` untouched).
2. Else if `caseMemoryFreePtrSafe defaultInitialFreePtr fns caseBody`, spill at `defaultSpillBase`
   and (when at least one word spilled, `highWater > 0`) prepend `mstore(64, highWater)` at case
   entry without rewriting any `mstore(64, ...)` inside `caseBody`.
3. Otherwise leave `caseBody` unchanged (fail-closed).
Precondition: every function named in `fns` satisfies `stmtsMemoryStaticBelow 64 fns`. -/
private def reuseAndSpillDispatchCase
    (maxStackLocals : Nat) (fns : List String) (caseBody : List YulStmt) : List YulStmt :=
  if !stmtsAlwaysTerminate caseBody then
    caseBody
  else if stmtsMemoryStaticBelow defaultSpillBase fns caseBody then
    let rewritten := reuseAndSpillTemps maxStackLocals [] true caseBody
    if spillHighWaterStmts rewritten ≤ maxSpillHighWater then rewritten else caseBody
  else if caseMemoryFreePtrSafe defaultInitialFreePtr fns caseBody then
    let rewritten := reuseAndSpillTemps maxStackLocals [] true caseBody
    let highWater := spillHighWaterStmts rewritten
    if highWater == 0 then
      rewritten
    else if highWater ≤ maxSpillHighWater && highWater % 32 == 0 then
      .exprStmt (.call "mstore" [.lit 64, .lit highWater]) :: rewritten
    else
      caseBody
  else
    caseBody

private def reuseAndSpillDispatchedCases (maxStackLocals : Nat) (fns : List String) :
    List (Nat × List YulStmt) → List (Nat × List YulStmt)
  | [] => []
  | (tag, body) :: rest =>
      (tag, reuseAndSpillDispatchCase maxStackLocals fns body) ::
        reuseAndSpillDispatchedCases maxStackLocals fns rest

private def splitLeadingFuncDefs : List YulStmt → List YulStmt × List YulStmt
  | (.funcDef name params rets body) :: rest =>
      let (defs, tail) := splitLeadingFuncDefs rest
      (.funcDef name params rets body :: defs, tail)
  | rest => ([], rest)

/-- Spill a runtime code section: uses whole-section static spilling when `sectionMemoryStaticBelow`
holds, otherwise pattern-matches the exact `[funcDefs..., mstore(64, 128), buildSwitch]` runtime
shape emitted by `CodegenCommon.runtimeCode` (when all section helper `funcDef`s stay within
`[0, 64)`) and applies `reuseAndSpillDispatchCase` to each selector arm and whole default arm.
Any other section shape is returned unchanged. -/
def reuseAndSpillTempsDispatchedSection (maxStackLocals : Nat) (code : List YulStmt) :
    List YulStmt :=
  if sectionMemoryStaticBelow defaultSpillBase code then
    reuseAndSpillTemps maxStackLocals [] true code
  else
    let (funcDefs, tail) := splitLeadingFuncDefs code
    let fns := funcDefs.filterMap fun
      | .funcDef name _ _ _ => some name
      | _ => none
    if !(fns.all fun name => !reservedBuiltins.contains name) ||
       !stmtsFuncDefsMemoryStaticBelow 64 fns funcDefs ||
       !(stmtsFuncDefNames tail).isEmpty then
      code
    else
      match tail with
      | [ .exprStmt (.call "mstore" [.lit 64, .lit 128]),
          .block [
            .let_ "__has_selector"
              (.call "iszero" [.call "lt" [.call "calldatasize" [], .lit 4]]),
            .if_ (.call "iszero" [.ident "__has_selector"]) noSelectorDefault,
            .if_ (.ident "__has_selector")
              [ .switch
                  (.call "shr" [.lit 224, .call "calldataload" [.lit 0]])
                  cases
                  (some switchDefault) ]
          ] ] =>
          if stmtsAssignIdent "__has_selector" noSelectorDefault then
            code
          else
            let noSelectorDefault' :=
              reuseAndSpillDispatchCase maxStackLocals fns noSelectorDefault
            let cases' := reuseAndSpillDispatchedCases maxStackLocals fns cases
            let switchDefault' :=
              reuseAndSpillDispatchCase maxStackLocals fns switchDefault
            funcDefs ++ [
              .exprStmt (.call "mstore" [.lit 64, .lit 128]),
              .block [
                .let_ "__has_selector"
                  (.call "iszero" [.call "lt" [.call "calldatasize" [], .lit 4]]),
                .if_ (.call "iszero" [.ident "__has_selector"]) noSelectorDefault',
                .if_ (.ident "__has_selector")
                  [ .switch
                      (.call "shr" [.lit 224, .call "calldataload" [.lit 0]])
                      cases'
                      (some switchDefault') ]
              ]
            ]
      | _ => code

/-- Entry point for `Compiler.emitYulSpilled` (Solidity import model Yul emission): applies
`reuseAndSpillTempsStaticSection` to `deployCode` and `reuseAndSpillTempsDispatchedSection`
to `runtimeCode`. -/
def reuseAndSpillTempsDispatchedObject
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (obj : YulObject) : YulObject :=
  { obj with
    deployCode := reuseAndSpillTempsStaticSection maxStackLocals obj.deployCode
    runtimeCode := reuseAndSpillTempsDispatchedSection maxStackLocals obj.runtimeCode }

end Compiler.Yul.TempReuse
