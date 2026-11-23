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
New spill slots start above any spill slot already used inside `stmts`. -/
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

mutual
/-- Recursively apply temporary reuse and spilling across a `YulStmt`.

Spill slots are fixed memory words, so spilling is only sound where no other live frame can
touch the same words. A function body never spills: it runs while its caller's spilled locals
are live and may recurse into itself, and its slots would not be disjoint from either. A `for`
initialiser never spills: its variables stay live while the body and post blocks run. Both
still reuse dead stack temporaries; a body that remains too deep fails closed in solc
(StackTooDeep) instead of aliasing memory. -/
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
        (reuseAndSpillTemps maxStackLocals protectedNames false init)
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
section) to `minFree` when that is higher. Spill slots live at fixed addresses from
`defaultSpillBase`; unless the free pointer starts above them, a runtime-sized allocation
(a `calldatacopy` of a `bytes` argument, an ABI encoding) can overwrite spilled locals. -/
def raiseFreePointerInit (minFree : Nat) : List YulStmt → List YulStmt
  | [] => []
  | (.exprStmt (.call "mstore" [.lit 64, .lit init])) :: rest =>
      .exprStmt (.call "mstore" [.lit 64, .lit (max init minFree)]) :: raiseFreePointerInit minFree rest
  | s :: rest => s :: raiseFreePointerInit minFree rest

/-- Spill a code section, then start its free memory above the spill slots it uses. -/
def reuseAndSpillTempsSection (maxStackLocals : Nat) (code : List YulStmt) : List YulStmt :=
  let spilled := reuseAndSpillTemps maxStackLocals [] true code
  let highWater := spillHighWaterStmts spilled
  if highWater = 0 then spilled else raiseFreePointerInit highWater spilled

/-- Apply temporary reuse and scratch-memory spilling to a full `YulObject`. When a code
section spills, its free-memory pointer starts above the spill slots, so memory allocated
at runtime never aliases a spilled local. -/
def reuseAndSpillTempsObject
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (obj : YulObject) : YulObject :=
  { obj with
    deployCode := reuseAndSpillTempsSection maxStackLocals obj.deployCode
    runtimeCode := reuseAndSpillTempsSection maxStackLocals obj.runtimeCode }

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
    "returndatasize", "datasize", "dataoffset", "invalid", "selfdestruct" ]

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

/-- Spill a code section only when the spill words are provably disjoint from every other
memory access: each access in `code` has a literal address and length below
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

/-- `reuseAndSpillTempsStaticSection` on the deploy and runtime code of a `YulObject`. -/
def reuseAndSpillTempsStaticObject
    (maxStackLocals : Nat := defaultMaxStackLocals)
    (obj : YulObject) : YulObject :=
  { obj with
    deployCode := reuseAndSpillTempsStaticSection maxStackLocals obj.deployCode
    runtimeCode := reuseAndSpillTempsStaticSection maxStackLocals obj.runtimeCode }

end Compiler.Yul.TempReuse
