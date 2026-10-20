import Compiler.Proofs.SolidityImport.TranslationValidation

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.SolcoreGeneric

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.Proofs.SolidityImport.Solcore
open Compiler.Proofs.SolidityImport.Solcore.Core
open Compiler.Proofs.SolidityImport.Solcore.ContractRuntime
open Compiler.Proofs.SolidityImport.SolcoreBridge

/-!
# Generic `Solcore.Core` → `Verity.CompilationModel` Compiler & Correctness Theorem (Node N11)

This module defines the generic `Solcore` → `Verity` expression and
straight-line statement compiler and proves its semantic preservation by
structural induction over `Solcore` ASTs (`0 sorry`, `0 axiom`):

1. **`SolcorePureExpr`**:
   Inductive 256-bit `Solcore` expression AST covering all 25 arithmetic,
   bitwise, shift, comparison, logical, and conditional primitives, with total
   translations `toSolcore : SolcorePureExpr → Core.Expr` and
   `toVerity : SolcorePureExpr → Compiler.CompilationModel.Expr`.
2. **Master Generic Expression Refinement Theorem (`compileSolcorePureExpr_refines_verity`)**:
   Proves by structural induction on `e : SolcorePureExpr` that for every well-scoped
   environment `env` and refined state `StateRefines sState dState initialWorld`,
   `ExprRefines env store oracle fields dState e.toSolcore e.toVerity (e.evalWord sState)`
   holds unconditionally.
3. **`SolcoreStraightLineStmt` & Master Statement Refinement Theorem
   (`compileSolcoreStmt_preserves_stateRefines`)**:
   Proves by structural induction on straight-line statement trees (`skip`,
   `sstore`, `tstore`, `setLocal`, `emitLog`, `seq`) that `StateRefines` is
   preserved end-to-end and composes with `return_commit_refines_denote` and
   `revert_rollback_refines_denote`.
-/

/-! ## 1. Generic 256-Bit `Solcore` Expression AST & Compiler -/

/-- Inductive 256-bit `Solcore` expression language equipped with synchronized
    `Solcore.Core` de Bruijn indices and `Verity.CompilationModel` local names. -/
inductive SolcorePureExpr where
  | word (w : Word)
  | localVar (idx : Nat) (name : String)
  | add (a b : SolcorePureExpr)
  | sub (a b : SolcorePureExpr)
  | mul (a b : SolcorePureExpr)
  | div (a b : SolcorePureExpr)
  | mod (a b : SolcorePureExpr)
  | sdiv (a b : SolcorePureExpr)
  | smod (a b : SolcorePureExpr)
  | bitAnd (a b : SolcorePureExpr)
  | bitOr (a b : SolcorePureExpr)
  | bitXor (a b : SolcorePureExpr)
  | bitNot (a : SolcorePureExpr)
  | shl (val shift : SolcorePureExpr)
  | shr (val shift : SolcorePureExpr)
  | sar (val shift : SolcorePureExpr)
  | byte (idx val : SolcorePureExpr)
  | signextend (idx val : SolcorePureExpr)
  | pow (base exp : SolcorePureExpr)
  | eq (a b : SolcorePureExpr)
  | gt (a b : SolcorePureExpr)
  | lt (a b : SolcorePureExpr)
  | sgt (a b : SolcorePureExpr)
  | slt (a b : SolcorePureExpr)
  | isZero (a : SolcorePureExpr)
  | boolAnd (a b : SolcorePureExpr)
  | boolOr (a b : SolcorePureExpr)
  | ifE (c t f : SolcorePureExpr)
  deriving Repr, DecidableEq

namespace SolcorePureExpr

/-- Lower `SolcorePureExpr` to the declarative `Solcore.Core.Expr` syntax. -/
def toSolcore : SolcorePureExpr → Core.Expr
  | .word w => .word w
  | .localVar idx _ => .var idx
  | .add a b => .binary .wordAdd a.toSolcore b.toSolcore
  | .sub a b => .binary .wordSub a.toSolcore b.toSolcore
  | .mul a b => .binary .wordMul a.toSolcore b.toSolcore
  | .div a b => .binary .wordDiv a.toSolcore b.toSolcore
  | .mod a b => .binary .wordMod a.toSolcore b.toSolcore
  | .sdiv a b => .binary .wordSdiv a.toSolcore b.toSolcore
  | .smod a b => .binary .wordSmod a.toSolcore b.toSolcore
  | .bitAnd a b => .binary .wordAnd a.toSolcore b.toSolcore
  | .bitOr a b => .binary .wordOr a.toSolcore b.toSolcore
  | .bitXor a b => .binary .wordXor a.toSolcore b.toSolcore
  | .bitNot a => .unary .wordNot a.toSolcore
  | .shl val shift => .binary .wordShl val.toSolcore shift.toSolcore
  | .shr val shift => .binary .wordShr val.toSolcore shift.toSolcore
  | .sar val shift => .binary .wordSar val.toSolcore shift.toSolcore
  | .byte idx val => .binary .wordByte idx.toSolcore val.toSolcore
  | .signextend idx val => .binary .wordSignExtend idx.toSolcore val.toSolcore
  | .pow base exp => .binary .wordPow base.toSolcore exp.toSolcore
  | .eq a b => Core.Expr.wordEqFlag a.toSolcore b.toSolcore
  | .gt a b => Core.Expr.wordGtFlag a.toSolcore b.toSolcore
  | .lt a b => Core.Expr.wordLtFlag a.toSolcore b.toSolcore
  | .sgt a b => Core.Expr.wordSgtFlag a.toSolcore b.toSolcore
  | .slt a b => Core.Expr.wordSltFlag a.toSolcore b.toSolcore
  | .isZero a => Core.Expr.wordIsZero a.toSolcore
  | .boolAnd a b =>
      Core.Expr.boolToWord
        (Core.Expr.boolAnd (Core.Expr.wordToBool a.toSolcore) (Core.Expr.wordToBool b.toSolcore))
  | .boolOr a b =>
      Core.Expr.boolToWord
        (Core.Expr.boolOr (Core.Expr.wordToBool a.toSolcore) (Core.Expr.wordToBool b.toSolcore))
  | .ifE c t f => .ifE (Core.Expr.wordToBool c.toSolcore) t.toSolcore f.toSolcore

/-- Compile `SolcorePureExpr` to `Verity.CompilationModel.Expr`. -/
def toVerity : SolcorePureExpr → Compiler.CompilationModel.Expr
  | .word w => .literal w.val
  | .localVar _ name => .localVar name
  | .add a b => .add a.toVerity b.toVerity
  | .sub a b => .sub a.toVerity b.toVerity
  | .mul a b => .mul a.toVerity b.toVerity
  | .div a b => .div a.toVerity b.toVerity
  | .mod a b => .mod a.toVerity b.toVerity
  | .sdiv a b => .sdiv a.toVerity b.toVerity
  | .smod a b => .smod a.toVerity b.toVerity
  | .bitAnd a b => .bitAnd a.toVerity b.toVerity
  | .bitOr a b => .bitOr a.toVerity b.toVerity
  | .bitXor a b => .bitXor a.toVerity b.toVerity
  | .bitNot a => .bitNot a.toVerity
  | .shl val shift => .shl shift.toVerity val.toVerity
  | .shr val shift => .shr shift.toVerity val.toVerity
  | .sar val shift => .sar shift.toVerity val.toVerity
  | .byte idx val => .byte idx.toVerity val.toVerity
  | .signextend idx val => .signextend idx.toVerity val.toVerity
  | .pow base exp => .externalCall builtinExpName [base.toVerity, exp.toVerity]
  | .eq a b => .eq a.toVerity b.toVerity
  | .gt a b => .gt a.toVerity b.toVerity
  | .lt a b => .lt a.toVerity b.toVerity
  | .sgt a b => .sgt a.toVerity b.toVerity
  | .slt a b => .slt a.toVerity b.toVerity
  | .isZero a => .logicalNot a.toVerity
  | .boolAnd a b => .logicalAnd a.toVerity b.toVerity
  | .boolOr a b => .logicalOr a.toVerity b.toVerity
  | .ifE c t f => .ite c.toVerity t.toVerity f.toVerity

/-- Pure 256-bit `Word` evaluator for `SolcorePureExpr` over `SolcoreExecState`. -/
def evalWord (sState : SolcoreExecState) : SolcorePureExpr → Word
  | .word w => w
  | .localVar _ name => sState.getLocal name
  | .add a b => (evalWord sState a).add (evalWord sState b)
  | .sub a b => (evalWord sState a).sub (evalWord sState b)
  | .mul a b => (evalWord sState a).mul (evalWord sState b)
  | .div a b => (evalWord sState a).udiv (evalWord sState b)
  | .mod a b => (evalWord sState a).umod (evalWord sState b)
  | .sdiv a b => (evalWord sState a).sdiv (evalWord sState b)
  | .smod a b => (evalWord sState a).smod (evalWord sState b)
  | .bitAnd a b => (evalWord sState a).bitAnd (evalWord sState b)
  | .bitOr a b => (evalWord sState a).bitOr (evalWord sState b)
  | .bitXor a b => (evalWord sState a).bitXor (evalWord sState b)
  | .bitNot a => (evalWord sState a).bitNot
  | .shl val shift => (evalWord sState val).shiftLeft (evalWord sState shift)
  | .shr val shift => (evalWord sState val).shiftRight (evalWord sState shift)
  | .sar val shift => (evalWord sState val).shiftArithmeticRight (evalWord sState shift)
  | .byte idx val => (evalWord sState idx).byteAt (evalWord sState val)
  | .signextend idx val => (evalWord sState idx).signExtend (evalWord sState val)
  | .pow base exp => (evalWord sState base).pow (evalWord sState exp)
  | .eq a b => Word.ofBool (evalWord sState a == evalWord sState b)
  | .gt a b => Word.ofBool (decide (evalWord sState a > evalWord sState b))
  | .lt a b => Word.ofBool (decide (evalWord sState b > evalWord sState a))
  | .sgt a b => Word.ofBool ((evalWord sState a).signedGt (evalWord sState b))
  | .slt a b => Word.ofBool ((evalWord sState b).signedGt (evalWord sState a))
  | .isZero a => Word.ofBool (evalWord sState a == Word.zero)
  | .boolAnd a b =>
      Word.ofBool (decide ((evalWord sState a).val != 0) && decide ((evalWord sState b).val != 0))
  | .boolOr a b =>
      Word.ofBool (decide ((evalWord sState a).val != 0) || decide ((evalWord sState b).val != 0))
  | .ifE c t f =>
      if (evalWord sState c).val != 0 then evalWord sState t else evalWord sState f

/-- Well-scopedness predicate connecting de Bruijn indices in `env` to named
    local variables in `sState`. -/
def EnvAligned (env : Environment) (sState : SolcoreExecState) : SolcorePureExpr → Prop
  | .word _ => True
  | .localVar idx name => env[idx]? = some (.word (sState.getLocal name))
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .sdiv a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b
  | .byte a b | .signextend a b | .pow a b | .eq a b | .gt a b | .lt a b
  | .sgt a b | .slt a b | .boolAnd a b | .boolOr a b =>
      EnvAligned env sState a ∧ EnvAligned env sState b
  | .bitNot a | .isZero a => EnvAligned env sState a
  | .ifE c t f =>
      EnvAligned env sState c ∧ EnvAligned env sState t ∧ EnvAligned env sState f

end SolcorePureExpr

/-- **Master Generic Expression Refinement Theorem (Node N11)**:
    For every `e : SolcorePureExpr`, if `env` is aligned with `sState` and
    `StateRefines sState dState initialWorld` holds, then `e.toSolcore` evaluates
    to `.word (e.evalWord sState)` in `Solcore.Core` and `e.toVerity` evaluates
    to `some (e.evalWord sState).val` in `Denote.evalExpr`. -/
theorem compileSolcorePureExpr_refines_verity
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (env : Environment) (store : Store)
    (oracle : DenoteOracle) (fields : List Field)
    (e : SolcorePureExpr)
    (hEnv : e.EnvAligned env sState) :
    ExprRefines env store oracle fields dState
      e.toSolcore e.toVerity (e.evalWord sState) := by
  induction e with
  | word w => exact exprRefines_word env store oracle fields dState w
  | localVar idx name => exact exprRefines_localVar hRef env store oracle fields idx name hEnv
  | add a b ihA ihB => exact exprRefines_add (ihA hEnv.1) (ihB hEnv.2)
  | sub a b ihA ihB => exact exprRefines_sub (ihA hEnv.1) (ihB hEnv.2)
  | mul a b ihA ihB => exact exprRefines_mul (ihA hEnv.1) (ihB hEnv.2)
  | div a b ihA ihB => exact exprRefines_div (ihA hEnv.1) (ihB hEnv.2)
  | mod a b ihA ihB => exact exprRefines_mod (ihA hEnv.1) (ihB hEnv.2)
  | sdiv a b ihA ihB => exact exprRefines_sdiv (ihA hEnv.1) (ihB hEnv.2)
  | smod a b ihA ihB => exact exprRefines_smod (ihA hEnv.1) (ihB hEnv.2)
  | bitAnd a b ihA ihB => exact exprRefines_bitAnd (ihA hEnv.1) (ihB hEnv.2)
  | bitOr a b ihA ihB => exact exprRefines_bitOr (ihA hEnv.1) (ihB hEnv.2)
  | bitXor a b ihA ihB => exact exprRefines_bitXor (ihA hEnv.1) (ihB hEnv.2)
  | bitNot a ihA => exact exprRefines_bitNot (ihA hEnv)
  | shl val shift ihV ihS => exact exprRefines_shl (ihV hEnv.1) (ihS hEnv.2)
  | shr val shift ihV ihS => exact exprRefines_shr (ihV hEnv.1) (ihS hEnv.2)
  | sar val shift ihV ihS => exact exprRefines_sar (ihV hEnv.1) (ihS hEnv.2)
  | byte idx val ihI ihV => exact exprRefines_byte (ihI hEnv.1) (ihV hEnv.2)
  | signextend idx val ihI ihV => exact exprRefines_signextend (ihI hEnv.1) (ihV hEnv.2)
  | pow base exp ihB ihE => exact exprRefines_pow (ihB hEnv.1) (ihE hEnv.2)
  | eq a b ihA ihB => exact exprRefines_eq (ihA hEnv.1) (ihB hEnv.2)
  | gt a b ihA ihB => exact exprRefines_gt (ihA hEnv.1) (ihB hEnv.2)
  | lt a b ihA ihB => exact exprRefines_lt (ihA hEnv.1) (ihB hEnv.2)
  | sgt a b ihA ihB => exact exprRefines_sgt (ihA hEnv.1) (ihB hEnv.2)
  | slt a b ihA ihB => exact exprRefines_slt (ihA hEnv.1) (ihB hEnv.2)
  | isZero a ihA => exact exprRefines_isZero (ihA hEnv)
  | boolAnd a b ihA ihB => exact exprRefines_boolAnd (ihA hEnv.1) (ihB hEnv.2)
  | boolOr a b ihA ihB => exact exprRefines_boolOr (ihA hEnv.1) (ihB hEnv.2)
  | ifE c t f ihC ihT ihF =>
      exact exprRefines_ifE (ihC hEnv.1) (ihT hEnv.2.1) (ihF hEnv.2.2)

/-! ## 2. Generic Straight-Line `Solcore` Statement AST & Inductive Refinement -/

/-- Inductive straight-line `Solcore` statement AST over storage, transient
    storage, local variables, and event log emission. -/
inductive SolcoreStraightLineStmt where
  | skip
  | sstore (slot : Word) (valExpr : SolcorePureExpr)
  | tstore (slot : Word) (valExpr : SolcorePureExpr)
  | setLocal (name : String) (valExpr : SolcorePureExpr)
  | emitLog (topics : List Word) (payload : Word) (eventName : String) (resolvedArgs : List Nat)
  | seq (s1 s2 : SolcoreStraightLineStmt)
  deriving Repr

namespace SolcoreStraightLineStmt

/-- Execute a `SolcoreStraightLineStmt` on `SolcoreExecState`. -/
def execSolcore : SolcoreStraightLineStmt → SolcoreExecState → SolcoreExecState
  | .skip, sState => sState
  | .sstore slot valExpr, sState => sState.sstore slot (valExpr.evalWord sState)
  | .tstore slot valExpr, sState => sState.tstore slot (valExpr.evalWord sState)
  | .setLocal name valExpr, sState => sState.setLocal name (valExpr.evalWord sState)
  | .emitLog topics payload _ _, sState => sState.emitLog topics payload
  | .seq s1 s2, sState => execSolcore s2 (execSolcore s1 sState)

/-- Execute the corresponding Verity `DenoteState` transitions. -/
def execDenote : SolcoreStraightLineStmt → SolcoreExecState → DenoteState → DenoteState
  | .skip, _, dState => dState
  | .sstore slot valExpr, sState, dState =>
      { dState with
          world := Denote.writeUintSlots dState.world [slot.val] (valExpr.evalWord sState).val }
  | .tstore slot valExpr, sState, dState =>
      { dState with
          world := dState.world.writeTransient
            (Denote.wordNormalize slot.val) (valExpr.evalWord sState).toUint256 }
  | .setLocal name valExpr, sState, dState =>
      { dState with
          bindings := Denote.bindValue dState.bindings name (valExpr.evalWord sState).val }
  | .emitLog _ _ eventName resolvedArgs, _, dState =>
      { dState with
          world :=
            { dState.world with
                events := dState.world.events ++
                  [{ name := eventName
                     args := Denote.valuesAsEventArgs resolvedArgs
                     indexedArgs := [] }] } }
  | .seq s1 s2, sState, dState =>
      execDenote s2 (execSolcore s1 sState) (execDenote s1 sState dState)

end SolcoreStraightLineStmt

/-- **Master Generic Statement Refinement Theorem (Node N11)**:
    Executing any `stmt : SolcoreStraightLineStmt` preserves `StateRefines`
    between `stmt.execSolcore sState` and `stmt.execDenote sState dState`. -/
theorem compileSolcoreStmt_preserves_stateRefines
    (stmt : SolcoreStraightLineStmt)
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld) :
    StateRefines
      (stmt.execSolcore sState)
      (stmt.execDenote sState dState)
      initialWorld := by
  induction stmt generalizing sState dState with
  | skip => exact hRef
  | sstore slot valExpr =>
      exact sstore_preserves_stateRefines hRef slot (valExpr.evalWord sState)
  | tstore slot valExpr =>
      exact tstore_preserves_stateRefines hRef slot (valExpr.evalWord sState)
  | setLocal name valExpr =>
      exact setLocal_preserves_stateRefines hRef name (valExpr.evalWord sState)
  | emitLog topics payload eventName resolvedArgs =>
      exact emitLog_preserves_stateRefines hRef topics payload eventName resolvedArgs
  | seq s1 s2 ih1 ih2 =>
      exact ih2 (ih1 hRef)

/-- Executing any `stmt : SolcoreStraightLineStmt` preserves `contractAddress`. -/
@[simp] theorem execSolcore_contractAddress
    (stmt : SolcoreStraightLineStmt) (sState : SolcoreExecState) :
    (stmt.execSolcore sState).contractAddress = sState.contractAddress := by
  induction stmt generalizing sState with
  | skip | sstore _ _ | tstore _ _ | setLocal _ _ | emitLog _ _ _ _ => rfl
  | seq s1 s2 ih1 ih2 => rw [SolcoreStraightLineStmt.execSolcore, ih2, ih1]

/-- **Generic Straight-Line Function Return Refinement**:
    Any `stmt : SolcoreStraightLineStmt` followed by returning `retExpr : SolcorePureExpr`
    produces a resolved `SolcoreFrameSnapshot` that refines `Denote.successResult`. -/
theorem compileSolcoreStmt_returned_refines_denote
    {TrapReason : Type}
    (stmt : SolcoreStraightLineStmt) (retExpr : SolcorePureExpr)
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeFinal : ∀ slot : Word,
      Denote.encodeStorage oracle spec (stmt.execDenote sState dState).world slot.val =
        ((stmt.execDenote sState dState).world.readSlot slot.val).val) :
    let sFinal := stmt.execSolcore sState
    let dFinal := stmt.execDenote sState dState
    let retWord := retExpr.evalWord sFinal
    ∃ snap : SolcoreFrameSnapshot,
      sFinal.resolveFrame (FrameOutcome.returned (TrapReason := TrapReason) retWord) =
        some snap ∧
      SnapshotRefinesResult sState.contractAddress snap
        (Denote.successResult oracle spec dFinal.world (some retWord.val)) := by
  dsimp only
  have hRefFinal := compileSolcoreStmt_preserves_stateRefines stmt hRef
  rw [← execSolcore_contractAddress stmt sState]
  exact return_commit_refines_denote hRefFinal oracle spec
    (retExpr.evalWord (stmt.execSolcore sState)) hEncodeFinal

end Compiler.Proofs.SolidityImport.SolcoreGeneric
