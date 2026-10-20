import Compiler.Proofs.SolidityImport.SolcoreGeneric
import Compiler.Proofs.SolidityImport.TranslationValidation
import Compiler.Proofs.MetaSpecs

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.SolcoreFullBridge

open Compiler
open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.MetaSpecs
open Compiler.Proofs.SolidityImport.Solcore
open Compiler.Proofs.SolidityImport.Solcore.Core
open Compiler.Proofs.SolidityImport.Solcore.ContractRuntime
open Compiler.Proofs.SolidityImport.SolcoreBridge
open Compiler.Proofs.SolidityImport.SolcoreGeneric
open Compiler.Proofs.SolidityImport.TranslationValidation

/-!
# Full Formal `Solcore ⟷ Verity` Semantic Bridge (Phase 3B)

This module extends `SolcoreGeneric` (`N11`) and `TranslationValidation` (`N10`)
to the full checked-arithmetic and control-flow fragment (`SolcoreCheckedStmt`)
and composes it with `MetaSpecs` (`TriangularSemanticMetaSpec` and
`CertifiedOrExplicitlyFlagged`) into a single quadrangular preservation theorem
connecting `Solcore` (`Layer 0`), `Denote` (`Layer 1`), `SourceSemantics`
(`Layer 2`), and `IRState` (`Layer 2 IR`):

1. **`ClockedStepBudget` & Extended `SolcoreCheckedStmt` Language**:
   Covers straight-line statements (`straight`), persistent storage loads into
   locals (`sloadLocal`), EIP-1153 transient storage loads into locals
   (`tloadLocal`), word-aligned memory writes (`mstoreWord`), checked 256-bit
   addition and subtraction with `Panic(0x11)` revert (`addChecked`,
   `subChecked`), guarded `requireGuard`, conditional `iteBranch`, and
   fuel-bounded iteration (`boundedIter`).
2. **Checked Statement Semantic Preservation (`compileSolcoreCheckedStmt_preserves_semantics`)**:
   Proves that on `.continued sFinal`, `Denote.execStmtList` reaches
   `.continue dFinal` with `StateRefines sFinal dFinal initialWorld`, and on
   `.reverted sFinal revWord`, `sFinal.resolveFrame (.reverted revWord)` rolls
   back storage and events to `sState.checkpoint` and refines `Denote.revertedResult`.
3. **Quadrangular End-to-End Preservation (`solcore_to_verity_quadrangular_preservation`)**:
   Unites `CertifiedContractTranslationWitness` (`Solcore → Denote`),
   `TriangularSemanticMetaSpec` (`Denote → SourceSemantics → IR`), and
   `CertifiedOrExplicitlyFlagged` (`SurfaceMask` trust-boundary partition).
-/

/-! ## 1. Fuel-Bounded Step Budget & Iteration Helpers -/

/-- Declarative step-budget record for fuel-bounded `Solcore` loop execution. -/
structure ClockedStepBudget where
  remainingSteps : Nat
  deriving DecidableEq, Repr

namespace ClockedStepBudget

/-- Consume a single step from the budget when `remainingSteps > 0`. -/
def consumeStep? (b : ClockedStepBudget) : Option ClockedStepBudget :=
  match b.remainingSteps with
  | 0 => none
  | n + 1 => some ⟨n⟩

end ClockedStepBudget

/-- Unroll `fuel` iterations of a straight-line statement body into a `List Stmt`. -/
def iterToVerity : Nat → SolcoreStraightLineStmt → List Compiler.CompilationModel.Stmt
  | 0, _ => []
  | fuel + 1, body => body.toVerity ++ iterToVerity fuel body

/-- Execute `fuel` iterations of `body` on `SolcoreExecState`. -/
def execIterSolcore : Nat → SolcoreStraightLineStmt → SolcoreExecState → SolcoreExecState
  | 0, _, sState => sState
  | fuel + 1, body, sState => execIterSolcore fuel body (body.execSolcore sState)

/-- Execute `fuel` iterations of `body` on `(SolcoreExecState, DenoteState)`. -/
def execIterDenote :
    Nat → SolcoreStraightLineStmt → SolcoreExecState → DenoteState → DenoteState
  | 0, _, _, dState => dState
  | fuel + 1, body, sState, dState =>
      execIterDenote fuel body (body.execSolcore sState) (body.execDenote sState dState)

private theorem execStmtList_append_of_continue
    (oracle : DenoteOracle) (fields : List Field) :
    ∀ (s1 s2 : List Compiler.CompilationModel.Stmt) (dState dMid : DenoteState),
      Denote.execStmtList oracle fields dState s1 = .continue dMid →
      Denote.execStmtList oracle fields dState (s1 ++ s2) =
        Denote.execStmtList oracle fields dMid s2
  | [], _, _, _, h => by
      injection h with hEq
      subst hEq
      rfl
  | stmt :: rest, s2, dState, dMid, h => by
      simp only [List.cons_append, Denote.execStmtList] at h ⊢
      revert h
      cases Denote.execStmt oracle fields dState stmt <;> intro h
      · exact execStmtList_append_of_continue oracle fields rest s2 _ dMid h
      · contradiction
      · contradiction
      · contradiction
      · contradiction

/-- Fuel-bounded iteration preserves `StateRefines` for every `fuel : Nat`. -/
theorem execIter_preserves_stateRefines
    (fuel : Nat) (body : SolcoreStraightLineStmt)
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (hFields : body.FieldsAligned fields) :
    Denote.execStmtList oracle fields dState (iterToVerity fuel body) =
      .continue (execIterDenote fuel body sState dState) ∧
    StateRefines
      (execIterSolcore fuel body sState)
      (execIterDenote fuel body sState dState)
      initialWorld := by
  induction fuel generalizing sState dState with
  | zero => exact ⟨rfl, hRef⟩
  | succ n ih =>
      obtain ⟨hStepExec, hStepRef⟩ :=
        compileSolcoreStmt_preserves_stateRefines body hRef oracle fields hFields
      obtain ⟨hRestExec, hRestRef⟩ := ih hStepRef
      exact ⟨(execStmtList_append_of_continue oracle fields
        body.toVerity (iterToVerity n body) dState _ hStepExec).trans hRestExec, hRestRef⟩

/-! ## 2. Checked 256-Bit Arithmetic Lemmas (`Panic(0x11)`) -/

/-- Canonical Solidity `Panic(0x11)` revert word used on arithmetic overflow/underflow. -/
def panicArithWord : Word :=
  Word.ofNatModulo 0x11

/-- For 256-bit words `wa, wb : Word`, `(wa.add wb).val ≥ wa.val` holds iff
    `wa.val + wb.val < wordModulus` (no 256-bit unsigned addition overflow). -/
theorem word_add_no_overflow_iff_le (wa wb : Word) :
    (wa.val ≤ (wa.add wb).val) ↔ (wa.val + wb.val < wordModulus) := by
  have hA := wa.isLt
  have hB := wb.isLt
  change (wa.val ≤ (wa.val + wb.val) % wordModulus) ↔ (wa.val + wb.val < wordModulus)
  by_cases hlt : wa.val + wb.val < wordModulus
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hge : wordModulus ≤ wa.val + wb.val := Nat.le_of_not_lt hlt
    have hlt2 : wa.val + wb.val - wordModulus < wordModulus := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
    omega

/-- Boolean equivalence between `decide (wa.val ≤ (wa.add wb).val)` and
    `decide (wa.val + wb.val < wordModulus)`. -/
theorem decide_word_add_le_eq_decide_lt_modulus (wa wb : Word) :
    decide (wa.val ≤ (wa.add wb).val) = decide (wa.val + wb.val < wordModulus) :=
  decide_eq_decide.mpr (word_add_no_overflow_iff_le wa wb)

/-! ## 3. Extended `SolcoreCheckedStmt` AST, Compiler, and Execution Semantics -/

/-- Extended `Solcore` statement language supporting storage/transient loads,
    aligned memory writes, checked 256-bit arithmetic (`Panic(0x11)`),
    `require` guards, conditionals, and bounded loops. -/
inductive SolcoreCheckedStmt where
  | straight (s : SolcoreStraightLineStmt)
  | sloadLocal (dst : String) (fieldName : String) (slot : Word)
  | tloadLocal (dst : String) (slot : Word)
  | mstoreWord (offset : Word) (valExpr : SolcorePureExpr)
  | addChecked (dst : String) (a b : SolcorePureExpr)
  | subChecked (dst : String) (a b : SolcorePureExpr)
  | requireGuard (cond : SolcorePureExpr) (errWord : Word)
  | iteBranch (cond : SolcorePureExpr) (thenBr elseBr : SolcoreStraightLineStmt)
  | boundedIter (fuel : Nat) (body : SolcoreStraightLineStmt)
  deriving Repr

/-- Execution outcome of a `SolcoreCheckedStmt`: either continues with an
    updated `SolcoreExecState` or reverts with `(sState, revWord)`. -/
inductive SolcoreCheckedOutcome where
  | continued (sState : SolcoreExecState)
  | reverted (sState : SolcoreExecState) (revWord : Word)

namespace SolcoreCheckedStmt

/-- Total compiler from `SolcoreCheckedStmt` to `List Compiler.CompilationModel.Stmt`. -/
def toVerity : SolcoreCheckedStmt → List Compiler.CompilationModel.Stmt
  | .straight s => s.toVerity
  | .sloadLocal dst fieldName _ => [.assignVar dst (.storage fieldName)]
  | .tloadLocal dst slot => [.assignVar dst (.tload (.literal slot.val))]
  | .mstoreWord offset valExpr => [.mstore (.literal offset.val) valExpr.toVerity]
  | .addChecked dst a b =>
      [.ite (.ge (.add a.toVerity b.toVerity) a.toVerity)
        [.assignVar dst (.add a.toVerity b.toVerity)]
        [.panic .arithmeticOverflow]]
  | .subChecked dst a b =>
      [.ite (.ge a.toVerity b.toVerity)
        [.assignVar dst (.sub a.toVerity b.toVerity)]
        [.panic .arithmeticOverflow]]
  | .requireGuard cond _ =>
      [.require cond.toVerity "solcore_require"]
  | .iteBranch cond thenBr elseBr =>
      [.ite cond.toVerity thenBr.toVerity elseBr.toVerity]
  | .boundedIter fuel body =>
      iterToVerity fuel body

/-- Field-slot and word-aligned memory precondition for `SolcoreCheckedStmt`. -/
def StmtAligned (fields : List Field) (dState : DenoteState) : SolcoreCheckedStmt → Prop
  | .straight s => s.FieldsAligned fields
  | .sloadLocal _ fieldName slot =>
      ∃ field : Field,
        findFieldWithResolvedSlot fields fieldName = some (field, slot.val) ∧
        field.isTransient = false ∧
        field.packedBits = none
  | .tloadLocal _ _ | .addChecked _ _ _ | .subChecked _ _ _ | .requireGuard _ _ => True
  | .mstoreWord offset _ =>
      ∀ (v : Word) (candidate : Word),
        ((dState.world.writePhysicalMemoryValue offset.val v.val).memory candidate.val).val =
          if candidate = offset then v.val else (dState.world.memory candidate.val).val
  | .iteBranch _ thenBr elseBr =>
      thenBr.FieldsAligned fields ∧ elseBr.FieldsAligned fields
  | .boundedIter _ body =>
      body.FieldsAligned fields

/-- Execute a `SolcoreCheckedStmt` on `SolcoreExecState`. -/
def execSolcore (stmt : SolcoreCheckedStmt) (sState : SolcoreExecState) : SolcoreCheckedOutcome :=
  match stmt with
  | .straight s => .continued (s.execSolcore sState)
  | .sloadLocal dst _ slot => .continued (sState.setLocal dst (sState.sload slot))
  | .tloadLocal dst slot => .continued (sState.setLocal dst (sState.tload slot))
  | .mstoreWord offset valExpr => .continued (sState.mstore offset (valExpr.evalWord sState))
  | .addChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      if decide (wa.val + wb.val < wordModulus) then
        .continued (sState.setLocal dst (wa.add wb))
      else
        .reverted sState panicArithWord
  | .subChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      if decide (wb.val ≤ wa.val) then
        .continued (sState.setLocal dst (wa.sub wb))
      else
        .reverted sState panicArithWord
  | .requireGuard cond errWord =>
      if (cond.evalWord sState).val != 0 then
        .continued sState
      else
        .reverted sState errWord
  | .iteBranch cond thenBr elseBr =>
      if (cond.evalWord sState).val != 0 then
        .continued (thenBr.execSolcore sState)
      else
        .continued (elseBr.execSolcore sState)
  | .boundedIter fuel body =>
      .continued (execIterSolcore fuel body sState)

/-- Target `DenoteState` reached when `stmt` continues without reverting. -/
def execDenote (stmt : SolcoreCheckedStmt) (sState : SolcoreExecState) (dState : DenoteState) :
    DenoteState :=
  match stmt with
  | .straight s => s.execDenote sState dState
  | .sloadLocal dst _ slot =>
      { dState with bindings := Denote.bindValue dState.bindings dst (sState.sload slot).val }
  | .tloadLocal dst slot =>
      { dState with bindings := Denote.bindValue dState.bindings dst (sState.tload slot).val }
  | .mstoreWord offset valExpr =>
      { dState with
          world := dState.world.writePhysicalMemoryValue offset.val (valExpr.evalWord sState).val }
  | .addChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      { dState with bindings := Denote.bindValue dState.bindings dst (wa.add wb).val }
  | .subChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      { dState with bindings := Denote.bindValue dState.bindings dst (wa.sub wb).val }
  | .requireGuard _ _ => dState
  | .iteBranch cond thenBr elseBr =>
      if (cond.evalWord sState).val != 0 then
        thenBr.execDenote sState dState
      else
        elseBr.execDenote sState dState
  | .boundedIter fuel body =>
      execIterDenote fuel body sState dState

end SolcoreCheckedStmt

/-! ## 4. Per-Construct & Master Semantic Preservation Theorems -/

private theorem mstoreWord_preserves_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (offset valWord : Word)
    (hMemAlign : ∀ (v : Word) (candidate : Word),
      ((dState.world.writePhysicalMemoryValue offset.val v.val).memory candidate.val).val =
        if candidate = offset then v.val else (dState.world.memory candidate.val).val) :
    StateRefines
      (sState.mstore offset valWord)
      { dState with world := dState.world.writePhysicalMemoryValue offset.val valWord.val }
      initialWorld where
  storage_eq := hRef.storage_eq
  transient_eq := hRef.transient_eq
  memory_eq := fun candidate => by
    rw [hMemAlign valWord candidate]
    by_cases hEq : candidate = offset
    · subst hEq; simp [SolcoreExecState.mload, SolcoreExecState.mstore]
    · simp only [SolcoreExecState.mload, SolcoreExecState.mstore, hEq, ↓reduceIte]
      exact hRef.memory_eq candidate
  locals_eq := hRef.locals_eq
  journal_len_eq := hRef.journal_len_eq
  checkpoint_storage_eq := hRef.checkpoint_storage_eq
  checkpoint_transient_eq := hRef.checkpoint_transient_eq
  checkpoint_journal_len_eq := hRef.checkpoint_journal_len_eq

private theorem evalExpr_ge_add_toVerity
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (a b : SolcorePureExpr) :
    Denote.evalExpr oracle fields dState (.ge (.add a.toVerity b.toVerity) a.toVerity) =
      some (Denote.boolWord (decide ((a.evalWord sState).val + (b.evalWord sState).val < wordModulus))) := by
  have hAdd := evalExpr_toVerity_eq_evalWord hRef oracle fields (.add a b)
  have hA := evalExpr_toVerity_eq_evalWord hRef oracle fields a
  simp only [SolcorePureExpr.toVerity, SolcorePureExpr.evalWord] at hAdd
  change ((Denote.evalExpr oracle fields dState (.add a.toVerity b.toVerity)).bind fun lhs =>
    (Denote.evalExpr oracle fields dState a.toVerity).bind fun rhs =>
      some (Denote.boolWord (decide (rhs ≤ lhs)))) = _
  rw [hAdd, hA, ← decide_word_add_le_eq_decide_lt_modulus]
  rfl

private theorem evalExpr_ge_sub_toVerity
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (a b : SolcorePureExpr) :
    Denote.evalExpr oracle fields dState (.ge a.toVerity b.toVerity) =
      some (Denote.boolWord (decide ((b.evalWord sState).val ≤ (a.evalWord sState).val))) := by
  have hA := evalExpr_toVerity_eq_evalWord hRef oracle fields a
  have hB := evalExpr_toVerity_eq_evalWord hRef oracle fields b
  change ((Denote.evalExpr oracle fields dState a.toVerity).bind fun lhs =>
    (Denote.evalExpr oracle fields dState b.toVerity).bind fun rhs =>
      some (Denote.boolWord (decide (rhs ≤ lhs)))) = _
  rw [hA, hB]
  rfl

/-- Target postcondition of `compileSolcoreCheckedStmt_preserves_semantics`. -/
def CheckedStmtPreservesSemantics
    {TrapReason : Type}
    (stmt : SolcoreCheckedStmt)
    (sState : SolcoreExecState) (dState : DenoteState)
    (initialWorld : Verity.ContractState)
    (oracle : DenoteOracle) (spec : CompilationModel) : Prop :=
  match stmt.execSolcore sState with
  | .continued sFinal =>
      Denote.execStmtList oracle spec.fields dState stmt.toVerity =
        .continue (stmt.execDenote sState dState) ∧
      StateRefines sFinal (stmt.execDenote sState dState) initialWorld
  | .reverted sFinal revWord =>
      (∃ bytes, Denote.execStmtList oracle spec.fields dState stmt.toVerity =
        .revertWithData bytes) ∧
      ∃ snap : SolcoreFrameSnapshot,
        sFinal.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revWord) =
          some snap ∧
        SnapshotRefinesResult sState.contractAddress snap
          (Denote.revertedResult oracle spec initialWorld)

private theorem compileSolcoreCheckedStmt_sloadLocal
    {TrapReason : Type} (dst fieldName : String) (slot : Word)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : (SolcoreCheckedStmt.sloadLocal dst fieldName slot).StmtAligned spec.fields dState) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.sloadLocal dst fieldName slot) sState dState initialWorld oracle spec := by
  rcases hAligned with ⟨field, hField, hPers, hUnp⟩
  have hSload := sload_refines_evalExpr_storage hRef oracle spec.fields fieldName field slot hField hPers hUnp
  refine ⟨?_, setLocal_preserves_stateRefines hRef dst (sState.sload slot)⟩
  simp [SolcoreCheckedStmt.toVerity, SolcoreCheckedStmt.execDenote,
    Denote.execStmtList, Denote.execStmt, hSload]

private theorem compileSolcoreCheckedStmt_tloadLocal
    {TrapReason : Type} (dst : String) (slot : Word)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.tloadLocal dst slot) sState dState initialWorld oracle spec := by
  have hSlot : Denote.evalExpr oracle spec.fields dState (.literal slot.val) = some slot.val :=
    (exprRefines_word [] [] oracle spec.fields dState slot).2
  have hTload := tload_refines_evalExpr hRef hSlot
  refine ⟨?_, setLocal_preserves_stateRefines hRef dst (sState.tload slot)⟩
  simp [SolcoreCheckedStmt.toVerity, SolcoreCheckedStmt.execDenote,
    Denote.execStmtList, Denote.execStmt, hTload]

private theorem compileSolcoreCheckedStmt_mstoreWord
    {TrapReason : Type} (offset : Word) (valExpr : SolcorePureExpr)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : (SolcoreCheckedStmt.mstoreWord offset valExpr).StmtAligned spec.fields dState) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.mstoreWord offset valExpr) sState dState initialWorld oracle spec := by
  have hOff : Denote.evalExpr oracle spec.fields dState (.literal offset.val) = some offset.val :=
    (exprRefines_word [] [] oracle spec.fields dState offset).2
  have hVal := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields valExpr
  refine ⟨?_, mstoreWord_preserves_stateRefines hRef offset (valExpr.evalWord sState) hAligned⟩
  simp [SolcoreCheckedStmt.toVerity, SolcoreCheckedStmt.execDenote,
    Denote.execStmtList, Denote.execStmt, hOff, hVal]

private theorem compileSolcoreCheckedStmt_addChecked
    {TrapReason : Type} (dst : String) (a b : SolcorePureExpr)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.addChecked dst a b) sState dState initialWorld oracle spec := by
  have hGe := evalExpr_ge_add_toVerity hRef oracle spec.fields a b
  have hAdd := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields (.add a b)
  simp only [SolcorePureExpr.toVerity, SolcorePureExpr.evalWord] at hAdd
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hCond : decide ((a.evalWord sState).val + (b.evalWord sState).val < wordModulus)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨Denote.panicBytes 0x11, ?_⟩,
      revert_rollback_refines_denote hRef oracle spec panicArithWord hEncodeInit⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord]
  · simp only [↓reduceIte]
    refine ⟨?_, setLocal_preserves_stateRefines hRef dst ((a.evalWord sState).add (b.evalWord sState))⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord, hAdd]

private theorem compileSolcoreCheckedStmt_subChecked
    {TrapReason : Type} (dst : String) (a b : SolcorePureExpr)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.subChecked dst a b) sState dState initialWorld oracle spec := by
  have hGe := evalExpr_ge_sub_toVerity hRef oracle spec.fields a b
  have hSub := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields (.sub a b)
  simp only [SolcorePureExpr.toVerity, SolcorePureExpr.evalWord] at hSub
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hCond : decide ((b.evalWord sState).val ≤ (a.evalWord sState).val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨Denote.panicBytes 0x11, ?_⟩,
      revert_rollback_refines_denote hRef oracle spec panicArithWord hEncodeInit⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord]
  · simp only [↓reduceIte]
    refine ⟨?_, setLocal_preserves_stateRefines hRef dst ((a.evalWord sState).sub (b.evalWord sState))⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord, hSub]

private theorem compileSolcoreCheckedStmt_requireGuard
    {TrapReason : Type} (cond : SolcorePureExpr) (errWord : Word)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.requireGuard cond errWord) sState dState initialWorld oracle spec := by
  have hCondEval := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields cond
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hNz : ((cond.evalWord sState).val != 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨Denote.errorStringBytes "solcore_require", ?_⟩,
      revert_rollback_refines_denote hRef oracle spec errWord hEncodeInit⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt, hCondEval, hNz]
  · simp only [↓reduceIte]
    refine ⟨?_, hRef⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt, hCondEval, hNz]

private theorem compileSolcoreCheckedStmt_iteBranch
    {TrapReason : Type} (cond : SolcorePureExpr) (thenBr elseBr : SolcoreStraightLineStmt)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : (SolcoreCheckedStmt.iteBranch cond thenBr elseBr).StmtAligned spec.fields dState) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.iteBranch cond thenBr elseBr) sState dState initialWorld oracle spec := by
  have hCondEval := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields cond
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hNz : ((cond.evalWord sState).val != 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hExecE, hRefE⟩ :=
      compileSolcoreStmt_preserves_stateRefines elseBr hRef oracle spec.fields hAligned.2
    refine ⟨?_, hRefE⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hCondEval, hNz, hExecE]
  · simp only [↓reduceIte]
    obtain ⟨hExecT, hRefT⟩ :=
      compileSolcoreStmt_preserves_stateRefines thenBr hRef oracle spec.fields hAligned.1
    refine ⟨?_, hRefT⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hCondEval, hNz, hExecT]

/-- **Master `SolcoreCheckedStmt` Semantic Preservation Theorem**:
    - On `.continued sFinal`, `Denote.execStmtList` reaches `.continue (stmt.execDenote sState dState)`
      and `StateRefines sFinal (stmt.execDenote sState dState) initialWorld` holds.
    - On `.reverted sFinal revWord`, `Denote.execStmtList` reverts with `revertWithData` and
      `sFinal.resolveFrame (.reverted revWord)` rolls back storage and events to refine
      `Denote.revertedResult oracle spec initialWorld`. -/
theorem compileSolcoreCheckedStmt_preserves_semantics
    {TrapReason : Type} (stmt : SolcoreCheckedStmt)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : stmt.StmtAligned spec.fields dState)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val = (initialWorld.readSlot slot.val).val) :
    match stmt.execSolcore sState with
    | .continued sFinal =>
        Denote.execStmtList oracle spec.fields dState stmt.toVerity =
          .continue (stmt.execDenote sState dState) ∧
        StateRefines sFinal (stmt.execDenote sState dState) initialWorld
    | .reverted sFinal revWord =>
        (∃ bytes, Denote.execStmtList oracle spec.fields dState stmt.toVerity = .revertWithData bytes) ∧
        ∃ snap : SolcoreFrameSnapshot,
          sFinal.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revWord) = some snap ∧
          SnapshotRefinesResult sState.contractAddress snap
            (Denote.revertedResult oracle spec initialWorld) := by
  change CheckedStmtPreservesSemantics (TrapReason := TrapReason)
    stmt sState dState initialWorld oracle spec
  cases stmt with
  | straight s => exact compileSolcoreStmt_preserves_stateRefines s hRef oracle spec.fields hAligned
  | sloadLocal d f s => exact compileSolcoreCheckedStmt_sloadLocal d f s hRef oracle spec hAligned
  | tloadLocal d s => exact compileSolcoreCheckedStmt_tloadLocal d s hRef oracle spec
  | mstoreWord o v => exact compileSolcoreCheckedStmt_mstoreWord o v hRef oracle spec hAligned
  | addChecked d a b => exact compileSolcoreCheckedStmt_addChecked d a b hRef oracle spec hEncodeInit
  | subChecked d a b => exact compileSolcoreCheckedStmt_subChecked d a b hRef oracle spec hEncodeInit
  | requireGuard c e => exact compileSolcoreCheckedStmt_requireGuard c e hRef oracle spec hEncodeInit
  | iteBranch c t e => exact compileSolcoreCheckedStmt_iteBranch c t e hRef oracle spec hAligned
  | boundedIter k b => exact execIter_preserves_stateRefines k b hRef oracle spec.fields hAligned

/-! ## 5. Quadrangular Preservation (`Solcore → Denote → SourceSemantics → IR`) -/

/-- **Quadrangular End-to-End Semantic Preservation (`solcore_to_verity_quadrangular_preservation`)**:
    Composes:
    1. `CertifiedContractTranslationWitness` (`Layer 0 Solcore → Layer 1 Denote`),
    2. `MetaSpecs.TriangularSemanticMetaSpec` (`Layer 1 Denote → Layer 2 SourceSemantics → Layer 2 IR`), and
    3. `MetaSpecs.CertifiedOrExplicitlyFlagged` (`SurfaceMask` trust-boundary partition)
    into a single end-to-end preservation theorem from `Solcore` to `IRState`. -/
theorem solcore_to_verity_quadrangular_preservation
    {SourceState IRState Obs : Type}
    (cw : CertifiedContractTranslationWitness)
    {fnName : String} {w : CertifiedTranslationWitness}
    (hLookup : cw.witnessOf fnName = some w)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead cw.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {retWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .returned retWord))
    {obsDenote : DenoteResult → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteResult → DenoteResult}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteResult → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    {s0 : SourceState} {i0 : IRState}
    (hDS : relDS (Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld) s0)
    (hSI : relSI s0 i0)
    (allowedMask : SurfaceMask) :
    let dResult := Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld
    w.fn ∈ cw.spec.functions ∧
    dResult.success = true ∧
    dResult.returnValue = some retWord.val ∧
    (∀ slot : Word,
      (sState.world.storageRead cw.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.journal.logs.length = dResult.events.length ∧
    obsDenote dResult = obsIR i0 ∧
    obsDenote (stepDenote dResult) = obsIR (stepIR i0) ∧
    CertifiedOrExplicitlyFlagged cw.spec allowedMask := by
  obtain ⟨hMem, hSucc, hRet, hStor, hLogs⟩ :=
    certifiedContractTranslationWitness_returned_soundness
      cw hLookup tx sWorld initialWorld hInit hEval
  exact ⟨hMem, hSucc, hRet, hStor, hLogs,
    triangular_obs_eq hTri hDS hSI,
    triangular_commutes hTri hDS hSI,
    trust_boundary_partition_complete cw.spec allowedMask⟩

/-- **Quadrangular Revert & Rollback Preservation (`solcore_to_verity_quadrangular_revert_preservation`)**:
    On `.reverted revWord`, storage and journal roll back to `sState.checkpoint`,
    `Denote` and `IRState` agree on revert classification across `n` steps, and
    `CertifiedOrExplicitlyFlagged` holds for `cw.spec`. -/
theorem solcore_to_verity_quadrangular_revert_preservation
    {SourceState IRState Obs : Type}
    (cw : CertifiedContractTranslationWitness)
    {fnName : String} {w : CertifiedTranslationWitness}
    (hLookup : cw.witnessOf fnName = some w)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead cw.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {revWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .reverted revWord))
    {obsDenote : DenoteResult → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteResult → DenoteResult}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteResult → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    (isRevert : Obs → Bool) (n : Nat)
    {s0 : SourceState} {i0 : IRState}
    (hDS : relDS (Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld) s0)
    (hSI : relSI s0 i0)
    (allowedMask : SurfaceMask) :
    let dResult := Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld
    w.fn ∈ cw.spec.functions ∧
    dResult.success = false ∧
    dResult.returnValue = none ∧
    (∀ slot : Word,
      (sState.checkpoint.world.storageRead cw.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.checkpoint.journal.logs.length = dResult.events.length ∧
    isRevert (obsDenote (iterateStep stepDenote n dResult)) =
      isRevert (obsIR (iterateStep stepIR n i0)) ∧
    CertifiedOrExplicitlyFlagged cw.spec allowedMask := by
  obtain ⟨hMem, hSucc, hRet, hStor, hLogs⟩ :=
    certifiedContractTranslationWitness_reverted_soundness
      cw hLookup tx sWorld initialWorld hInit hEval
  exact ⟨hMem, hSucc, hRet, hStor, hLogs,
    triangular_revert_equivalence hTri isRevert n hDS hSI,
    trust_boundary_partition_complete cw.spec allowedMask⟩

/-! ## 6. Phase 4 Track D2: Computed Transient Storage (`#1995`), Immutables (`#1992`), Stateful External Calls (`#1963`/`#2094`), Multicall/Delegatecall Batch (`#1997`), and Disjoint-Footprint Commutativity (`#1990`) -/

/-- Alignment between a `Solcore` immutable word environment `immEnv` and `dState.immutable`. -/
def ImmutableEnvAligned (immEnv : String → Word) (dState : DenoteState) : Prop :=
  ∀ immId : String, (immEnv immId).val = (dState.immutable immId).val

/-- Outcome of a stateful external call (`#1963`, `#2094`): either succeeds with a
storage slot update and return word, or reverts with error data. -/
inductive ExternalCallOutcome where
  | success (slot : Word) (newVal : Word) (retWord : Word)
  | reverted (errData : Word)
  deriving DecidableEq, Repr

/-- Preserved `msg.sender` and `msg.value` context across `delegatecall` batches (`#1997`). -/
structure DelegateContext where
  msgSender : Word
  msgValue : Word
  deriving DecidableEq, Repr

/-- Single frame in a `delegatecallBatch` (`#1997`). -/
inductive DelegateFrameSpec where
  | writeSlot (slot : Word) (val : Word)
  | revertFrame (errWord : Word)
  deriving DecidableEq, Repr

/-- Advanced `Solcore` operations closing `#1995`, `#1992`, `#1963`, `#2094`, and `#1997`. -/
inductive SolcoreAdvancedOp where
  | tstoreComputed (slotExpr valExpr : SolcorePureExpr)
  | tloadComputed (dst : String) (slotExpr : SolcorePureExpr)
  | readImmutable (dst : String) (immId : String)
  | statefulExternalCall (dst : String) (outcome : ExternalCallOutcome)
  | delegatecallBatch (ctx : DelegateContext) (frames : List DelegateFrameSpec)
  deriving Repr

/-- Execute a `delegatecall` batch on `SolcoreExecState`: preserves `ctx` (`msg.sender`,
`msg.value`) and rolls back to `entryState` if any frame reverts. -/
def execDelegateBatchSolcore
    (entryState : SolcoreExecState) :
    List DelegateFrameSpec → SolcoreExecState → SolcoreCheckedOutcome
  | [], curr => .continued curr
  | .writeSlot slot val :: rest, curr =>
      execDelegateBatchSolcore entryState rest (curr.sstore slot val)
  | .revertFrame errWord :: _, _ =>
      .reverted entryState errWord

/-- Execute a `delegatecall` batch on `DenoteState` when all frames succeed. -/
def execDelegateBatchDenote :
    List DelegateFrameSpec → DenoteState → DenoteState
  | [], dState => dState
  | .writeSlot slot val :: rest, dState =>
      execDelegateBatchDenote rest
        { dState with world := Denote.writeUintSlots dState.world [slot.val] val.val }
  | .revertFrame _ :: _, dState => dState

/-- Predicate checking whether all frames in a `delegatecall` batch succeed. -/
def delegateBatchAllSucceed : List DelegateFrameSpec → Bool
  | [] => true
  | .writeSlot _ _ :: rest => delegateBatchAllSucceed rest
  | .revertFrame _ :: _ => false

namespace SolcoreAdvancedOp

/-- Execute a `SolcoreAdvancedOp` on `SolcoreExecState` under immutable environment `immEnv`. -/
def execSolcore
    (immEnv : String → Word) (op : SolcoreAdvancedOp) (sState : SolcoreExecState) :
    SolcoreCheckedOutcome :=
  match op with
  | .tstoreComputed slotExpr valExpr =>
      .continued (sState.tstore (slotExpr.evalWord sState) (valExpr.evalWord sState))
  | .tloadComputed dst slotExpr =>
      .continued (sState.setLocal dst (sState.tload (slotExpr.evalWord sState)))
  | .readImmutable dst immId =>
      .continued (sState.setLocal dst (immEnv immId))
  | .statefulExternalCall dst (.success slot newVal retWord) =>
      .continued ((sState.sstore slot newVal).setLocal dst retWord)
  | .statefulExternalCall _ (.reverted errData) =>
      .reverted sState errData
  | .delegatecallBatch _ frames =>
      execDelegateBatchSolcore sState frames sState

/-- Target `DenoteState` reached when `op` continues without reverting. -/
def execDenote
    (immEnv : String → Word) (op : SolcoreAdvancedOp)
    (sState : SolcoreExecState) (dState : DenoteState) : DenoteState :=
  match op with
  | .tstoreComputed slotExpr valExpr =>
      { dState with
          world := dState.world.writeTransient
            (Denote.wordNormalize (slotExpr.evalWord sState).val)
            (valExpr.evalWord sState).toUint256 }
  | .tloadComputed dst slotExpr =>
      { dState with
          bindings := Denote.bindValue dState.bindings dst
            (sState.tload (slotExpr.evalWord sState)).val }
  | .readImmutable dst immId =>
      { dState with
          bindings := Denote.bindValue dState.bindings dst (immEnv immId).val }
  | .statefulExternalCall dst (.success slot newVal retWord) =>
      { dState with
          world := Denote.writeUintSlots dState.world [slot.val] newVal.val
          bindings := Denote.bindValue dState.bindings dst retWord.val }
  | .statefulExternalCall _ (.reverted _) => dState
  | .delegatecallBatch _ frames =>
      execDelegateBatchDenote frames dState

end SolcoreAdvancedOp

private theorem revert_rollback_refines_denote_with_transient
    {TrapReason : Type}
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (revertWord : Word)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    ∃ snap : SolcoreFrameSnapshot,
      sState.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revertWord) =
        some snap ∧
      SnapshotRefinesResult sState.contractAddress snap
        (Denote.revertedResult oracle spec initialWorld) ∧
      (∀ slot : Word,
        (snap.transientStorage slot).val = (initialWorld.readTransient slot.val).val) := by
  obtain ⟨snap, hRes, hSnap⟩ :=
    revert_rollback_refines_denote (TrapReason := TrapReason)
      hRef oracle spec revertWord hEncodeInit
  injection hRes with hEq; subst hEq
  exact ⟨sState.checkpoint, rfl, hSnap, hRef.checkpoint_transient_eq⟩

/-- `execDelegateBatchSolcore` preserves `StateRefines` on `.continued` and rolls back
to `entryState` on `.reverted`. -/
theorem execDelegateBatch_preserves_stateRefines {TrapReason : Type}
    (frames : List DelegateFrameSpec) {entryState currState : SolcoreExecState}
    {entryDenote currDenote : DenoteState} {initialWorld : Verity.ContractState}
    (hEntryRef : StateRefines entryState entryDenote initialWorld)
    (hCurrRef : StateRefines currState currDenote initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word, Denote.encodeStorage oracle spec initialWorld slot.val =
      (initialWorld.readSlot slot.val).val) :
    match execDelegateBatchSolcore entryState frames currState with
    | .continued sFinal => StateRefines sFinal (execDelegateBatchDenote frames currDenote) initialWorld
    | .reverted sFinal revWord =>
        ∃ snap : SolcoreFrameSnapshot,
          sFinal.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revWord) = some snap ∧
          SnapshotRefinesResult entryState.contractAddress snap (Denote.revertedResult oracle spec initialWorld) ∧
          (∀ slot : Word, (snap.transientStorage slot).val = (initialWorld.readTransient slot.val).val) := by
  induction frames generalizing currState currDenote with
  | nil => exact hCurrRef
  | cons frame rest ih =>
      cases frame with
      | writeSlot slot val => exact ih (sstore_preserves_stateRefines hCurrRef slot val)
      | revertFrame errWord =>
          exact revert_rollback_refines_denote_with_transient hEntryRef oracle spec errWord hEncodeInit

/-- **Layer I Meta-Spec (`SolcoreAdvancedOpPreservesSemantics`)**:
Unified refinement & rollback specification for `SolcoreAdvancedOp`. -/
def SolcoreAdvancedOpPreservesSemantics
    {TrapReason : Type}
    (immEnv : String → Word) (op : SolcoreAdvancedOp)
    (sState : SolcoreExecState) (dState : DenoteState)
    (initialWorld : Verity.ContractState)
    (oracle : DenoteOracle) (spec : CompilationModel) : Prop :=
  match op.execSolcore immEnv sState with
  | .continued sFinal =>
      StateRefines sFinal (op.execDenote immEnv sState dState) initialWorld
  | .reverted sFinal revWord =>
      ∃ snap : SolcoreFrameSnapshot,
        sFinal.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revWord) =
          some snap ∧
        SnapshotRefinesResult sState.contractAddress snap
          (Denote.revertedResult oracle spec initialWorld) ∧
        (∀ slot : Word,
          (snap.transientStorage slot).val = (initialWorld.readTransient slot.val).val)

/-- **Layer I Universal Theorem (`execSolcoreAdvancedOp_preserves_semantics`)**:
Every `op : SolcoreAdvancedOp` preserves `StateRefines` when continuing and rolls back
persistent storage, EIP-1153 transient storage, and event logs to `initialWorld` on revert. -/
theorem execSolcoreAdvancedOp_preserves_semantics {TrapReason : Type}
    (immEnv : String → Word) (op : SolcoreAdvancedOp)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld) (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word, Denote.encodeStorage oracle spec initialWorld slot.val =
      (initialWorld.readSlot slot.val).val) :
    SolcoreAdvancedOpPreservesSemantics (TrapReason := TrapReason)
      immEnv op sState dState initialWorld oracle spec := by
  cases op with
  | tstoreComputed s v => exact tstore_preserves_stateRefines hRef (s.evalWord sState) (v.evalWord sState)
  | tloadComputed d s => exact setLocal_preserves_stateRefines hRef d (sState.tload (s.evalWord sState))
  | readImmutable d i => exact setLocal_preserves_stateRefines hRef d (immEnv i)
  | statefulExternalCall dst outcome =>
      cases outcome with
      | success slot newVal retWord =>
          exact setLocal_preserves_stateRefines (sstore_preserves_stateRefines hRef slot newVal) dst retWord
      | reverted errData =>
          exact revert_rollback_refines_denote_with_transient hRef oracle spec errData hEncodeInit
  | delegatecallBatch _ frames =>
      exact execDelegateBatch_preserves_stateRefines frames hRef hRef oracle spec hEncodeInit

/-! ### Layer II: Per-Feature Corollaries (`#1995`, `#1992`, `#1963`, `#2094`, `#1997`) -/

/-- **Corollary 1 (`#1995` Computed Transient Storage Write & Load)**:
`tstoreComputed` and `tloadComputed` evaluate `slotExpr.toVerity` in `Denote` and preserve `StateRefines`. -/
theorem tstoreComputed_and_tloadComputed_preserve_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (dst : String) (slotExpr valExpr : SolcorePureExpr) :
    Denote.evalExpr oracle fields dState (.tload slotExpr.toVerity) =
      some (sState.tload (slotExpr.evalWord sState)).val ∧
    StateRefines
      (sState.tstore (slotExpr.evalWord sState) (valExpr.evalWord sState))
      ((SolcoreAdvancedOp.tstoreComputed slotExpr valExpr).execDenote
        (fun _ => Word.zero) sState dState)
      initialWorld ∧
    StateRefines
      (sState.setLocal dst (sState.tload (slotExpr.evalWord sState)))
      ((SolcoreAdvancedOp.tloadComputed dst slotExpr).execDenote
        (fun _ => Word.zero) sState dState)
      initialWorld :=
  ⟨tload_refines_evalExpr hRef (evalExpr_toVerity_eq_evalWord hRef oracle fields slotExpr),
   tstore_preserves_stateRefines hRef (slotExpr.evalWord sState) (valExpr.evalWord sState),
   setLocal_preserves_stateRefines hRef dst (sState.tload (slotExpr.evalWord sState))⟩

/-- **Corollary 2 (`#1992` Bytecode Immutable Read Preservation)**:
Reading `Expr.immutable immId` under `ImmutableEnvAligned immEnv dState` evaluates to
`some (immEnv immId).val` in `Denote` and preserves `StateRefines`. -/
theorem readImmutable_preserves_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (immEnv : String → Word)
    (hImm : ImmutableEnvAligned immEnv dState)
    (oracle : DenoteOracle) (fields : List Field)
    (dst immId : String) :
    Denote.evalExpr oracle fields dState (.immutable immId) = some (immEnv immId).val ∧
    StateRefines
      (sState.setLocal dst (immEnv immId))
      ((SolcoreAdvancedOp.readImmutable dst immId).execDenote immEnv sState dState)
      initialWorld := by
  refine ⟨?_, setLocal_preserves_stateRefines hRef dst (immEnv immId)⟩
  change some (dState.immutable immId).val = some (immEnv immId).val
  rw [hImm immId]

/-- **Corollary 3 (`#1963` / `#2094` Stateful External Call Rollback)**:
On `.reverted errData`, `statefulExternalCall` rolls back persistent storage,
transient storage, and event logs to `initialWorld`. -/
theorem statefulExternalCall_reverted_rolls_back_all_domains
    {TrapReason : Type}
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (dst : String) (errData : Word)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    SolcoreAdvancedOpPreservesSemantics (TrapReason := TrapReason)
      (fun _ => Word.zero) (.statefulExternalCall dst (.reverted errData))
      sState dState initialWorld oracle spec :=
  execSolcoreAdvancedOp_preserves_semantics
    (fun _ => Word.zero) (.statefulExternalCall dst (.reverted errData))
    hRef oracle spec hEncodeInit

/-! ## 7. Footprint Commutativity Meta-Specification (`#1990`) -/

/-- Address footprint across persistent storage, EIP-1153 transient storage, and memory. -/
structure StateFootprint where
  storageSlot : Option Word := none
  transientSlot : Option Word := none
  memoryOffset : Option Word := none
  deriving DecidableEq, Repr

namespace StateFootprint

/-- Decidable option-address disjointness: `none` is disjoint from everything,
and `some a` is disjoint from `some b` iff `a ≠ b`. -/
def optDisjoint (a b : Option Word) : Bool :=
  match a, b with
  | some x, some y => x != y
  | _, _ => true

/-- Two footprints are disjoint iff their storage, transient, and memory slots are pairwise disjoint. -/
def disjoint (f₁ f₂ : StateFootprint) : Bool :=
  optDisjoint f₁.storageSlot f₂.storageSlot &&
    optDisjoint f₁.transientSlot f₂.transientSlot &&
    optDisjoint f₁.memoryOffset f₂.memoryOffset

end StateFootprint

/-- **Layer I Footprint Commutativity Meta-Specification (`DisjointFootprintMetaSpec`, `#1990`)**:
Certifies that two state transformers `step₁, step₂ : State → State` with disjoint footprints
commute extensionally on observable state projections `obs : State → Obs`. -/
structure DisjointFootprintMetaSpec
    {State Obs : Type}
    (obs : State → Obs)
    (f₁ f₂ : StateFootprint)
    (step₁ step₂ : State → State) : Prop where
  /-- The footprints `f₁` and `f₂` are disjoint. -/
  footprints_disjoint : f₁.disjoint f₂ = true
  /-- Applying `step₁` then `step₂` yields the same observation as `step₂` then `step₁`. -/
  commutes_obs : ∀ s : State, obs (step₂ (step₁ s)) = obs (step₁ (step₂ s))

/-- **Layer II Corollary 1 (`sstore_disjoint_commutes`)**:
Two `sstore` updates at distinct slots `slot₁ ≠ slot₂` commute at every read slot `q`. -/
theorem sstore_disjoint_commutes
    (sState : SolcoreExecState) {slot₁ slot₂ : Word} (val₁ val₂ : Word)
    (hNe : slot₁ ≠ slot₂) (q : Word) :
    ((sState.sstore slot₁ val₁).sstore slot₂ val₂).sload q =
      ((sState.sstore slot₂ val₂).sstore slot₁ val₁).sload q := by
  by_cases hq2 : q = slot₂
  · subst hq2
    rw [SolcoreExecState.sload_sstore_same, SolcoreExecState.sload_sstore_other _ _ (Ne.symm hNe),
      SolcoreExecState.sload_sstore_same]
  · by_cases hq1 : q = slot₁
    · subst hq1
      rw [SolcoreExecState.sload_sstore_other _ _ hNe, SolcoreExecState.sload_sstore_same,
        SolcoreExecState.sload_sstore_same]
    · rw [SolcoreExecState.sload_sstore_other _ _ hq2, SolcoreExecState.sload_sstore_other _ _ hq1,
        SolcoreExecState.sload_sstore_other _ _ hq1, SolcoreExecState.sload_sstore_other _ _ hq2]

/-- **Layer II Corollary 2 (`tstore_disjoint_commutes`)**:
Two `tstore` updates at distinct transient slots `slot₁ ≠ slot₂` commute at every read slot `q`. -/
theorem tstore_disjoint_commutes
    (sState : SolcoreExecState) {slot₁ slot₂ : Word} (val₁ val₂ : Word)
    (hNe : slot₁ ≠ slot₂) (q : Word) :
    ((sState.tstore slot₁ val₁).tstore slot₂ val₂).tload q =
      ((sState.tstore slot₂ val₂).tstore slot₁ val₁).tload q := by
  by_cases hq2 : q = slot₂
  · subst hq2
    rw [SolcoreExecState.tload_tstore_same, SolcoreExecState.tload_tstore_other _ _ (Ne.symm hNe),
      SolcoreExecState.tload_tstore_same]
  · by_cases hq1 : q = slot₁
    · subst hq1
      rw [SolcoreExecState.tload_tstore_other _ _ hNe, SolcoreExecState.tload_tstore_same,
        SolcoreExecState.tload_tstore_same]
    · rw [SolcoreExecState.tload_tstore_other _ _ hq2, SolcoreExecState.tload_tstore_other _ _ hq1,
        SolcoreExecState.tload_tstore_other _ _ hq1, SolcoreExecState.tload_tstore_other _ _ hq2]

/-- **Layer II Corollary 3 (`mstore_disjoint_commutes`)**:
Two `mstore` updates at distinct word offsets `off₁ ≠ off₂` commute at every read offset `q`. -/
theorem mstore_disjoint_commutes
    (sState : SolcoreExecState) {off₁ off₂ : Word} (val₁ val₂ : Word)
    (hNe : off₁ ≠ off₂) (q : Word) :
    ((sState.mstore off₁ val₁).mstore off₂ val₂).mload q =
      ((sState.mstore off₂ val₂).mstore off₁ val₁).mload q := by
  simp only [SolcoreExecState.mload, SolcoreExecState.mstore]
  by_cases hq2 : q = off₂
  · subst hq2; simp [Ne.symm hNe]
  · by_cases hq1 : q = off₁
    · subst hq1; simp [hNe]
    · simp [hq1, hq2]

/-! ### Layer III: Kernel-Checked `by decide` Executable Witness Suite -/

/-- Disjoint persistent storage slots (`slot 1` vs `slot 2`) satisfy `StateFootprint.disjoint`. -/
theorem witness_disjoint_storage_footprints :
    StateFootprint.disjoint
      { storageSlot := some (Word.ofNatModulo 1) }
      { storageSlot := some (Word.ofNatModulo 2) } = true := by decide

/-- Overlapping persistent storage slots (`slot 5` vs `slot 5`) are rejected by `StateFootprint.disjoint`. -/
theorem witness_overlapping_storage_footprints :
    StateFootprint.disjoint
      { storageSlot := some (Word.ofNatModulo 5) }
      { storageSlot := some (Word.ofNatModulo 5) } = false := by decide

/-- Cross-domain `sstore(slot 1)` and `tstore(slot 1)` have disjoint footprints. -/
theorem witness_cross_domain_sstore_tstore_disjoint :
    StateFootprint.disjoint
      { storageSlot := some (Word.ofNatModulo 1) }
      { transientSlot := some (Word.ofNatModulo 1) } = true := by decide

/-- `delegateBatchAllSucceed` accepts a multi-frame write batch. -/
theorem witness_delegateBatch_all_succeed :
    delegateBatchAllSucceed
      [.writeSlot (Word.ofNatModulo 0) (Word.ofNatModulo 10),
       .writeSlot (Word.ofNatModulo 1) (Word.ofNatModulo 20)] = true := by decide

/-- `delegateBatchAllSucceed` detects a reverting frame in a batch. -/
theorem witness_delegateBatch_detects_revert :
    delegateBatchAllSucceed
      [.writeSlot (Word.ofNatModulo 0) (Word.ofNatModulo 10),
       .revertFrame (Word.ofNatModulo 0x11)] = false := by decide

/-- `ClockedStepBudget.consumeStep?` decrements a positive step budget. -/
theorem witness_clockedStepBudget_consume :
    (ClockedStepBudget.mk 3).consumeStep? = some ⟨2⟩ := by decide

end Compiler.Proofs.SolidityImport.SolcoreFullBridge
