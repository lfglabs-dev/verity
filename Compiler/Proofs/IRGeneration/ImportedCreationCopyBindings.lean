import Compiler.SolidityImport.AbiMemory

namespace Compiler.Proofs.IRGeneration.ImportedCreationCopyBindings
open Compiler.CompilationModel Denote

/-- The actual two temporary lets and mstore preserve every other local,
without requiring arithmetic, zero lanes or successful copy preconditions. -/
theorem lets_store (oracle : DenoteOracle) (fields : List Field) (initial final : DenoteState)
    (byteName addressName key : String) (byteExpr addressExpr offset value : Expr)
    (byteFresh : byteName ≠ key) (addressFresh : addressName ≠ key)
    (executed : execStmtList oracle fields initial
      [.letVar byteName byteExpr, .letVar addressName addressExpr, .mstore offset value] = .continue final) :
    lookupValue final.bindings key = lookupValue initial.bindings key := by
  rw [SolidityImport.exec_let_cons] at executed
  cases first : evalExpr oracle fields initial byteExpr with
  | none => simp only [first] at executed; cases executed
  | some byte =>
    simp only [first] at executed
    rw [SolidityImport.exec_let_cons] at executed
    cases second : evalExpr oracle fields { initial with bindings := bindValue initial.bindings byteName byte } addressExpr with
    | none => simp only [second] at executed; cases executed
    | some address =>
      simp only [second] at executed
      rw [SolidityImport.exec_singleton] at executed
      cases whereAt : evalExpr oracle fields
          { initial with bindings := bindValue (bindValue initial.bindings byteName byte) addressName address } offset
        <;> cases word : evalExpr oracle fields
          { initial with bindings := bindValue (bindValue initial.bindings byteName byte) addressName address } value
        <;> simp only [execStmt, whereAt, word] at executed
      all_goals try cases executed
      simp only [SolidityImport.lookup_bind_other _ _ _ _ addressFresh,
        SolidityImport.lookup_bind_other _ _ _ _ byteFresh]

/-- The body extracted from copyBytes is the actual two-let/store pattern. -/
theorem generated_body (oracle : DenoteOracle) (fields : List Field) (initial final : DenoteState)
    (source destination start index byte address key : String)
    (byteFresh : byte ≠ key) (addressFresh : address ≠ key)
    (executed : execStmtList oracle fields initial
      (abiGeneratedCopyBody source destination start index byte address) = .continue final) :
    lookupValue final.bindings key = lookupValue initial.bindings key := by
  unfold abiGeneratedCopyBody SolidityImport.AbiEncoding.copyBytes at executed
  exact lets_store oracle fields initial final byte address key _ _ _ _ byteFresh addressFresh executed

/-- Successful finite executions preserve arbitrary protected locals, including
when no iteration is executed. The executor's index rebinding is included. -/
theorem loop (oracle : DenoteOracle) (fields : List Field)
    (source destination start index byte address key : String)
    (indexFresh : index ≠ key) (byteFresh : byte ≠ key) (addressFresh : address ≠ key)
    (remaining cursor : Nat) (initial final : DenoteState)
    (executed : execForEachLoop index (fun state => execStmtList oracle fields state
      (abiGeneratedCopyBody source destination start index byte address)) initial cursor remaining = .continue final) :
    lookupValue final.bindings key = lookupValue initial.bindings key := by
  induction remaining generalizing cursor initial with
  | zero => cases executed; rfl
  | succ remaining ih =>
    simp only [execForEachLoop] at executed
    cases step : execStmtList oracle fields
        { initial with bindings := bindValue initial.bindings index (wordNormalize cursor) }
        (abiGeneratedCopyBody source destination start index byte address) with
    | «continue» next =>
      rw [step] at executed
      rw [ih (cursor + 1) next executed]
      rw [generated_body oracle fields _ next source destination start index byte address key byteFresh addressFresh step]
      exact SolidityImport.lookup_bind_other _ _ _ _ indexFresh
    | stop state => rw [step] at executed; cases executed
    | «return» value state => rw [step] at executed; cases executed
    | revert => rw [step] at executed; cases executed
    | revertWithData data => rw [step] at executed; cases executed
    | interpretationError message => rw [step] at executed; cases executed
    | exceptional state => rw [step] at executed; cases executed

/-- Lift the arbitrary-local frame through the actual generated statement,
including count evaluation and its initial index binding. -/
theorem statement (oracle : DenoteOracle) (fields : List Field) (initial final : DenoteState)
    (source destination start index byte address key : String) (count : Expr)
    (indexFresh : index ≠ key) (byteFresh : byte ≠ key) (addressFresh : address ≠ key)
    (executed : execStmt oracle fields initial (SolidityImport.AbiEncoding.copyBytes
      (.localVar source) (.localVar destination) (.localVar start) count index byte address) = .continue final) :
    lookupValue final.bindings key = lookupValue initial.bindings key := by
  simp only [SolidityImport.AbiEncoding.copyBytes, execStmt] at executed
  cases evaluated : evalExpr oracle fields initial count with
  | none => simp only [evaluated] at executed; cases executed
  | some size =>
    simp only [evaluated] at executed
    have same := loop oracle fields source destination start index byte address key
      indexFresh byteFresh addressFresh size 0
      { initial with bindings := bindValue initial.bindings index (wordNormalize 0) } final executed
    exact same.trans (SolidityImport.lookup_bind_other _ _ _ _ indexFresh)

end Compiler.Proofs.IRGeneration.ImportedCreationCopyBindings

