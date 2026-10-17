import Compiler.Proofs.IRGeneration.ImportedCalldataWord

namespace Compiler.Proofs.IRGeneration.ImportedCalldataFields
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory

abbrev Entry := Nat × Bool
abbrev address (name : String) (offset : Nat) : Expr := .add (.localVar name) (.literal offset)
def field (sourceName destinationName : String) (entry : Entry) : List Stmt :=
  let value := Expr.calldataload (address sourceName entry.1)
  (if entry.2 then [SolidityImport.AbiLowering.guard (.lt value (.literal (2^160)))] else []) ++
    [.mstore (address destinationName entry.1) value]
def program (sourceName destinationName : String) (entries : List Entry) : List Stmt :=
  entries.flatMap (field sourceName destinationName)
def run (state : DenoteState) (source destination : Nat) : List Entry → DenoteState
  | [] => state
  | entry :: rest => run (ImportedCalldataWord.copied state (source + entry.1) (destination + entry.1)) source destination rest

/-- A generated local plus a checked constant offset, without truncation. -/
theorem address_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (name : String) (base offset : Nat) (held : lookupValue state.bindings name = base)
    (bound : base + offset < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (address name offset) = some (base + offset) := by
  exact ImportedAbiWordBinding.add_evaluated oracle fields state _ _ base offset
    (by simp only [evalExpr, held]) (by
      change some (wordNormalize offset) = some offset
      rw [show wordNormalize offset = offset from Nat.mod_eq_of_lt (by omega)]) bound

/-- Execute an actual scalar/address field; names are arbitrary generated locals. -/
theorem execute_field (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (sourceName destinationName : String) (source destination : Nat) (entry : Entry)
    (read : lookupValue state.bindings sourceName = source)
    (write : lookupValue state.bindings destinationName = destination)
    (readBound : source + entry.1 < Verity.Core.Uint256.modulus)
    (writeBound : destination + entry.1 < Verity.Core.Uint256.modulus)
    (canonical : entry.2 = true → ImportedCalldataWord.word state (source + entry.1) < 2^160) :
    execStmtList oracle fields state (field sourceName destinationName entry) =
      .continue (ImportedCalldataWord.copied state (source + entry.1) (destination + entry.1)) := by
  have r := address_evaluated
    oracle fields state sourceName source entry.1 read readBound
  have w := address_evaluated
    oracle fields state destinationName destination entry.1 write writeBound
  have copied := ImportedCalldataWord.execute oracle fields state _ _ _ _ r w
  cases flag : entry.2 with
  | false => simpa only [field, flag, Bool.false_eq_true, if_false, List.nil_append, SolidityImport.exec_singleton] using copied
  | true =>
      have guardEval := ImportedCalldataWord.canonical_evaluated oracle fields state _ _ (2^160)
        r (by decide) (canonical flag)
      simp only [field, flag, ite_true, List.cons_append, List.nil_append]
      rw [ImportedAbiTupleHead.guard_cons oracle fields _ _ _ guardEval, SolidityImport.exec_singleton]
      exact copied

/-- Run every actual field with canonicality taken from original calldata. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (sourceName destinationName : String) (source destination : Nat) (entries : List Entry)
    (read : lookupValue state.bindings sourceName = source)
    (write : lookupValue state.bindings destinationName = destination)
    (bounds : ∀ entry ∈ entries, source + entry.1 < Verity.Core.Uint256.modulus ∧
      destination + entry.1 < Verity.Core.Uint256.modulus)
    (canonical : ∀ entry ∈ entries, entry.2 = true → ImportedCalldataWord.word state (source + entry.1) < 2^160) :
    execStmtList oracle fields state (program sourceName destinationName entries) =
      .continue (run state source destination entries) := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      have first := execute_field oracle fields state sourceName destinationName source destination entry
        read write (bounds entry (by simp)).1 (bounds entry (by simp)).2 (canonical entry (by simp))
      rw [program, List.flatMap_cons, SolidityImport.exec_append, first]
      exact ih (ImportedCalldataWord.copied state (source + entry.1) (destination + entry.1)) read write
        (fun e member => bounds e (by simp [member]))
        (fun e member flag => canonical e (by simp [member]) flag)

/-- Calldata words and every binding survive an arbitrary sequence of field stores. -/
theorem input_word (state : DenoteState) (source destination : Nat) (entries : List Entry) (query : Nat) :
    ImportedCalldataWord.word (run state source destination entries) query = ImportedCalldataWord.word state query := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact (ih _).trans (ImportedCalldataWord.input_word _ _ _ _)

theorem binding_frame (state : DenoteState) (source destination : Nat) (entries : List Entry) :
    (run state source destination entries).bindings = state.bindings := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact ih _

theorem coherent (state : DenoteState) (source destination : Nat) (entries : List Entry)
    (initial : Coherent state.world) : Coherent (run state source destination entries).world := by
  induction entries generalizing state with
  | nil => exact initial
  | cons entry rest ih => exact ih _ (ImportedCalldataWord.coherent _ _ _)

theorem byte_frame (state : DenoteState) (source destination query : Nat) (entries : List Entry)
    (outside : ∀ entry ∈ entries, query < destination + entry.1 ∨ destination + entry.1 + 32 ≤ query) :
    (run state source destination entries).world.physicalByte query = state.world.physicalByte query := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      exact (ih _ (fun e member => outside e (by simp [member]))).trans
        (ImportedCalldataWord.byte_frame _ _ _ _ (outside entry (by simp)))

end Compiler.Proofs.IRGeneration.ImportedCalldataFields
