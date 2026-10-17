import Compiler.Proofs.IRGeneration.ImportedCalldataFields
import Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayBounds

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderElementFields
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

def entries : List ImportedCalldataFields.Entry := [(0, true), (32, false), (64, false), (96, true)]
def segment : List Stmt := ImportedCalldataFields.program
  "_verity_slice_tmp_0_array3_element_source" "_verity_slice_tmp_0_array3_element_element" entries
abbrev completed (state : DenoteState) (source destination : Nat) :=
  ImportedCalldataFields.run state source destination entries

def actualLoopBody : List Stmt :=
  let stmt : Option Stmt := ImportedCreationPrefixFrames.imported.model.functions.head?.bind (fun fn => fn.body[28]?)
  match stmt with
  | some (.forEach _ _ body) => body
  | _ => []

theorem actual_segment : actualLoopBody.drop 8 = segment := by rfl

/-- All four actual struct fields with their two eager canonical-address guards. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source destination : Nat)
    (read : lookupValue state.bindings "_verity_slice_tmp_0_array3_element_source" = source)
    (write : lookupValue state.bindings "_verity_slice_tmp_0_array3_element_element" = destination)
    (sourceBound : source + 96 < Verity.Core.Uint256.modulus)
    (destinationBound : destination + 96 < Verity.Core.Uint256.modulus)
    (canonical0 : ImportedCalldataWord.word state source < 2^160)
    (canonical96 : ImportedCalldataWord.word state (source + 96) < 2^160) :
    execStmtList oracle fields state segment = .continue (completed state source destination) := by
  apply ImportedCalldataFields.execute oracle fields state _ _ source destination entries read write
  · intro entry member
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> constructor <;> omega
  · intro entry member flag
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa only [Nat.add_zero] using canonical0
    · contradiction
    · contradiction
    · exact canonical96

theorem input_word (state : DenoteState) (source destination query : Nat) :
    ImportedCalldataWord.word (completed state source destination) query = ImportedCalldataWord.word state query :=
  ImportedCalldataFields.input_word _ _ _ _ _

theorem binding_frame (state : DenoteState) (source destination : Nat) :
    (completed state source destination).bindings = state.bindings :=
  ImportedCalldataFields.binding_frame _ _ _ _

theorem coherent (state : DenoteState) (source destination : Nat) (initial : Coherent state.world) :
    Coherent (completed state source destination).world := ImportedCalldataFields.coherent _ _ _ _ initial

theorem byte_frame (state : DenoteState) (source destination query : Nat)
    (outside : query < destination ∨ destination + 128 ≤ query) :
    (completed state source destination).world.physicalByte query = state.world.physicalByte query := by
  apply ImportedCalldataFields.byte_frame
  intro entry member
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> omega

/-- Every byte of actual field0 comes from the original calldata word. -/
theorem bytes0 (state : DenoteState) (source destination : Nat) (index : Fin 32) :
    (completed state source destination).world.physicalByte (destination + 0 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (source + 0))) index := by
  have small := index.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_at]

/-- Every byte of actual field1 comes from the original calldata word. -/
theorem bytes32 (state : DenoteState) (source destination : Nat) (index : Fin 32) :
    (completed state source destination).world.physicalByte (destination + 32 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (source + 32))) index := by
  have small := index.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_at]
  rfl

/-- Every byte of actual field2 comes from the original calldata word. -/
theorem bytes64 (state : DenoteState) (source destination : Nat) (index : Fin 32) :
    (completed state source destination).world.physicalByte (destination + 64 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (source + 64))) index := by
  have small := index.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_at]
  rfl

/-- Every byte of actual field3 comes from the original calldata word. -/
theorem bytes96 (state : DenoteState) (source destination : Nat) (index : Fin 32) :
    (completed state source destination).world.physicalByte (destination + 96 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (source + 96))) index := by
  have small := index.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_at]
  rfl

end Contracts.SolidityImportSmoke.ImportedCreationDecoderElementFields
