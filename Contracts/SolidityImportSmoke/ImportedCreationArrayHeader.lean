import Contracts.SolidityImportSmoke.ImportedCreationArrayLoop

namespace Contracts.SolidityImportSmoke.ImportedCreationArrayHeader
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

def offsetExpr : Expr := .sub (.localVar "_verity_slice_tmp_11")
  (.add (.localVar "_verity_slice_tmp_3") (.literal 32))
def addressExpr : Expr := .add (.add (.localVar "_verity_slice_tmp_3") (.literal 32)) (.literal 96)
def segment : List Stmt := [.mstore addressExpr offsetExpr,
  .mstore (.localVar "_verity_slice_tmp_11") (.localVar "_verity_slice_tmp_9")]

def prepared (state : DenoteState) (head count : Nat) : DenoteState :=
  { state with world := ((state.world.writePhysicalMemoryValue (head + 128) (Verity.Core.Uint256.ofNat 256)).writePhysicalMemoryValue
    (head + 288) (Verity.Core.Uint256.ofNat count)) }

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 59).take 2) = some segment := by rfl

/-- The actual tail minus tuple-head pointer is256, derived from layout. -/
theorem offset_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (head : Nat) (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = head + 288)
    (bound : head + 288 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state offsetExpr = some 256 := by
  have a : head + 32 < Verity.Core.Uint256.modulus := by omega
  have h : head < Verity.Core.Uint256.modulus := by omega
  have sum : evalExpr oracle fields state (.add (.localVar "_verity_slice_tmp_3") (.literal 32)) = some (head + 32) := by
    simp only [evalExpr, heldHead]
    change some ((head % Verity.Core.Uint256.modulus + 32) % Verity.Core.Uint256.modulus) = _
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt a]
  rw [offsetExpr, evalExpr, sum]
  simp only [evalExpr, heldTail]
  change some ((Verity.Core.Uint256.ofNat (head + 288) - Verity.Core.Uint256.ofNat (head + 32)).val) = _
  have ordered : (Verity.Core.Uint256.ofNat (head + 32)).val ≤ (Verity.Core.Uint256.ofNat (head + 288)).val := by
    simp only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt bound]
    omega
  rw [Verity.Core.Uint256.sub_eq_of_le ordered]
  simp only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt bound]
  congr 1
  omega

/-- The actual destination of the dynamic-offset word is head+128. -/
theorem address_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (head : Nat) (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (bound : head + 128 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state addressExpr = some (head + 128) := by
  have h : head < Verity.Core.Uint256.modulus := by omega
  have a : head + 32 < Verity.Core.Uint256.modulus := by omega
  have b : head + 32 + 96 < Verity.Core.Uint256.modulus := by omega
  simp only [addressExpr, evalExpr, heldHead]
  change some (((head % Verity.Core.Uint256.modulus + 32) % Verity.Core.Uint256.modulus %
    Verity.Core.Uint256.modulus + 96) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt b]

/-- Execute both real metadata stores; no desired memory is supplied. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (head count : Nat) (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = head + 288)
    (heldCount : lookupValue state.bindings "_verity_slice_tmp_9" = count)
    (bound : head + 288 < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state segment = .continue (prepared state head count) := by
  have first := execStmt_mstore_physical oracle fields state addressExpr offsetExpr (head + 128) 256
    (address_evaluated oracle fields state head heldHead (by omega))
    (offset_evaluated oracle fields state head heldHead heldTail bound)
  let middle := { state with world := state.world.writePhysicalMemoryValue (head + 128) (Verity.Core.Uint256.ofNat 256) }
  have second := execStmt_mstore_physical oracle fields middle (.localVar "_verity_slice_tmp_11")
    (.localVar "_verity_slice_tmp_9") (head + 288) count
    (by simp only [evalExpr, middle, heldTail]) (by simp only [evalExpr, middle, heldCount])
  change execStmt oracle fields state (.mstore addressExpr offsetExpr) = .continue middle at first
  simp only [segment, execStmtList, first, second]
  rfl

/-- Metadata stores preserve every earlier source byte. -/
theorem bytes_before (state : DenoteState) (head count query : Nat) (before : query < head + 128) :
    (prepared state head count).world.physicalByte query = state.world.physicalByte query := by
  rw [prepared, writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inl (by omega)),
    writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inl before)]

/-- Exact original pointer observations before the metadata writes. -/
theorem words_before (state : DenoteState) (head count query : Nat) (coherent : Coherent state.world)
    (before : query + 32 ≤ head + 128) :
    (prepared state head count).world.memory query = state.world.memory query := by
  apply ImportedAbiArray.word_of_bytes state.world _ query coherent (writePhysicalMemoryValue_coherent _ _ _)
  intro offset
  exact bytes_before state head count (query + offset.val) (by have := offset.isLt; omega)

/-- The stored length is derived from the actual count descriptor. -/
theorem length_word (state : DenoteState) (head count : Nat) :
    (prepared state head count).world.memory (head + 288) = Verity.Core.Uint256.ofNat count := by
  exact writePhysicalMemoryValue_at _ _ _

/-- The dynamic offset is retained after the following count store. -/
theorem offset_word (state : DenoteState) (head count : Nat) :
    (prepared state head count).world.memory (head + 128) = Verity.Core.Uint256.ofNat 256 := by
  change ((state.world.writePhysicalMemoryValue (head + 128) (Verity.Core.Uint256.ofNat 256)).writePhysicalMemoryWord
    (head + 288) (valueWord (Verity.Core.Uint256.ofNat count))).memory (head + 128) = _
  rw [writePhysicalMemoryWord_outside _ _ _ _
    (writePhysicalMemoryValue_coherent state.world (head + 128) (Verity.Core.Uint256.ofNat 256)) (Or.inl (by omega))]
  exact writePhysicalMemoryValue_at _ _ _

/-- Original pointer-array values survive both real metadata stores. -/
theorem source_at (state : DenoteState) (head count base index : Nat) (coherent : Coherent state.world)
    (before : base + 32 * index + 32 ≤ head) :
    ImportedAbiArray.sourceAt (prepared state head count).world base index =
      ImportedAbiArray.sourceAt state.world base index := by
  unfold ImportedAbiArray.sourceAt
  rw [words_before state head count _ coherent (by omega)]

def fullSegment := segment ++ [ImportedCreationArrayLoop.statement]
def completed (state : DenoteState) (head base count : Nat) :=
  ImportedCreationArrayLoop.runElements (prepared state head count) base (head + 288) count

theorem actual_full_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 59).take 3) = some fullSegment := by rfl

/-- Execute actual offset+length stores and the COMPLETE arbitrary-count loop.
The prior layout supplies only geometry/bindings, not any output observations. -/
theorem execute_full (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (head base count : Nat) (coherent : Coherent state.world)
    (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = head + 288)
    (heldCount : lookupValue state.bindings "_verity_slice_tmp_9" = count)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (pointers : base + 32 * count ≤ head)
    (sources : ∀ i < count, ImportedAbiArray.sourceAt state.world base i + 128 ≤ head)
    (budget : head + 320 + 128 * count ≤ 2^64 - 1) :
    execStmtList oracle fields state fullSegment = .continue (completed state head base count) := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have metadata := execute oracle fields state head count heldHead heldTail heldCount (by omega)
  have original : ∀ i < count, ImportedAbiArray.sourceAt (prepared state head count).world base i =
      ImportedAbiArray.sourceAt state.world base i := by
    intro i live
    apply source_at state head count base i coherent
    omega
  have copied := ImportedCreationArrayLoop.execute oracle fields (prepared state head count)
    base (head + 288) count (writePhysicalMemoryValue_coherent _ _ _) heldBase heldTail heldCount
    (by omega) (by intro i live; rw [original i live]; have := sources i live; omega) (by omega)
  rw [fullSegment, SolidityImport.exec_append, metadata]
  exact (SolidityImport.exec_singleton oracle fields (prepared state head count) _).trans copied

/-- Every output element is the original pre-metadata struct snapshot. -/
theorem output_bytes (state : DenoteState) (head base count : Nat) (coherent : Coherent state.world)
    (pointers : base + 32 * count ≤ head)
    (sources : ∀ i < count, ImportedAbiArray.sourceAt state.world base i + 128 ≤ head)
    (index : Fin count) (offset : Fin 128) :
    (completed state head base count).world.physicalByte (head + 320 + 128 * index.val + offset.val) =
      state.world.physicalByte (ImportedAbiArray.sourceAt state.world base index.val + offset.val) := by
  have original : ∀ i < count, ImportedAbiArray.sourceAt (prepared state head count).world base i =
      ImportedAbiArray.sourceAt state.world base i := by
    intro i live
    apply source_at state head count base i coherent
    omega
  have bytes := ImportedCreationArrayLoop.output_bytes (prepared state head count) base (head + 288) count
    (by intro i live; rw [original i live]; have := sources i live; omega) index offset
  rw [original index.val index.isLt] at bytes
  have preserved := bytes_before state head count
    (ImportedAbiArray.sourceAt state.world base index.val + offset.val)
    (by have := sources index.val index.isLt; have := offset.isLt; omega)
  exact bytes.trans preserved

/-- The loop starts after both metadata words, so it preserves them completely. -/
theorem metadata_word (state : DenoteState) (head base count query : Nat)
    (before : query + 32 ≤ head + 320) :
    (completed state head base count).world.memory query = (prepared state head count).world.memory query := by
  rw [completed, ImportedCreationArrayLoop.world_eq]
  exact ImportedAbiArray.word_frame _ _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _) (Or.inl (by omega))

theorem completed_length (state : DenoteState) (head base count : Nat) :
    (completed state head base count).world.memory (head + 288) = Verity.Core.Uint256.ofNat count := by
  rw [metadata_word state head base count _ (by omega)]
  exact length_word state head count

theorem completed_offset (state : DenoteState) (head base count : Nat) :
    (completed state head base count).world.memory (head + 128) = Verity.Core.Uint256.ofNat 256 := by
  rw [metadata_word state head base count _ (by omega)]
  exact offset_word state head count

end Contracts.SolidityImportSmoke.ImportedCreationArrayHeader
