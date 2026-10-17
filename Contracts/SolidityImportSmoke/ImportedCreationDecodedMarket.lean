import Contracts.SolidityImportSmoke.ImportedCreationDecodedArray

namespace Contracts.SolidityImportSmoke.ImportedCreationDecodedMarket
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev rootPointer := ImportedCreationDecodedArray.rootPointer
abbrev count := ImportedCreationDecodedArray.count
abbrev data := ImportedCreationDecodedArray.data
abbrev header := ImportedCreationDecodedArray.header
abbrev free := ImportedCreationDecodedArray.free

def entries : List ImportedCalldataFields.Entry := [(128, false), (160, false), (192, true), (224, true)]
def pointerStore : Stmt := .mstore (ImportedCalldataFields.address "_verity_slice_tmp_0_memory" 96)
  (.localVar "_verity_slice_tmp_0_array3_memory")
def stored (state : DenoteState) (base array : Nat) : DenoteState :=
  { state with world := state.world.writePhysicalMemoryValue (base + 96) (Verity.Core.Uint256.ofNat array) }
def segment : List Stmt := [pointerStore] ++ ImportedCalldataFields.program
  "_verity_slice_tmp_0_calldata" "_verity_slice_tmp_0_memory" entries
def completed (state : DenoteState) (root base array : Nat) : DenoteState :=
  ImportedCalldataFields.run (stored state base array) root base entries

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 29).take 7) = some segment := by rfl

/-- Actual pointer member store followed by all remaining scalar/address fields. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (root base array : Nat)
    (rootHeld : lookupValue state.bindings "_verity_slice_tmp_0_calldata" = root)
    (baseHeld : lookupValue state.bindings "_verity_slice_tmp_0_memory" = base)
    (arrayHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = array)
    (sourceBound : root + 224 < Verity.Core.Uint256.modulus)
    (destinationBound : base + 224 < Verity.Core.Uint256.modulus)
    (canonical192 : ImportedCalldataWord.word state (root + 192) < 2^160)
    (canonical224 : ImportedCalldataWord.word state (root + 224) < 2^160) :
    execStmtList oracle fields state segment = .continue (completed state root base array) := by
  have pointer := execStmt_mstore_physical oracle fields state
    (ImportedCalldataFields.address "_verity_slice_tmp_0_memory" 96)
    (.localVar "_verity_slice_tmp_0_array3_memory") (base + 96) array
    (ImportedCalldataFields.address_evaluated oracle fields state _ _ _ baseHeld (by omega))
    (by simp only [evalExpr, arrayHeld])
  have tail := ImportedCalldataFields.execute oracle fields (stored state base array)
    "_verity_slice_tmp_0_calldata" "_verity_slice_tmp_0_memory" root base entries rootHeld baseHeld (by
      intro entry member
      simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> constructor <;> omega) (by
      intro entry member flag
      simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · contradiction
      · contradiction
      · exact canonical192
      · exact canonical224)
  rw [segment, SolidityImport.exec_append, SolidityImport.exec_singleton, pointerStore, pointer]
  exact tail

theorem original_word (state : DenoteState) (query : Nat) :
    ImportedCalldataWord.word (ImportedCreationDecodedArray.completed state) query = ImportedCalldataWord.word state query := by
  rw [ImportedCreationDecodedArray.completed, ImportedCreationDecoderArrayLoop.input_word,
    ImportedCreationDecodedArray.original_word]

theorem original_size (state : DenoteState) :
    (ImportedCreationDecodedArray.completed state).world.calldataSize = state.world.calldataSize := by
  rw [ImportedCreationDecodedArray.completed, ImportedCreationDecoderArrayLoop.input_size,
    ImportedCreationDecodedArray.original_size]

theorem array_binding (state : DenoteState) :
    lookupValue (ImportedCreationDecodedArray.completed state).bindings "_verity_slice_tmp_0_array3_memory" = 384 := by
  rw [ImportedCreationDecodedArray.completed, ImportedCreationDecoderArrayLoop.binding_frame _ _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide)]
  exact (ImportedCreationDecodedArray.descriptors state).2.1

def prefixSegment : List Stmt := ImportedCreationDecodedArray.segment ++ segment
def prefixCompleted (state : DenoteState) : DenoteState :=
  completed (ImportedCreationDecodedArray.completed state) (rootPointer state) 128 384

theorem actual_prefix :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 36) = some prefixSegment := by rfl

/-- Complete actual memory Market decoder, from ORIGINAL transaction state. -/
theorem execute_prefix (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (rootOffsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160)
    (offsetBound : ImportedCreationDecoderArrayHead.relative state (rootPointer state) ≤ 2^64 - 1)
    (arrayAvailable : header state + 32 ≤ state.world.calldataSize.val)
    (budget : free state + count state * 128 ≤ 2^64 - 1)
    (payloadAvailable : data state + count state * 128 ≤ state.world.calldataSize.val)
    (canonical : ∀ i < count state, ImportedCalldataWord.word state (data state + i * 128) < 2^160 ∧
      ImportedCalldataWord.word state (data state + i * 128 + 96) < 2^160)
    (canonical192 : ImportedCalldataWord.word state (rootPointer state + 192) < 2^160)
    (canonical224 : ImportedCalldataWord.word state (rootPointer state + 224) < 2^160) :
    execStmtList oracle fields state prefixSegment = .continue (prefixCompleted state) := by
  have first := ImportedCreationDecodedArray.execute oracle fields state headAvailable rootOffsetBound tupleAvailable
    sizeBound canonical32 canonical64 offsetBound arrayAvailable budget payloadAvailable canonical
  have held := ImportedCreationDecodedArray.market_bindings state
  have sourceBound : rootPointer state + 224 < Verity.Core.Uint256.modulus := by
    have ceiling : Verity.Core.Int256.signBit < Verity.Core.Uint256.modulus := Verity.Core.Int256.signBit_lt_modulus
    omega
  have last := execute oracle fields (ImportedCreationDecodedArray.completed state) (rootPointer state) 128 384
    held.1 held.2 (array_binding state) sourceBound (by decide)
    (by rw [original_word]; exact canonical192) (by rw [original_word]; exact canonical224)
  rw [prefixSegment, SolidityImport.exec_append, first]
  exact last

theorem binding_frame (state : DenoteState) (root base array : Nat) :
    (completed state root base array).bindings = state.bindings := by
  rw [completed, ImportedCalldataFields.binding_frame]
  rfl

theorem input_word (state : DenoteState) (root base array query : Nat) :
    ImportedCalldataWord.word (completed state root base array) query = ImportedCalldataWord.word state query := by
  rw [completed, ImportedCalldataFields.input_word]
  rfl

theorem coherent (state : DenoteState) (root base array : Nat) : Coherent (completed state root base array).world :=
  ImportedCalldataFields.coherent _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _)

theorem byte_frame (state : DenoteState) (root base array query : Nat)
    (outside : query < base + 96 ∨ base + 256 ≤ query) :
    (completed state root base array).world.physicalByte query = state.world.physicalByte query := by
  rw [completed, ImportedCalldataFields.byte_frame _ _ _ _ _ (by
    intro entry member
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> omega)]
  exact writePhysicalMemoryValue_byte_outside _ _ _ _ (by omega)

/-- Every byte of the stored array pointer survives all four subsequent copies. -/
theorem pointer_byte (state : DenoteState) (root base array : Nat) (lane : Fin 32) :
    (completed state root base array).world.physicalByte (base + 96 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat array) lane := by
  rw [completed, ImportedCalldataFields.byte_frame _ _ _ _ _ (by
    intro entry member
    simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
    have small := lane.isLt
    rcases member with rfl | rfl | rfl | rfl <;> omega)]
  exact writePhysicalMemoryValue_byte_at _ _ _ _

theorem pointer_word (state : DenoteState) (root base array : Nat) :
    (completed state root base array).world.memory (base + 96) = Verity.Core.Uint256.ofNat array := by
  have equality := ImportedAbiArray.word_of_bytes (stored state base array).world
    (completed state root base array).world (base + 96) (writePhysicalMemoryValue_coherent _ _ _)
    (coherent state root base array) (by
      intro lane
      rw [pointer_byte]
      exact (writePhysicalMemoryValue_byte_at _ _ _ _).symm)
  exact equality.trans (writePhysicalMemoryValue_at _ _ _)

theorem free_pointer (state : DenoteState) (root base array : Nat) (pastPointer : 96 ≤ base)
    (initial : Coherent state.world) :
    (completed state root base array).world.memory 64 = state.world.memory 64 := by
  apply ImportedAbiArray.word_of_bytes state.world _ 64 initial (coherent state root base array)
  intro lane
  exact byte_frame state root base array (64 + lane.val) (Or.inl (by have := lane.isLt; omega))

theorem stored_input_word (state : DenoteState) (base array query : Nat) :
    ImportedCalldataWord.word (stored state base array) query = ImportedCalldataWord.word state query := by rfl

theorem bytes128 (state : DenoteState) (root base array : Nat) (lane : Fin 32) :
    (completed state root base array).world.physicalByte (base + 128 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (root + 128))) lane := by
  have small := lane.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_at]
  rw [stored_input_word]

theorem bytes160 (state : DenoteState) (root base array : Nat) (lane : Fin 32) :
    (completed state root base array).world.physicalByte (base + 160 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (root + 160))) lane := by
  have small := lane.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_at]
  rw [ImportedCalldataWord.input_word]
  rw [stored_input_word]

theorem bytes192 (state : DenoteState) (root base array : Nat) (lane : Fin 32) :
    (completed state root base array).world.physicalByte (base + 192 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (root + 192))) lane := by
  have small := lane.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  rw [ImportedCalldataWord.byte_at]
  rw [ImportedCalldataWord.input_word]
  rw [ImportedCalldataWord.input_word]
  rw [stored_input_word]

theorem bytes224 (state : DenoteState) (root base array : Nat) (lane : Fin 32) :
    (completed state root base array).world.physicalByte (base + 224 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (root + 224))) lane := by
  have small := lane.isLt
  simp only [completed, entries, ImportedCalldataFields.run]
  rw [ImportedCalldataWord.byte_at]
  rw [ImportedCalldataWord.input_word]
  rw [ImportedCalldataWord.input_word]
  rw [ImportedCalldataWord.input_word]
  rw [stored_input_word]

theorem prefix_bindings (state : DenoteState) :
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_calldata" = rootPointer state ∧
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_memory" = 128 := by
  unfold prefixCompleted
  rw [binding_frame]
  exact ImportedCreationDecodedArray.market_bindings state

theorem prefix_input_word (state : DenoteState) (query : Nat) :
    ImportedCalldataWord.word (prefixCompleted state) query = ImportedCalldataWord.word state query := by
  rw [prefixCompleted, input_word, original_word]

theorem prefix_coherent (state : DenoteState) : Coherent (prefixCompleted state).world :=
  coherent _ _ _ _

theorem prefix_pointer (state : DenoteState) (budget : free state + count state * 128 ≤ 2^64 - 1) :
    ((prefixCompleted state).world.memory 64).val = free state + count state * 128 := by
  rw [prefixCompleted, free_pointer _ _ _ _ (by decide) (ImportedCreationDecodedArray.coherent state)]
  exact ImportedCreationDecodedArray.free_pointer state budget

/-- Completing Market cannot alter the already materialized pointer array or structs. -/
theorem prefix_array_byte (state : DenoteState) (query : Nat) (pastMarket : 384 ≤ query) :
    (prefixCompleted state).world.physicalByte query = (ImportedCreationDecodedArray.completed state).world.physicalByte query := by
  exact byte_frame _ _ _ _ _ (Or.inr pastMarket)

theorem prefix_array_word (state : DenoteState) (query : Nat) (pastMarket : 384 ≤ query) :
    (prefixCompleted state).world.memory query = (ImportedCreationDecodedArray.completed state).world.memory query := by
  apply ImportedAbiArray.word_of_bytes (ImportedCreationDecodedArray.completed state).world
    (prefixCompleted state).world query (ImportedCreationDecodedArray.coherent state) (prefix_coherent state)
  intro lane
  exact prefix_array_byte state (query + lane.val) (by omega)

theorem prefix_count_word (state : DenoteState) :
    (prefixCompleted state).world.memory 384 = Verity.Core.Uint256.ofNat (count state) := by
  rw [prefix_array_word _ _ (by decide)]
  exact ImportedCreationDecodedArray.count_word state

theorem prefix_array_pointer (state : DenoteState) :
    (prefixCompleted state).world.memory 224 = Verity.Core.Uint256.ofNat 384 := by
  exact pointer_word _ _ _ _

/-- The first three decoded words survive the entire remaining Market decoder. -/
theorem prefix_first_byte (state : DenoteState) (query : Nat) (lower : 128 ≤ query) (upper : query < 224) :
    (prefixCompleted state).world.physicalByte query =
      (ImportedCreationDecoderFields.prefixCompleted state).world.physicalByte query := by
  have kept := byte_frame (ImportedCreationDecodedArray.completed state) (rootPointer state) 128 384 query
    (Or.inl upper)
  exact kept.trans (ImportedCreationDecodedArray.market_byte state query (by omega) (by omega))

end Contracts.SolidityImportSmoke.ImportedCreationDecodedMarket
