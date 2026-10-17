import Contracts.SolidityImportSmoke.ImportedCreationDecodedMarket

namespace Contracts.SolidityImportSmoke.ImportedCreationDecodedPrefix
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev rootPointer := ImportedCreationDecodedMarket.rootPointer
abbrev count := ImportedCreationDecodedMarket.count
abbrev data := ImportedCreationDecodedMarket.data
abbrev header := ImportedCreationDecodedMarket.header
abbrev free := ImportedCreationDecodedMarket.free
abbrev actualFields := effectiveFields ImportedCreationPrefixFrames.imported.model

def key (state : DenoteState) := ImportedCalldataWord.word state 36
def value (state : DenoteState) := ImportedCalldataWord.word state 68
def bound (state : DenoteState) : DenoteState :=
  { state with
    bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_1" (key state))
      "_verity_slice_tmp_2" (value state) }
def written (oracle : DenoteOracle) (state : DenoteState) : DenoteState :=
  { (bound state) with
    world := state.world.writeSlot (wordNormalize (oracle.mappingSlot 0 (key state))) (Verity.Core.Uint256.ofNat (value state)) }

def segment : List Stmt :=
  [.letVar "_verity_slice_tmp_1" (.calldataload (.literal 36)),
   .letVar "_verity_slice_tmp_2" (.calldataload (.literal 68)),
   .setStructMember "values" (.localVar "_verity_slice_tmp_1") "__solidity_value" (.localVar "_verity_slice_tmp_2")]

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 36).take 3) = some segment := by rfl

theorem operands (state : DenoteState) :
    lookupValue (bound state).bindings "_verity_slice_tmp_1" = key state ∧
    lookupValue (bound state).bindings "_verity_slice_tmp_2" = value state := by
  simp [bound, SolidityImport.lookup_bind_other]

/-- Execute both actual calldata reads and the real mapping node with its exact
imported field layout. The full slot update is derived, with no target slot premise. -/
theorem execute (oracle : DenoteOracle) (state : DenoteState) :
    execStmtList oracle actualFields state segment = .continue (written oracle state) := by
  have first : evalExpr oracle actualFields state (.calldataload (.literal 36)) = some (key state) := by rfl
  let middle : DenoteState := { state with bindings := bindValue state.bindings "_verity_slice_tmp_1" (key state) }
  have second : evalExpr oracle actualFields middle (.calldataload (.literal 68)) = some (value state) := by rfl
  have stored := ImportedCreationPrefixFrames.actual_mapping_instruction oracle (bound state)
  rw [(operands state).1, (operands state).2] at stored
  rw [segment, SolidityImport.exec_let_cons, first]
  change execStmtList oracle actualFields middle (_ :: _) = _
  rw [SolidityImport.exec_let_cons, second]
  exact (SolidityImport.exec_singleton oracle actualFields (bound state) _).trans stored

/-- Mapping writes preserve all physical-memory bytes and word observations. -/
theorem memory_frame (oracle : DenoteOracle) (state : DenoteState) :
    (written oracle state).world.byteMemory = state.world.byteMemory ∧
    (written oracle state).world.memory = state.world.memory := by exact ⟨rfl, rfl⟩

theorem binding_frame (oracle : DenoteOracle) (state : DenoteState) (name : String)
    (notKey : "_verity_slice_tmp_1" ≠ name) (notValue : "_verity_slice_tmp_2" ≠ name) :
    lookupValue (written oracle state).bindings name = lookupValue state.bindings name := by
  exact (SolidityImport.lookup_bind_other _ _ _ _ notValue).trans
    (SolidityImport.lookup_bind_other _ _ _ _ notKey)

def prefixSegment : List Stmt := ImportedCreationDecodedMarket.prefixSegment ++ segment
def completed (oracle : DenoteOracle) (state : DenoteState) : DenoteState :=
  written oracle (ImportedCreationDecodedMarket.prefixCompleted state)

theorem actual_prefix :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 39) = some prefixSegment := by rfl

/-- Whole original-transaction decoder and persistent write, actual nodes0..38. -/
theorem execute_prefix (oracle : DenoteOracle) (state : DenoteState)
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
    execStmtList oracle actualFields state prefixSegment = .continue (completed oracle state) := by
  have decoded := ImportedCreationDecodedMarket.execute_prefix oracle actualFields state headAvailable rootOffsetBound
    tupleAvailable sizeBound canonical32 canonical64 offsetBound arrayAvailable budget payloadAvailable canonical
    canonical192 canonical224
  rw [prefixSegment, SolidityImport.exec_append, decoded]
  exact execute oracle (ImportedCreationDecodedMarket.prefixCompleted state)

theorem original_key (state : DenoteState) : key (ImportedCreationDecodedMarket.prefixCompleted state) = key state :=
  ImportedCreationDecodedMarket.prefix_input_word state 36

theorem original_value (state : DenoteState) : value (ImportedCreationDecodedMarket.prefixCompleted state) = value state :=
  ImportedCreationDecodedMarket.prefix_input_word state 68

/-- Entire persistent slot effect uses the ORIGINAL transaction arguments. -/
theorem world_effect (oracle : DenoteOracle) (state : DenoteState) :
    (completed oracle state).world = (ImportedCreationDecodedMarket.prefixCompleted state).world.writeSlot
      (wordNormalize (oracle.mappingSlot 0 (key state))) (Verity.Core.Uint256.ofNat (value state)) := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.writeSlot _ _ = _
  rw [original_key, original_value]

theorem coherent (oracle : DenoteOracle) (state : DenoteState) : Coherent (completed oracle state).world := by
  exact ImportedCreationDecodedMarket.prefix_coherent state

theorem pointer (oracle : DenoteOracle) (state : DenoteState)
    (budget : free state + count state * 128 ≤ 2^64 - 1) :
    ((completed oracle state).world.memory 64).val = free state + count state * 128 := by
  rw [completed, (memory_frame oracle _).2]
  exact ImportedCreationDecodedMarket.prefix_pointer state budget

end Contracts.SolidityImportSmoke.ImportedCreationDecodedPrefix
