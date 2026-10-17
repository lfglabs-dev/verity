import Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayHead

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayBounds
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev lengthExpr : Expr := .localVar "_verity_slice_tmp_0_array3_length"
abbrev arrayExpr : Expr := .localVar "_verity_slice_tmp_0_array3_memory"
abbrev headerExpr : Expr := .localVar "_verity_slice_tmp_0_array3_header"
abbrev nextExpr : Expr := .add arrayExpr (.mul (.literal 32) (.add lengthExpr (.literal 1)))
def nextState (state : DenoteState) (base count : Nat) : DenoteState :=
  { state with bindings := bindValue state.bindings "_verity_slice_tmp_0_array3_next" (base + 32 * (count + 1)) }
def completed (state : DenoteState) (base count header : Nat) : DenoteState :=
  { (nextState state base count) with
    bindings := bindValue (nextState state base count).bindings "_verity_slice_tmp_0_array3_data" (header + 32) }

def segment : List Stmt :=
  [.ite (.le lengthExpr (.literal (2^64 - 1))) [] [.panicCode (.literal 0x41)],
   .letVar "_verity_slice_tmp_0_array3_next" nextExpr,
   .ite (.le (.localVar "_verity_slice_tmp_0_array3_next") (.literal (2^64 - 1))) [] [.panicCode (.literal 0x41)],
   .ite (.ge (.localVar "_verity_slice_tmp_0_array3_next") arrayExpr) [] [.panicCode (.literal 0x41)],
   .letVar "_verity_slice_tmp_0_array3_data" (.add headerExpr (.literal 32)),
   SolidityImport.AbiLowering.guard
     (.le (.add (.localVar "_verity_slice_tmp_0_array3_data") (.mul (.literal 128) lengthExpr)) .calldatasize)]

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 20).take 6) = some segment := by rfl

/-- Prove actual count+1, multiplication and base addition do not wrap. -/
theorem next_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base count : Nat)
    (array : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = base)
    (length : lookupValue state.bindings "_verity_slice_tmp_0_array3_length" = count)
    (budget : base + 32 * (count + 1) ≤ 2^64 - 1) :
    evalExpr oracle fields state nextExpr = some (base + 32 * (count + 1)) := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have increment := ImportedAbiWordBinding.add_evaluated oracle fields state lengthExpr (.literal 1) count 1
    (by simp only [evalExpr, length]) (by rfl) (by omega)
  have product := ImportedAbiBounds.mul_evaluated oracle fields state (.literal 32)
    (.add lengthExpr (.literal 1)) 32 (count + 1) (by rfl) increment
    (by decide) (by omega) (by omega)
  exact ImportedAbiWordBinding.add_evaluated oracle fields state arrayExpr _ base (32 * (count + 1))
    (by simp only [evalExpr, array]) product (by omega)

/-- Actual end-of-payload guard, deriving all arithmetic from input descriptors. -/
theorem payload_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (data count : Nat)
    (dataHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_data" = data)
    (countHeld : lookupValue state.bindings "_verity_slice_tmp_0_array3_length" = count)
    (available : data + 128 * count ≤ state.world.calldataSize.val) :
    evalExpr oracle fields state
      (.le (.add (.localVar "_verity_slice_tmp_0_array3_data") (.mul (.literal 128) lengthExpr)) .calldatasize) = some 1 := by
  have sizeBound : state.world.calldataSize.val < Verity.Core.Uint256.modulus := state.world.calldataSize.isLt
  have countBound : count < Verity.Core.Uint256.modulus := by omega
  have product := ImportedAbiBounds.mul_evaluated oracle fields state (.literal 128) lengthExpr
    128 count (by rfl) (by simp only [evalExpr, countHeld]) (by decide) countBound (by omega)
  have endEval := ImportedAbiWordBinding.add_evaluated oracle fields state
    (.localVar "_verity_slice_tmp_0_array3_data") _ data (128 * count)
    (by simp only [evalExpr, dataHeld]) product (by omega)
  exact ImportedAbiBounds.le_evaluated oracle fields state _ _ _ _ endEval (by rfl) available

/-- All six actual allocation/range instructions, with exact complete poststate.
The count/size constraints are numerical, not evaluated-expression premises. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base count header : Nat)
    (array : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = base)
    (length : lookupValue state.bindings "_verity_slice_tmp_0_array3_length" = count)
    (head : lookupValue state.bindings "_verity_slice_tmp_0_array3_header" = header)
    (budget : base + 32 * (count + 1) ≤ 2^64 - 1)
    (available : header + 32 + 128 * count ≤ state.world.calldataSize.val) :
    execStmtList oracle fields state segment = .continue (completed state base count header) := by
  have countGuard := ImportedAbiBounds.le_evaluated oracle fields state lengthExpr (.literal (2^64 - 1))
    count (2^64 - 1) (by simp only [evalExpr, length]) (by rfl) (by omega)
  have nextEval := next_evaluated oracle fields state base count array length budget
  have nextHeld : evalExpr oracle fields (nextState state base count)
      (.localVar "_verity_slice_tmp_0_array3_next") = some (base + 32 * (count + 1)) := by
    simp [evalExpr, nextState]
  have nextGuard := ImportedAbiBounds.le_evaluated oracle fields (nextState state base count)
    (.localVar "_verity_slice_tmp_0_array3_next") (.literal (2^64 - 1)) _ (2^64 - 1) nextHeld (by rfl) budget
  have noWrap : evalExpr oracle fields (nextState state base count)
      (.ge (.localVar "_verity_slice_tmp_0_array3_next") arrayExpr) = some 1 := by
    simp [evalExpr, nextState, SolidityImport.lookup_bind_other, array, boolWord]
  have dataEval := ImportedAbiWordBinding.add_evaluated oracle fields (nextState state base count)
    headerExpr (.literal 32) header 32
    (by simp [evalExpr, nextState, SolidityImport.lookup_bind_other, head]) (by rfl)
    (by have sizeBound : state.world.calldataSize.val < Verity.Core.Uint256.modulus := state.world.calldataSize.isLt; omega)
  have payload := payload_evaluated oracle fields (completed state base count header) (header + 32) count
    (by simp [completed]) (by simp [completed, nextState, SolidityImport.lookup_bind_other, length]) available
  rw [segment, ImportedAbiBounds.allocation_cons oracle fields _ _ _ countGuard,
    SolidityImport.exec_let_cons, nextEval]
  change execStmtList oracle fields (nextState state base count) (_ :: _) = _
  rw [ImportedAbiBounds.allocation_cons oracle fields _ _ _ nextGuard,
    ImportedAbiBounds.allocation_cons oracle fields _ _ _ noWrap, SolidityImport.exec_let_cons, dataEval]
  change execStmtList oracle fields (completed state base count header) [_] = _
  rw [ImportedAbiTupleHead.guard_cons oracle fields _ _ [] payload]
  rfl

theorem world_eq (state : DenoteState) (base count header : Nat) :
    (completed state base count header).world = state.world := by rfl

theorem descriptors (state : DenoteState) (base count header : Nat) :
    lookupValue (completed state base count header).bindings "_verity_slice_tmp_0_array3_next" =
      base + 32 * (count + 1) ∧
    lookupValue (completed state base count header).bindings "_verity_slice_tmp_0_array3_data" = header + 32 := by
  simp [completed, nextState, SolidityImport.lookup_bind_other]

theorem binding_frame (state : DenoteState) (base count header : Nat) (key : String)
    (notNext : "_verity_slice_tmp_0_array3_next" ≠ key)
    (notData : "_verity_slice_tmp_0_array3_data" ≠ key) :
    lookupValue (completed state base count header).bindings key = lookupValue state.bindings key := by
  change lookupValue (bindValue (bindValue state.bindings "_verity_slice_tmp_0_array3_next" _)
    "_verity_slice_tmp_0_array3_data" _) key = _
  rw [SolidityImport.lookup_bind_other _ _ _ _ notData, SolidityImport.lookup_bind_other _ _ _ _ notNext]

abbrev rootPointer := ImportedCreationDecoderArrayHead.rootPointer
abbrev originalCount (state : DenoteState) := ImportedCreationDecoderArrayHead.count state (rootPointer state)
abbrev originalHeader (state : DenoteState) := ImportedCreationDecoderArrayHead.header state (rootPointer state)
def prefixSegment : List Stmt := ImportedCreationDecoderArrayHead.prefixSegment ++ segment
def prefixCompleted (state : DenoteState) : DenoteState :=
  completed (ImportedCreationDecoderArrayHead.prefixCompleted state) 384 (originalCount state) (originalHeader state)

theorem actual_prefix :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 26) = some prefixSegment := by rfl

theorem original_size (state : DenoteState) :
    (ImportedCreationDecoderArrayHead.prefixCompleted state).world.calldataSize = state.world.calldataSize := by
  rw [ImportedCreationDecoderArrayHead.prefixCompleted, ImportedCreationDecoderArrayHead.world_eq,
    ImportedCreationDecoderArrayHead.original_size]

/-- The entire actual allocation/range prefix is derived from original calldata.
No intermediate success, evaluated guard or postworld is assumed. -/
theorem execute_prefix (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (rootOffsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160)
    (offsetBound : ImportedCreationDecoderArrayHead.relative state (rootPointer state) ≤ 2^64 - 1)
    (arrayAvailable : originalHeader state + 32 ≤ state.world.calldataSize.val)
    (budget : 384 + 32 * (originalCount state + 1) ≤ 2^64 - 1)
    (payloadAvailable : originalHeader state + 32 + 128 * originalCount state ≤ state.world.calldataSize.val) :
    execStmtList oracle fields state prefixSegment = .continue (prefixCompleted state) := by
  have first := ImportedCreationDecoderArrayHead.execute_prefix oracle fields state
    headAvailable rootOffsetBound tupleAvailable sizeBound canonical32 canonical64 offsetBound arrayAvailable
  have bound := ImportedCreationDecoderArrayHead.prefix_descriptors state
  have last := execute oracle fields (ImportedCreationDecoderArrayHead.prefixCompleted state)
    384 (originalCount state) (originalHeader state) bound.1 bound.2.2 bound.2.1 budget
    (by simpa only [original_size] using payloadAvailable)
  rw [prefixSegment, SolidityImport.exec_append, first]
  exact last

/-- The actual computed allocation end and data pointer use original input count/header. -/
theorem prefix_descriptors (state : DenoteState) :
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_array3_next" =
      384 + 32 * (originalCount state + 1) ∧
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_array3_data" = originalHeader state + 32 := by
  exact descriptors _ _ _ _

def stores : List Stmt :=
  [.mstore arrayExpr lengthExpr, .mstore (.literal 64) (.localVar "_verity_slice_tmp_0_array3_next")]
def allocated (state : DenoteState) (base count : Nat) : DenoteState :=
  { state with world := ((state.world.writePhysicalMemoryValue base (Verity.Core.Uint256.ofNat count)).writePhysicalMemoryValue
    64 (Verity.Core.Uint256.ofNat (base + 32 * (count + 1)))) }

theorem actual_stores :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 26).take 2) = some stores := by rfl

/-- Execute both actual stores with exact bytes, overlapping views and expansion. -/
theorem execute_stores (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base count : Nat)
    (array : lookupValue state.bindings "_verity_slice_tmp_0_array3_memory" = base)
    (length : lookupValue state.bindings "_verity_slice_tmp_0_array3_length" = count)
    (next : lookupValue state.bindings "_verity_slice_tmp_0_array3_next" = base + 32 * (count + 1)) :
    execStmtList oracle fields state stores = .continue (allocated state base count) := by
  have first := execStmt_mstore_physical oracle fields state arrayExpr lengthExpr base count
    (by simp only [evalExpr, array]) (by simp only [evalExpr, length])
  let stored : DenoteState := { state with
    world := state.world.writePhysicalMemoryValue base (Verity.Core.Uint256.ofNat count) }
  have second := execStmt_mstore_physical oracle fields stored (.literal 64)
    (.localVar "_verity_slice_tmp_0_array3_next") 64 (base + 32 * (count + 1))
    (by rfl) (by simp only [evalExpr, stored, next])
  change execStmtList oracle fields state
    ([.mstore arrayExpr lengthExpr] ++ [.mstore (.literal 64) (.localVar "_verity_slice_tmp_0_array3_next")]) = _
  rw [SolidityImport.exec_append, SolidityImport.exec_singleton, first]
  exact (SolidityImport.exec_singleton oracle fields stored _).trans second

/-- The allocator update preserves the array's actual stored count. -/
theorem allocated_count (state : DenoteState) (base count : Nat) (pastPointer : 96 ≤ base) :
    (allocated state base count).world.memory base = Verity.Core.Uint256.ofNat count := by
  change ((state.world.writePhysicalMemoryValue base (Verity.Core.Uint256.ofNat count)).writePhysicalMemoryWord
    64 (valueWord (Verity.Core.Uint256.ofNat (base + 32 * (count + 1))))).memory base = _
  rw [writePhysicalMemoryWord_outside _ _ _ _ (writePhysicalMemoryValue_coherent _ _ _) (Or.inr pastPointer)]
  exact writePhysicalMemoryValue_at _ _ _

theorem allocated_pointer (state : DenoteState) (base count : Nat) :
    (allocated state base count).world.memory 64 = Verity.Core.Uint256.ofNat (base + 32 * (count + 1)) := by
  exact writePhysicalMemoryValue_at _ _ _

theorem allocated_frame (state : DenoteState) (base count query : Nat)
    (outsidePointer : query < 64 ∨ 96 ≤ query) (outsideArray : query < base ∨ base + 32 ≤ query) :
    (allocated state base count).world.physicalByte query = state.world.physicalByte query := by
  rw [allocated, writePhysicalMemoryValue_byte_outside _ _ _ _ outsidePointer,
    writePhysicalMemoryValue_byte_outside _ _ _ _ outsideArray]

theorem allocated_coherent (state : DenoteState) (base count : Nat) : Coherent (allocated state base count).world :=
  writePhysicalMemoryValue_coherent _ _ _

theorem prefix_inputs (state : DenoteState) :
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_array3_memory" = 384 ∧
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_array3_length" = originalCount state := by
  constructor
  · exact (binding_frame _ _ _ _ _ (by decide) (by decide)).trans
      (ImportedCreationDecoderArrayHead.prefix_descriptors state).1
  · exact (binding_frame _ _ _ _ _ (by decide) (by decide)).trans
      (ImportedCreationDecoderArrayHead.prefix_descriptors state).2.2

def allocationPrefix : List Stmt := prefixSegment ++ stores
def allocationCompleted (state : DenoteState) : DenoteState :=
  allocated (prefixCompleted state) 384 (originalCount state)

theorem actual_allocation_prefix :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 28) = some allocationPrefix := by rfl

/-- All real original-transaction instructions through both array allocator stores. -/
theorem execute_allocation_prefix (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (rootOffsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160)
    (offsetBound : ImportedCreationDecoderArrayHead.relative state (rootPointer state) ≤ 2^64 - 1)
    (arrayAvailable : originalHeader state + 32 ≤ state.world.calldataSize.val)
    (budget : 384 + 32 * (originalCount state + 1) ≤ 2^64 - 1)
    (payloadAvailable : originalHeader state + 32 + 128 * originalCount state ≤ state.world.calldataSize.val) :
    execStmtList oracle fields state allocationPrefix = .continue (allocationCompleted state) := by
  have first := execute_prefix oracle fields state headAvailable rootOffsetBound tupleAvailable sizeBound
    canonical32 canonical64 offsetBound arrayAvailable budget payloadAvailable
  have inputs := prefix_inputs state
  have last := execute_stores oracle fields (prefixCompleted state) 384 (originalCount state)
    inputs.1 inputs.2 (prefix_descriptors state).1
  rw [allocationPrefix, SolidityImport.exec_append, first]
  exact last

end Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayBounds
