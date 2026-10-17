import Compiler.Proofs.IRGeneration.ImportedAbiBounds
import Contracts.SolidityImportSmoke.ImportedCreationDecoderFields

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayHead
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev rootExpr : Expr := .localVar "_verity_slice_tmp_0_calldata"
abbrev relativeExpr : Expr := .calldataload (ImportedCreationDecoderFields.sourceExpr 96)
def relative (state : DenoteState) (root : Nat) := ImportedCalldataWord.word state (root + 96)
def header (state : DenoteState) (root : Nat) := root + relative state root
def count (state : DenoteState) (root : Nat) := ImportedCalldataWord.word state (header state root)
def pointerState (state : DenoteState) (base : Nat) : DenoteState :=
  { state with bindings := bindValue state.bindings "_verity_slice_tmp_0_array3_memory" base }
def headerState (state : DenoteState) (root base : Nat) : DenoteState :=
  { (pointerState state base) with
    bindings := bindValue (pointerState state base).bindings "_verity_slice_tmp_0_array3_header" (header state root) }
def completed (state : DenoteState) (root base : Nat) : DenoteState :=
  { (headerState state root base) with
    bindings := bindValue (headerState state root base).bindings "_verity_slice_tmp_0_array3_length" (count state root) }

def segment : List Stmt :=
  [.letVar "_verity_slice_tmp_0_array3_memory" (.mload (.literal 64)),
   SolidityImport.AbiLowering.guard (.le relativeExpr (.literal (2^64 - 1))),
   .letVar "_verity_slice_tmp_0_array3_header" (.add rootExpr relativeExpr),
   SolidityImport.AbiLowering.guard
     (.slt (.add (.localVar "_verity_slice_tmp_0_array3_header") (.literal 31)) .calldatasize),
   .letVar "_verity_slice_tmp_0_array3_length" (.calldataload (.localVar "_verity_slice_tmp_0_array3_header"))]

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 15).take 5) = some segment := by rfl

/-- No world observation changes while reading the actual array descriptors. -/
theorem world_eq (state : DenoteState) (root base : Nat) :
    (completed state root base).world = state.world := by rfl

/-- Real root+relative computation derives the original array-header pointer. -/
theorem header_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (root : Nat) (held : lookupValue state.bindings "_verity_slice_tmp_0_calldata" = root)
    (rootBound : root + 96 < Verity.Core.Uint256.modulus)
    (headerBound : header state root < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.add rootExpr relativeExpr) = some (header state root) := by
  exact ImportedAbiWordBinding.add_evaluated oracle fields state _ _ root (relative state root)
    (by simp only [evalExpr, held])
    (ImportedCalldataWord.read_evaluated oracle fields state _ _
      (ImportedCreationDecoderFields.address_evaluated oracle fields state _ _ _ held rootBound)) headerBound

/-- The actual signed header+31 guard follows from a complete calldata word. -/
theorem header_guard_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (root base : Nat) (available : header state root + 32 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit) :
    evalExpr oracle fields (headerState state root base)
      (.slt (.add (.localVar "_verity_slice_tmp_0_array3_header") (.literal 31)) .calldatasize) = some 1 := by
  have wordBound : header state root + 31 < Verity.Core.Uint256.modulus := by
    have signBound : Verity.Core.Int256.signBit < Verity.Core.Uint256.modulus :=
      Verity.Core.Int256.signBit_lt_modulus
    omega
  have pointer := ImportedAbiWordBinding.add_evaluated oracle fields (headerState state root base)
    (.localVar "_verity_slice_tmp_0_array3_header") (.literal 31) (header state root) 31
    (by simp [evalExpr, headerState]) (by rfl) wordBound
  exact ImportedAbiBounds.slt_evaluated oracle fields _ _ _ _ _ pointer (by rfl)
    (by omega) sizeBound (by omega)

/-- Execute all actual descriptor extraction and range checking. The header and
count are derived from original calldata, with no output binding hypotheses. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (root base : Nat) (held : lookupValue state.bindings "_verity_slice_tmp_0_calldata" = root)
    (pointer : (state.world.memory 64).val = base)
    (rootBound : root + 96 < Verity.Core.Uint256.modulus)
    (offsetBound : relative state root ≤ 2^64 - 1)
    (available : header state root + 32 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit) :
    execStmtList oracle fields state segment = .continue (completed state root base) := by
  have pointerEval : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  have kept : lookupValue (pointerState state base).bindings "_verity_slice_tmp_0_calldata" = root := by
    exact (SolidityImport.lookup_bind_other _ _ _ _ (by decide)).trans held
  have relativeEval := ImportedCalldataWord.read_evaluated oracle fields (pointerState state base) _ _
    (ImportedCreationDecoderFields.address_evaluated oracle fields _ _ _ _ kept rootBound)
  have offsetGuard := ImportedAbiBounds.le_evaluated oracle fields (pointerState state base) relativeExpr
    (.literal (2^64 - 1)) (relative state root) (2^64 - 1) relativeEval (by rfl) offsetBound
  have headerBound : header state root < Verity.Core.Uint256.modulus := by
    have signBound : Verity.Core.Int256.signBit < Verity.Core.Uint256.modulus :=
      Verity.Core.Int256.signBit_lt_modulus
    omega
  have added := header_evaluated oracle fields (pointerState state base) root kept rootBound headerBound
  have checked := header_guard_evaluated oracle fields state root base available sizeBound
  have loaded : evalExpr oracle fields (headerState state root base)
      (.calldataload (.localVar "_verity_slice_tmp_0_array3_header")) = some (count state root) := by
    exact ImportedCalldataWord.read_evaluated oracle fields _ _ _ (by simp [evalExpr, headerState])
  rw [segment, SolidityImport.exec_let_cons, pointerEval]
  change execStmtList oracle fields (pointerState state base) (_ :: _) = _
  rw [ImportedAbiTupleHead.guard_cons oracle fields _ _ _ offsetGuard,
    SolidityImport.exec_let_cons, added]
  change execStmtList oracle fields (headerState state root base) (_ :: _) = _
  rw [ImportedAbiTupleHead.guard_cons oracle fields _ _ _ checked, SolidityImport.exec_let_cons, loaded]
  rfl

/-- All three actual bindings, with original transaction header and count. -/
theorem descriptors (state : DenoteState) (root base : Nat) :
    lookupValue (completed state root base).bindings "_verity_slice_tmp_0_array3_memory" = base ∧
    lookupValue (completed state root base).bindings "_verity_slice_tmp_0_array3_header" = header state root ∧
    lookupValue (completed state root base).bindings "_verity_slice_tmp_0_array3_length" = count state root := by
  simp [completed, headerState, pointerState, SolidityImport.lookup_bind_other]

/-- Descriptor extraction preserves every other local, including Market/root. -/
theorem binding_frame (state : DenoteState) (root base : Nat) (key : String)
    (notArray : "_verity_slice_tmp_0_array3_memory" ≠ key)
    (notHeader : "_verity_slice_tmp_0_array3_header" ≠ key)
    (notCount : "_verity_slice_tmp_0_array3_length" ≠ key) :
    lookupValue (completed state root base).bindings key = lookupValue state.bindings key := by
  change lookupValue (bindValue (bindValue (bindValue state.bindings
    "_verity_slice_tmp_0_array3_memory" base) "_verity_slice_tmp_0_array3_header" (header state root))
    "_verity_slice_tmp_0_array3_length" (count state root)) key = _
  rw [SolidityImport.lookup_bind_other _ _ _ _ notCount,
    SolidityImport.lookup_bind_other _ _ _ _ notHeader,
    SolidityImport.lookup_bind_other _ _ _ _ notArray]

def prefixSegment : List Stmt := ImportedCreationDecoderFields.prefixSegment ++ segment
abbrev rootPointer := ImportedCreationDecoderFields.rootPointer
def prefixCompleted (state : DenoteState) : DenoteState :=
  completed (ImportedCreationDecoderFields.prefixCompleted state) (rootPointer state) 384

theorem actual_prefix :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 20) = some prefixSegment := by rfl

/-- Factor the input frame before composing deeper physical memory states. -/
theorem original_word (state : DenoteState) (query : Nat) :
    ImportedCalldataWord.word (ImportedCreationDecoderFields.prefixCompleted state) query =
      ImportedCalldataWord.word state query := by
  unfold ImportedCreationDecoderFields.prefixCompleted ImportedCreationDecoderFields.completed
  rw [ImportedCalldataWord.input_word, ImportedCalldataWord.input_word, ImportedCalldataWord.input_word]
  rfl

theorem copied_size (state : DenoteState) (source destination : Nat) :
    (ImportedCalldataWord.copied state source destination).world.calldataSize = state.world.calldataSize := by rfl

theorem original_size (state : DenoteState) :
    (ImportedCreationDecoderFields.prefixCompleted state).world.calldataSize = state.world.calldataSize := by
  unfold ImportedCreationDecoderFields.prefixCompleted ImportedCreationDecoderFields.completed
  rw [copied_size, copied_size, copied_size]
  rfl

theorem original_header (state : DenoteState) (root : Nat) :
    header (ImportedCreationDecoderFields.prefixCompleted state) root = header state root := by
  unfold header relative
  rw [original_word]

theorem original_count (state : DenoteState) (root : Nat) :
    count (ImportedCreationDecoderFields.prefixCompleted state) root = count state root := by
  unfold count
  rw [original_header, original_word]

/-- All actual original-transaction instructions through array count extraction. -/
theorem execute_prefix (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (rootOffsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160)
    (offsetBound : relative state (rootPointer state) ≤ 2^64 - 1)
    (arrayAvailable : header state (rootPointer state) + 32 ≤ state.world.calldataSize.val) :
    execStmtList oracle fields state prefixSegment = .continue (prefixCompleted state) := by
  have first := ImportedCreationDecoderFields.execute_prefix oracle fields state
    headAvailable rootOffsetBound tupleAvailable sizeBound canonical32 canonical64
  have held := (ImportedCreationDecoderFields.prefix_bindings state).1
  have pointer : ((ImportedCreationDecoderFields.prefixCompleted state).world.memory 64).val = 384 := by
    rw [ImportedCreationDecoderFields.prefix_free_pointer]
    rfl
  have rootBound : rootPointer state + 96 < Verity.Core.Uint256.modulus := by
    have signBound : Verity.Core.Int256.signBit < Verity.Core.Uint256.modulus :=
      Verity.Core.Int256.signBit_lt_modulus
    omega
  have last := execute oracle fields (ImportedCreationDecoderFields.prefixCompleted state)
    (rootPointer state) 384 held pointer rootBound
    (by simpa only [relative, original_word] using offsetBound)
    (by simpa only [original_header, original_size] using arrayAvailable)
    (by simpa only [original_size] using sizeBound)
  rw [prefixSegment, SolidityImport.exec_append, first]
  exact last

/-- The complete successful prefix derives its new descriptors from original calldata. -/
theorem prefix_descriptors (state : DenoteState) :
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_array3_memory" = 384 ∧
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_array3_header" = header state (rootPointer state) ∧
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_array3_length" = count state (rootPointer state) := by
  have bindings := descriptors (ImportedCreationDecoderFields.prefixCompleted state) (rootPointer state) 384
  unfold prefixCompleted
  simpa only [original_header, original_count] using bindings

end Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayHead
