import Compiler.Proofs.IRGeneration.ImportedCalldataWord
import Contracts.SolidityImportSmoke.ImportedCreationDecoderHead

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderFields
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev sourceExpr (offset : Nat) : Expr := .add (.localVar "_verity_slice_tmp_0_calldata") (.literal offset)
abbrev destinationExpr (offset : Nat) : Expr := .add (.localVar "_verity_slice_tmp_0_memory") (.literal offset)
def store (offset : Nat) : Stmt := .mstore (destinationExpr offset) (.calldataload (sourceExpr offset))
def guarded (offset : Nat) : List Stmt :=
  [SolidityImport.AbiLowering.guard (.lt (.calldataload (sourceExpr offset)) (.literal (2^160))), store offset]
def segment : List Stmt := [store 0] ++ guarded 32 ++ guarded 64
abbrev copied (state : DenoteState) (root base offset : Nat) :=
  ImportedCalldataWord.copied state (root + offset) (base + offset)
def completed (state : DenoteState) (root base : Nat) : DenoteState :=
  copied (copied (copied state root base 0) root base 32) root base 64

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 10).take 5) = some segment := by rfl

/-- Resolve the actual source/base local additions without word wrap. -/
theorem address_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (name : String) (base offset : Nat) (held : lookupValue state.bindings name = base)
    (bound : base + offset < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.add (.localVar name) (.literal offset)) = some (base + offset) := by
  exact ImportedAbiWordBinding.add_evaluated oracle fields state _ _ base offset
    (by simp only [evalExpr, held]) (by
      change some (wordNormalize offset) = some offset
      rw [show wordNormalize offset = offset from Nat.mod_eq_of_lt (by omega)]) bound

/-- A real scalar field copy, including actual physical memory expansion. -/
theorem execute_store (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (root base offset : Nat)
    (source : lookupValue state.bindings "_verity_slice_tmp_0_calldata" = root)
    (destination : lookupValue state.bindings "_verity_slice_tmp_0_memory" = base)
    (sourceBound : root + offset < Verity.Core.Uint256.modulus)
    (destinationBound : base + offset < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state [store offset] = .continue (copied state root base offset) := by
  rw [SolidityImport.exec_singleton]
  exact ImportedCalldataWord.execute oracle fields state _ _ _ _
    (address_evaluated oracle fields state _ _ _ source sourceBound)
    (address_evaluated oracle fields state _ _ _ destination destinationBound)

/-- Check the canonical address at its real read before performing the copy. -/
theorem execute_guarded (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (root base offset : Nat)
    (source : lookupValue state.bindings "_verity_slice_tmp_0_calldata" = root)
    (destination : lookupValue state.bindings "_verity_slice_tmp_0_memory" = base)
    (sourceBound : root + offset < Verity.Core.Uint256.modulus)
    (destinationBound : base + offset < Verity.Core.Uint256.modulus)
    (canonical : ImportedCalldataWord.word state (root + offset) < 2^160) :
    execStmtList oracle fields state (guarded offset) = .continue (copied state root base offset) := by
  have guardEval := ImportedCalldataWord.canonical_evaluated oracle fields state _ _ (2^160)
    (address_evaluated oracle fields state _ _ _ source sourceBound) (by decide) canonical
  rw [guarded, ImportedAbiTupleHead.guard_cons oracle fields state _ _ guardEval]
  exact execute_store oracle fields state root base offset source destination sourceBound destinationBound

/-- Execute all five real instructions; canonical values are ORIGINAL calldata
words, not assumed evaluated guards or intermediate memory values. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (root base : Nat)
    (source : lookupValue state.bindings "_verity_slice_tmp_0_calldata" = root)
    (destination : lookupValue state.bindings "_verity_slice_tmp_0_memory" = base)
    (sourceBound : root + 64 < Verity.Core.Uint256.modulus)
    (destinationBound : base + 64 < Verity.Core.Uint256.modulus)
    (canonical32 : ImportedCalldataWord.word state (root + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (root + 64) < 2^160) :
    execStmtList oracle fields state segment = .continue (completed state root base) := by
  have first := execute_store oracle fields state root base 0 source destination (by omega) (by omega)
  have second := execute_guarded oracle fields (copied state root base 0) root base 32
    source destination (by omega) (by omega) canonical32
  have third := execute_guarded oracle fields (copied (copied state root base 0) root base 32)
    root base 64 source destination sourceBound destinationBound canonical64
  rw [segment, SolidityImport.exec_append, SolidityImport.exec_append, first]
  change (match execStmtList oracle fields (copied state root base 0) (guarded 32) with
    | .continue next => execStmtList oracle fields next (guarded 64)
    | outcome => outcome) = _
  rw [second]
  exact third

/-- The first stored word survives both later field writes. -/
theorem first_bytes (state : DenoteState) (root base : Nat) (index : Fin 32) :
    (completed state root base).world.physicalByte (base + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state root)) index := by
  have small := index.isLt
  rw [completed, ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega)),
    ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega))]
  exact ImportedCalldataWord.byte_at state (root + 0) (base + 0) index

/-- The middle word is original calldata and survives the final write. -/
theorem middle_bytes (state : DenoteState) (root base : Nat) (index : Fin 32) :
    (completed state root base).world.physicalByte (base + 32 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (root + 32))) index := by
  have small := index.isLt
  rw [completed, ImportedCalldataWord.byte_frame _ _ _ _ (Or.inl (by omega)),
    ImportedCalldataWord.byte_at]
  rfl

theorem last_bytes (state : DenoteState) (root base : Nat) (index : Fin 32) :
    (completed state root base).world.physicalByte (base + 64 + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (root + 64))) index := by
  exact ImportedCalldataWord.byte_at _ _ _ _

/-- The entire five-instruction field segment preserves every outside byte. -/
theorem byte_frame (state : DenoteState) (root base query : Nat)
    (outside : query < base ∨ base + 96 ≤ query) :
    (completed state root base).world.physicalByte query = state.world.physicalByte query := by
  rw [completed, ImportedCalldataWord.byte_frame _ _ _ _ (by omega),
    ImportedCalldataWord.byte_frame _ _ _ _ (by omega),
    ImportedCalldataWord.byte_frame _ _ _ _ (by omega)]

theorem coherent (state : DenoteState) (root base : Nat) : Coherent (completed state root base).world :=
  ImportedCalldataWord.coherent _ _ _

def prefixSegment : List Stmt := ImportedCreationDecoderHead.segment ++ segment
abbrev rootPointer (state : DenoteState) := 4 + ImportedAbiTupleHead.rawOffset state 0
def prefixCompleted (state : DenoteState) : DenoteState :=
  completed (ImportedCreationDecoderHead.completed state) (rootPointer state) 128

theorem actual_prefix :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 15) = some prefixSegment := by rfl

/-- Actual full original-transaction decoder prefix, including eager canonical
address validation before the dynamic-array header is inspected. -/
theorem execute_prefix (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (offsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160) :
    execStmtList oracle fields state prefixSegment = .continue (prefixCompleted state) := by
  have head := ImportedCreationDecoderHead.execute oracle fields state
    headAvailable offsetBound tupleAvailable sizeBound
  have source := ImportedCreationDecoderHead.root_binding state
  have destination : lookupValue (ImportedCreationDecoderHead.completed state).bindings
      "_verity_slice_tmp_0_memory" = 128 := by
    exact (SolidityImport.lookup_bind_other _ "_verity_slice_tmp_0_next" _ _ (by decide)).trans
      (SolidityImport.lookup_bind_same _ _ _)
  have sourceBound : rootPointer state + 64 < Verity.Core.Uint256.modulus := by
    have : state.world.calldataSize.val < Verity.Core.Uint256.modulus :=
      lt_trans sizeBound Verity.Core.Int256.signBit_lt_modulus
    omega
  have fieldsRun := execute oracle fields (ImportedCreationDecoderHead.completed state)
    (rootPointer state) 128 source destination sourceBound (by decide) canonical32 canonical64
  rw [prefixSegment, SolidityImport.exec_append, head]
  exact fieldsRun

/-- The real field stores cannot clobber the allocator word below the object. -/
theorem free_pointer (state : DenoteState) (root base : Nat) (pastPointer : 96 ≤ base)
    (inputCoherent : Coherent state.world) :
    (completed state root base).world.memory 64 = state.world.memory 64 := by
  apply ImportedAbiArray.word_of_bytes state.world _ 64 inputCoherent (coherent state root base)
  intro index
  exact byte_frame state root base (64 + index.val) (Or.inl (by have := index.isLt; omega))

/-- All real prefix bindings needed by the next array decoder are retained. -/
theorem prefix_bindings (state : DenoteState) :
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_calldata" = rootPointer state ∧
    lookupValue (prefixCompleted state).bindings "_verity_slice_tmp_0_memory" = 128 := by
  constructor
  · exact ImportedCreationDecoderHead.root_binding state
  · exact (SolidityImport.lookup_bind_other _ "_verity_slice_tmp_0_next" _ _ (by decide)).trans
      (SolidityImport.lookup_bind_same _ _ _)

/-- At the actual array-decoder entry, the free pointer is derived384. -/
theorem prefix_free_pointer (state : DenoteState) :
    (prefixCompleted state).world.memory 64 = Verity.Core.Uint256.ofNat 384 := by
  rw [prefixCompleted, free_pointer _ _ _ (by decide) (ImportedCreationDecoderHead.coherent state)]
  exact ImportedCreationDecoderHead.free_pointer state

end Contracts.SolidityImportSmoke.ImportedCreationDecoderFields
