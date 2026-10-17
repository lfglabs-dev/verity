import Contracts.SolidityImportSmoke.ImportedCreationHeaderAllocation

namespace Contracts.SolidityImportSmoke.ImportedCreationHeaderPreparation
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

def sizeExpression : Expr := .add (.add (.literal 0) (.literal 11)) (.localVar "_verity_slice_tmp_19")
def totalBinding : Stmt := .letVar "_verity_slice_tmp_22" sizeExpression
def segment := ImportedCreationHeaderAllocation.segment ++ [totalBinding]

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 71).take 7) = some segment := by rfl

/-- Keep the actual free-memory-pointer write, then frame the header store
away from that pointer's entire word window. -/
theorem header_pointer (oracle : DenoteOracle) (fields : List Field)
    (initial final : DenoteState) (base : Nat) (pastPointer : 96 ≤ base)
    (pointer : (initial.world.memory 64).val = base) (bounded : base + 32 ≤ 2^64 - 1)
    (executed : execStmtList oracle fields initial ImportedCreationHeaderAllocation.segment = .continue final) :
    (final.world.memory 64).val = base + 32 := by
  have same := StmtOutcome.continue.inj
    ((ImportedCreationHeaderAllocation.execute oracle fields initial base pointer bounded).symm.trans executed)
  rw [← same]
  have frame := writePhysicalMemoryWord_outside
    (initial.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (base + 32)))
    base (valueWord (Verity.Core.Uint256.ofNat ImportedCreationHeaderAllocation.word)) 64
    (writePhysicalMemoryValue_coherent initial.world 64 _) (Or.inl (by omega))
  change (((initial.world.writePhysicalMemoryValue 64 _).writePhysicalMemoryWord base _).memory 64).val = _
  rw [frame, writePhysicalMemoryValue_at]
  have range : base + 32 < Verity.Core.Uint256.modulus := by
    have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  exact Nat.mod_eq_of_lt range

/-- The real header allocator preserves any unrelated original local. -/
theorem header_binding (oracle : DenoteOracle) (fields : List Field)
    (initial final : DenoteState) (base : Nat) (key : String)
    (pointer : (initial.world.memory 64).val = base) (bounded : base + 32 ≤ 2^64 - 1)
    (executed : execStmtList oracle fields initial ImportedCreationHeaderAllocation.segment = .continue final)
    (baseFresh : "_verity_slice_tmp_20" ≠ key) (endFresh : "_verity_slice_tmp_21" ≠ key) :
    lookupValue final.bindings key = lookupValue initial.bindings key := by
  have same := StmtOutcome.continue.inj
    ((ImportedCreationHeaderAllocation.execute oracle fields initial base pointer bounded).symm.trans executed)
  rw [← same]
  exact (SolidityImport.lookup_bind_other _ _ _ _ endFresh).trans
    (SolidityImport.lookup_bind_other _ _ _ _ baseFresh)

/-- Exact modulo-safe evaluation of actual node77's total-size expression. -/
theorem total_size (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) (size : Nat)
    (length : lookupValue state.bindings "_verity_slice_tmp_19" = size)
    (bounded : 11 + size < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state sizeExpression = some (11 + size) := by
  have sizeBound : size < Verity.Core.Uint256.modulus := by omega
  simp only [sizeExpression, evalExpr, length]
  change some ((11 + size % Verity.Core.Uint256.modulus) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt sizeBound, Nat.mod_eq_of_lt bounded]

/-- Execute the total-size let after the ACTUAL header run. All incoming
state fields other than the freshly bound total length are retained. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base size : Nat) (pointer : (state.world.memory 64).val = base)
    (bounded : base + 32 ≤ 2^64 - 1)
    (length : lookupValue state.bindings "_verity_slice_tmp_19" = size)
    (range : 11 + size < Verity.Core.Uint256.modulus) :
    ∃ header final,
      execStmtList oracle fields state ImportedCreationHeaderAllocation.segment = .continue header ∧
      execStmtList oracle fields state segment = .continue final ∧
      final = { header with bindings := bindValue header.bindings "_verity_slice_tmp_22" (11 + size) } := by
  let header : DenoteState := { state with
    bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_20" base) "_verity_slice_tmp_21" (base + 32)
    world := (state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (base + 32))).writePhysicalMemoryValue
      base (Verity.Core.Uint256.ofNat ImportedCreationHeaderAllocation.word) }
  have ran : execStmtList oracle fields state ImportedCreationHeaderAllocation.segment = .continue header :=
    ImportedCreationHeaderAllocation.execute oracle fields state base pointer bounded
  have held := (header_binding oracle fields state header base "_verity_slice_tmp_19" pointer bounded
    ran (by decide) (by decide)).trans length
  refine ⟨header, { header with bindings := bindValue header.bindings "_verity_slice_tmp_22" (11 + size) }, ran, ?_, rfl⟩
  rw [segment, SolidityImport.exec_append, ran]
  simp only [totalBinding, execStmtList, execStmt, total_size oracle fields header size held range]

structure Prepared (initial ready : DenoteState) (base source size : Nat) : Prop where
  pointer : (ready.world.memory 64).val = base + 32
  header : lookupValue ready.bindings "_verity_slice_tmp_20" = base
  payload : lookupValue ready.bindings "_verity_slice_tmp_3" = source
  count : lookupValue ready.bindings "_verity_slice_tmp_19" = size
  total : lookupValue ready.bindings "_verity_slice_tmp_22" = 11 + size
  original : ∀ index < size, ready.world.physicalByte (source + index) = initial.world.physicalByte (source + index)
  bytes : ∀ index : Fin 11, UInt8.ofNat (ready.world.physicalByte (base + index.val)).val =
    ImportedCreationHeaderAllocation.prefixBytes[index.val]!

/-- Derive all descriptors needed by packing, the original payload snapshot
and actual header bytes from the seven executed preparation statements. -/
theorem prepare (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base source size : Nat) (pastPointer : 96 ≤ source) (beforeHeader : source + size ≤ base)
    (pointer : (state.world.memory 64).val = base) (bounded : base + 32 ≤ 2^64 - 1)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = source)
    (length : lookupValue state.bindings "_verity_slice_tmp_19" = size)
    (range : 11 + size < Verity.Core.Uint256.modulus) :
    ∃ ready, execStmtList oracle fields state segment = .continue ready ∧ Prepared state ready base source size := by
  obtain ⟨header, ready, hrun, run, equality⟩ := execute oracle fields state base size pointer bounded length range
  have original := ImportedCreationHeaderAllocation.payload_byte oracle fields state header base source size
    pointer bounded hrun pastPointer beforeHeader
  have literal := ImportedCreationHeaderAllocation.header_byte oracle fields state header base pointer bounded hrun
  have baseBinding : lookupValue header.bindings "_verity_slice_tmp_20" = base := by
    have same := StmtOutcome.continue.inj
      ((ImportedCreationHeaderAllocation.execute oracle fields state base pointer bounded).symm.trans hrun)
    rw [← same]
    simp only [SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_21" ≠ "_verity_slice_tmp_20"), SolidityImport.lookup_bind_same]
  refine ⟨ready, run, ?_⟩
  rw [equality]
  refine ⟨header_pointer oracle fields state header base (by omega) pointer bounded hrun, ?_, ?_, ?_, ?_, original, literal⟩
  · simpa only [SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_22" ≠ "_verity_slice_tmp_20")] using baseBinding
  · simpa only [SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_22" ≠ "_verity_slice_tmp_3")] using
      (header_binding oracle fields state header base "_verity_slice_tmp_3" pointer bounded hrun
        (by decide) (by decide)).trans payload
  · simpa only [SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_22" ≠ "_verity_slice_tmp_19")] using
      (header_binding oracle fields state header base "_verity_slice_tmp_19" pointer bounded hrun
        (by decide) (by decide)).trans length
  · exact SolidityImport.lookup_bind_same _ _ _

end Contracts.SolidityImportSmoke.ImportedCreationHeaderPreparation

