import Contracts.SolidityImportSmoke.ImportedCreationOriginalSnapshots

namespace Contracts.SolidityImportSmoke.ImportedCreationHeaderAllocation
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory

/-- Literal emitted by the actual importer for the eleven-byte IdLib prefix. -/
def word : Nat := 43441855373900879501489557976705837587736829351010673829379042307146688495616

def segment : List Stmt := SolidityImport.AbiEncoding.reserve
  "_verity_slice_tmp_20" "_verity_slice_tmp_21" (.literal 32) ++
  [.mstore (.add (.localVar "_verity_slice_tmp_20") (.literal 0)) (.literal word)]

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 71).take 6) = some segment := by rfl

/-- Exact whole-state header allocation/write, not a supplied header memory. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) (base : Nat)
    (pointer : (state.world.memory 64).val = base) (bounded : base + 32 ≤ 2^64 - 1) :
    execStmtList oracle fields state segment = .continue
      { state with
        bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_20" base)
          "_verity_slice_tmp_21" (base + 32)
        world := (state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (base + 32))).writePhysicalMemoryValue
          base (Verity.Core.Uint256.ofNat word) } := by
  let reserved : DenoteState := { state with
    bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_20" base) "_verity_slice_tmp_21" (base + 32)
    world := state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (base + 32)) }
  have allocated := execStmtList_reserve_physical oracle fields state "_verity_slice_tmp_20"
    "_verity_slice_tmp_21" (.literal 32) base 32 pointer (by decide) (by rfl) bounded
  have baseBound : base < Verity.Core.Uint256.modulus := by
    have limit : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  have descriptor : lookupValue reserved.bindings "_verity_slice_tmp_20" = base := by
    simp only [reserved, SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_21" ≠ "_verity_slice_tmp_20"), SolidityImport.lookup_bind_same]
  have address : evalExpr oracle fields reserved (.add (.localVar "_verity_slice_tmp_20") (.literal 0)) = some base := by
    simp only [evalExpr, descriptor]
    change some ((base % Verity.Core.Uint256.modulus + 0) % Verity.Core.Uint256.modulus) = _
    rw [Nat.mod_eq_of_lt baseBound, Nat.add_zero, Nat.mod_eq_of_lt baseBound]
  rw [segment, SolidityImport.exec_append, allocated]
  exact (SolidityImport.exec_singleton oracle fields reserved _).trans
    (execStmt_mstore_physical oracle fields reserved _ _ base word address (by rfl))

/-- Header allocation preserves each original payload byte before its output
and beyond the free-pointer word, with both actual stores retained. -/
theorem payload_byte (oracle : DenoteOracle) (fields : List Field)
    (initial final : DenoteState) (base source size : Nat)
    (pointer : (initial.world.memory 64).val = base) (bounded : base + 32 ≤ 2^64 - 1)
    (executed : execStmtList oracle fields initial segment = .continue final)
    (pastPointer : 96 ≤ source) (beforeHeader : source + size ≤ base) :
    ∀ index < size, final.world.physicalByte (source + index) = initial.world.physicalByte (source + index) := by
  have same := StmtOutcome.continue.inj ((execute oracle fields initial base pointer bounded).symm.trans executed)
  intro index inside
  rw [← same]
  rw [writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inl (by omega)),
    writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inr (by omega))]

def prefixBytes : ByteArray := ⟨#[0x60, 0x0b, 0x38, 0x03, 0x80, 0x60, 0x0b, 0x5f, 0x39, 0x5f, 0xf3]⟩

/-- Fixed eleven-byte word certificate, independent of any interpreter run. -/
theorem word_prefix : ∀ index : Fin 11,
    UInt8.ofNat ((valueWord (Verity.Core.Uint256.ofNat word)) ⟨index.val, by omega⟩).val =
      prefixBytes[index.val]! := by decide

/-- Actual header bytes come from executed code, not a desired input buffer. -/
theorem header_byte (oracle : DenoteOracle) (fields : List Field)
    (initial final : DenoteState) (base : Nat)
    (pointer : (initial.world.memory 64).val = base) (bounded : base + 32 ≤ 2^64 - 1)
    (executed : execStmtList oracle fields initial segment = .continue final) (index : Fin 11) :
    UInt8.ofNat (final.world.physicalByte (base + index.val)).val = prefixBytes[index.val]! := by
  have same := StmtOutcome.continue.inj ((execute oracle fields initial base pointer bounded).symm.trans executed)
  rw [← same]
  rw [writePhysicalMemoryValue_byte_at _ base _ ⟨index.val, by omega⟩]
  exact word_prefix index

end Contracts.SolidityImportSmoke.ImportedCreationHeaderAllocation

