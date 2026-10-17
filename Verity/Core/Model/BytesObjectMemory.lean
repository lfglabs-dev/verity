import Verity.Core.Model.InitCodeExecution

/-!
Byte-level representation for an immutable Solidity memory bytes object.
This is a representation bridge, not an importer rule or an allocation/gas
equivalence assertion. Callers must establish the source object's base address,
allocation bounds and scope before using it. Numeric pointer observations are
not justified by a representation relation alone.
-/

namespace Compiler.CompilationModel.BytesObjectMemory

open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.InitCodeExecution

/-- Big-endian length word; admission must additionally check length < 2^256. -/
def lengthWord (length : Nat) : Word :=
  fun index => ⟨length / 256^(31 - index.val) % 256, Nat.mod_lt _ (by decide)⟩

def paddedLength (length : Nat) : Nat := expandedLength length

/-- Initialize the header, logical payload and zero padding. This operation
does not choose a Solidity allocator or modify the free-memory-pointer word. -/
def materialize (memory : Memory) (base : Nat) (payload : List Byte) : Memory :=
  (memory.writeWord base (lengthWord payload.length)).copyFrom
    (listByte payload) (base + 32) 0 (paddedLength payload.length)

/-- A descriptor relates only the header and the logical payload; padding is
proved separately and no unrestricted pointer expression follows from it. -/
def Represents (memory : Memory) (base : Nat) (payload : List Byte) : Prop :=
  memory.readWord base = lengthWord payload.length ∧
  ∀ index : Fin payload.length,
    memory.readByte (base + 32 + index.val) = listByte payload index.val

theorem writeWord_readByte_at (memory : Memory) (base : Nat) (word : Word)
    (index : Fin 32) :
    (memory.writeWord base word).readByte (base + index.val) = word index := by
  have bound : base + 32 ≤ (memory.writeWord base word).size :=
    Nat.le_trans (expandedLength_ge _) (Nat.le_max_right _ _)
  have inside : base + index.val < (memory.writeWord base word).size := by
    have := index.isLt
    omega
  rw [Memory.readByte, if_pos inside]
  exact Memory.writeWord_at memory base word index

theorem writeWord_readByte_outside (memory : Memory) (base : Nat) (word : Word)
    (address : Nat) (outside : address < base ∨ base + 32 ≤ address) :
    (memory.writeWord base word).readByte address = memory.readByte address := by
  have notInside : ¬ (base ≤ address ∧ address < base + 32) := by omega
  have grows : memory.size ≤ (memory.writeWord base word).size := Nat.le_max_left _ _
  by_cases inside : address < (memory.writeWord base word).size
  · rw [Memory.readByte, if_pos inside]
    simp only [Memory.writeWord, dif_neg notInside]
  · have oldOutside : ¬ address < memory.size := by omega
    rw [Memory.readByte, if_neg inside, Memory.readByte, if_neg oldOutside]

theorem materialize_header (memory : Memory) (base : Nat) (payload : List Byte) :
    (materialize memory base payload).readWord base = lengthWord payload.length := by
  funext index
  change (materialize memory base payload).readByte (base + index.val) = _
  unfold materialize
  rw [copyFrom_readByte_outside _ _ _ _ _ _ (Or.inl (by have := index.isLt; omega))]
  exact writeWord_readByte_at memory base (lengthWord payload.length) index

theorem materialize_payload (memory : Memory) (base : Nat) (payload : List Byte)
    (index : Fin payload.length) :
    (materialize memory base payload).readByte (base + 32 + index.val) =
      listByte payload index.val := by
  have paddingBound : payload.length ≤ paddedLength payload.length := expandedLength_ge _
  have bound : index.val < paddedLength payload.length := by have := index.isLt; omega
  simpa only [materialize, Nat.zero_add] using
    copyFrom_readByte_at (memory.writeWord base (lengthWord payload.length))
      (listByte payload) (base + 32) 0 (paddedLength payload.length) ⟨index.val, bound⟩

theorem materialize_padding (memory : Memory) (base : Nat) (payload : List Byte)
    (index : Fin (paddedLength payload.length)) (outside : payload.length ≤ index.val) :
    (materialize memory base payload).readByte (base + 32 + index.val) = zeroByte := by
  have copied := copyFrom_readByte_at (memory.writeWord base (lengthWord payload.length))
    (listByte payload) (base + 32) 0 (paddedLength payload.length) index
  simpa [materialize, listByte, List.getD, List.getElem?_eq_none (by omega)] using copied

theorem materialize_represents (memory : Memory) (base : Nat) (payload : List Byte) :
    Represents (materialize memory base payload) base payload :=
  ⟨materialize_header memory base payload, materialize_payload memory base payload⟩

theorem materialize_outside (memory : Memory) (base : Nat) (payload : List Byte)
    (address : Nat)
    (outside : address < base ∨ base + 32 + paddedLength payload.length ≤ address) :
    (materialize memory base payload).readByte address = memory.readByte address := by
  unfold materialize
  rw [copyFrom_readByte_outside _ _ _ _ _ _ (by omega)]
  exact writeWord_readByte_outside memory base (lengthWord payload.length) address (by omega)

/-- A later disjoint allocation preserves both the header and payload of an
earlier object. This applies to aliases of the same earlier descriptor too. -/
theorem materialize_preserves_before (memory : Memory) (base nextBase : Nat)
    (payload nextPayload : List Byte)
    (represented : Represents memory base payload)
    (disjoint : base + 32 + payload.length ≤ nextBase) :
    Represents (materialize memory nextBase nextPayload) base payload := by
  constructor
  · funext index
    change (materialize memory nextBase nextPayload).readByte (base + index.val) = _
    rw [materialize_outside _ _ _ _ (Or.inl (by have := index.isLt; omega))]
    exact congrFun represented.1 index
  · intro index
    rw [materialize_outside _ _ _ _ (Or.inl (by have := index.isLt; omega))]
    exact represented.2 index

end Compiler.CompilationModel.BytesObjectMemory
