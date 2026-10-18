import Init.Data.List.OfFn
import Verity.Core.Uint256

/-! Byte-memory data and pure operations, factored below ContractState so that
canonical execution can own its physical memory without importing Denote.
The historical namespace is retained to preserve existing theorem statements
and clients; this module has no model, compiler or external-call dependency. -/
namespace Compiler.CompilationModel.DenoteMemory

abbrev Byte := Fin 256
abbrev Word := Fin 32 → Byte

def zeroByte : Byte := ⟨0, by decide⟩

/-- Runtime EVM memory. `size` is the expanded byte length and is always
intended to be a multiple of 32; `bytes` is total to expose zero-filled reads
without partial indexing. -/
structure Memory where
  bytes : Nat → Byte
  size : Nat

/-- Zero-extended read of a finite byte list. -/
def listByte (bytes : List Byte) (offset : Nat) : Byte :=
  bytes.getD offset zeroByte

def Memory.empty : Memory :=
  { bytes := fun _ => zeroByte, size := 0 }

instance : Nonempty Memory := ⟨Memory.empty⟩

def expandedLength (endOffset : Nat) : Nat :=
  if endOffset = 0 then 0 else 32 * ((endOffset + 31) / 32)

def Memory.readByte (memory : Memory) (offset : Nat) : Byte :=
  if offset < memory.size then memory.bytes offset else zeroByte


def Memory.expand (memory : Memory) (endOffset : Nat) : Memory :=
  { bytes := memory.readByte, size := Nat.max memory.size (expandedLength endOffset) }


def Memory.writeByte (memory : Memory) (offset : Nat) (value : Byte) : Memory :=
  let expanded := memory.expand (offset + 1)
  { expanded with bytes := fun address => if address = offset then value else memory.readByte address }

/-- The `size` bytes starting at `offset`, zero-extended. -/
def Memory.slice (memory : Memory) (offset size : Nat) : List Byte :=
  (List.range size).map (fun index => memory.readByte (offset + index))

def Memory.readWord (memory : Memory) (offset : Nat) : Word :=
  fun index => memory.readByte (offset + index)

def Memory.writeWord (memory : Memory) (offset : Nat) (value : Word) : Memory :=
  let expanded := memory.expand (offset + 32)
  { expanded with
    bytes := fun address =>
      if h : offset ≤ address ∧ address < offset + 32 then
        value ⟨address - offset, by omega⟩
      else
        memory.readByte address }

def Memory.copyFrom (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) : Memory :=
  if size = 0 then memory else
    let expanded := memory.expand (destOffset + size)
    { expanded with
      bytes := fun address =>
        if _h : destOffset ≤ address ∧ address < destOffset + size then
          source (sourceOffset + (address - destOffset))
        else
          memory.readByte address }

@[simp] theorem Memory.copyFrom_zero (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset : Nat) :
    memory.copyFrom source destOffset sourceOffset 0 = memory := rfl

theorem Memory.expand_readByte_active (memory : Memory) (endOffset address : Nat)
    (active : address < memory.size) :
    (memory.expand endOffset).readByte address = memory.readByte address := by
  have inside : address < (memory.expand endOffset).size :=
    Nat.lt_of_lt_of_le active (Nat.le_max_left _ _)
  rw [Memory.readByte, if_pos inside]
  rfl

theorem Memory.expand_readByte_fresh (memory : Memory) (endOffset address : Nat)
    (fresh : memory.size ≤ address) :
    (memory.expand endOffset).readByte address = zeroByte := by
  have outside : ¬ address < memory.size := by omega
  by_cases inside : address < (memory.expand endOffset).size
  · rw [Memory.readByte, if_pos inside]
    change memory.readByte address = zeroByte
    simp only [Memory.readByte, outside, if_false]
  · simp only [Memory.readByte, inside, if_false]

theorem expandedLength_aligned (endOffset : Nat) :
    expandedLength endOffset % 32 = 0 := by
  by_cases h : endOffset = 0
  · simp [expandedLength, h]
  · simp [expandedLength, h]

theorem Memory.expand_size_ge (memory : Memory) (endOffset : Nat) :
    memory.size ≤ (memory.expand endOffset).size := by
  exact Nat.le_max_left _ _

theorem Memory.writeByte_at (memory : Memory) (offset : Nat) (value : Byte) :
    (memory.writeByte offset value).bytes offset = value := by
  simp [Memory.writeByte]

theorem Memory.readByte_writeByte_outside (memory : Memory) (offset : Nat)
    (value : Byte) (address : Nat) (outside : address ≠ offset) :
    (memory.writeByte offset value).readByte address = memory.readByte address := by
  have expanded := Memory.expand_size_ge memory (offset + 1)
  simp [Memory.writeByte, Memory.readByte, outside]
  omega

theorem Memory.readWord_writeByte_outside (memory : Memory) (offset : Nat)
    (value : Byte) (query : Nat) (disjoint : query + 32 ≤ offset ∨ offset + 1 ≤ query) :
    (memory.writeByte offset value).readWord query = memory.readWord query := by
  funext index
  apply Memory.readByte_writeByte_outside
  have bound := index.isLt
  omega

theorem Memory.writeWord_at (memory : Memory) (offset : Nat) (value : Word)
    (index : Fin 32) :
    (memory.writeWord offset value).bytes (offset + index) = value index := by
  simp only [Memory.writeWord]
  split
  · congr
    omega
  · rename_i h
    exact False.elim (h ⟨by omega, by omega⟩)

theorem Memory.copyFrom_at (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) (index : Fin size) :
    (memory.copyFrom source destOffset sourceOffset size).bytes (destOffset + index) =
      source (sourceOffset + index) := by
  have nonzero : size ≠ 0 := by have := index.isLt; omega
  simp only [Memory.copyFrom, nonzero, if_false]
  split
  · congr
    omega
  · rename_i h
    exact False.elim (h ⟨by omega, by omega⟩)

/-- A fixed-width big-endian word, normalized to the EVM word type. -/
def wordValue (word : Word) : Verity.Core.Uint256 :=
  Verity.Core.Uint256.ofNat ((List.ofFn word).foldl (fun acc byte => acc * 256 + byte.val) 0)

/-- Big-endian bytes of an already bounded EVM word. -/
def valueWord (value : Verity.Core.Uint256) : Word :=
  fun index => ⟨value.val / 256^(31 - index.val) % 256, Nat.mod_lt _ (by decide)⟩

theorem expandedLength_covers (endOffset : Nat) : endOffset ≤ expandedLength endOffset := by
  by_cases h : endOffset = 0
  · simp [expandedLength, h]
  · simp only [expandedLength, h, if_false]
    omega

theorem Memory.readByte_writeWord_at (memory : Memory) (offset : Nat) (word : Word)
    (index : Fin 32) :
    (memory.writeWord offset word).readByte (offset + index.val) = word index := by
  have bound : offset + 32 ≤ (memory.writeWord offset word).size :=
    Nat.le_trans (expandedLength_covers _) (Nat.le_max_right _ _)
  have inside : offset + index.val < (memory.writeWord offset word).size := by
    have := index.isLt
    omega
  rw [Memory.readByte, if_pos inside]
  exact Memory.writeWord_at memory offset word index

theorem Memory.readWord_writeWord_at (memory : Memory) (offset : Nat) (word : Word) :
    (memory.writeWord offset word).readWord offset = word := by
  funext index
  exact Memory.readByte_writeWord_at memory offset word index

theorem Memory.readByte_writeWord_outside (memory : Memory) (offset : Nat) (word : Word)
    (address : Nat) (outside : address < offset ∨ offset + 32 ≤ address) :
    (memory.writeWord offset word).readByte address = memory.readByte address := by
  have notInside : ¬ (offset ≤ address ∧ address < offset + 32) := by omega
  have grows : memory.size ≤ (memory.writeWord offset word).size := Nat.le_max_left _ _
  by_cases inside : address < (memory.writeWord offset word).size
  · rw [Memory.readByte, if_pos inside]
    simp only [Memory.writeWord, dif_neg notInside]
  · have oldOutside : ¬ address < memory.size := by omega
    rw [Memory.readByte, if_neg inside, Memory.readByte, if_neg oldOutside]

theorem Memory.readWord_writeWord_outside (memory : Memory) (offset : Nat) (word : Word)
    (query : Nat) (disjoint : query + 32 ≤ offset ∨ offset + 32 ≤ query) :
    (memory.writeWord offset word).readWord query = memory.readWord query := by
  funext index
  exact Memory.readByte_writeWord_outside memory offset word (query + index.val)
    (by have := index.isLt; omega)

end Compiler.CompilationModel.DenoteMemory
