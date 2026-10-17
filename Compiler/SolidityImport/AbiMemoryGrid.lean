import Verity.Core
import Compiler.SolidityImport.AbiByteLanes

namespace Compiler.CompilationModel.Denote

/-- Read a byte from the encoder's aligned word grid, in EVM big-endian order.
This observation is restricted to the aligned representation; it does not
assert that arbitrary overlapping Denote stores have byte-memory semantics. -/
def abiMemoryByte (memory : Nat → Verity.Core.Uint256) (address : Nat) : Nat :=
  (memory (address / 32 * 32)).val / 256^(31 - address % 32) % 256

/-- Mathematical memory update performed by the aligned byte-copy step.
The generated statement still needs an evaluation lemma connecting its shifts
and bindings to this update. -/
def abiInsertByte (memory : Nat → Verity.Core.Uint256) (address byte : Nat) :
    Nat → Verity.Core.Uint256 :=
  fun cell => if cell = address / 32 * 32 then
    Verity.Core.Uint256.ofNat (SolidityImport.AbiByteLanes.insert
      (memory cell).val byte (31 - address % 32)) else memory cell

theorem abiInsertByte_word (memory : Nat → Verity.Core.Uint256) (address byte : Nat)
    (empty : abiMemoryByte memory address = 0) (bounded : byte < 256) :
    (abiInsertByte memory address byte (address / 32 * 32)).val =
      SolidityImport.AbiByteLanes.insert (memory (address / 32 * 32)).val
        byte (31 - address % 32) := by
  have wordBound : (memory (address / 32 * 32)).val < 256^32 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      using (memory (address / 32 * 32)).isLt
  have laneBound : 31 - address % 32 < 32 := by omega
  simp only [abiInsertByte, if_pos rfl, Verity.Core.Uint256.val_ofNat]
  change _ % 256^32 = _
  exact SolidityImport.AbiByteLanes.insertion_modulus _ _ _ wordBound laneBound empty bounded

theorem abiInsertByte_read (memory : Nat → Verity.Core.Uint256) (address byte : Nat)
    (empty : abiMemoryByte memory address = 0) (bounded : byte < 256) :
    abiMemoryByte (abiInsertByte memory address byte) address = byte := by
  unfold abiMemoryByte
  rw [abiInsertByte_word memory address byte empty bounded]
  exact SolidityImport.AbiByteLanes.inserted_byte _ _ _ empty bounded

/-- Byte insertion preserves every other address, even within the same word. -/
theorem abiInsertByte_frame (memory : Nat → Verity.Core.Uint256) (address byte other : Nat)
    (empty : abiMemoryByte memory address = 0) (bounded : byte < 256)
    (different : other ≠ address) :
    abiMemoryByte (abiInsertByte memory address byte) other = abiMemoryByte memory other := by
  by_cases grid : other / 32 * 32 = address / 32 * 32
  · have lanes : 31 - other % 32 ≠ 31 - address % 32 := by
      have first := Nat.mod_lt other (by decide : 0 < 32)
      have second := Nat.mod_lt address (by decide : 0 < 32)
      omega
    unfold abiMemoryByte
    rw [grid, abiInsertByte_word memory address byte empty bounded]
    exact SolidityImport.AbiByteLanes.other_byte_preserved _ _ _ _ empty bounded lanes
  · simp [abiMemoryByte, abiInsertByte, grid]

/-- Exact prefix invariant: copied bytes equal the source snapshot, and every
other byte still equals the initial memory. -/
def AbiCopyPrefix (initial memory : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination count : Nat) : Prop :=
  ∀ address, abiMemoryByte memory address =
    if destination ≤ address ∧ address < destination + count then
      bytes (address - destination) else abiMemoryByte initial address

theorem abiCopyPrefix_zero (initial : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination : Nat) :
    AbiCopyPrefix initial initial bytes destination 0 := by
  intro address
  simp only [Nat.add_zero]
  rw [if_neg (by omega)]

theorem abiCopyPrefix_step (initial memory : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination count : Nat)
    (copied : AbiCopyPrefix initial memory bytes destination count)
    (zero : abiMemoryByte initial (destination + count) = 0)
    (bounded : bytes count < 256) :
    AbiCopyPrefix initial (abiInsertByte memory (destination + count) (bytes count))
      bytes destination (count + 1) := by
  have empty : abiMemoryByte memory (destination + count) = 0 := by
    rw [copied, if_neg (by omega)]
    exact zero
  intro address
  by_cases current : address = destination + count
  · subst address
    rw [abiInsertByte_read memory _ _ empty bounded, if_pos (by omega)]
    simp
  · rw [abiInsertByte_frame memory _ _ address empty bounded current, copied]
    have same : (destination ≤ address ∧ address < destination + count) ↔
        (destination ≤ address ∧ address < destination + (count + 1)) := by omega
    simp only [same]

/-- Finite mathematical copy on the aligned representation. -/
def abiCopyBytes (initial : Nat → Verity.Core.Uint256) (bytes : Nat → Nat)
    (destination : Nat) : Nat → (Nat → Verity.Core.Uint256)
  | 0 => initial
  | count + 1 => abiInsertByte (abiCopyBytes initial bytes destination count)
      (destination + count) (bytes count)

/-- Exact bytes and the complete outside frame for any finite copied prefix.
This theorem concerns the mathematical update; generated-body equivalence
remains a separate obligation. -/
theorem abiCopyBytes_correct (initial : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination count : Nat)
    (zero : ∀ index, index < count → abiMemoryByte initial (destination + index) = 0)
    (bounded : ∀ index, index < count → bytes index < 256) :
    AbiCopyPrefix initial (abiCopyBytes initial bytes destination count) bytes destination count := by
  induction count with
  | zero => exact abiCopyPrefix_zero initial bytes destination
  | succ count ih =>
      exact abiCopyPrefix_step initial _ bytes destination count
        (ih (fun index inside => zero index (by omega))
          (fun index inside => bounded index (by omega)))
        (zero count (by omega)) (bounded count (by omega))


end Compiler.CompilationModel.Denote
