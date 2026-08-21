import Compiler.Constants

namespace Compiler.Proofs.YulGeneration

open Compiler.Constants

def selectorWord (selector : Nat) : Nat :=
  (selector % selectorModulus) * (2 ^ selectorShift)

def calldataloadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset = 0 then
    selectorWord selector
  else if offset < 4 then
    0
  else
    -- EVM-faithful byte-addressed read. The `calldata : List Nat` is the data
    -- region (starting at byte 4), each entry a 32-byte big-endian word. A read
    -- at byte `offset` returns the 32 bytes `[offset, offset+32)` of that region,
    -- big-endian, zero-padded past the end. Aligned reads (`r = 0`) reduce to the
    -- single word `calldata.getD q 0`, preserving the previous behaviour exactly.
    let p := offset - 4
    let q := p / 32
    let r := p % 32
    if r = 0 then
      calldata.getD q 0 % evmModulus
    else
      let hi := calldata.getD q 0 % evmModulus
      let lo := calldata.getD (q + 1) 0 % evmModulus
      ((hi % (2 ^ (8 * (32 - r)))) * (2 ^ (8 * r)) + lo / (2 ^ (8 * (32 - r)))) % evmModulus

/-- Memory word offsets written by `calldatacopy dst src size` under the
word-addressed memory model used by the source semantics and the IR
interpreter: the `size / 32` aligned words `dst, dst + 32, …`. -/
def calldatacopyWritesAt (dst size offset : Nat) : Prop :=
  dst ≤ offset ∧ offset < dst + 32 * (size / 32) ∧ (offset - dst) % 32 = 0

instance (dst size offset : Nat) : Decidable (calldatacopyWritesAt dst size offset) := by
  unfold calldatacopyWritesAt; infer_instance

/-- Word-granular `calldatacopy(dst, src, size)` on an abstract word-addressed
memory. Each written word is the calldata word at the corresponding source
byte offset, so the result is expressible with `calldataloadWord` alone. -/
def calldatacopyMemory (selector : Nat) (calldata : List Nat)
    (dst src size : Nat) (memory : Nat → Nat) : Nat → Nat :=
  fun offset =>
    if calldatacopyWritesAt dst size offset then
      calldataloadWord selector calldata (src + (offset - dst))
    else memory offset

/-! ## Calldatacopy memory-readback helpers -/

private theorem calldatacopyWritesAt_of_index (dst size i : Nat)
    (hi : i < size / 32) :
    calldatacopyWritesAt dst size (dst + i * 32) := by
  unfold calldatacopyWritesAt
  exact ⟨by omega, by omega, by omega⟩

theorem calldatacopyMemory_at_index
    (selector : Nat) (calldata : List Nat)
    (dst src size : Nat) (mem : Nat → Nat) (i : Nat)
    (hi : i < size / 32) :
    calldatacopyMemory selector calldata dst src size mem (dst + i * 32) =
      calldataloadWord selector calldata (src + i * 32) := by
  simp only [calldatacopyMemory]
  rw [if_pos (calldatacopyWritesAt_of_index dst size i hi)]
  congr 1
  omega

theorem calldatacopyMemory_outside
    (selector : Nat) (calldata : List Nat)
    (dst src size : Nat) (mem : Nat → Nat) (offset : Nat)
    (h : ¬calldatacopyWritesAt dst size offset) :
    calldatacopyMemory selector calldata dst src size mem offset = mem offset := by
  simp [calldatacopyMemory, h]

end Compiler.Proofs.YulGeneration
