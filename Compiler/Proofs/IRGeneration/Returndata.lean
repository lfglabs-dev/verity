import Compiler.Constants
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBuiltinSemantics

/-!
# Returndata readback helpers

Bounded `returndatacopy` on the abstract word-addressed memory shared by the
source semantics and the IR interpreter, mirroring the `calldatacopy` model in
`Compiler.Proofs.YulGeneration.Calldata` (reached here through the sanctioned
EvmYulLean bridge import, exactly like the interpreter's own calldata lane).

The EIP-211 returndata buffer is carried as `List Nat`, one entry per 32-byte
big-endian word (see `Verity.ContractState.returndata` and `IRState.returndata`).
`returndataloadWord` is the byte-addressed read: a read at byte `offset` returns
the 32 bytes `[offset, offset + 32)` of the buffer, big-endian, zero-padded past
the end. Unlike calldata there is no 4-byte selector prefix, so byte 0 of the
buffer is the high byte of word 0.

EVM `RETURNDATACOPY(dst, src, size)` exceptionally halts when `src + size`
exceeds `returndatasize()`. The in-bounds copy is modelled here; the callers
(`SourceSemantics.execStmt`, `Denote.execStmt`, and the IR interpreter) guard
the extent with `src + size ≤ 32 * buffer.length` and observe every
out-of-bounds extent as a reverting frame, identically on all layers.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.Constants

/-- Byte-addressed word read from the EIP-211 returndata buffer. Aligned reads
(`offset % 32 = 0`) reduce to the single word `returndata.getD (offset / 32)`;
unaligned reads splice the high bytes of word `q` with the low bytes of word
`q + 1`, exactly as `calldataloadWord` does for the calldata region. Reads past
the end of the buffer are zero-extended. -/
def returndataloadWord (returndata : List Nat) (offset : Nat) : Nat :=
  let q := offset / 32
  let r := offset % 32
  if r = 0 then
    returndata.getD q 0 % evmModulus
  else
    let hi := returndata.getD q 0 % evmModulus
    let lo := returndata.getD (q + 1) 0 % evmModulus
    ((hi % (2 ^ (8 * (32 - r)))) * (2 ^ (8 * r)) + lo / (2 ^ (8 * (32 - r)))) % evmModulus

/-- Word-granular `returndatacopy(dst, src, size)` on an abstract
word-addressed memory: the destination region is the same
`Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst size` word range used by the calldata lane, and each
written word is the buffer word at the corresponding source byte offset. The
in-bounds extent guard (`src + size ≤ 32 * returndata.length`) is supplied by
the callers, matching EVM's exceptional halt on out-of-bounds copies. -/
def returndatacopyMemory (returndata : List Nat)
    (dst src size : Nat) (memory : Nat → Nat) : Nat → Nat :=
  fun offset =>
    if Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst size offset then
      returndataloadWord returndata (src + (offset - dst))
    else memory offset

/-! ## Readback characterizations -/

theorem returndatacopyWritesAt_of_index (dst size i : Nat)
    (hi : i < size / 32) :
    Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst size (dst + i * 32) := by
  unfold Compiler.Proofs.YulGeneration.calldatacopyWritesAt
  exact ⟨by omega, by omega, by omega⟩

theorem returndatacopyMemory_at_index
    (returndata : List Nat)
    (dst src size : Nat) (mem : Nat → Nat) (i : Nat)
    (hi : i < size / 32) :
    returndatacopyMemory returndata dst src size mem (dst + i * 32) =
      returndataloadWord returndata (src + i * 32) := by
  simp only [returndatacopyMemory]
  rw [if_pos (returndatacopyWritesAt_of_index dst size i hi)]
  congr 1
  omega

theorem returndatacopyMemory_outside
    (returndata : List Nat)
    (dst src size : Nat) (mem : Nat → Nat) (offset : Nat)
    (h : ¬Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst size offset) :
    returndatacopyMemory returndata dst src size mem offset = mem offset := by
  simp [returndatacopyMemory, h]

/-- The zero-extent copy leaves memory untouched: it writes nothing whatever
the destination offset is, which keeps the historic admitted fragment
`returndataCopy dst 0 0` behaving identically under the bounded-copy
semantics. -/
@[simp] theorem returndatacopyMemory_zero (returndata : List Nat) (dst src : Nat)
    (mem : Nat → Nat) :
    returndatacopyMemory returndata dst src 0 mem = mem := by
  funext offset
  have h : ¬Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst 0 offset := by
    intro hw
    obtain ⟨_, h2, _⟩ := hw
    simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero] at h2
    omega
  simp [returndatacopyMemory, h]

/-- Aligned read: word `offset / 32` of the buffer, normalized. -/
theorem returndataloadWord_aligned (returndata : List Nat) (offset : Nat)
    (h : offset % 32 = 0) :
    returndataloadWord returndata offset =
      returndata.getD (offset / 32) 0 % evmModulus := by
  simp [returndataloadWord, h]

/-- Aligned read of a word-aligned buffer entry below the modulus: the copy is
the identity on already-normalized words. -/
theorem returndataloadWord_aligned_of_lt (returndata : List Nat) (q : Nat)
    (hmod : returndata.getD q 0 < evmModulus) :
    returndataloadWord returndata (q * 32) = returndata.getD q 0 := by
  rw [returndataloadWord_aligned returndata (q * 32) (by omega)]
  have hq : q * 32 / 32 = q := by omega
  rw [hq, Nat.mod_eq_of_lt hmod]

/-- Reads past the end of an empty buffer are zero. -/
@[simp] theorem returndataloadWord_nil (offset : Nat) :
    returndataloadWord [] offset = 0 := by
  simp [returndataloadWord]

/-- Every word the copy writes is already below the EVM modulus, so wrapping
through `Uint256.ofNat` is the identity on the copied region. This is the
returndata analogue of the private
`FunctionBody.calldataloadWord_lt_evmModulus`. -/
theorem returndataloadWord_lt_evmModulus (returndata : List Nat) (offset : Nat) :
    returndataloadWord returndata offset < evmModulus := by
  simp only [returndataloadWord]
  split <;> exact Nat.mod_lt _ (by decide)

end Compiler.Proofs.IRGeneration
