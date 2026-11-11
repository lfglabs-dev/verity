import Compiler.Keccak.Sponge
import Verity.Core.Model.Constants

/-!
# Keccak-256 of a word-addressed memory slice

`keccak256(offset, size)` over Verity's word-addressed memory (`Nat → Nat`, one word per
byte offset written): the words at `offset, offset + 32, …` are serialized big-endian and
truncated to `size` bytes, then hashed with the in-tree Keccak.

These mirror `Compiler.Proofs.IRGeneration.{byteWordCount, memorySliceWords,
irWordToBytesBE, irMemorySliceBytesBE, abstractKeccakMemorySlice}` without the proof-IR
imports, so the EDSL (`Contracts.keccak256Live`) can use them. The bridge
`Compiler.Proofs.IRGeneration.abstractKeccakMemorySlice_eq_memorySlice` proves the two equal.
-/

namespace Compiler.Keccak.MemorySlice

/-- Number of 32-byte words covering `size` bytes. -/
def byteWordCount (size : Nat) : Nat :=
  (size + 31) / 32

/-- The words at `offset, offset + 32, …` covering `size` bytes (offsets wrap mod 2^256). -/
def words (memory : Nat → Nat) (offset size : Nat) : List Nat :=
  (List.range (byteWordCount size)).map
    (fun i => memory ((offset + i * 32) % Compiler.Constants.evmModulus))

/-- Big-endian 32-byte encoding of a word. -/
def wordToBytesBE (word : Nat) : ByteArray :=
  ⟨((List.range 32).map
    (fun index => UInt8.ofNat ((word / (256 ^ (31 - index))) % 256))).toArray⟩

/-- The exact `size`-byte slice starting at `offset`. -/
def bytesBE (memory : Nat → Nat) (offset size : Nat) : ByteArray :=
  let bytes := (words memory offset size).foldl
    (fun acc word => acc ++ wordToBytesBE word)
    ByteArray.empty
  bytes.extract 0 size

/-- `keccak256(offset, size)` as a 256-bit word. -/
def keccak (memory : Nat → Nat) (offset size : Nat) : Nat :=
  KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 (bytesBE memory offset size)) %
    Compiler.Constants.evmModulus

end Compiler.Keccak.MemorySlice
