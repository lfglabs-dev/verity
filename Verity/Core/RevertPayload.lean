import Verity.Core.Panic

/-!
# Revert payloads

A revert carries returndata bytes. `RevertPayload` names the shapes Solidity
produces, and `RevertPayload.encode` gives their ABI bytes. Layers that observe
a revert compare encoded bytes, never constructors, so two payloads that
encode equally are the same observable.
-/

namespace Verity.Core

/-- The data a reverting call returns. -/
inductive RevertPayload where
  /-- `Error(string)`: `require(cond, msg)` and `revert(msg)`. -/
  | errorString (msg : String)
  /-- `Panic(uint256)`: checked arithmetic, failed `assert`, out-of-bounds access. -/
  | panic (code : Nat)
  /-- A custom error: 4-byte selector, then the ABI-encoded argument words. -/
  | custom (selector : Nat) (args : List Nat)
  /-- Bytes forwarded verbatim, such as a callee's returndata. -/
  | raw (bytes : List UInt8)
  /-- `revert()` with no data. -/
  | empty
  deriving Repr, DecidableEq

namespace RevertPayload

/-- Big-endian bytes of `n mod 2^(8*len)`, `len` bytes long. -/
def bytesBE (len n : Nat) : List UInt8 :=
  (List.range len).map fun i => UInt8.ofNat (n / 2 ^ (8 * (len - 1 - i)))

/-- One 32-byte ABI word: `n mod 2^256`, big-endian. -/
def word (n : Nat) : List UInt8 := bytesBE 32 n

/-- Right-pad `bytes` with zeros to a multiple of 32 bytes. -/
def padRight32 (bytes : List UInt8) : List UInt8 :=
  bytes ++ List.replicate ((32 - bytes.length % 32) % 32) 0

/-- Selector of `Error(string)`. -/
def errorStringSelector : Nat := 0x08c379a0

/-- Selector of `Panic(uint256)`. -/
def panicSelector : Nat := 0x4e487b71

/-- Solidity ABI bytes of a revert payload. -/
def encode : RevertPayload → List UInt8
  | .errorString msg =>
      let utf8 := msg.toUTF8.data.toList
      bytesBE 4 errorStringSelector ++ word 32 ++ word utf8.length ++ padRight32 utf8
  | .panic code => bytesBE 4 panicSelector ++ word code
  | .custom selector args => bytesBE 4 selector ++ (args.map word).flatten
  | .raw bytes => bytes
  | .empty => []

/-- A typed arithmetic panic. -/
def ofPanicCode (code : PanicCode) : RevertPayload := .panic code.toNat

@[simp] theorem length_bytesBE (len n : Nat) : (bytesBE len n).length = len := by
  simp [bytesBE]

@[simp] theorem length_word (n : Nat) : (word n).length = 32 := length_bytesBE 32 n

@[simp] theorem encode_empty : encode .empty = [] := rfl

@[simp] theorem encode_raw (bytes : List UInt8) : encode (.raw bytes) = bytes := rfl

theorem encode_panic (code : Nat) :
    encode (.panic code) = bytesBE 4 panicSelector ++ word code := rfl

@[simp] theorem length_encode_panic (code : Nat) : (encode (.panic code)).length = 36 := by
  simp [encode_panic]

@[simp] theorem length_encode_custom (selector : Nat) (args : List Nat) :
    (encode (.custom selector args)).length = 4 + 32 * args.length := by
  induction args with
  | nil => simp [encode]
  | cons a args ih =>
    simp only [encode, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons, length_bytesBE, length_word] at ih ⊢
    omega

/-- The first four bytes of a `Panic(uint256)` payload are its selector. -/
@[simp] theorem take_four_encode_panic (code : Nat) :
    (encode (.panic code)).take 4 = [0x4e, 0x48, 0x7b, 0x71] := by
  simp only [encode_panic]
  rw [List.take_left' (length_bytesBE 4 _)]
  rfl

/-- The first four bytes of an `Error(string)` payload are its selector. -/
@[simp] theorem take_four_encode_errorString (msg : String) :
    (encode (.errorString msg)).take 4 = [0x08, 0xc3, 0x79, 0xa0] := by
  simp only [encode, List.append_assoc]
  rw [List.take_left' (length_bytesBE 4 _)]
  rfl

/-- A panic is never observable as an `Error(string)`, whatever the message:
reverting with `Error("Panic(0x11)")` instead of `Panic(0x11)` changes the bytes. -/
theorem encode_panic_ne_errorString (code : Nat) (msg : String) :
    encode (.panic code) ≠ encode (.errorString msg) := by
  intro h
  have := congrArg (List.take 4) h
  simp at this

example : encode (ofPanicCode .arithmeticOverflow) =
    [0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x11] := by decide

example : encode (.panic 0x12) =
    [0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x12] := by decide

example : encode (.custom 0x3ee5aeb5 []) = [0x3e, 0xe5, 0xae, 0xb5] := by decide

/-! Reference bytes from `cast calldata "Error(string)" …` (Foundry). -/

/-- Exactly one data word: no padding. -/
example : encode (.errorString "Panic(0x11): arithmetic overflow") =
    [0x08, 0xc3, 0x79, 0xa0] ++ List.replicate 31 0 ++ [0x20] ++ List.replicate 31 0 ++ [0x20] ++
      [0x50, 0x61, 0x6e, 0x69, 0x63, 0x28, 0x30, 0x78, 0x31, 0x31, 0x29, 0x3a, 0x20, 0x61, 0x72,
        0x69, 0x74, 0x68, 0x6d, 0x65, 0x74, 0x69, 0x63, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x66, 0x6c,
        0x6f, 0x77] := by decide

/-- UTF-8 bytes, zero-padded to a word. -/
example : encode (.errorString "héllo") =
    [0x08, 0xc3, 0x79, 0xa0] ++ List.replicate 31 0 ++ [0x20] ++ List.replicate 31 0 ++ [0x06] ++
      [0x68, 0xc3, 0xa9, 0x6c, 0x6c, 0x6f] ++ List.replicate 26 0 := by decide

/-- The empty message has a length word and no data word. -/
example : encode (.errorString "") =
    [0x08, 0xc3, 0x79, 0xa0] ++ List.replicate 31 0 ++ [0x20] ++ List.replicate 32 0 := by decide

end RevertPayload

end Verity.Core
