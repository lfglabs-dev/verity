/-
  Compiler.Constants: Shared EVM numeric constants

  Lightweight module with zero imports beyond the Lean prelude.
  Constants defined here are referenced by CompilationModel, Codegen, proofs,
  and the interpreter — centralising them avoids duplication and prevents
  silent divergence if a value is updated in one place but not another.
-/

namespace Compiler.Constants

/-- EVM word modulus: 2^256. -/
abbrev evmModulus : Nat := 2 ^ 256

/-- Selector modulus: function selectors are 4 bytes (2^32). -/
def selectorModulus : Nat := 2 ^ 32

/-- Selector shift: function selectors occupy the top 4 bytes of a 32-byte
    EVM word, so calldata word 0 is right-shifted by 224 bits to extract
    the selector, and error hashes are left-shifted by 224 bits to pack them. -/
def selectorShift : Nat := 224

/-- The 4-byte selector for `Error(string)` (keccak256("Error(string)")[0:4]),
    left-shifted to fill a 32-byte EVM word.  This is 0x08c379a0 << 224.
    Used in `revertWithMessage` (compiler) and concrete IR proofs. -/
def errorStringSelectorWord : Nat := 0x08c379a0 * (2 ^ 224)

/-- The 4-byte selector for Solidity's built-in `Panic(uint256)` error. -/
def panicSelector : Nat := 0x4e487b71

/-- The 4-byte selector for Solidity's built-in `Panic(uint256)` error,
    left-shifted to fill a 32-byte EVM word. -/
def panicSelectorWord : Nat := panicSelector * (2 ^ 224)

def wordByteBE (word : Nat) (idx : Nat) : UInt8 :=
  UInt8.ofNat ((word / (256 ^ (31 - idx))) % 256)

def wordBytesBE (word : Nat) : List UInt8 :=
  (List.range 32).map (wordByteBE word)

/-- Canonical ABI revert payload for Solidity's `Panic(uint256)`.
    The payload is `0x4e487b71 ++ abi.encode(code)`, exactly 36 bytes. -/
def solidityPanicRevertPayload (code : Nat) : ByteArray :=
  ByteArray.mk
    ([ UInt8.ofNat (panicSelector / 2^24 % 256)
     , UInt8.ofNat (panicSelector / 2^16 % 256)
     , UInt8.ofNat (panicSelector / 2^8 % 256)
     , UInt8.ofNat (panicSelector % 256)
     ] ++ wordBytesBE code).toArray

/-- 160-bit address mask used to normalize EVM addresses (bitwise AND).
    EVM addresses are 20 bytes; calldataload reads a full 32-byte word,
    so the upper 96 bits must be cleared. -/
def addressMask : Nat := (2 ^ 160) - 1

/-- 160-bit address modulus (2^160).
    Used by the interpreter to bound address values. -/
def addressModulus : Nat := 2 ^ 160

/-- Solidity free memory pointer address (0x40 = 64).
    By convention, `mload(0x40)` returns the next available memory offset.
    Used in custom error emission and event encoding to allocate scratch space. -/
def freeMemoryPointer : Nat := 0x40

end Compiler.Constants
