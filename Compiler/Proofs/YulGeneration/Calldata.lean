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

end Compiler.Proofs.YulGeneration
