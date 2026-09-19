/-!
# Solidity arithmetic panic codes

The typed panic domain is intentionally limited to the arithmetic codes emitted
by checked arithmetic. Other panic sources continue to use their raw numeric
code paths.
-/

namespace Verity.Core

/-- Solidity panic codes emitted by checked arithmetic. -/
inductive PanicCode where
  | arithmeticOverflow
  | divisionByZero
  deriving Repr

/-- The numeric code stored in Solidity's `Panic(uint256)` ABI payload. -/
def PanicCode.toNat : PanicCode → Nat
  | .arithmeticOverflow => 0x11
  | .divisionByZero => 0x12

@[simp] theorem PanicCode.toNat_arithmeticOverflow :
    PanicCode.arithmeticOverflow.toNat = 0x11 := rfl

@[simp] theorem PanicCode.toNat_divisionByZero :
    PanicCode.divisionByZero.toNat = 0x12 := rfl

end Verity.Core
