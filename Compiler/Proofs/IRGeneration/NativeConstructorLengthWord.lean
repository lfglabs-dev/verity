import Compiler.Proofs.IRGeneration.NativeMidnightConstructorData

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Native CODESIZE followed by SUB(11) yields the actual payload length.
The explicit code-size bound prevents UInt256 truncation. -/
theorem subtract_header_length (size : Nat) (bounded : 11 + size < UInt256.size) :
    UInt256.ofNat (11 + size) - UInt256.ofNat 11 = UInt256.ofNat size := by
  have eleven : 11 < UInt256.size := by omega
  have payload : size < UInt256.size := by omega
  apply congrArg UInt256.mk
  apply Fin.ext
  change (((UInt256.size - (11 % UInt256.size)) + ((11 + size) % UInt256.size)) %
    UInt256.size) = size % UInt256.size
  rw [Nat.mod_eq_of_lt eleven, Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt payload]
  rw [show UInt256.size - 11 + (11 + size) = UInt256.size + size from by omega]
  simp only [Nat.add_mod_left, Nat.mod_eq_of_lt payload]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
