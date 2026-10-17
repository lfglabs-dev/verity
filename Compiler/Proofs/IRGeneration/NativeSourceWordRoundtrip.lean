import Compiler.Proofs.IRGeneration.NativeSourcePointerBytes
import Compiler.Proofs.IRGeneration.NativeCreate2DigestBytes

namespace Compiler.Proofs.IRGeneration.NativeSourceWordRoundtrip
open EvmYul

theorem fixed_decode (x count : Nat) (bounded : x < 256 ^ count) :
    fromBytes' (toLeBytesFixed x count) = x := by
  induction count generalizing x with
  | zero =>
    have zero : x = 0 := by simpa using bounded
    subst x
    rfl
  | succ count ih =>
    have highBound : x / 256 < 256 ^ count := by
      rw [pow_succ] at bounded
      omega
    simp only [toLeBytesFixed, fromBytes']
    change (UInt8.ofNat (x % 256)).toNat + 256 * fromBytes' (toLeBytesFixed (x / 256) count) = x
    rw [UInt8.toNat_ofNat', Nat.mod_mod]
    rw [ih (x / 256) highBound]
    omega

theorem word_decode (value : UInt256) :
    fromByteArrayBigEndian value.toByteArray = value.toNat := by
  change fromBytes' value.toByteArray.toList.reverse = _
  rw [NativeMidnightConstructor.native_bytes_list, UInt256.toList_data_toByteArray]
  unfold toBeBytesFixed
  rw [List.reverse_reverse]
  exact fixed_decode value.toNat 32 value.val.isLt

theorem word_roundtrip (value : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian value.toByteArray) = value := by
  rw [word_decode]
  apply congrArg UInt256.mk
  apply Fin.ext
  exact Nat.mod_eq_of_lt value.val.isLt

theorem lookup_of_bytes (machine : MachineState) (address value : UInt256)
    (carrier : address.toNat < machine.memory.size)
    (active : ¬address ≥ machine.activeWords * ⟨32⟩)
    (bytes : machine.memory.readWithPadding address.toNat 32 = value.toByteArray) :
    machine.lookupMemory address = value := by
  unfold MachineState.lookupMemory
  rw [if_neg (not_or_intro (by omega) active), bytes, word_roundtrip]

end Compiler.Proofs.IRGeneration.NativeSourceWordRoundtrip

