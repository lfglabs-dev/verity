import Compiler.Proofs.IRGeneration.NativeCreate2AddressEncoding

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model

private theorem native_toList_loop (bytes : ByteArray) (index : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bytes index acc = acc.reverse ++ bytes.data.toList.drop index := by
  induction index, acc using ByteArray.toList.loop.induct bytes with
  | case1 index acc active ih =>
    unfold ByteArray.toList.loop
    rw [if_pos active, ih]
    have activeList : index < bytes.data.toList.length := by
      simpa only [Array.length_toList] using (show index < bytes.data.size from active)
    conv_rhs => rw [List.drop_eq_getElem_cons activeList]
    have byte : bytes.get! index = bytes.data.toList[index]'activeList := by
      change bytes.data[index]! = bytes.data.toList[index]
      rw [getElem!_pos bytes.data index (show index < bytes.data.size from active)]
      rfl
    rw [byte]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  | case2 index acc inactive =>
    unfold ByteArray.toList.loop
    rw [if_neg inactive, List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using (show bytes.data.size ≤ index from Nat.le_of_not_lt inactive))]
    exact (List.append_nil _).symm

/-- Native ByteArray.toList really observes every packed byte in order. -/
theorem native_bytes_list (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  unfold ByteArray.toList
  rw [native_toList_loop]
  rfl

private theorem native_from_bytes_bound (bytes : List UInt8) :
    fromBytes' bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp only [fromBytes', List.length_nil, pow_zero]; omega
  | cons byte bytes ih =>
    have digit : byte.toNat < 256 := byte.toNat_lt_size
    simp only [fromBytes', List.length_cons, pow_succ]
    change byte.toNat + 256 * fromBytes' bytes < 256 ^ bytes.length * 256
    omega

/-- Fixed-width native encoding recovers the original little-endian bytes. -/
theorem native_fixed_bytes_roundtrip (bytes : List UInt8) :
    toLeBytesFixed (fromBytes' bytes) bytes.length = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    have digit : byte.toNat < 256 := byte.toNat_lt_size
    have low : (fromBytes' (byte :: bytes)) % 256 = byte.toNat := by
      change (byte.toNat + 256 * fromBytes' bytes) % 256 = byte.toNat
      omega
    have high : (fromBytes' (byte :: bytes)) / 256 = fromBytes' bytes := by
      change (byte.toNat + 256 * fromBytes' bytes) / 256 = fromBytes' bytes
      omega
    simp only [List.length_cons, toLeBytesFixed, low, high, ih, UInt8.ofNat_toNat]

/-- A complete 32-byte native digest survives decoding to a word and native
re-encoding, including leading zero bytes. -/
theorem native_digest_roundtrip (digest : ByteArray) (sized : digest.size = 32) :
    (UInt256.ofNat (fromByteArrayBigEndian digest)).toByteArray = digest := by
  have decoded : fromByteArrayBigEndian digest = fromBytes' digest.data.toList.reverse := by
    simp only [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp_apply, native_bytes_list]
  have length : digest.data.toList.reverse.length = 32 := by
    simpa only [List.length_reverse, Array.length_toList] using (show digest.data.size = 32 from sized)
  have bounded : fromByteArrayBigEndian digest < UInt256.size := by
    rw [decoded]
    have bound := native_from_bytes_bound digest.data.toList.reverse
    rw [length] at bound
    exact bound
  have value : (UInt256.ofNat (fromByteArrayBigEndian digest)).toNat = fromByteArrayBigEndian digest :=
    Nat.mod_eq_of_lt bounded
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [UInt256.toList_data_toByteArray, value, toBeBytesFixed, decoded]
  have reencoded := native_fixed_bytes_roundtrip digest.data.toList.reverse
  rw [length] at reencoded
  rw [reencoded, List.reverse_reverse]

/-- The actual 32-byte digest can enter the universally proved preimage
encoding directly; it is not replaced by a selected byte or predicted hash. -/
theorem native_digest_preimage (sender : AccountAddress) (salt : UInt256)
    (digest : ByteArray) (sized : digest.size = 32) :
    BE 255 ++ sender.toByteArray ++ salt.toByteArray ++ digest =
      ({ deployer := Verity.Core.Address.ofNat sender.val
         salt := Verity.Core.Uint256.ofNat salt.toNat
         initcodeHash := Verity.Core.Uint256.ofNat
           (UInt256.ofNat (fromByteArrayBigEndian digest)).toNat } : Create2.Preimage).bytes := by
  conv_lhs => rw [← native_digest_roundtrip digest sized]
  exact native_create2_preimage_encoding sender salt (UInt256.ofNat (fromByteArrayBigEndian digest))

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
