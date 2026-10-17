import Compiler.Proofs.IRGeneration.NativeCreate2DigestBytes

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Keeping low little-endian bytes is exactly natural modular reduction. -/
theorem native_take_mod (bytes : List UInt8) (width : Nat) :
    fromBytes' (bytes.take width) = fromBytes' bytes % 256 ^ width := by
  induction width generalizing bytes with
  | zero => simp only [List.take_zero, fromBytes', pow_zero, Nat.mod_one]
  | succ width ih =>
    cases bytes with
    | nil => simp only [List.take_nil, fromBytes', Nat.zero_mod]
    | cons byte bytes =>
      have digit : byte.toNat < 256 := byte.toNat_lt_size
      have low : (byte.toNat + 256 * fromBytes' bytes) % 256 = byte.toNat := by omega
      have high : (byte.toNat + 256 * fromBytes' bytes) / 256 = fromBytes' bytes := by omega
      simp only [List.take_succ_cons, fromBytes']
      change byte.toNat + 256 * fromBytes' (bytes.take width) =
        (byte.toNat + 256 * fromBytes' bytes) % 256 ^ (width + 1)
      rw [ih, pow_succ', Nat.mod_mul, low, high]

/-- The native extraction of the low 160 bits is exactly reduction modulo
2^160 for every actual 32-byte digest, including leading zeros. -/
theorem native_digest_low160 (digest : ByteArray) (sized : digest.size = 32) :
    fromByteArrayBigEndian (digest.extract 12 32) = fromByteArrayBigEndian digest % AccountAddress.size := by
  simp only [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp_apply, native_bytes_list,
    ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  have length : digest.data.toList.length = 32 := by
    simpa only [Array.length_toList] using (show digest.data.size = 32 from sized)
  have suffix : (digest.data.toList.drop 12).take (32 - 12) = digest.data.toList.drop 12 := by
    apply List.take_of_length_le
    simp only [List.length_drop, length]
    exact Nat.le_refl _
  rw [suffix]
  have reversed : (digest.data.toList.drop 12).reverse = digest.data.toList.reverse.take 20 := by
    rw [List.take_reverse, length]
  rw [reversed, native_take_mod]
  rfl

/-- Actual native CREATE2 target truncation is low-160 reduction of its actual
outer hash. The opaque primitive's output size is explicit, not assumed globally. -/
theorem native_create2_target_mod (sender : AccountAddress) (salt init : ByteArray)
    (sized : (ffi.KEC (BE 255 ++ sender.toByteArray ++ salt ++ ffi.KEC init)).size = 32) :
    (nativeCreate2Target sender salt init).val =
      fromByteArrayBigEndian (ffi.KEC (BE 255 ++ sender.toByteArray ++ salt ++ ffi.KEC init)) % AccountAddress.size := by
  unfold nativeCreate2Target
  change fromByteArrayBigEndian ((ffi.KEC (BE 255 ++ sender.toByteArray ++ salt ++ ffi.KEC init)).extract 12 32) % AccountAddress.size = _
  rw [native_digest_low160 _ sized, Nat.mod_mod]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
