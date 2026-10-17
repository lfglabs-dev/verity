import Compiler.Proofs.IRGeneration.NativeCreate2MemorySlice

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model

/-- Canonical big-endian digits equal the native fixed-width encoding. -/
theorem fixed_bytes_eq_canonical (number width : Nat) :
    (⟨(toBeBytesFixed number width).toArray⟩ : ByteArray) = Create2.natBytesBE width number := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [List.size_toArray, length_toBeBytesFixed, Create2.natBytesBE, Array.size_ofFn]
  · intro index left right
    simp only [List.getElem_toArray, Create2.natBytesBE, Array.getElem_ofFn]
    rw [getElem_toBeBytesFixed]

/-- All 32 actual native salt bytes agree with the canonical word encoding. -/
theorem native_create2_salt_encoding (salt : UInt256) :
    salt.toByteArray = Create2.wordBytes (Verity.Core.Uint256.ofNat salt.toNat) := by
  have value : (Verity.Core.Uint256.ofNat salt.toNat).val = salt.toNat :=
    Nat.mod_eq_of_lt salt.val.isLt
  rw [Create2.wordBytes, value, ← fixed_bytes_eq_canonical]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [UInt256.toList_data_toByteArray, List.toList_toArray]

private theorem address_padding_count (count : Nat) (bounded : count ≤ 20) :
    ({ toBitVec := (20 : BitVec System.Platform.numBits) - (count : BitVec System.Platform.numBits) } : USize).toNat = 20 - count := by
  have wide : 20 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> omega
  have small : count < 2 ^ System.Platform.numBits := by omega
  have twenty : (20 : BitVec System.Platform.numBits).toNat = 20 := by
    change 20 % 2 ^ System.Platform.numBits = 20
    exact Nat.mod_eq_of_lt wide
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, twenty]
  rw [show 2 ^ System.Platform.numBits - count + 20 = 2 ^ System.Platform.numBits + (20 - count) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- Actual 20-byte native caller encoding equals canonical address encoding. -/
theorem native_create2_sender_encoding (sender : AccountAddress) :
    sender.toByteArray = Create2.addressBytes (Verity.Core.Address.ofNat sender.val) := by
  have bounded : sender.val < 256 ^ 20 := sender.isLt
  have padded := toBeBytesFixed_eq_zeroPad sender.val 20 bounded
  have length := congrArg List.length padded
  simp only [length_toBeBytesFixed, List.length_append, List.length_replicate] at length
  have short : (BE sender.val).size ≤ 20 := by
    rw [show (BE sender.val).size = (toBytesBigEndian sender.val).length from List.size_toByteArray]
    omega
  have value : (Verity.Core.Address.ofNat sender.val).toNat = sender.val := Nat.mod_eq_of_lt sender.isLt
  rw [Create2.addressBytes, value, ← fixed_bytes_eq_canonical]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  unfold AccountAddress.toByteArray
  rw [ByteArray.toList_data_append]
  have zeroes : ∀ u : USize, (ffi.ByteArray.zeroes u).data.toList = List.replicate u.toNat 0 := by
    intro u; simp only [ffi.ByteArray.zeroes, Array.toList_replicate]
  rw [zeroes, address_padding_count _ short]
  rw [show (BE sender.val).data.toList = toBytesBigEndian sender.val from List.toList_data_toByteArray]
  rw [show (BE sender.val).size = (toBytesBigEndian sender.val).length from List.size_toByteArray]
  exact padded.symm

/-- The native marker is exactly the canonical 0xff byte. -/
theorem native_create2_marker : BE 255 = Create2.marker := by cbv

/-- All 85 preimage bytes agree for native sender, salt and digest words.
This is a universal encoding theorem; no equality of hash engines is assumed. -/
theorem native_create2_preimage_encoding (sender : AccountAddress) (salt digest : UInt256) :
    BE 255 ++ sender.toByteArray ++ salt.toByteArray ++ digest.toByteArray =
      ({ deployer := Verity.Core.Address.ofNat sender.val
         salt := Verity.Core.Uint256.ofNat salt.toNat
         initcodeHash := Verity.Core.Uint256.ofNat digest.toNat } : Create2.Preimage).bytes := by
  rw [native_create2_marker, native_create2_sender_encoding, native_create2_salt_encoding salt,
    native_create2_salt_encoding digest]
  apply ByteArray.ext
  simp only [ByteArray.data_append, Create2.Preimage.bytes, CodeData.byteAppend]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
