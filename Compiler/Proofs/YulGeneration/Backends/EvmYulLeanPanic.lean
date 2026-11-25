import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeCalldata
import Verity.Core.Panic
import Verity.Core.RevertPayload

namespace Compiler.Proofs.YulGeneration.Backends.Panic

/-- Solidity's panic selector followed by the ABI-encoded panic code. -/
def expectedPanicBytes (code : EvmYul.UInt256) : ByteArray :=
  (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ : ByteArray) ++ code.toByteArray

theorem expectedPanicBytes_size (code : EvmYul.UInt256) :
    (expectedPanicBytes code).size = 36 := by
  simp only [expectedPanicBytes, ByteArray.size_append, Native.uint256_toByteArray_size]
  rfl

private theorem byteArray_append_zeroes_zero (source : ByteArray) :
    source ++ ffi.ByteArray.zeroes ⟨0⟩ = source := by
  apply ByteArray.ext
  simp [ByteArray.data_append, ffi.ByteArray.zeroes]

private theorem byteArray_write_full (source dest : ByteArray) (offset : Nat)
    (hSource : 0 < source.size) (hOffset : offset ≤ dest.size) :
    source.write 0 dest offset source.size =
      dest.extract 0 offset ++ source ++ dest.extract (offset + source.size) dest.size := by
  unfold ByteArray.write
  have hZero : source.size ≠ 0 := by omega
  have hAddr : ¬ 0 ≥ source.size := by omega
  have hPadding : min dest.size (offset + source.size) - (offset + source.size) = 0 := by omega
  have hDestPadding : offset - dest.size = 0 := by omega
  simp only [hZero, hAddr, ↓reduceIte, Nat.sub_zero, Nat.min_self, hPadding,
    hDestPadding, Nat.add_zero]
  apply ByteArray.ext
  simp [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    ffi.ByteArray.zeroes, -ByteArray.size_data, ByteArray.size]

private theorem byteArray_readWithPadding_prefix (source suffix : ByteArray)
    (hPositive : 0 < source.size) (hSmall : source.size < 2 ^ 64) :
    (source ++ suffix).readWithPadding 0 source.size = source := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  have hLen : ¬ source.size ≥ 2 ^ 64 := by omega
  have hAddr : ¬ 0 ≥ (source ++ suffix).size := by
    simp only [ByteArray.size_append]
    omega
  rw [if_neg hLen, if_neg hAddr]
  simp only [ByteArray.size_append, Nat.min_eq_left (Nat.le_add_right _ _), Nat.zero_add]
  have hExtract : (source ++ suffix).extract 0 source.size = source := by
    apply ByteArray.ext
    simp [ByteArray.data_extract, ByteArray.data_append, -ByteArray.size_data, ByteArray.size]
  rw [hExtract]
  simpa using byteArray_append_zeroes_zero source

private theorem selectorWord_prefix :
    (EvmYul.UInt256.ofNat (0x4e487b71 * 2 ^ 224)).toByteArray.extract 0 4 =
      (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ : ByteArray) := by
  have hBytes : BE (EvmYul.UInt256.ofNat (0x4e487b71 * 2 ^ 224)).toNat =
      (⟨#[0x4e, 0x48, 0x7b, 0x71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
          0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) := by
    decide +kernel
  simp only [EvmYul.UInt256.toByteArray, hBytes]
  simp [ffi.ByteArray.zeroes, ByteArray.size, -ByteArray.size_data]
  rfl

/-- The two generated panic stores and the 36-byte revert return the complete
ABI payload, independently of the initial byte-addressed memory. -/
theorem machineState_panicPayload_bytes
    (state : EvmYul.MachineState) (code : EvmYul.UInt256) :
    (((state.mstore (.ofNat 0) (.ofNat (0x4e487b71 * 2 ^ 224))).mstore
        (.ofNat 4) code).evmRevert (.ofNat 0) (.ofNat 36)).H_return =
      expectedPanicBytes code := by
  let selector := (EvmYul.UInt256.ofNat (0x4e487b71 * 2 ^ 224)).toByteArray
  have hSelector : selector.size = 32 := Native.uint256_toByteArray_size _
  have hCode : code.toByteArray.size = 32 := Native.uint256_toByteArray_size _
  let first := selector.write 0 state.memory 0 32
  have hFirst : first = selector ++ state.memory.extract 32 state.memory.size := by
    dsimp [first]
    rw [← hSelector, byteArray_write_full selector state.memory 0 (by omega) (by omega)]
    simp [hSelector]
  have hFirstSize : 32 ≤ first.size := by
    rw [hFirst, ByteArray.size_append, hSelector]
    omega
  have hPrefix : first.extract 0 4 = (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ : ByteArray) := by
    rw [hFirst]
    have hExtract : (selector ++ state.memory.extract 32 state.memory.size).extract 0 4 =
        selector.extract 0 4 := by
      apply ByteArray.ext
      simp [ByteArray.data_extract, ByteArray.data_append, -ByteArray.size_data,
        ByteArray.size] at hSelector ⊢
      simp [hSelector]
    rw [hExtract]
    exact selectorWord_prefix
  change (code.toByteArray.write 0 first 4 32).readWithPadding 0 36 = _
  rw [← hCode, byteArray_write_full code.toByteArray first 4 (by omega) (by omega)]
  rw [hPrefix]
  change (expectedPanicBytes code ++ first.extract (4 + code.toByteArray.size) first.size).readWithPadding 0 36 = _
  rw [← expectedPanicBytes_size code]
  apply byteArray_readWithPadding_prefix
  · rw [expectedPanicBytes_size]; omega
  · rw [expectedPanicBytes_size]; norm_num

/-- The native revert result contains exactly the 4-byte selector and 32-byte code. -/
theorem machineState_panicPayload_size
    (state : EvmYul.MachineState) (code : EvmYul.UInt256) :
    (((state.mstore (.ofNat 0) (.ofNat (0x4e487b71 * 2 ^ 224))).mstore
        (.ofNat 4) code).evmRevert (.ofNat 0) (.ofNat 36)).H_return.size = 36 := by
  rw [machineState_panicPayload_bytes, expectedPanicBytes_size]

/-- `UInt256.ofNat` keeps the value modulo `2^256`. -/
private theorem uint256_toNat_ofNat (n : Nat) :
    (EvmYul.UInt256.ofNat n).toNat = n % EvmYul.UInt256.size := by
  simp only [EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, BitVec.toNat_ofNat]

/-- Reducing modulo `2^256` keeps every base-256 digit below the 32nd. -/
private theorem mod_size_digit (n k : Nat) (hk : k < 32) :
    n % EvmYul.UInt256.size / 256 ^ k % 256 = n / 256 ^ k % 256 := by
  have hsize : EvmYul.UInt256.size = 256 ^ k * 256 ^ (32 - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk.le]; rfl
  rw [hsize, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (by omega))]

/-- An ABI word is EVMYulLean's 32-byte big-endian encoding of the value
modulo `2^256`. -/
theorem word_eq_toByteArray (n : Nat) :
    Verity.Core.RevertPayload.word n =
      (EvmYul.UInt256.ofNat n).toByteArray.data.toList := by
  rw [EvmYul.UInt256.toList_data_toByteArray, uint256_toNat_ofNat]
  apply List.ext_getElem (by simp [Verity.Core.RevertPayload.word,
    Verity.Core.RevertPayload.bytesBE])
  intro i h1 h2
  have hi : i < 32 := by simpa using h2
  simp only [Verity.Core.RevertPayload.word, Verity.Core.RevertPayload.bytesBE,
    List.getElem_map, List.getElem_range, EvmYul.getElem_toBeBytesFixed]
  rw [mod_size_digit _ _ (by omega), pow_mul]
  apply UInt8.toNat_inj.mp
  simp

/-- The source-level panic payload and EVMYulLean's native panic bytes agree
for every panic code, including a computed one (`Stmt.panicCode`). -/
theorem encode_panic_eq_expectedPanicBytes (code : Nat) :
    Verity.Core.RevertPayload.encode (.panic code) =
      (expectedPanicBytes (.ofNat code)).data.toList := by
  rw [Verity.Core.RevertPayload.encode_panic, word_eq_toByteArray, expectedPanicBytes,
    ByteArray.toList_data_append]
  rfl

end Compiler.Proofs.YulGeneration.Backends.Panic
