import TranslationValidationGuardedExecution
import TranslationValidationImported
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeCalldata

namespace SolidityTranslationValidation.AstBridge
open EvmYul Yul
open Compiler.Proofs.YulGeneration.Backends.Native

private theorem padding_size (n : Nat) (h : n ≤ 128) :
    (ffi.ByteArray.zeroes ⟨n⟩).size = n := by
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [USize.toNat_ofNat_of_lt]
  rcases System.Platform.numBits_eq with hbits | hbits
  all_goals simp [USize.size, hbits]; omega

private theorem write128_shape (source dest : ByteArray) (hs : source.size = 32) :
    (source.write 0 dest 128 32).data =
      (dest ++ ffi.ByteArray.zeroes ⟨(128 - dest.size : Nat)⟩).data.extract 0 128 ++ source.data ++
      (dest ++ ffi.ByteArray.zeroes ⟨(128 - dest.size : Nat)⟩).data.extract 160
        (dest ++ ffi.ByteArray.zeroes ⟨(128 - dest.size : Nat)⟩).data.size := by
  unfold ByteArray.write
  have hp : min dest.size (128 + 32) - (128 + min 32 (source.size - 0)) = 0 := by omega
  simp only [show ¬ 32 = 0 by decide, show ¬ 0 ≥ source.size by omega, ↓reduceIte, hp]
  have hz (a : ByteArray) : a ++ ffi.ByteArray.zeroes ⟨(0 : Nat)⟩ = a := by
    apply ByteArray.ext
    simp [ByteArray.data_append, ffi.ByteArray.zeroes]
  rw [hz]
  have hsd : source.data.size = 32 := hs
  have he : source.data.extract 0 32 = source.data := by rw [← hsd]; simp
  simp [ByteArray.data_copySlice, hsd, hs, he]

private theorem write128_extract (source dest : ByteArray) (hs : source.size = 32) :
    (source.write 0 dest 128 32).extract 128 160 = source := by
  have hp : 128 ≤ (dest ++ ffi.ByteArray.zeroes ⟨(128 - dest.size : Nat)⟩).data.size := by
    change 128 ≤ (dest ++ ffi.ByteArray.zeroes ⟨(128 - dest.size : Nat)⟩).size
    rw [ByteArray.size_append, padding_size _ (by omega)]
    omega
  apply ByteArray.ext
  rw [ByteArray.data_extract, write128_shape source dest hs]
  generalize (dest ++ ffi.ByteArray.zeroes ⟨(128 - dest.size : Nat)⟩).data = padded at hp ⊢
  simp [Array.extract_append, Array.size_extract, Nat.min_eq_left hp, show source.data.size = 32 from hs]

/-- A complete native word write at the captured pointer is returned exactly,
for arbitrary initial memory (including shorter and longer memory buffers). -/
theorem write128_return32 (source dest : ByteArray) (hs : source.size = 32) :
    (source.write 0 dest 128 32).readWithPadding 128 32 = source := by
  have he := write128_extract source dest hs
  have hsize : 160 ≤ (source.write 0 dest 128 32).size := by
    have h := congrArg ByteArray.size he
    simp only [ByteArray.size_extract, hs] at h
    omega
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp only [show ¬ 32 ≥ 2^64 by norm_num, show ¬ 128 ≥ (source.write 0 dest 128 32).size by omega,
    ↓reduceIte, show min 32 (source.write 0 dest 128 32).size = 32 by omega]
  rw [he, hs]
  apply ByteArray.ext
  simp [ByteArray.data_append, ffi.ByteArray.zeroes]

/-- The real captured body's successful final state's return buffer is the
big-endian 32-byte quotient word; no initial-memory restriction is required. -/
theorem successfulBodyState_bytes (shared : SharedState .Yul) (store : Yul.VarStore)
    (x y d : Nat) :
    (successfulBodyState shared store x y d).sharedState.H_return =
      (UInt256.ofNat (x * y / d)).toByteArray := by
  change ((shared.toMachineState.mstore (UInt256.ofNat 128) (UInt256.ofNat (x*y/d))).evmReturn
    (UInt256.ofNat 128) (UInt256.ofNat 32)).H_return = _
  simp only [MachineState.mstore, MachineState.writeWord, writeBytes, MachineState.evmReturn]
  exact write128_return32 _ _ (uint256_toByteArray_size _)

/-- Observe bytes only from the native successful RETURN status. This is not
an observation semantics for failure payloads, which the native exception lacks. -/
def nativeReturnBytes (result : Except Yul.Exception Yul.State) : Option ByteArray :=
  match result with
  | .error (.YulHalt state status) =>
      if status = UInt256.ofNat 1 then some state.sharedState.H_return else none
  | _ => none

/-- Exact successful returned bytes of the captured arithmetic-body slice agree
with the ABI word encoding of the actual solidity_import wrapper result.
The decoded input and memory-pointer premises remain dispatcher obligations. -/
theorem captured_body_bytes_match_imported
    (oracle : Compiler.CompilationModel.Denote.DenoteOracle) (world : Verity.ContractState)
    (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) (x y d : Verity.Core.Uint256)
    (hfit : x.val * y.val < Verity.Core.Uint256.modulus) (hdzero : d.val ≠ 0)
    (hX : variableValue (.Ok shared store) "value" = UInt256.ofNat x.val)
    (hY : variableValue (.Ok shared store) "value_1" = UInt256.ofNat y.val)
    (hD : variableValue (.Ok shared store) "value_2" = UInt256.ofNat d.val)
    (hPtr : variableValue (.Ok shared store) "_1" = UInt256.ofNat 128) :
    nativeReturnBytes (Yul.exec 100 capturedArithmeticBody code (.Ok shared store)) =
      (captured.mulDivDown oracle world x y d).map
        (fun word => (UInt256.ofNat word.val).toByteArray) := by
  rw [captured_arithmetic_body_success shared store code x.val y.val d.val
    x.isLt y.isLt d.isLt hfit hdzero hX hY hD hPtr]
  simp only [nativeReturnBytes, ↓reduceIte, successfulBodyState_bytes,
    captured_success oracle world x y d hfit hdzero, Option.map_some]
  have hquot : x.val * y.val / d.val < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hfit
  simp only [Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hquot]

#print axioms captured_body_bytes_match_imported
#print axioms write128_return32
#print axioms successfulBodyState_bytes
end SolidityTranslationValidation.AstBridge
