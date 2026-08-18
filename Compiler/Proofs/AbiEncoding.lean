import Compiler.CompilationModel.AbiEncoding
import Compiler.Proofs.IRGeneration.IRInterpreter

/-!
# ABI scalar encoding correctness

This module provides the shared scalar-normalization library for issue #2082.
It characterizes the real Yul-expression encoders, rather than introducing a
parallel word-level encoder:

* `Compiler.CompilationModel.encodeStaticCustomErrorArg`, used by typed
  revert payload bridges for `requireError`/`revertError`.
* `Compiler.CompilationModel.normalizeEventWord`, used by the scalar event data
  bridge in `Compiler/Proofs/IRGeneration/GenericInduction/EventBridge.lean`.
* Future return-values memory-layout proofs that need the same scalar word
  normalization facts.
-/

namespace Compiler.Proofs.AbiEncoding

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration

/-- Nat-level ABI scalar normalization matched to the real Yul expression
encoders under `evalIRExpr`. Full-word scalar encoders are expression
passthroughs, so the spec is identity for `uint256`, `int256`, and `bytes32`. -/
def abiScalarNormalize : ParamType → Nat → Nat
  | .uint8, v => (v % Compiler.Constants.evmModulus) &&& 255
  | .uint16, v => (v % Compiler.Constants.evmModulus) &&& 65535
  | .uintN bits, v => (v % Compiler.Constants.evmModulus) &&& (2 ^ bits - 1)
  | .intN bits, v =>
      (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (bits / 8 - 1))
        (Verity.Core.Uint256.ofNat v)).val
  | .bytesN bytes, v =>
      (v % Compiler.Constants.evmModulus) &&&
        ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))
  | .address, v => (v % Compiler.Constants.evmModulus) &&& Compiler.Constants.addressMask
  | .bool, v => if v % Compiler.Constants.evmModulus = 0 then 0 else 1
  | .newtypeOf _ baseType, v => abiScalarNormalize baseType v
  | _, v => v

@[simp] theorem abiScalarNormalize_uint256 (v : Nat) :
    abiScalarNormalize ParamType.uint256 v = v := rfl

@[simp] theorem abiScalarNormalize_int256 (v : Nat) :
    abiScalarNormalize ParamType.int256 v = v := rfl

@[simp] theorem abiScalarNormalize_bytes32 (v : Nat) :
    abiScalarNormalize ParamType.bytes32 v = v := rfl

@[simp] theorem abiScalarNormalize_uint8 (v : Nat) :
    abiScalarNormalize ParamType.uint8 v =
      ((v % Compiler.Constants.evmModulus) &&& 255) := rfl

@[simp] theorem abiScalarNormalize_uint16 (v : Nat) :
    abiScalarNormalize ParamType.uint16 v =
      ((v % Compiler.Constants.evmModulus) &&& 65535) := rfl

@[simp] theorem abiScalarNormalize_address (v : Nat) :
    abiScalarNormalize ParamType.address v =
      ((v % Compiler.Constants.evmModulus) &&& Compiler.Constants.addressMask) := rfl

@[simp] theorem abiScalarNormalize_bool (v : Nat) :
    abiScalarNormalize ParamType.bool v =
      (if v % Compiler.Constants.evmModulus = 0 then 0 else 1) := rfl

@[simp] theorem abiScalarNormalize_newtypeOf (name : String) (baseType : ParamType) (v : Nat) :
    abiScalarNormalize (ParamType.newtypeOf name baseType) v =
      abiScalarNormalize baseType v := rfl

/-- The ABI head word for one scalar argument.  Every scalar in this fragment
occupies one 32-byte ABI head slot; the word value is its ABI normalization.

This deliberately exposes words rather than a byte list: the Yul backend's
`mstore` observable is word-addressed, and the bridge lemmas below establish
that its stored words are precisely these heads. -/
def abiEncodeScalarHead (ty : ParamType) (value : Nat) : Nat :=
  abiScalarNormalize ty value

/-- ABI head encoding for a sequence of scalar arguments.  Keeping the type
tag paired with its value makes concatenation structural and avoids any
implicit positional convention at typed ABI boundaries. -/
def abiEncodeScalarHeads (args : List (ParamType × Nat)) : List Nat :=
  args.map (fun arg => abiEncodeScalarHead arg.1 arg.2)

@[simp] theorem abiEncodeScalarHead_uint256 (value : Nat) :
    abiEncodeScalarHead .uint256 value = value := rfl

/-- ABI addresses are left-zero-padded: only their low 160 bits occupy the
rightmost portion of the 256-bit head word. -/
@[simp] theorem abiEncodeScalarHead_address (value : Nat) :
    abiEncodeScalarHead .address value =
      ((value % Compiler.Constants.evmModulus) &&& Compiler.Constants.addressMask) := rfl

/-- ABI booleans are canonical full words, zero for false and one for true. -/
@[simp] theorem abiEncodeScalarHead_bool (value : Nat) :
    abiEncodeScalarHead .bool value =
      (if value % Compiler.Constants.evmModulus = 0 then 0 else 1) := rfl

/-- `bytes32` already fills a complete ABI head word, so it has no padding or
sign-extension transformation. -/
@[simp] theorem abiEncodeScalarHead_bytes32 (value : Nat) :
    abiEncodeScalarHead .bytes32 value = value := rfl

/-- Scalar ABI heads compose by concatenation, as required for the static
head portion of `abi.encode(a₁, …, aₙ)`. -/
theorem abiEncodeScalarHeads_append (left right : List (ParamType × Nat)) :
    abiEncodeScalarHeads (left ++ right) =
      abiEncodeScalarHeads left ++ abiEncodeScalarHeads right := by
  simp [abiEncodeScalarHeads]

private theorem lit_255_mod_evm :
    (255 : Nat) % Compiler.Constants.evmModulus = 255 :=
  Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])

private theorem lit_65535_mod_evm :
    (65535 : Nat) % Compiler.Constants.evmModulus = 65535 :=
  Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])

private theorem addressMask_mod_evm :
    Compiler.Constants.addressMask % Compiler.Constants.evmModulus =
      Compiler.Constants.addressMask :=
  Nat.mod_eq_of_lt
    (by norm_num [Compiler.Constants.addressMask, Compiler.Constants.evmModulus])

@[simp] theorem normalizeEventWord_uint8_eval (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord ParamType.uint8 e) =
      (evalIRExpr s e).map (abiScalarNormalize ParamType.uint8) := by
  cases he : evalIRExpr s e <;>
    simp [normalizeEventWord, abiScalarNormalize, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, he, lit_255_mod_evm]

@[simp] theorem normalizeEventWord_uint16_eval (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord ParamType.uint16 e) =
      (evalIRExpr s e).map (abiScalarNormalize ParamType.uint16) := by
  cases he : evalIRExpr s e <;>
    simp [normalizeEventWord, abiScalarNormalize, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, he, lit_65535_mod_evm]

@[simp] theorem normalizeEventWord_address_eval (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord ParamType.address e) =
      (evalIRExpr s e).map (abiScalarNormalize ParamType.address) := by
  cases he : evalIRExpr s e <;>
    simp [normalizeEventWord, abiScalarNormalize, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, he, addressMask_mod_evm]

@[simp] theorem normalizeEventWord_bool_eval (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord ParamType.bool e) =
      (evalIRExpr s e).map (abiScalarNormalize ParamType.bool) := by
  cases he : evalIRExpr s e with
  | none =>
      simp [normalizeEventWord, CompilationModel.yulToBool, evalIRExpr, evalIRCall,
        evalIRExprs, he]
  | some v =>
      by_cases hz : v % Compiler.Constants.evmModulus = 0
      · simp [normalizeEventWord, CompilationModel.yulToBool, abiScalarNormalize,
          evalIRExpr, evalIRCall, evalIRExprs,
          Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
          Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
          he, hz]
      · simp [normalizeEventWord, CompilationModel.yulToBool, abiScalarNormalize,
          evalIRExpr, evalIRCall, evalIRExprs,
          Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
          Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
          he, hz]

@[simp] theorem normalizeEventWord_uint256_eval (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord ParamType.uint256 e) =
      (evalIRExpr s e).map (abiScalarNormalize ParamType.uint256) := by
  simp [normalizeEventWord, abiScalarNormalize]

@[simp] theorem normalizeEventWord_int256_eval (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord ParamType.int256 e) =
      (evalIRExpr s e).map (abiScalarNormalize ParamType.int256) := by
  simp [normalizeEventWord, abiScalarNormalize]

@[simp] theorem normalizeEventWord_bytes32_eval (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord ParamType.bytes32 e) =
      (evalIRExpr s e).map (abiScalarNormalize ParamType.bytes32) := by
  simp [normalizeEventWord, abiScalarNormalize]

theorem normalizeEventWord_newtypeOf_eval
    (s : IRState) (e : YulExpr) (name : String) (baseType : ParamType)
    (hbase :
      evalIRExpr s (normalizeEventWord baseType e) =
        (evalIRExpr s e).map (abiScalarNormalize baseType)) :
    evalIRExpr s (normalizeEventWord (ParamType.newtypeOf name baseType) e) =
      (evalIRExpr s e).map (abiScalarNormalize (ParamType.newtypeOf name baseType)) := by
  simpa [normalizeEventWord, abiScalarNormalize] using hbase

@[simp] theorem encodeStaticCustomErrorArg_uint8_eval
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.uint8 e = .ok out) :
    evalIRExpr s out = (evalIRExpr s e).map (abiScalarNormalize ParamType.uint8) := by
  simp [encodeStaticCustomErrorArg] at hout
  cases hout
  exact normalizeEventWord_uint8_eval s e

@[simp] theorem encodeStaticCustomErrorArg_uint16_eval
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.uint16 e = .ok out) :
    evalIRExpr s out = (evalIRExpr s e).map (abiScalarNormalize ParamType.uint16) := by
  simp [encodeStaticCustomErrorArg] at hout
  cases hout
  exact normalizeEventWord_uint16_eval s e

@[simp] theorem encodeStaticCustomErrorArg_address_eval
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.address e = .ok out) :
    evalIRExpr s out = (evalIRExpr s e).map (abiScalarNormalize ParamType.address) := by
  simp [encodeStaticCustomErrorArg] at hout
  cases hout
  exact normalizeEventWord_address_eval s e

@[simp] theorem encodeStaticCustomErrorArg_bool_eval
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.bool e = .ok out) :
    evalIRExpr s out = (evalIRExpr s e).map (abiScalarNormalize ParamType.bool) := by
  simp [encodeStaticCustomErrorArg] at hout
  cases hout
  exact normalizeEventWord_bool_eval s e

@[simp] theorem encodeStaticCustomErrorArg_uint256_eval
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.uint256 e = .ok out) :
    evalIRExpr s out = (evalIRExpr s e).map (abiScalarNormalize ParamType.uint256) := by
  simp [encodeStaticCustomErrorArg] at hout
  cases hout
  simp [abiScalarNormalize]

@[simp] theorem encodeStaticCustomErrorArg_int256_eval
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.int256 e = .ok out) :
    evalIRExpr s out = (evalIRExpr s e).map (abiScalarNormalize ParamType.int256) := by
  simp [encodeStaticCustomErrorArg] at hout
  cases hout
  simp [abiScalarNormalize]

@[simp] theorem encodeStaticCustomErrorArg_bytes32_eval
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.bytes32 e = .ok out) :
    evalIRExpr s out = (evalIRExpr s e).map (abiScalarNormalize ParamType.bytes32) := by
  simp [encodeStaticCustomErrorArg] at hout
  cases hout
  simp [abiScalarNormalize]

theorem encodeStaticCustomErrorArg_eval_eq_normalizeEventWord_eval
    (name : String) (ty : ParamType) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ty e = .ok out)
    (hty : ty = ParamType.uint256 ∨ ty = ParamType.int256 ∨ ty = ParamType.uint8 ∨
      ty = ParamType.uint16 ∨ ty = ParamType.address ∨ ty = ParamType.bool ∨
      ty = ParamType.bytes32) :
    evalIRExpr s out = evalIRExpr s (normalizeEventWord ty e) := by
  rcases hty with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [encodeStaticCustomErrorArg_uint256_eval name s e out hout]
    simp
  · rw [encodeStaticCustomErrorArg_int256_eval name s e out hout]
    simp
  · rw [encodeStaticCustomErrorArg_uint8_eval name s e out hout]
    simp
  · rw [encodeStaticCustomErrorArg_uint16_eval name s e out hout]
    simp
  · rw [encodeStaticCustomErrorArg_address_eval name s e out hout]
    simp
  · rw [encodeStaticCustomErrorArg_bool_eval name s e out hout]
    simp
  · rw [encodeStaticCustomErrorArg_bytes32_eval name s e out hout]
    simp

theorem encodeStaticCustomErrorArg_agrees_with_normalizeEventWord_uint8
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.uint8 e = .ok out) :
    evalIRExpr s out = evalIRExpr s (normalizeEventWord ParamType.uint8 e) :=
  encodeStaticCustomErrorArg_eval_eq_normalizeEventWord_eval name ParamType.uint8 s e out hout
    (Or.inr (Or.inr (Or.inl rfl)))

theorem encodeStaticCustomErrorArg_agrees_with_normalizeEventWord_uint16
    (name : String) (s : IRState) (e out : YulExpr)
    (hout : encodeStaticCustomErrorArg name ParamType.uint16 e = .ok out) :
    evalIRExpr s out = evalIRExpr s (normalizeEventWord ParamType.uint16 e) :=
  encodeStaticCustomErrorArg_eval_eq_normalizeEventWord_eval name ParamType.uint16 s e out hout
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

@[simp] theorem encodeStaticCustomErrorArg_uintN_eq
    (name : String) (bits : Nat) (e : YulExpr) :
    encodeStaticCustomErrorArg name (.uintN bits) e =
      .ok (normalizeEventWord (.uintN bits) e) := by
  rfl

@[simp] theorem encodeStaticCustomErrorArg_intN_eq
    (name : String) (bits : Nat) (e : YulExpr) :
    encodeStaticCustomErrorArg name (.intN bits) e =
      .ok (normalizeEventWord (.intN bits) e) := by
  rfl

@[simp] theorem encodeStaticCustomErrorArg_bytesN_eq
    (name : String) (bytes : Nat) (e : YulExpr) :
    encodeStaticCustomErrorArg name (.bytesN bytes) e =
      .ok (normalizeEventWord (.bytesN bytes) e) := by
  rfl

theorem abiScalarNormalize_bool_output (v : Nat) :
    abiScalarNormalize ParamType.bool v = 0 ∨ abiScalarNormalize ParamType.bool v = 1 := by
  unfold abiScalarNormalize
  split <;> simp

theorem abiScalarNormalize_uint8_lt_evm (v : Nat) :
    abiScalarNormalize ParamType.uint8 v < Compiler.Constants.evmModulus := by
  simpa [abiScalarNormalize] using
    Nat.lt_trans (Nat.and_lt_two_pow (v % Compiler.Constants.evmModulus)
      (by norm_num : 255 < 2 ^ 8)) (by norm_num [Compiler.Constants.evmModulus])

theorem abiScalarNormalize_uint16_lt_evm (v : Nat) :
    abiScalarNormalize ParamType.uint16 v < Compiler.Constants.evmModulus := by
  simpa [abiScalarNormalize] using
    Nat.lt_trans (Nat.and_lt_two_pow (v % Compiler.Constants.evmModulus)
      (by norm_num : 65535 < 2 ^ 16)) (by norm_num [Compiler.Constants.evmModulus])

theorem abiScalarNormalize_address_lt_evm (v : Nat) :
    abiScalarNormalize ParamType.address v < Compiler.Constants.evmModulus := by
  simpa [abiScalarNormalize] using
    Nat.lt_trans
    (Nat.and_lt_two_pow (v % Compiler.Constants.evmModulus) (by norm_num [Compiler.Constants.addressMask] :
      Compiler.Constants.addressMask < 2 ^ 160))
    (by norm_num [Compiler.Constants.evmModulus])

theorem abiScalarNormalize_bool_lt_evm (v : Nat) :
    abiScalarNormalize ParamType.bool v < Compiler.Constants.evmModulus := by
  rcases abiScalarNormalize_bool_output v with h | h <;>
    simp [h, Compiler.Constants.evmModulus]

theorem abiScalarNormalize_lt_evm_of_lt_evm
    (ty : ParamType) {v : Nat} (hv : v < Compiler.Constants.evmModulus) :
    abiScalarNormalize ty v < Compiler.Constants.evmModulus := by
  cases ty with
  | uint256 => simpa using hv
  | int256 => simpa using hv
  | uint8 => exact abiScalarNormalize_uint8_lt_evm v
  | uint16 => exact abiScalarNormalize_uint16_lt_evm v
  | uintN bits =>
      exact lt_of_le_of_lt (Nat.and_le_left) (Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus]))
  | intN bits =>
      exact (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (bits / 8 - 1))
        (Verity.Core.Uint256.ofNat v)).isLt
  | bytesN bytes =>
      exact lt_of_le_of_lt (Nat.and_le_left) (Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus]))
  | address => exact abiScalarNormalize_address_lt_evm v
  | bool => exact abiScalarNormalize_bool_lt_evm v
  | bytes32 => simpa using hv
  | string => simpa [abiScalarNormalize] using hv
  | tuple elemTypes => simpa [abiScalarNormalize] using hv
  | array elemType => simpa [abiScalarNormalize] using hv
  | fixedArray elemType size => simpa [abiScalarNormalize] using hv
  | bytes => simpa [abiScalarNormalize] using hv
  | adt name maxFields => simpa [abiScalarNormalize] using hv
  | newtypeOf name baseType =>
      exact abiScalarNormalize_lt_evm_of_lt_evm baseType hv

theorem abiScalarNormalize_address_fixed {v : Nat} (hv : v < 2 ^ 160) :
    abiScalarNormalize ParamType.address v = v := by
  rw [abiScalarNormalize_address]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hv (by norm_num [Compiler.Constants.evmModulus]))]
  rw [show Compiler.Constants.addressMask = 2 ^ 160 - 1 by
    norm_num [Compiler.Constants.addressMask]]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hv

private theorem land_idempotent_right (v mask : Nat) :
    (v &&& mask) &&& mask = v &&& mask := by
  rw [Nat.land_assoc, Nat.and_self]

private theorem uint256_ofNat_val (value : Verity.Core.Uint256) :
    Verity.Core.Uint256.ofNat value.val = value := by
  apply Verity.Core.Uint256.ext
  exact Nat.mod_eq_of_lt value.isLt

private theorem uint256_signextend_idempotent
    (byteIdx value : Verity.Core.Uint256) :
    Verity.Core.Uint256.signextend byteIdx
        (Verity.Core.Uint256.signextend byteIdx value) =
      Verity.Core.Uint256.signextend byteIdx value := by
  unfold Verity.Core.Uint256.signextend
  by_cases hlarge : byteIdx.val ≥ 31
  · simp [hlarge]
  · by_cases hsign : value.val &&& 2 ^ (byteIdx.val * 8 + 7) = 0
    · have hbit : value.val.testBit (byteIdx.val * 8 + 7) = false := by
        rw [Nat.and_two_pow] at hsign
        cases h : value.val.testBit (byteIdx.val * 8 + 7) <;> simp_all
      have hmaskedLt : value.val % 2 ^ (byteIdx.val * 8 + 7 + 1) <
          Verity.Core.Uint256.modulus := by
        have hpow : 2 ^ (byteIdx.val * 8 + 7 + 1) < 2 ^ 256 := by
          apply Nat.pow_lt_pow_right (by omega)
          omega
        exact lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) (by simpa [Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS] using hpow)
      have hmaskedSign :
          value.val % 2 ^ (byteIdx.val * 8 + 7 + 1) &&&
              2 ^ (byteIdx.val * 8 + 7) = 0 := by
        rw [Nat.and_two_pow]
        simp [Nat.testBit_mod_two_pow, hbit]
      simp [hlarge, hsign, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt hmaskedLt, hmaskedSign]
    · have hbit : value.val.testBit (byteIdx.val * 8 + 7) = true := by
        rw [Nat.and_two_pow] at hsign
        cases h : value.val.testBit (byteIdx.val * 8 + 7) <;> simp_all
      let highMask := Verity.Core.Uint256.modulus - 1 -
        (2 ^ (byteIdx.val * 8 + 7 + 1) - 1)
      have hhighLt : highMask < 2 ^ 256 := by
        dsimp [highMask, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
        omega
      have horLt : value.val ||| highMask < Verity.Core.Uint256.modulus := by
        simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using
          Nat.or_lt_two_pow value.isLt hhighLt
      have horSign : (value.val ||| highMask) &&&
          2 ^ (byteIdx.val * 8 + 7) ≠ 0 := by
        rw [Nat.and_two_pow]
        simp [Nat.testBit_or, hbit]
      simp [hlarge, hsign, highMask, Nat.mod_eq_of_lt horLt, horSign,
        Nat.or_self_right]

@[simp] theorem abiScalarNormalize_uint8_idem (v : Nat) :
    abiScalarNormalize ParamType.uint8 (abiScalarNormalize ParamType.uint8 v) =
      abiScalarNormalize ParamType.uint8 v := by
  rw [abiScalarNormalize_uint8]
  rw [Nat.mod_eq_of_lt (abiScalarNormalize_uint8_lt_evm v)]
  rw [abiScalarNormalize_uint8]
  exact land_idempotent_right (v % Compiler.Constants.evmModulus) 255

@[simp] theorem abiScalarNormalize_uint16_idem (v : Nat) :
    abiScalarNormalize ParamType.uint16 (abiScalarNormalize ParamType.uint16 v) =
      abiScalarNormalize ParamType.uint16 v := by
  rw [abiScalarNormalize_uint16]
  rw [Nat.mod_eq_of_lt (abiScalarNormalize_uint16_lt_evm v)]
  rw [abiScalarNormalize_uint16]
  exact land_idempotent_right (v % Compiler.Constants.evmModulus) 65535

private theorem abiScalarNormalize_uintN_idem (bits v : Nat) :
    abiScalarNormalize (.uintN bits) (abiScalarNormalize (.uintN bits) v) =
      abiScalarNormalize (.uintN bits) v := by
  have hlt : (v % Compiler.Constants.evmModulus &&& (2 ^ bits - 1)) <
      Compiler.Constants.evmModulus :=
    lt_of_le_of_lt Nat.and_le_left
      (Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus]))
  simp only [abiScalarNormalize]
  rw [Nat.mod_eq_of_lt hlt]
  exact land_idempotent_right (v % Compiler.Constants.evmModulus) (2 ^ bits - 1)

private theorem abiScalarNormalize_intN_idem (bits v : Nat) :
    abiScalarNormalize (.intN bits) (abiScalarNormalize (.intN bits) v) =
      abiScalarNormalize (.intN bits) v := by
  simp only [abiScalarNormalize]
  rw [uint256_ofNat_val]
  exact congrArg Verity.Core.Uint256.val
    (uint256_signextend_idempotent
      (Verity.Core.Uint256.ofNat (bits / 8 - 1))
      (Verity.Core.Uint256.ofNat v))

private theorem abiScalarNormalize_bytesN_idem (bytes v : Nat) :
    abiScalarNormalize (.bytesN bytes) (abiScalarNormalize (.bytesN bytes) v) =
      abiScalarNormalize (.bytesN bytes) v := by
  have hlt : (v % Compiler.Constants.evmModulus &&&
      ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))) <
      Compiler.Constants.evmModulus :=
    lt_of_le_of_lt Nat.and_le_left
      (Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus]))
  simp only [abiScalarNormalize]
  rw [Nat.mod_eq_of_lt hlt]
  exact land_idempotent_right (v % Compiler.Constants.evmModulus)
    ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))

@[simp] theorem abiScalarNormalize_address_idem (v : Nat) :
    abiScalarNormalize ParamType.address (abiScalarNormalize ParamType.address v) =
      abiScalarNormalize ParamType.address v := by
  rw [abiScalarNormalize_address]
  rw [Nat.mod_eq_of_lt (abiScalarNormalize_address_lt_evm v)]
  rw [abiScalarNormalize_address]
  exact land_idempotent_right (v % Compiler.Constants.evmModulus) Compiler.Constants.addressMask

@[simp] theorem abiScalarNormalize_bool_idem (v : Nat) :
    abiScalarNormalize ParamType.bool (abiScalarNormalize ParamType.bool v) =
      abiScalarNormalize ParamType.bool v := by
  by_cases hz : v % Compiler.Constants.evmModulus = 0
  · simp [abiScalarNormalize, hz, Compiler.Constants.evmModulus]
  · simp [abiScalarNormalize, hz, Compiler.Constants.evmModulus]

theorem abiScalarNormalize_idempotent (ty : ParamType) (v : Nat) :
    abiScalarNormalize ty (abiScalarNormalize ty v) = abiScalarNormalize ty v := by
  cases ty with
  | uint256 => rfl
  | int256 => rfl
  | uint8 => exact abiScalarNormalize_uint8_idem v
  | uint16 => exact abiScalarNormalize_uint16_idem v
  | uintN bits => exact abiScalarNormalize_uintN_idem bits v
  | intN bits => exact abiScalarNormalize_intN_idem bits v
  | bytesN bytes => exact abiScalarNormalize_bytesN_idem bytes v
  | address => exact abiScalarNormalize_address_idem v
  | bool => exact abiScalarNormalize_bool_idem v
  | bytes32 => rfl
  | string => rfl
  | tuple elemTypes => rfl
  | array elemType => rfl
  | fixedArray elemType size => rfl
  | bytes => rfl
  | adt name maxFields => rfl
  | newtypeOf name baseType =>
      exact abiScalarNormalize_idempotent baseType v

def IsStaticScalarParamType : ParamType → Prop
  | .uint256 | .int256 | .uint8 | .uint16
  | .uintN _ | .intN _ | .bytesN _
  | .address | .bool | .bytes32 => True
  | .newtypeOf _ baseType => IsStaticScalarParamType baseType
  | _ => False

theorem eventHeadWordSize_static_scalar_eq_32
    {ty : ParamType} (h : IsStaticScalarParamType ty) :
    eventHeadWordSize ty = 32 := by
  cases ty with
  | uint256 => simp [eventHeadWordSize, paramHeadSize]
  | int256 => simp [eventHeadWordSize, paramHeadSize]
  | uint8 => simp [eventHeadWordSize, paramHeadSize]
  | uint16 => simp [eventHeadWordSize, paramHeadSize]
  | uintN _ => simp [eventHeadWordSize, paramHeadSize]
  | intN _ => simp [eventHeadWordSize, paramHeadSize]
  | bytesN _ => simp [eventHeadWordSize, paramHeadSize]
  | address => simp [eventHeadWordSize, paramHeadSize]
  | bool => simp [eventHeadWordSize, paramHeadSize]
  | bytes32 => simp [eventHeadWordSize, paramHeadSize]
  | string => cases h
  | tuple elemTypes => cases h
  | array elemType => cases h
  | fixedArray elemType size => cases h
  | bytes => cases h
  | adt name maxFields => cases h
  | newtypeOf name baseType =>
      simp [IsStaticScalarParamType] at h
      simpa [eventHeadWordSize, paramHeadSize] using
        eventHeadWordSize_static_scalar_eq_32 (ty := baseType) h

private theorem foldl_eventHeadWordSize_static_scalar_eq
    (tys : List ParamType) (acc : Nat)
    (h : ∀ ty ∈ tys, IsStaticScalarParamType ty) :
    tys.foldl (fun acc ty => acc + eventHeadWordSize ty) acc =
      acc + 32 * tys.length := by
  induction tys generalizing acc with
  | nil => simp
  | cons ty rest ih =>
      have hty : IsStaticScalarParamType ty := h ty (by simp)
      have hrest : ∀ restTy ∈ rest, IsStaticScalarParamType restTy := by
        intro restTy hmem
        exact h restTy (by simp [hmem])
      simp [eventHeadWordSize_static_scalar_eq_32 hty, ih (acc + 32) hrest]
      omega

theorem abiHeadSize_static_scalars_eq
    (tys : List ParamType)
    (h : ∀ ty ∈ tys, IsStaticScalarParamType ty) :
    abiHeadSize tys = 32 * tys.length := by
  simpa [abiHeadSize] using foldl_eventHeadWordSize_static_scalar_eq tys 0 h

/-! ## Dynamic ABI argument layout

The byte-level emit and revert encoders write words with `mstore`, so this
small specification deliberately uses ABI *words*.  `AbiBytes.dataWords` is
the already-packed, right-zero-padded sequence of data words for a byte
string; `AbiBytes.WellFormed` records the one fact a byte packer must supply.
This keeps the head/tail layout independent of a particular memory byte
packer, while making the ABI length word and every offset explicit.
-/

/-- A bytes value represented by its byte length and its packed ABI data
words.  The last word, when partial, is right-zero-padded by the producer. -/
structure AbiBytes where
  byteLength : Nat
  dataWords : List Nat

/-- Packed bytes occupy one word per (possibly partial) 32-byte chunk. -/
def AbiBytes.WellFormed (value : AbiBytes) : Prop :=
  value.dataWords.length = (value.byteLength + 31) / 32

/-- The dynamic argument fragment needed by #2082: bytes and arrays whose
elements are scalar ABI words.  A scalar array is the ABI dynamic-array case,
so its tail starts with the element count. -/
inductive AbiArg where
  | scalar (ty : ParamType) (value : Nat)
  | bytes (value : AbiBytes)
  | scalarArray (elementType : ParamType) (values : List Nat)

namespace AbiArg

def isDynamic : AbiArg → Bool
  | .scalar _ _ => false
  | .bytes _ | .scalarArray _ _ => true

/-- The tail of a dynamic argument.  Both supported dynamic forms have a
length word followed by ABI words. -/
def tail : AbiArg → List Nat
  | .scalar _ _ => []
  | .bytes value => value.byteLength :: value.dataWords
  | .scalarArray elementType values =>
      values.length :: values.map (abiScalarNormalize elementType)

def tailSize (arg : AbiArg) : Nat := arg.tail.length * 32

@[simp] theorem tail_scalar (ty : ParamType) (value : Nat) :
    (.scalar ty value : AbiArg).tail = [] := rfl

@[simp] theorem tail_bytes (value : AbiBytes) :
    (.bytes value : AbiArg).tail = value.byteLength :: value.dataWords := rfl

@[simp] theorem tail_scalarArray (elementType : ParamType) (values : List Nat) :
    (.scalarArray elementType values : AbiArg).tail =
      values.length :: values.map (abiScalarNormalize elementType) := rfl

theorem scalarArray_elements_lt_evm (elementType : ParamType) (values : List Nat)
    (hvalues : ∀ value ∈ values, value < Compiler.Constants.evmModulus) :
    ∀ word ∈ (.scalarArray elementType values : AbiArg).tail.tail,
      word < Compiler.Constants.evmModulus := by
  intro word hword
  simp only [tail_scalarArray, List.tail_cons] at hword
  rcases List.mem_map.1 hword with ⟨value, hvalue, rfl⟩
  exact abiScalarNormalize_lt_evm_of_lt_evm elementType (hvalues value hvalue)

end AbiArg

/-- Total size in bytes of the dynamic tails in argument order. -/
def abiDynamicTailSize (args : List AbiArg) : Nat :=
  (args.map AbiArg.tailSize).sum

/-- The head words for `args`, given the byte address at which their tails
begin.  Dynamic heads are offsets relative to the beginning of the argument
block, exactly as required by the ABI. -/
def abiEncodeArgHeads : List AbiArg → Nat → List Nat
  | [], _ => []
  | .scalar ty value :: rest, tailOffset =>
      abiEncodeScalarHead ty value :: abiEncodeArgHeads rest tailOffset
  | arg@(.bytes _) :: rest, tailOffset =>
      tailOffset :: abiEncodeArgHeads rest (tailOffset + arg.tailSize)
  | arg@(.scalarArray _ _) :: rest, tailOffset =>
      tailOffset :: abiEncodeArgHeads rest (tailOffset + arg.tailSize)

/-- ABI encoding of the complete argument block: all heads, followed by tails
in their original argument order. -/
def abiEncodeArgs (args : List AbiArg) : List Nat :=
  abiEncodeArgHeads args (32 * args.length) ++ args.flatMap AbiArg.tail

@[simp] theorem abiEncodeArgHeads_length (args : List AbiArg) (tailOffset : Nat) :
    (abiEncodeArgHeads args tailOffset).length = args.length := by
  induction args generalizing tailOffset with
  | nil => rfl
  | cons arg rest ih =>
      cases arg <;> simp [abiEncodeArgHeads, ih]

/-- Every argument contributes exactly one head word, including dynamic
arguments whose head is an offset. -/
theorem abiEncodeArgs_headSize (args : List AbiArg) :
    (abiEncodeArgHeads args (32 * args.length)).length * 32 = 32 * args.length := by
  rw [abiEncodeArgHeads_length, Nat.mul_comm]

/-- The byte offset of the tail belonging to the argument at `index`.  It is
the fixed head area plus the tails of earlier arguments. -/
def abiTailOffset (args : List AbiArg) (index : Nat) : Nat :=
  32 * args.length + abiDynamicTailSize (args.take index)

private theorem abiDynamicTailSize_cons (arg : AbiArg) (args : List AbiArg) :
    abiDynamicTailSize (arg :: args) = arg.tailSize + abiDynamicTailSize args := by
  simp [abiDynamicTailSize, AbiArg.tailSize, Nat.mul_add, Nat.add_mul]

/-- A dynamic head is the actual byte offset at which its tail starts.  The
induction also preserves tail order, because preceding tail sizes are added
left-to-right. -/
private theorem abiEncodeArgHeads_getElem?_dynamic
    (pre : List AbiArg) (arg : AbiArg) (suffix : List AbiArg)
    (hdynamic : arg.isDynamic = true) (tailOffset : Nat) :
    (abiEncodeArgHeads (pre ++ arg :: suffix) tailOffset)[pre.length]? =
      some (tailOffset + abiDynamicTailSize pre) := by
  induction pre generalizing tailOffset with
  | nil =>
      cases arg <;>
        simp [AbiArg.isDynamic, abiEncodeArgHeads, abiDynamicTailSize] at hdynamic ⊢
  | cons first rest ih =>
      cases first <;>
        simp only [List.cons_append, abiEncodeArgHeads, List.getElem?_cons_succ, ih,
          abiDynamicTailSize_cons, AbiArg.tailSize, AbiArg.tail_scalar, AbiArg.tail_bytes,
          AbiArg.tail_scalarArray, List.length_cons, List.length_nil, Nat.zero_mul,
          Option.some.injEq] <;>
        omega

theorem abiEncodeArgHeads_dynamic_offset
    (pre : List AbiArg) (arg : AbiArg) (suffix : List AbiArg)
    (hdynamic : arg.isDynamic = true) :
    (abiEncodeArgHeads (pre ++ arg :: suffix)
        (32 * (pre ++ arg :: suffix).length))[pre.length]? =
      some (abiTailOffset (pre ++ arg :: suffix) pre.length) := by
  rw [abiEncodeArgHeads_getElem?_dynamic pre arg suffix hdynamic]
  simp [abiTailOffset]

/-- The tail portion of an appended argument list composes by append. -/
theorem abiEncodeArgs_tails_append (left right : List AbiArg) :
    (left ++ right).flatMap AbiArg.tail =
      left.flatMap AbiArg.tail ++ right.flatMap AbiArg.tail := by
  simp

/-- Head composition for adjacent argument blocks.  The second block's
dynamic offsets are translated by the first block's tail size. -/
theorem abiEncodeArgHeads_append (left right : List AbiArg) (tailOffset : Nat) :
    abiEncodeArgHeads (left ++ right) tailOffset =
      abiEncodeArgHeads left tailOffset ++
        abiEncodeArgHeads right (tailOffset + abiDynamicTailSize left) := by
  induction left generalizing tailOffset with
  | nil => simp [abiEncodeArgHeads, abiDynamicTailSize]
  | cons arg rest ih =>
      cases arg <;>
        simp [abiEncodeArgHeads, abiDynamicTailSize_cons, AbiArg.tailSize, ih, Nat.add_assoc]

theorem abiEncodeArgs_append (left right : List AbiArg) :
    abiEncodeArgs (left ++ right) =
      abiEncodeArgHeads left (32 * (left.length + right.length)) ++
      abiEncodeArgHeads right (32 * (left.length + right.length) + abiDynamicTailSize left) ++
      left.flatMap AbiArg.tail ++ right.flatMap AbiArg.tail := by
  simp only [abiEncodeArgs, List.length_append, abiEncodeArgHeads_append,
    abiEncodeArgs_tails_append]
  ac_rfl

section Examples

private def exampleState : IRState :=
  (IRState.initial 0).setVar "x" 300

example :
    evalIRExpr exampleState (normalizeEventWord ParamType.uint8 (YulExpr.ident "x")) =
      some 44 := by
  have hx : evalIRExpr exampleState (YulExpr.ident "x") = some 300 := by
    simp [exampleState, evalIRExpr, IRState.initial, IRState.getVar, IRState.setVar]
  rw [normalizeEventWord_uint8_eval]
  simp [hx, abiScalarNormalize]
  decide

example :
    evalIRExpr exampleState (normalizeEventWord ParamType.bool (YulExpr.ident "x")) =
      some 1 := by
  have hx : evalIRExpr exampleState (YulExpr.ident "x") = some 300 := by
    simp [exampleState, evalIRExpr, IRState.initial, IRState.getVar, IRState.setVar]
  rw [normalizeEventWord_bool_eval]
  simp [hx, abiScalarNormalize]

example :
    evalIRExpr exampleState (normalizeEventWord ParamType.address (YulExpr.ident "x")) =
      some 300 := by
  have hx : evalIRExpr exampleState (YulExpr.ident "x") = some 300 := by
    simp [exampleState, evalIRExpr, IRState.initial, IRState.getVar, IRState.setVar]
  rw [normalizeEventWord_address_eval]
  simp [hx, abiScalarNormalize]
  decide

end Examples

end Compiler.Proofs.AbiEncoding
