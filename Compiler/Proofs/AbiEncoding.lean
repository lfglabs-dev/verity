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
  | uintN _ => simpa [abiScalarNormalize] using hv
  | intN _ => simpa [abiScalarNormalize] using hv
  | bytesN _ => simpa [abiScalarNormalize] using hv
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
  | uintN _ => rfl
  | intN _ => rfl
  | bytesN _ => rfl
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
