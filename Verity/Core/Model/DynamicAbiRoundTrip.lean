import Verity.Core.Model.DynamicAbi

/-!
# Canonical-word round-trip for the supported ABI parameter decoder

First brick of the proved ABI-encoding library (Tier 3, #2082): a canonicity
predicate for ABI words and the theorem that `decodeSupportedParamWord`
recovers a canonical word *exactly* — so an encoder that emits canonical words
(the identity on already-in-range values, which is what solc's head encoding
does for static types) is provably inverted by the decoder used by the
parameter-loading semantics.  The list-level corollary shows
`bindSupportedParams` reconstructs precisely the intended name/value bindings
from canonically encoded arguments.

Signed (`intN`) canonicity is the sign-extension fixed point and `bytesN`
canonicity is the alignment-mask fixed point: exactly the words the decoder
returns unchanged, which is what a correct encoder must emit.
-/
namespace Compiler.CompilationModel.DynamicAbi

/-- A word is canonical for a parameter type when it is exactly the value the
ABI intends: in range for its width, with no dirty high bits for the decoder
to strip. -/
def CanonicalParamWord : ParamType → Nat → Prop
  | .uint256, v => v < Compiler.Constants.evmModulus
  | .int256, v => v < Compiler.Constants.evmModulus
  | .bytes32, v => v < Compiler.Constants.evmModulus
  | .uint8, v => v < 2 ^ 8
  | .uint16, v => v < 2 ^ 16
  | .uintN bits, v => v < 2 ^ bits ∧ v < Compiler.Constants.evmModulus
  | .address, v => v < 2 ^ 160
  | .bool, v => v = 0 ∨ v = 1
  | .intN bits, v =>
      (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (bits / 8 - 1))
        (Verity.Core.Uint256.ofNat v)).val = v ∧
      v < Compiler.Constants.evmModulus
  | .bytesN bytes, v =>
      v &&& ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))) = v ∧
      v < Compiler.Constants.evmModulus
  | _, _ => False

private theorem and_mask_eq_mod (n k : Nat) : n &&& (2 ^ k - 1) = n % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod n k

private theorem wordNormalize_eq_of_lt (v : Nat)
    (h : v < Compiler.Constants.evmModulus) : wordNormalize v = v := by
  show (Verity.Core.Uint256.ofNat v).val = v
  exact Nat.mod_eq_of_lt h

private theorem pow_le_evmModulus (k : Nat) (hk : k ≤ 256) :
    (2 : Nat) ^ k ≤ Compiler.Constants.evmModulus :=
  Nat.pow_le_pow_right (by decide) hk

private theorem decode_intN_canonical (bits v : Nat)
    (h : CanonicalParamWord (.intN bits) v) :
    decodeSupportedParamWord (.intN bits) v = some v := by
  obtain ⟨hfix, hmod⟩ := h
  simp [decodeSupportedParamWord, wordNormalize_eq_of_lt v hmod, hfix]

private theorem decode_bytesN_canonical (bytes v : Nat)
    (h : CanonicalParamWord (.bytesN bytes) v) :
    decodeSupportedParamWord (.bytesN bytes) v = some v := by
  obtain ⟨hfix, hmod⟩ := h
  simp [decodeSupportedParamWord, wordNormalize_eq_of_lt v hmod, hfix]

/-- The decoder is the identity on canonical words: no information is lost or
altered, so canonical encoding round-trips. -/
theorem decodeSupportedParamWord_canonical :
    ∀ (ty : ParamType) (v : Nat), CanonicalParamWord ty v →
      decodeSupportedParamWord ty v = some v
  | .uint256, v, h => by
      simp [decodeSupportedParamWord, wordNormalize_eq_of_lt v h]
  | .int256, v, h => by
      simp [decodeSupportedParamWord, wordNormalize_eq_of_lt v h]
  | .bytes32, v, h => by
      simp [decodeSupportedParamWord, wordNormalize_eq_of_lt v h]
  | .uint8, v, h => by
      have hlt : v < Compiler.Constants.evmModulus :=
        Nat.lt_of_lt_of_le h (pow_le_evmModulus 8 (by decide))
      have hmask := and_mask_eq_mod v 8
      simp only [decodeSupportedParamWord, uint8Modulus, wordNormalize_eq_of_lt v hlt]
      simpa [Nat.mod_eq_of_lt h] using hmask
  | .uint16, v, h => by
      have hlt : v < Compiler.Constants.evmModulus :=
        Nat.lt_of_lt_of_le h (pow_le_evmModulus 16 (by decide))
      have hmask := and_mask_eq_mod v 16
      simp only [decodeSupportedParamWord, wordNormalize_eq_of_lt v hlt]
      simpa [Nat.mod_eq_of_lt h] using hmask
  | .uintN bits, v, h => by
      obtain ⟨hbits, hmod⟩ := h
      simp [decodeSupportedParamWord, wordNormalize_eq_of_lt v hmod,
        and_mask_eq_mod, Nat.mod_eq_of_lt hbits]
  | .address, v, h => by
      have hlt : v < Compiler.Constants.evmModulus :=
        Nat.lt_of_lt_of_le h (pow_le_evmModulus 160 (by decide))
      have hmask := and_mask_eq_mod v 160
      simp only [decodeSupportedParamWord, Compiler.Constants.addressMask,
        wordNormalize_eq_of_lt v hlt]
      simpa [Nat.mod_eq_of_lt h] using hmask
  | .bool, v, h => by
      rcases h with h | h <;> subst h
      · simp [decodeSupportedParamWord, wordNormalize_eq_of_lt 0 (by decide)]
      · simp [decodeSupportedParamWord, wordNormalize_eq_of_lt 1 (by decide)]
  | .intN bits, v, h => decode_intN_canonical bits v h
  | .bytesN bytes, v, h => decode_bytesN_canonical bytes v h
  | .string, _, h => h.elim
  | .tuple _, _, h => h.elim
  | .array _, _, h => h.elim
  | .fixedArray _ _, _, h => h.elim
  | .bytes, _, h => h.elim
  | .adt _ _, _, h => h.elim
  | .newtypeOf _ _, _, h => h.elim

/-- Every `bytesN` word the decoder produces is canonical: the alignment mask
is idempotent, so decode-of-decode is stable and the canonicity predicate
characterizes exactly the decoder's image. -/
theorem decode_bytesN_output_canonical (bytes : Nat) (v w : Nat)
    (h : decodeSupportedParamWord (.bytesN bytes) v = some w) :
    CanonicalParamWord (.bytesN bytes) w := by
  have hw : w = wordNormalize v &&& ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))) := by
    simpa [decodeSupportedParamWord] using h.symm
  constructor
  · rw [hw, Nat.and_assoc, Nat.and_self]
  · calc w ≤ wordNormalize v := by rw [hw]; exact Nat.and_le_left
      _ < Compiler.Constants.evmModulus := by
          show (Verity.Core.Uint256.ofNat v).val < _
          exact (Verity.Core.Uint256.ofNat v).isLt

/-- Pointwise canonicity of an argument list for a parameter list (also forces
equal lengths). -/
inductive CanonicalArgs : List Param → List Nat → Prop
  | nil : CanonicalArgs [] []
  | cons {p : Param} {ps : List Param} {a : Nat} {as : List Nat} :
      CanonicalParamWord p.ty a → CanonicalArgs ps as →
      CanonicalArgs (p :: ps) (a :: as)

/-- List-level round-trip: canonically encoded arguments bind to exactly the
intended name/value pairs. -/
theorem bindSupportedParams_canonical :
    ∀ {params : List Param} {args : List Nat}, CanonicalArgs params args →
      bindSupportedParams params args =
        some (List.zipWith (fun (p : Param) a => (p.name, a)) params args)
  | [], _, _ => by simp [bindSupportedParams]
  | _ :: _, [], h => by cases h
  | param :: rest, arg :: restArgs, h => by
      cases h with
      | cons hhead htail =>
          simp [bindSupportedParams,
            decodeSupportedParamWord_canonical param.ty arg hhead,
            bindSupportedParams_canonical htail]

end Compiler.CompilationModel.DynamicAbi
