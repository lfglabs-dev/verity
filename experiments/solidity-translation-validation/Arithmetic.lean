import Compiler.SolidityImport.Access
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas

/-!
Universal arithmetic obligations for the captured solc `mulDivDown` overflow
guard. These theorems are intermediate lemmas, not a translation certificate:
they do not execute the imported wrapper or the captured dispatcher.
-/

namespace SolidityTranslationValidation

open Verity.Core
open Compiler.CompilationModel.SolidityImport
open Compiler.Proofs.YulGeneration.Backends

/-- The zero-aware division guard used by solc detects precisely whether the
mathematical product fits in a positive modulus. No operand bound is needed. -/
theorem mul_overflow_guard_iff (modulus x y : Nat) (hm : 0 < modulus) :
    (x = 0 ∨ (x * y % modulus) / x = y) ↔ x * y < modulus := by
  by_cases hx : x = 0
  · subst x
    simp [hm]
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx
  constructor
  · intro h
    have hdiv := h.resolve_left hx
    by_contra hoverflow
    have hres : x * y % modulus < y * x := by
      rw [Nat.mul_comm y x]
      exact lt_of_lt_of_le (Nat.mod_lt _ hm) (Nat.le_of_not_gt hoverflow)
    have hlt := (Nat.div_lt_iff_lt_mul hxpos).mpr hres
    omega
  · intro h
    exact Or.inr (by rw [Nat.mod_eq_of_lt h, Nat.mul_div_cancel_left y hxpos])

/-- Same guard using Denote's actual 256-bit multiplication and division.
Input bounds are essential: `Uint256.ofNat` normalizes its arguments. -/
theorem denote_word_mul_overflow_guard_iff (x y : Nat)
    (hx : x < Uint256.modulus) (hy : y < Uint256.modulus) :
    (x = 0 ∨
      ((Uint256.ofNat x * Uint256.ofNat y) / Uint256.ofNat x).val = y) ↔
      x * y < Uint256.modulus := by
  have hprod : (Uint256.ofNat x * Uint256.ofNat y).val =
      x * y % Uint256.modulus := by
    change (Uint256.mul _ _).val = _
    simp [Uint256.mul, Uint256.ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  have hdiv : ((Uint256.ofNat x * Uint256.ofNat y) / Uint256.ofNat x).val =
      (x * y % Uint256.modulus) / x := by
    change (Uint256.div _ _).val = _
    by_cases hzero : x = 0
    · subst x
      simp [Uint256.div, Uint256.ofNat]
    · simp only [Uint256.div, hprod]
      simp only [Uint256.ofNat, Nat.mod_eq_of_lt hx, hzero, ↓reduceIte]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt
          (Nat.div_le_self (x * y % Uint256.modulus) x)
          (Nat.mod_lt _ (by decide : 0 < Uint256.modulus)))
  rw [hdiv]
  exact mul_overflow_guard_iff _ _ _ (by decide)

/-- The real EVMYulLean builtin bridge computes the same overflow predicate.
This proves a relation between native builtin observations, not interpreter
execution of the whole optimized AST. -/
theorem native_mul_overflow_guard_iff (x y : Nat)
    (hx : x < Compiler.Constants.evmModulus) :
    (x = 0 ∨
      evalPureBuiltinViaEvmYulLean "div" [x * y % Compiler.Constants.evmModulus, x] =
        some y) ↔ x * y < Compiler.Constants.evmModulus := by
  rw [evalPureBuiltinViaEvmYulLean_div_native]
  simp only [Nat.mod_mod, Nat.mod_eq_of_lt hx]
  by_cases hzero : x = 0
  · subst x
    simp [Compiler.Constants.evmModulus]
  · simp only [hzero, ↓reduceIte, Option.some.injEq, false_or]
    simpa only [hzero, false_or] using
      mul_overflow_guard_iff Compiler.Constants.evmModulus x y (by decide)

/-- Native modular multiplication supplies exactly the product consumed by the
previous theorem, for all natural-number representatives. -/
theorem native_product (x y : Nat) :
    evalPureBuiltinViaEvmYulLean "mul" [x, y] =
      some (x * y % Compiler.Constants.evmModulus) :=
  evalPureBuiltinViaEvmYulLean_mul_native x y

/-- On the successful arithmetic path, the actual native multiply/divide
builtins return the mathematical quotient. Zero denominators are excluded here;
their panic payload is a separate, currently blocked interpreter obligation. -/
theorem native_mul_div_success (x y d : Nat)
    (hprod : x * y < Compiler.Constants.evmModulus)
    (hd : d < Compiler.Constants.evmModulus) (hdzero : d ≠ 0) :
    (evalPureBuiltinViaEvmYulLean "mul" [x, y]).bind
      (fun product => evalPureBuiltinViaEvmYulLean "div" [product, d]) =
      some (x * y / d) := by
  rw [native_product, Nat.mod_eq_of_lt hprod]
  simp only [Option.bind_some, evalPureBuiltinViaEvmYulLean_div_native,
    Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hd, hdzero, ↓reduceIte]

/-- The corresponding actual Denote word operations yield that same quotient.
This uses all canonical input bounds, rather than proving a natural-number
model unrelated to the executable word semantics. -/
theorem denote_mul_div_success (x y d : Nat)
    (hx : x < Uint256.modulus) (hy : y < Uint256.modulus)
    (hd : d < Uint256.modulus) (hprod : x * y < Uint256.modulus) (hdzero : d ≠ 0) :
    ((Uint256.ofNat x * Uint256.ofNat y) / Uint256.ofNat d).val = x * y / d := by
  have hp : (Uint256.ofNat x * Uint256.ofNat y).val = x * y := by
    change (Uint256.mul _ _).val = _
    simp [Uint256.mul, Uint256.ofNat, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hprod]
  change (Uint256.div _ _).val = _
  simp only [Uint256.div, hp]
  simp only [Uint256.ofNat, Nat.mod_eq_of_lt hd, hdzero, ↓reduceIte]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self (x * y) d) hprod)

#print axioms mul_overflow_guard_iff
#print axioms denote_word_mul_overflow_guard_iff
#print axioms native_mul_overflow_guard_iff
#print axioms native_product
#print axioms native_mul_div_success
#print axioms denote_mul_div_success

end SolidityTranslationValidation
