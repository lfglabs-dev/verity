import Compiler.CompilationModel.RequirePayloadValidation
import Compiler.Proofs.IRGeneration.FunctionBody.RequireBytes

/-! Explicit address bounds for every reachable require message, using the
canonical child-list enumeration so nested forms are not silently skipped. -/
namespace Compiler.Proofs.IRGeneration.FunctionBody
open Compiler.CompilationModel

inductive RequireMessageOccurs : List Stmt → String → Prop where
  | here {condition message rest} : RequireMessageOccurs (.require condition message :: rest) message
  | tail {head rest message} : RequireMessageOccurs rest message →
      RequireMessageOccurs (head :: rest) message
  | child {head rest body message} : body ∈ head.childLists → RequireMessageOccurs body message →
      RequireMessageOccurs (head :: rest) message

def requirePayloadsFit (statements : List Stmt) : Prop :=
  ∀ message, RequireMessageOccurs statements message →
    68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤ Verity.Core.Uint256.modulus

/-- Canonical traversal detects a matching node in any declared child list. -/
theorem anyDeep_of_child (predicate : Stmt → Bool) (statement : Stmt)
    (body : List Stmt) (member : body ∈ statement.childLists)
    (nested : Stmt.anyDeepList predicate body = true) :
    Stmt.anyDeep predicate statement = true := by
  obtain ⟨child, childMember, found⟩ := List.any_eq_true.mp nested
  rw [Stmt.anyDeep]
  apply Bool.or_eq_true_iff.mpr
  right
  apply List.any_eq_true.mpr
  refine ⟨⟨body, member⟩, by simp, ?_⟩
  apply List.any_eq_true.mpr
  exact ⟨⟨child, childMember⟩, by simp, found⟩

/-- Every semantic message occurrence is visited by the production validator. -/
theorem requireMessageOccurs_overflow {statements : List Stmt} {message : String}
    (occurs : RequireMessageOccurs statements message)
    (oversized : requirePayloadFitsWord message = false) :
    Stmt.anyDeepList requirePayloadOverflow statements = true := by
  induction occurs with
  | here =>
      simp only [Stmt.anyDeepList, List.any_cons]
      rw [Stmt.anyDeep]
      simp only [requirePayloadOverflow, oversized, Bool.not_false, Bool.true_or]
  | tail _ ih =>
      exact Bool.or_eq_true_iff.mpr (.inr (ih oversized))
  | child member _ ih =>
      exact Bool.or_eq_true_iff.mpr (.inl (anyDeep_of_child _ _ _ member (ih oversized)))

/-- Successful validation supplies the actual physical extent bound, including
messages nested in canonical child lists. -/
theorem requirePayloadsFit_of_validation (owner : String) (statements : List Stmt)
    (validated : validateRequirePayloads owner statements = .ok ()) :
    requirePayloadsFit statements := by
  intro message occurs
  by_contra oversized
  have detected := requireMessageOccurs_overflow occurs (show requirePayloadFitsWord message = false by
    simpa [requirePayloadFitsWord, Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] using oversized)
  simp [validateRequirePayloads, detected] at validated

theorem requirePayloadsFit_tail {head rest} (fits : requirePayloadsFit (head :: rest)) :
    requirePayloadsFit rest := fun message occurs => fits message (.tail occurs)

theorem requirePayloadsFit_child {head rest body}
    (fits : requirePayloadsFit (head :: rest)) (member : body ∈ head.childLists) :
    requirePayloadsFit body := fun message occurs => fits message (.child member occurs)

theorem requirePayloadsFit_here {condition message rest}
    (fits : requirePayloadsFit (.require condition message :: rest)) :
    68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤ Verity.Core.Uint256.modulus :=
  fits message .here

/-- Reachability respects concatenation, including messages in nested child lists. -/
theorem requireMessageOccurs_append {left right : List Stmt} {message : String} :
    RequireMessageOccurs (left ++ right) message ↔
      RequireMessageOccurs left message ∨ RequireMessageOccurs right message := by
  induction left with
  | nil =>
      constructor
      · exact Or.inr
      · intro occurs
        rcases occurs with impossible | occurs
        · cases impossible
        · exact occurs
  | cons head rest ih =>
      constructor
      · intro occurs
        cases occurs with
        | here => exact Or.inl .here
        | tail occurs =>
            rcases ih.mp occurs with before | after
            · exact Or.inl (.tail before)
            · exact Or.inr after
        | child member occurs => exact Or.inl (.child member occurs)
      · intro occurs
        rcases occurs with before | after
        · cases before with
          | here => exact .here
          | tail occurs => exact .tail (ih.mpr (Or.inl occurs))
          | child member occurs => exact .child member occurs
        · exact .tail (ih.mpr (Or.inr after))

theorem requirePayloadsFit_nil : requirePayloadsFit [] := by
  intro message occurs
  cases occurs

theorem requirePayloadsFit_append {left right : List Stmt} :
    requirePayloadsFit (left ++ right) ↔
      requirePayloadsFit left ∧ requirePayloadsFit right := by
  constructor
  · intro fits
    exact ⟨fun message occurs => fits message (requireMessageOccurs_append.mpr (.inl occurs)),
      fun message occurs => fits message (requireMessageOccurs_append.mpr (.inr occurs))⟩
  · rintro ⟨leftFits, rightFits⟩ message occurs
    rcases requireMessageOccurs_append.mp occurs with before | after
    · exact leftFits message before
    · exact rightFits message after

theorem requirePayloadsFit_singleton_of_cons {head rest}
    (fits : requirePayloadsFit (head :: rest)) : requirePayloadsFit [head] :=
  (requirePayloadsFit_append.mp (show requirePayloadsFit ([head] ++ rest) from fits)).1

theorem requirePayloadsFit_ite_then {condition thenBranch elseBranch rest}
    (fits : requirePayloadsFit (.ite condition thenBranch elseBranch :: rest)) :
    requirePayloadsFit thenBranch :=
  requirePayloadsFit_child fits (by simp [Stmt.childLists])

theorem requirePayloadsFit_ite_else {condition thenBranch elseBranch rest}
    (fits : requirePayloadsFit (.ite condition thenBranch elseBranch :: rest)) :
    requirePayloadsFit elseBranch :=
  requirePayloadsFit_child fits (by simp [Stmt.childLists])

/-- Extra reserve for sequential compile-core lists. Their constructors
exclude nested branches and loops; the separate terminal proof uses sizeOf. -/
def requireFuelReserve : List Stmt → Nat
  | [] => 0
  | .require _ message :: rest =>
      max ((PhysicalErrorStringExecution.writes message).length + 2) (requireFuelReserve rest)
  | _ :: rest => requireFuelReserve rest

theorem requireFuelReserve_tail (head : Stmt) (rest : List Stmt) :
    requireFuelReserve rest ≤ requireFuelReserve (head :: rest) := by
  cases head <;> simp only [requireFuelReserve] <;> try exact Nat.le_refl _
  exact Nat.le_max_right _ _

end Compiler.Proofs.IRGeneration.FunctionBody
