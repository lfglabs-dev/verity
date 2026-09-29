import TranslationValidationCapturedNodes
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativePrimOps

namespace SolidityTranslationValidation.AstBridge

open EvmYul Yul

/-- Read a variable through the actual interpreter. At fuel one the variable
case always succeeds; `eval_variableValue` below rules out the error fallback. -/
def variableValue (s : Yul.State) (name : String) : UInt256 :=
  match Yul.eval 1 (.Var name) none s with
  | .ok (_, value) => value
  | .error _ => UInt256.ofNat 0

theorem eval_variableValue (s : Yul.State) (name : String)
    (code : Option Yul.Ast.YulContract) :
    Yul.eval 1 (.Var name) code s = .ok (s, variableValue s name) := by
  simp [variableValue, Yul.eval]


/-- Real interpreter execution of the product expression decoded from the
pinned optimized AST. The state, including memory and storage, is unchanged. -/
theorem eval_captured_product (s : Yul.State) (code : Option Yul.Ast.YulContract) :
    Yul.eval 10 capturedProductExpr code s =
      .ok (s, UInt256.mul (variableValue s "value") (variableValue s "value_1")) := by
  simp [variableValue, capturedProductExpr, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.evalPrimCall, Yul.reverse', Yul.cons', Yul.head']

/-- Real interpreter execution of the quotient expression selected from the
return-word mstore argument, with no substitution of a hand-written model. -/
theorem eval_captured_quotient (s : Yul.State) (code : Option Yul.Ast.YulContract) :
    Yul.eval 10 capturedQuotientExpr code s =
      .ok (s, UInt256.div (variableValue s "product") (variableValue s "value_2")) := by
  simp [variableValue, capturedQuotientExpr, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.evalPrimCall, Yul.reverse', Yul.cons', Yul.head']

/-- Pair the kernel-checked JSON decoder equation with actual native execution.
The artifact-to-JSON quotation boundary is documented separately. -/
theorem decoded_product_executes (s : Yul.State) (code : Option Yul.Ast.YulContract) :
    decodeExpr 8 capturedProductJson = .ok capturedProductExpr ∧
    Yul.eval 10 capturedProductExpr code s =
      .ok (s, UInt256.mul (variableValue s "value") (variableValue s "value_1")) :=
  ⟨decodeProduct, eval_captured_product s code⟩

theorem decoded_quotient_executes (s : Yul.State) (code : Option Yul.Ast.YulContract) :
    decodeExpr 8 capturedQuotientJson = .ok capturedQuotientExpr ∧
    Yul.eval 10 capturedQuotientExpr code s =
      .ok (s, UInt256.div (variableValue s "product") (variableValue s "value_2")) :=
  ⟨decodeQuotient, eval_captured_quotient s code⟩

/-- Execute the actual captured `let product := mul(value, value_1)` statement.
Only the named local changes; the native insertion preserves shared state. -/
theorem exec_captured_product_declaration (s : Yul.State)
    (code : Option Yul.Ast.YulContract) :
    Yul.exec 10 capturedProductDeclaration code s =
      .ok (s.insert "product"
        (UInt256.mul (variableValue s "value") (variableValue s "value_1"))) := by
  simp [capturedProductDeclaration, capturedProductExpr, variableValue,
    Yul.exec, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.execPrimCall, Yul.reverse', Yul.cons', Yul.multifill']
  cases s <;> rfl

/-- Successful mathematical quotient under explicit bindings at the selected
program point. Establishing those bindings through the product statement and
both guards is still a separate statement-execution obligation. -/
theorem captured_quotient_success (s : Yul.State) (code : Option Yul.Ast.YulContract)
    (x y d : Nat) (hfit : x * y < UInt256.size) (hd : d < UInt256.size) (_hdzero : d ≠ 0)
    (hproduct : (variableValue s "product") = UInt256.ofNat (x * y))
    (hdenominator : (variableValue s "value_2") = UInt256.ofNat d) :
    Yul.eval 10 capturedQuotientExpr code s =
      .ok (s, UInt256.ofNat (x * y / d)) := by
  rw [eval_captured_quotient, hproduct, hdenominator]
  have hdiv : UInt256.div (UInt256.ofNat (x * y)) (UInt256.ofNat d) =
      UInt256.ofNat (x * y / d) := by
    apply congrArg UInt256.mk
    apply Fin.ext
    change (x * y % UInt256.size) / (d % UInt256.size) =
      (x * y / d) % UInt256.size
    rw [Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt hd,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hfit)]
  rw [hdiv]

#print axioms decodeProduct
#print axioms decodeQuotient
#print axioms decodeProductDeclaration
#print axioms exec_captured_product_declaration
#print axioms decoded_product_executes
#print axioms decoded_quotient_executes
#print axioms captured_quotient_success

end SolidityTranslationValidation.AstBridge
