import TranslationValidationDispatcherBoundary
import TranslationValidationGuardedExecution

namespace SolidityTranslationValidation.AstBridge.MemoryGuard
open EvmYul Yul Lean

/-- Explicit extension for post-optimization literal memoryguard declarations.
Native nodes retain the original interpreter. No claim about solc's optimizer
or correctness of the C++ code generator is part of this definition. -/
inductive Statement where
  | native (statement : Yul.Ast.Stmt)
  | memoryguardDeclaration (name : String) (literal : UInt256)
  | block (statements : List Statement)

/-- Interpretation of the extended builtin: preserve state and bind its literal.
This is a specified dialect extension, not an existing EVMYulLean operation. -/
def execute : Nat → Statement → Option Yul.Ast.YulContract → Yul.State → Except Yul.Exception Yul.State
  | 0, _, _, _ => .error .OutOfFuel
  | fuel + 1, .native statement, code, state => Yul.exec (fuel + 1) statement code state
  | _ + 1, .memoryguardDeclaration name literal, _, state => .ok (state.insert name literal)
  | _ + 1, .block [], _, state => .ok state
  | fuel + 1, .block (head :: tail), code, state => do
      let next ← execute fuel head code state
      execute fuel (.block tail) code next

def lower : Statement → Yul.Ast.Stmt
  | .native statement => statement
  | .memoryguardDeclaration name literal => .Let [name] (some (.Lit literal))
  | .block statements => .Block (statements.map lower)

/-- Conservativity on every native statement, including exhaustion and errors. -/
theorem native_conservative (fuel : Nat) (statement : Yul.Ast.Stmt)
    (code : Option Yul.Ast.YulContract) (state : Yul.State) :
    execute fuel (.native statement) code state = Yul.exec fuel statement code state := by
  cases fuel <;> simp [execute, Yul.exec]

/-- The explicit lowering preserves complete interpreter results for every
extended statement, state, code override and fuel, including arbitrary blocks.
The memoryguard interpretation is the stated extension boundary above. -/
theorem lowering_preserves_execution (fuel : Nat) (statement : Statement)
    (code : Option Yul.Ast.YulContract) (state : Yul.State) :
    execute fuel statement code state = Yul.exec fuel (lower statement) code state := by
  induction fuel generalizing statement state with
  | zero => simp [execute, Yul.exec]
  | succ fuel ih =>
    cases statement with
    | native statement => simp only [execute, lower]
    | memoryguardDeclaration name literal => simp [execute, lower]
    | block statements =>
      cases statements with
      | nil => simp [execute, lower, Yul.exec]
      | cons head tail =>
        simp only [execute, lower, List.map_cons]
        simp only [ih]
        rw [Yul.exec]
        cases Yul.exec fuel (lower head) code state <;> (simp only [lower]; rfl)

private def field (node : Json) (key : String) : Except String String := do
  (← node.getObjVal? key).getStr?

private def keys (node : Json) (allowed : List String) : Except String Unit := do
  for (key, _) in (← node.getObj?).toList do
    unless allowed.contains key do throw s!"unknown memoryguard AST field {key}"
  for key in ["src", "nativeSrc"] do
    let _ ← field node key

/-- Strictly decode a literal memoryguard declaration, preserving its distinct
constructor. This decoder neither accepts dynamic arguments nor rewrites JSON. -/
def decodeDeclaration (node : Json) : Except String Statement := do
  keys node ["nodeType", "variables", "value", "src", "nativeSrc"]
  unless (← field node "nodeType") == "YulVariableDeclaration" do throw "expected memoryguard declaration"
  let bindings ← (← node.getObjVal? "variables").getArr?
  unless bindings.size == 1 do throw "expected one memoryguard binding"
  let binding := bindings[0]!
  keys binding ["name", "type", "nodeType", "src", "nativeSrc"]
  unless (← field binding "nodeType") == "YulTypedName" do throw "expected typed memoryguard binding"
  unless (← field binding "type") == "" do throw "unsupported memoryguard binding type"
  let name ← field binding "name"
  unless !name.isEmpty do throw "empty memoryguard binding"
  let call ← node.getObjVal? "value"
  keys call ["nodeType", "functionName", "arguments", "src", "nativeSrc"]
  unless (← field call "nodeType") == "YulFunctionCall" do throw "expected memoryguard call"
  let callee ← call.getObjVal? "functionName"
  keys callee ["nodeType", "name", "src", "nativeSrc"]
  unless (← field callee "nodeType") == "YulIdentifier" do throw "expected memoryguard callee identifier"
  unless (← field callee "name") == "memoryguard" do throw "expected memoryguard builtin"
  let arguments ← (← call.getObjVal? "arguments").getArr?
  unless arguments.size == 1 do throw "expected one memoryguard literal"
  unless (← field arguments[0]! "nodeType") == "YulLiteral" do throw "memoryguard requires literal"
  let literal ← AstBridge.decodeExpr 2 arguments[0]!
  match literal with
  | .Lit value => pure (.memoryguardDeclaration name value)
  | _ => throw "memoryguard requires numeric literal"

/-- Exact captured JSON, including the unchanged memoryguard callee. -/
theorem decode_captured_memoryguard :
    decodeDeclaration capturedPointerDeclarationJson =
      .ok (.memoryguardDeclaration "_1" (UInt256.ofNat 128)) := by rfl

/-- Derive the pointer premise under the explicit dialect extension. -/
theorem captured_pointer_binding (fuel : Nat) (code : Option Yul.Ast.YulContract)
    (shared : SharedState .Yul) (store : Yul.VarStore) :
    let initial := Yul.State.Ok shared store
    let next := initial.insert "_1" (UInt256.ofNat 128)
    execute (fuel + 1) (.memoryguardDeclaration "_1" (UInt256.ofNat 128)) code initial = .ok next ∧
      variableValue next "_1" = UInt256.ofNat 128 := by
  exact ⟨rfl, variableValue_insert_self shared store "_1" (UInt256.ofNat 128)⟩

/-- Bind the real captured JSON declaration directly to its execution result. -/
theorem captured_node_executes (fuel : Nat) (code : Option Yul.Ast.YulContract)
    (shared : SharedState .Yul) (store : Yul.VarStore) :
    (decodeDeclaration capturedPointerDeclarationJson).map
      (fun statement => execute (fuel + 1) statement code (.Ok shared store)) =
      .ok (.ok ((Yul.State.Ok shared store).insert "_1" (UInt256.ofNat 128))) := by
  rw [decode_captured_memoryguard]
  rfl

/-- The explicit extension does not change shared state or any other binding. -/
theorem captured_pointer_frame (shared : SharedState .Yul) (store : Yul.VarStore)
    (name : String) (hne : name ≠ "_1") :
    let initial := Yul.State.Ok shared store
    let next := initial.insert "_1" (UInt256.ofNat 128)
    next.sharedState = shared ∧ variableValue next name = variableValue initial name := by
  exact ⟨rfl, variableValue_insert_other (.Ok shared store) name "_1" (UInt256.ofNat 128) hne⟩

#print axioms captured_node_executes
#print axioms captured_pointer_frame
#print axioms native_conservative
#print axioms lowering_preserves_execution
#print axioms decode_captured_memoryguard
#print axioms captured_pointer_binding
end SolidityTranslationValidation.AstBridge.MemoryGuard
