-- Generated from the unchanged pinned optimized AST by check_dispatcher_boundary.py.
import TranslationValidationAstDecoder
namespace SolidityTranslationValidation.AstBridge
-- JSON path: ["subObjects", 0, "code", "block", "statements", 0, "statements", 0]
-- nativeSrc 629:27:0: let _1 := memoryguard(0x80)
def capturedPointerDeclarationJson : Lean.Json := (Lean.Json.mkObj [("nativeSrc", (.str "629:27:0")), ("nodeType", (.str "YulVariableDeclaration")), ("src", (.str "122:165:0")), ("value", (Lean.Json.mkObj [("arguments", (.arr #[(Lean.Json.mkObj [("kind", (.str "number")), ("nativeSrc", (.str "651:4:0")), ("nodeType", (.str "YulLiteral")), ("src", (.str "122:165:0")), ("type", (.str "")), ("value", (.str "0x80"))])])), ("functionName", (Lean.Json.mkObj [("name", (.str "memoryguard")), ("nativeSrc", (.str "639:11:0")), ("nodeType", (.str "YulIdentifier")), ("src", (.str "122:165:0"))])), ("nativeSrc", (.str "639:17:0")), ("nodeType", (.str "YulFunctionCall")), ("src", (.str "122:165:0"))])), ("variables", (.arr #[(Lean.Json.mkObj [("name", (.str "_1")), ("nativeSrc", (.str "633:2:0")), ("nodeType", (.str "YulTypedName")), ("src", (.str "122:165:0")), ("type", (.str ""))])]))])
theorem captured_pointer_declaration_rejected :
    decodeDeclaration 20 capturedPointerDeclarationJson =
      .error "unsupported Yul builtin memoryguard" := by rfl
#print axioms captured_pointer_declaration_rejected
end SolidityTranslationValidation.AstBridge
