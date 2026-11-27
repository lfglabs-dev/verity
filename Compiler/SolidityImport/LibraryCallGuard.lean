import Lean
import Compiler.SolidityImport.AstIndex

set_option autoImplicit false

/-!
# External Library Call Inlining Guard & Initialization Transcription Helpers (`Compiler.SolidityImport.LibraryCallGuard`)

Formalizes two total, decidable structural guards and transcription descriptors
for the Solidity importer:

1. **External / Public Library Call `DELEGATECALL` Rejection (`#2596` / PR `#2595`)**:
   A `public` or `external` library function called from outside its library
   (either directly via `L.f(...)` or through `using L for T`) is compiled by
   `solc` into a `DELEGATECALL` targeting the library address linked at deployment.
   Because the source AST body may be an empty stub or differ from the bytecode
   linked at deployment, the importer must reject such calls at their call-site
   source location rather than silently inlining the AST body as an internal jump.
   Internal library functions, and `public` library functions called by unqualified
   name inside their own library, compile to internal jumps and remain eligible
   for inlining.

2. **Internal `String` Helper & Contract-Creation Initialization Transcription (`#2465`)**:
   Formalizes effect-bounded initialization transcription descriptors for pure/view
   internal `String` formatting helpers (`Strings.toString`, `string.concat`) and
   checked contract-creation (`create2` / `new`) templates during initialization,
   certifying free-memory pointer monotonicity and disjoint storage-slot frame
   preservation.

## Three-Layer Specification Architecture
* **Layer I (`LibraryCallInliningMetaSpec` & `InitTranscriptionMetaSpec`)**:
  Parametric specification structures and universal satisfaction theorems.
* **Layer II (Projection Corollaries)**:
  1–3 line corollaries certifying that no `external` or cross-library `public`
  library call passes the inlining filter and that `String`/creation init helpers
  preserve unmodified storage slots.
* **Layer III (`by decide` Executable Witness Suite)**:
  Kernel-checked positive and negative witnesses covering all 9 rejection/acceptance
  controls from `check_library_call_rejections.py` and initialization helper frames.
-/

namespace Compiler.CompilationModel.SolidityImport

open Lean

/-! ## External / Public Library Call Guard (`#2596` / PR `#2595`) -/

/-- Solidity function visibility qualifier relevant to library call dispatch. -/
inductive LibraryFunctionVisibility where
  | internal
  | privateVis
  | publicVis
  | externalVis
  deriving DecidableEq, Repr, Inhabited

/-- True iff a library function's visibility is `public` or `external`. -/
def isExternalOrPublicLibraryFunction : LibraryFunctionVisibility → Bool
  | .publicVis | .externalVis => true
  | .internal | .privateVis => false

/-- Kernel-reducible prefix check on character lists. -/
def isCharListPrefix : List Char → List Char → Bool
  | [], _ => true
  | _, [] => false
  | p :: ps, x :: xs => p == x && isCharListPrefix ps xs

/-- True iff a `solc` `typeDescriptions.typeIdentifier` string denotes a
`DELEGATECALL` library function pointer (`"t_function_delegatecall..."`). -/
def isDelegateCallTypeIdentifier (tid : String) : Bool :=
  isCharListPrefix "t_function_delegatecall".toList tid.toList

/-- A callee of `delegatecall` function type in the `solc --standard-json` AST:
a `public` or `external` library function called from outside its library,
directly (`L.f(...)`) or through `using L for T`. `solc` emits a `DELEGATECALL`
to the library address linked at deployment, whose code the source does not
determine (the body may be a stub for bytecode produced by another toolchain),
so the call is not inlined unless the import states `Profile.linkedLibrariesMatchSource`
(see `linkedLibraryParamKind` and `linkedLibraryFrameHazard?`). -/
def isLibraryDelegateCall (callee : Json) : Bool :=
  match jsonStrField? ((jsonField? callee "typeDescriptions").getD Json.null) "typeIdentifier" with
  | some tid => isDelegateCallTypeIdentifier tid
  | none => false

/-- Structural descriptor for a candidate library or helper function call site. -/
structure LibraryCallCandidate where
  /-- Whether the target declaration resides inside a Solidity `library`. -/
  isLibraryDecl : Bool
  /-- Declared visibility of the target function. -/
  visibility : LibraryFunctionVisibility
  /-- Whether the call crosses the library boundary (`L.f(...)` or `x.f(...)` via `using L for T`). -/
  calledFromOutsideLibrary : Bool
  /-- `solc` `typeDescriptions.typeIdentifier` attached to the callee expression. -/
  typeIdentifier : String
  deriving DecidableEq, Repr, Inhabited

/-- True iff `cand` lowers to an external library `DELEGATECALL` in `solc` and
must not be inlined as an internal helper call. -/
def requiresDelegateCallBoundary (cand : LibraryCallCandidate) : Bool :=
  isDelegateCallTypeIdentifier cand.typeIdentifier ||
    (cand.isLibraryDecl && cand.calledFromOutsideLibrary &&
      isExternalOrPublicLibraryFunction cand.visibility)

/-- Canonical located diagnostic emitted when an external library call is reached. -/
def externalLibraryCallDiagnostic : String :=
  "external library calls are outside this slice"

/-- Verdict of the library call inlining guard. -/
inductive LibraryInliningVerdict where
  | allowInline
  | rejectDelegateCall (diagnostic : String)
  deriving DecidableEq, Repr, Inhabited

/-- Total structural filter deciding whether `cand` may be inlined as an internal
helper call or must be rejected at the call site as an external library `DELEGATECALL`. -/
def checkLibraryCallInliningAllowed (cand : LibraryCallCandidate) : LibraryInliningVerdict :=
  if requiresDelegateCallBoundary cand then
    .rejectDelegateCall externalLibraryCallDiagnostic
  else
    .allowInline

/-! ## Linked library calls under `Profile.linkedLibrariesMatchSource` (`#2728`)

With the profile's trust assumption (the linked account's code behaves as solc's compilation
of the library in the same solc input), a direct `L.f(...)` `DELEGATECALL` is equivalent to
running `f`'s body in the caller's frame when nothing in the body, or in a function or
modifier it reaches, depends on what a `DELEGATECALL` frame does not share with its caller,
and when the arguments and results cross the ABI boundary unchanged:

* storage, transient storage, `msg.sender`, `msg.value`, `address(this)` and the block and
  transaction context are the caller's; the library's revert data is forwarded as is;
* value-type arguments and results are ABI-encoded clean and decode to the same values;
  a `storage` reference is passed as its slot; `bytes memory` arguments and results are
  explicitly copied into fresh 32-byte-aligned memory on entry and on return, matching
  the `DELEGATECALL` ABI boundary without aliasing;
* `msg.data`, `msg.sig`, `gasleft()` and any frame-dependent inline-assembly block
  (calldata, returndata, code, memory, storage, call, address/caller/value and gas builtins,
  or non-value-local external references) may observe the library frame, so they are rejected;
  only flat Yul `let` / single-target assignment blocks over `extcodesize` and pure word
  arithmetic/bitwise/comparison builtins referencing mutable value-type locals or parameters
  of the enclosing callable are admitted;
  non-`bytes` memory, calldata and function-typed arguments and results are copied or
  re-encoded across the boundary, so they are rejected too. -/

/-- A solc `typeIdentifier` of an elementary value type, an enum or a user-defined value type:
its ABI encoding decodes to the same value in the library and back in the caller. -/
def isLinkedLibraryValueTypeIdentifier (tid : String) : Bool :=
  let cs := tid.toList
  ["t_uint", "t_int", "t_address", "t_bool", "t_enum$", "t_userDefinedValueType$"].any
      (fun p => isCharListPrefix p.toList cs) ||
    (isCharListPrefix "t_bytes".toList cs && ((cs.drop 7).head?.map Char.isDigit).getD false)

/-- How an argument or result of a linked library function crosses the `DELEGATECALL`. -/
inductive LinkedLibraryOperandKind where
  /-- A value type (`isLinkedLibraryValueTypeIdentifier`). -/
  | value
  /-- A `storage` reference, passed as its slot. -/
  | storageRef
  /-- `bytes memory`, copied into fresh callee memory on entry and fresh caller memory on return. -/
  | bytesMemory
  /-- Non-`bytes` memory, calldata or function-typed: copied or re-encoded, outside this slice. -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- Classify a parameter from its solc `storageLocation` and `typeIdentifier`. -/
def linkedLibraryOperandKind (storageLocation tid : String) : LinkedLibraryOperandKind :=
  if storageLocation == "storage" then .storageRef
  else if storageLocation == "default" && isLinkedLibraryValueTypeIdentifier tid then .value
  else if storageLocation == "memory" && tid == "t_bytes_memory_ptr" then .bytesMemory
  else .other

/-- Classify a solc `VariableDeclaration` (parameter or return parameter). -/
def linkedLibraryParamKind (decl : Json) : LinkedLibraryOperandKind :=
  linkedLibraryOperandKind ((jsonStrField? decl "storageLocation").getD "")
    (((jsonField? decl "typeDescriptions").bind (jsonStrField? · "typeIdentifier")).getD "")

/-- Strip redundant parentheses (single-component, non-inline-array `TupleExpression`s).
Returns `none` if `fuel` runs out while parentheses remain, so callers fail closed. -/
def stripTupleParens : Nat → Json → Option Json
  | 0, j =>
      if astNodeType? j == some "TupleExpression" then none else some j
  | fuel + 1, j =>
      if astNodeType? j == some "TupleExpression" &&
          ((jsonField? j "isInlineArray").bind (·.getBool?.toOption)) == some false then
        match (jsonField? j "components").bind (·.getArr?.toOption) with
        | some #[only] => if only.isNull then some j else stripTupleParens fuel only
        | _ => some j
      else some j

/-- Extract an optional boolean field from a `Lean.Json` object. -/
def jsonBoolField? (j : Json) (key : String) : Option Bool :=
  (jsonField? j key).bind (·.getBool?.toOption)

/-- Expected arity of a Yul builtin admitted inside an inlined linked-library
`InlineAssembly` block (`extcodesize` plus pure word arithmetic, bitwise and comparison
operations). Frame-dependent, memory, storage, calldata, returndata and call/code builtins
(`address`, `caller`, `callvalue`, `calldata*`, `selfbalance`, `codesize`, `codecopy`,
`returndata*`, `gas`, `msize`, `mload`, `mstore*`, `mcopy`, `keccak256`, `sload`, `sstore`,
`tload`, `tstore`, `call*`, `create*`, `return`, `revert`, etc.) return `none`. -/
def linkedLibraryFrameNeutralBuiltinArity? : String → Option Nat
  | "extcodesize" | "iszero" | "not" => some 1
  | "add" | "sub" | "mul" | "div" | "sdiv" | "mod" | "smod" | "exp" | "signextend"
  | "lt" | "gt" | "slt" | "sgt" | "eq"
  | "and" | "or" | "xor" | "byte" | "shl" | "shr" | "sar" => some 2
  | "addmod" | "mulmod" => some 3
  | _ => none

/-- Collect `(declId, name)` for every mutable value-type local or parameter
`VariableDeclaration` inside `j` (bounded by `fuel`; fails closed if `fuel` runs out on
a composite JSON node). State variables, constants and immutables are excluded. -/
def collectValueLocalDecls : Nat → List (Nat × String) → Json → Option (List (Nat × String))
  | 0, _, .obj _ | 0, _, .arr _ => none
  | 0, acc, _ => some acc
  | fuel + 1, acc, j@(.obj kvs) =>
      let acc1 :=
        if astNodeType? j == some "VariableDeclaration" &&
            jsonBoolField? j "stateVariable" == some false &&
            jsonBoolField? j "constant" == some false &&
            jsonStrField? j "mutability" == some "mutable" &&
            linkedLibraryParamKind j == .value then
          match astNodeId? j, astNodeName? j with
          | some id, some name =>
              if name != "" && !(acc.any (·.1 == id)) then (id, name) :: acc else acc
          | _, _ => acc
        else acc
      kvs.foldl (fun m _ v => m.bind (collectValueLocalDecls fuel · v)) (some acc1)
  | fuel + 1, acc, .arr xs =>
      xs.toList.foldl (fun m v => m.bind (collectValueLocalDecls fuel · v)) (some acc)
  | _ + 1, acc, _ => some acc

/-- Validate every entry of `InlineAssembly.externalReferences` against `valueLocals`,
returning `(src, declName)` pairs when every external reference is a plain value-word
reference (`!isOffset`, `!isSlot`, no `suffix`, `valueSize == 1`) to a mutable value-type
local or parameter of the enclosing callable. -/
def resolveFrameNeutralExtRefs? (valueLocals : List (Nat × String)) (asm : Json) :
    Option (List (String × String)) := do
  let refsJson ← jsonField? asm "externalReferences"
  let refs ← refsJson.getArr?.toOption
  refs.toList.foldlM (init := []) fun acc ref => do
    guard (jsonBoolField? ref "isOffset" == some false)
    guard (jsonBoolField? ref "isSlot" == some false)
    guard ((jsonField? ref "suffix").isNone)
    guard (jsonNatField? ref "valueSize" == some 1)
    let src ← jsonStrField? ref "src"
    let declId ← jsonNatField? ref "declaration"
    let (_, declName) ← valueLocals.find? (·.1 == declId)
    pure ((src, declName) :: acc)

/-- True iff `node` is a `YulIdentifier` resolving either to an in-scope Yul local in
`yulLocals` (not an external reference) or to an unshadowed verified Solidity value
local/parameter in `extRefs`. -/
def isFrameNeutralYulIdent (extRefs : List (String × String)) (yulLocals : List String)
    (node : Json) : Bool :=
  astNodeType? node == some "YulIdentifier" &&
    match astNodeName? node, jsonStrField? node "src" with
    | some name, some src =>
        if yulLocals.contains name then !(extRefs.any (·.1 == src))
        else extRefs.contains (src, name)
    | _, _ => false

/-- True iff `expr` is a frame-neutral Yul expression over `extRefs` and `yulLocals`
within recursion depth `fuel`. -/
def isFrameNeutralYulExpr (extRefs : List (String × String)) (yulLocals : List String) :
    Nat → Json → Bool
  | 0, _ => false
  | fuel + 1, expr =>
      match astNodeType? expr with
      | some "YulLiteral" =>
          let k := (jsonStrField? expr "kind").getD ""
          let ty := (jsonStrField? expr "type").getD ""
          (k == "number" || k == "bool") && ty == ""
      | some "YulIdentifier" =>
          isFrameNeutralYulIdent extRefs yulLocals expr
      | some "YulFunctionCall" =>
          match jsonField? expr "functionName",
                (jsonField? expr "arguments").bind (·.getArr?.toOption) with
          | some fnNode, some args =>
              astNodeType? fnNode == some "YulIdentifier" &&
                match astNodeName? fnNode with
                | some fname =>
                    !yulLocals.contains fname && !(extRefs.any (·.2 == fname)) &&
                      match linkedLibraryFrameNeutralBuiltinArity? fname with
                      | some arity =>
                          args.size == arity &&
                            args.toList.all (isFrameNeutralYulExpr extRefs yulLocals fuel)
                      | none => false
                | none => false
          | _, _ => false
      | _ => false

/-- True iff every statement in `stmts` is a single-variable untyped `let` declaration
or single-target assignment over frame-neutral expressions, with no shadowing of
external Solidity references. -/
def isFrameNeutralYulStmts (extRefs : List (String × String)) (exprFuel : Nat := 128) :
    List String → List Json → Bool
  | _, [] => true
  | yulLocals, stmt :: rest =>
      match astNodeType? stmt with
      | some "YulVariableDeclaration" =>
          match (jsonField? stmt "variables").bind (·.getArr?.toOption) with
          | some #[varNode] =>
              let ty := (jsonStrField? varNode "type").getD ""
              match astNodeName? varNode with
              | some vname =>
                  let freshName := vname != "" && !yulLocals.contains vname &&
                    !(extRefs.any (·.2 == vname))
                  let rhsOk := match jsonField? stmt "value" with
                    | none => true
                    | some valNode =>
                        valNode.isNull ||
                          isFrameNeutralYulExpr extRefs yulLocals exprFuel valNode
                  freshName && ty == "" && rhsOk &&
                    isFrameNeutralYulStmts extRefs exprFuel (vname :: yulLocals) rest
              | none => false
          | _ => false
      | some "YulAssignment" =>
          match (jsonField? stmt "variableNames").bind (·.getArr?.toOption),
                jsonField? stmt "value" with
          | some #[varNode], some valNode =>
              !valNode.isNull &&
                isFrameNeutralYulIdent extRefs yulLocals varNode &&
                isFrameNeutralYulExpr extRefs yulLocals exprFuel valNode &&
                isFrameNeutralYulStmts extRefs exprFuel yulLocals rest
          | _, _ => false
      | _ => false

/-- True iff `asm` is an `InlineAssembly` block inside callable `owner` (`FunctionDefinition`
or `ModifierDefinition`) whose external references are all mutable value-type Solidity
locals or parameters of `owner` and whose Yul body consists solely of `let` declarations
and single-target assignments over `linkedLibraryFrameNeutralBuiltinArity?`. -/
def isLinkedLibraryFrameNeutralInlineAssembly (owner asm : Json) (fuel : Nat := 128) : Bool :=
  (astNodeType? owner == some "FunctionDefinition" ||
    astNodeType? owner == some "ModifierDefinition") &&
    astNodeType? asm == some "InlineAssembly" &&
    match (collectValueLocalDecls fuel [] ((jsonField? owner "parameters").getD Json.null)).bind
        (fun a => collectValueLocalDecls fuel a
          ((jsonField? owner "returnParameters").getD Json.null)) |>.bind
        (fun a => collectValueLocalDecls fuel a ((jsonField? owner "body").getD Json.null)) with
    | none => false
    | some valueLocals =>
        match resolveFrameNeutralExtRefs? valueLocals asm, jsonField? asm "AST" with
        | some extRefs, some ast =>
            astNodeType? ast == some "YulBlock" &&
              match (jsonField? ast "statements").bind (·.getArr?.toOption) with
              | some stmts => isFrameNeutralYulStmts extRefs fuel [] stmts.toList
              | none => false
        | _, _ => false

/-- The reason node `j` inside enclosing callable `owner` depends on the `DELEGATECALL` frame,
if it does: non-frame-neutral inline assembly, `msg.data`, `msg.sig` (including parenthesized
`(msg).sig` / `(msg).data`) or `gasleft`. -/
def linkedLibraryFrameHazardIn (owner j : Json) : Option String :=
  let builtin (n : Json) : Bool := ((jsonIntField? n "referencedDeclaration").getD 0) < 0
  match astNodeType? j with
  | some "InlineAssembly" =>
      if isLinkedLibraryFrameNeutralInlineAssembly owner j then
        none
      else
        some "inline assembly in a linked library call can observe the library's call frame"
  | some "MemberAccess" =>
      if ["data", "sig"].contains ((jsonStrField? j "memberName").getD "") then
        match (jsonField? j "expression").bind (stripTupleParens 256) with
        | some base =>
            if astNodeType? base == some "Identifier" && astNodeName? base == some "msg" &&
                builtin base then
              some "msg.data and msg.sig in a linked library call are the library call's calldata"
            else none
        | none =>
            some "msg.data and msg.sig in a linked library call are the library call's calldata"
      else none
  | some "Identifier" =>
      if astNodeName? j == some "gasleft" && builtin j then
        some "gasleft() in a linked library call reads the library frame's gas"
      else none
  | _ => none

/-- Context-free frame-hazard check on `j` (with no enclosing callable context). -/
def linkedLibraryFrameHazard (j : Json) : Option String :=
  linkedLibraryFrameHazardIn Json.null j

/-- Walk `j` inside enclosing callable `owner` and every function, operator or modifier
declaration it references (`decl`, transitively, each once, via `referencedDeclaration`
or overloaded-operator `function`). Returns the first frame-dependent node and its reason,
or the visited ids. -/
partial def linkedLibraryFrameHazardWalk (decl : Nat → Option Json) (owner : Json) :
    List Nat → Json → Except (Json × String) (List Nat)
  | seen, .arr xs => xs.foldl (fun acc x => acc.bind (linkedLibraryFrameHazardWalk decl owner · x))
      (.ok seen)
  | seen, j@(.obj o) =>
      match linkedLibraryFrameHazardIn owner j with
      | some reason => .error (j, reason)
      | none =>
        let step (s : List Nat) (edge : String) : Except (Json × String) (List Nat) :=
          match jsonNatField? j edge with
          | some id =>
              if s.contains id then .ok s
              else match decl id with
                | some d =>
                    let nextOwner :=
                      if astNodeType? d == some "FunctionDefinition" ||
                          astNodeType? d == some "ModifierDefinition" then d
                      else owner
                    linkedLibraryFrameHazardWalk decl nextOwner (id :: s) d
                | none => .ok s
          | none => .ok s
        let start := (step seen "referencedDeclaration").bind (step · "function")
        o.foldl (fun acc _ v => acc.bind (linkedLibraryFrameHazardWalk decl owner · v)) start
  | seen, _ => .ok seen

/-- The first frame-dependent node reached from the library function declaration `fn`. -/
def linkedLibraryFrameHazard? (decl : Nat → Option Json) (fn : Json) : Option (Json × String) :=
  let start := (astNodeId? fn).toList
  match linkedLibraryFrameHazardWalk decl fn start fn with
  | .error found => some found
  | .ok _ => none

/-- Witness: elementary value types, enums and UDVTs are value operands. -/
theorem witness_linked_library_value_types :
    linkedLibraryOperandKind "default" "t_uint256" = .value ∧
    linkedLibraryOperandKind "default" "t_bytes32" = .value ∧
    linkedLibraryOperandKind "default" "t_address_payable" = .value ∧
    linkedLibraryOperandKind "default" "t_enum$_E_$12" = .value ∧
    linkedLibraryOperandKind "default" "t_userDefinedValueType$_U_$3" = .value := by decide

/-- Witness: storage references and `bytes memory` are classified distinctly; other memory,
calldata and function types remain `.other`. -/
theorem witness_linked_library_reference_types :
    linkedLibraryOperandKind "storage" "t_struct$_S_$4_storage_ptr" = .storageRef ∧
    linkedLibraryOperandKind "memory" "t_bytes_memory_ptr" = .bytesMemory ∧
    linkedLibraryOperandKind "memory" "t_string_memory_ptr" = .other ∧
    linkedLibraryOperandKind "memory" "t_array$_t_uint256_$dyn_memory_ptr" = .other ∧
    linkedLibraryOperandKind "calldata" "t_bytes_calldata_ptr" = .other ∧
    linkedLibraryOperandKind "default" "t_bytes_memory_ptr" = .other ∧
    linkedLibraryOperandKind "default" "t_function_external_view$__$returns$__$" = .other ∧
    linkedLibraryOperandKind "default" "t_contract$_C_$5" = .other := by decide

/-- Witness: parenthesized `(msg).sig` is caught as a frame hazard while `(msg).sender` is not. -/
theorem witness_linked_library_paren_msg_hazard :
    let msgIdent := Json.mkObj [("nodeType", .str "Identifier"), ("name", .str "msg"),
      ("referencedDeclaration", .num (-15))]
    let parenMsg := Json.mkObj [("nodeType", .str "TupleExpression"),
      ("isInlineArray", .bool false), ("components", .arr #[msgIdent])]
    let parenSig := Json.mkObj [("nodeType", .str "MemberAccess"), ("memberName", .str "sig"),
      ("expression", parenMsg)]
    let parenSender := Json.mkObj [("nodeType", .str "MemberAccess"),
      ("memberName", .str "sender"), ("expression", parenMsg)]
    (linkedLibraryFrameHazard parenSig).isSome = true ∧
    linkedLibraryFrameHazard parenSender = none := by decide

/-- Witness: `extcodesize` and pure arithmetic/comparison builtins are allowlisted, while
frame-dependent, memory and storage builtins are excluded. -/
theorem witness_linked_library_frame_neutral_builtins :
    linkedLibraryFrameNeutralBuiltinArity? "extcodesize" = some 1 ∧
    linkedLibraryFrameNeutralBuiltinArity? "iszero" = some 1 ∧
    linkedLibraryFrameNeutralBuiltinArity? "add" = some 2 ∧
    linkedLibraryFrameNeutralBuiltinArity? "addmod" = some 3 ∧
    linkedLibraryFrameNeutralBuiltinArity? "caller" = none ∧
    linkedLibraryFrameNeutralBuiltinArity? "codecopy" = none ∧
    linkedLibraryFrameNeutralBuiltinArity? "mstore" = none ∧
    linkedLibraryFrameNeutralBuiltinArity? "sload" = none := by decide

/-- Witness: `assembly { size := extcodesize(p) }` over a value-type parameter and local passes,
while `caller()` and `bytes memory` external references fail (`address()` is pinned in
`LinkedLibraryCallChecks` so the `allowlist-address` mutant can rebuild `Import`). -/
theorem witness_linked_library_frame_neutral_asm :
    let pDecl := Json.mkObj [("nodeType", .str "VariableDeclaration"), ("id", .num 1),
      ("name", .str "p"), ("stateVariable", .bool false), ("constant", .bool false),
      ("mutability", .str "mutable"), ("storageLocation", .str "default"),
      ("typeDescriptions", Json.mkObj [("typeIdentifier", .str "t_address")])]
    let szDecl := Json.mkObj [("nodeType", .str "VariableDeclaration"), ("id", .num 2),
      ("name", .str "size"), ("stateVariable", .bool false), ("constant", .bool false),
      ("mutability", .str "mutable"), ("storageLocation", .str "default"),
      ("typeDescriptions", Json.mkObj [("typeIdentifier", .str "t_uint256")])]
    let bDecl := Json.mkObj [("nodeType", .str "VariableDeclaration"), ("id", .num 3),
      ("name", .str "b"), ("stateVariable", .bool false), ("constant", .bool false),
      ("mutability", .str "mutable"), ("storageLocation", .str "memory"),
      ("typeDescriptions", Json.mkObj [("typeIdentifier", .str "t_bytes_memory_ptr")])]
    let fn := Json.mkObj [("nodeType", .str "FunctionDefinition"),
      ("parameters", Json.mkObj [("parameters", .arr #[pDecl, bDecl])]),
      ("body", Json.mkObj [("statements", .arr #[szDecl])])]
    let ref2 := Json.mkObj [("declaration", .num 2), ("isOffset", .bool false),
      ("isSlot", .bool false), ("valueSize", .num 1), ("src", .str "a")]
    let ref1 := Json.mkObj [("declaration", .num 1), ("isOffset", .bool false),
      ("isSlot", .bool false), ("valueSize", .num 1), ("src", .str "b")]
    let ref3 := Json.mkObj [("declaration", .num 3), ("isOffset", .bool false),
      ("isSlot", .bool false), ("valueSize", .num 1), ("src", .str "b")]
    let lhs := Json.mkObj [("nodeType", .str "YulIdentifier"), ("name", .str "size"),
      ("src", .str "a")]
    let rhsOk := Json.mkObj [("nodeType", .str "YulFunctionCall"),
      ("functionName", Json.mkObj [("nodeType", .str "YulIdentifier"),
        ("name", .str "extcodesize")]),
      ("arguments", .arr #[Json.mkObj [("nodeType", .str "YulIdentifier"),
        ("name", .str "p"), ("src", .str "b")]])]
    let rhsCaller := Json.mkObj [("nodeType", .str "YulFunctionCall"),
      ("functionName", Json.mkObj [("nodeType", .str "YulIdentifier"), ("name", .str "caller")]),
      ("arguments", .arr #[])]
    let rhsBytes := Json.mkObj [("nodeType", .str "YulIdentifier"), ("name", .str "b"),
      ("src", .str "b")]
    let mkAsm (rs : Array Json) (r : Json) := Json.mkObj [("nodeType", .str "InlineAssembly"),
      ("externalReferences", .arr rs), ("AST", Json.mkObj [("nodeType", .str "YulBlock"),
        ("statements", .arr #[Json.mkObj [("nodeType", .str "YulAssignment"),
          ("variableNames", .arr #[lhs]), ("value", r)]])])]
    isLinkedLibraryFrameNeutralInlineAssembly fn (mkAsm #[ref2, ref1] rhsOk) 8 = true ∧
    isLinkedLibraryFrameNeutralInlineAssembly fn (mkAsm #[ref2] rhsCaller) 8 = false ∧
    isLinkedLibraryFrameNeutralInlineAssembly fn (mkAsm #[ref2, ref3] rhsBytes) 8 = false := by
  decide

/-! ## Initialization Transcription Helper Descriptors (`#2465`) -/

/-- Classification of initialization-time helper transcriptions (`#2465`). -/
inductive InitHelperKind where
  /-- Pure/view internal `String` helper (`Strings.toString`, `string.concat`) allocating
  a memory buffer of `byteLength` bytes without touching persistent storage. -/
  | internalStringHelper (helperName : String) (byteLength : Nat)
  /-- Checked contract-creation / `create2` initcode template of `templateBytes` bytes
  writing a bounded set of persistent storage slots `initSlotWrites`. -/
  | contractCreationInit (templateBytes : Nat) (initSlotWrites : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Abstract EVM state slice tracked across initialization helper transcription. -/
structure InitState where
  /-- Current free-memory pointer (`memory[0x40]`). -/
  freeMemoryPtr : Nat := 128
  /-- Persistent storage word valuation (`slot ↦ word`). -/
  persistentSlots : Nat → Nat := fun _ => 0
  /-- Count of child contracts deployed during initialization. -/
  deployedCount : Nat := 0

/-- Effect and frame descriptor for an initialization helper transcription step. -/
structure InitHelperDescriptor where
  /-- Underlying helper classification. -/
  kind : InitHelperKind
  /-- Whether the helper may modify any persistent storage slot. -/
  writesStorage : Bool
  /-- Decidable footprint predicate over persistent storage slots. -/
  modifiesSlot : Nat → Bool
  /-- Number of 32-byte-aligned memory bytes reserved by the helper. -/
  memoryAdvanceBytes : Nat
  /-- Number of child contracts created by the helper (`0` or `1`). -/
  createdContracts : Nat

/-- Construct the initialization descriptor for a pure internal `String` helper. -/
def mkStringHelperDescriptor (helperName : String) (byteLength : Nat) : InitHelperDescriptor where
  kind := .internalStringHelper helperName byteLength
  writesStorage := false
  modifiesSlot := fun _ => false
  memoryAdvanceBytes := 32 + ((byteLength + 31) / 32) * 32
  createdContracts := 0

/-- Construct the initialization descriptor for a checked contract-creation helper. -/
def mkCreationInitDescriptor (templateBytes : Nat) (initSlotWrites : List Nat) :
    InitHelperDescriptor where
  kind := .contractCreationInit templateBytes initSlotWrites
  writesStorage := !initSlotWrites.isEmpty
  modifiesSlot := fun slot => initSlotWrites.contains slot
  memoryAdvanceBytes := ((templateBytes + 31) / 32) * 32
  createdContracts := 1

/-- Execute an abstract initialization helper transcription step on `s` with slot
valuation `writeVal`. Slots outside `desc.modifiesSlot` are preserved identically. -/
def transcribeInitHelperStep
    (desc : InitHelperDescriptor) (writeVal : Nat → Nat) (s : InitState) : InitState where
  freeMemoryPtr := s.freeMemoryPtr + desc.memoryAdvanceBytes
  persistentSlots := fun slot =>
    if desc.modifiesSlot slot then writeVal slot else s.persistentSlots slot
  deployedCount := s.deployedCount + desc.createdContracts

/-! ## Layer I: Parametric Meta-Specifications & Universal Theorems -/

/-- **Layer I Meta-Spec 1 (`LibraryCallInliningMetaSpec`)**:
Certifies that `checkLibraryCallInliningAllowed` rejects every call whose `solc`
`typeIdentifier` starts with `"t_function_delegatecall"` or that invokes a `public`
or `external` library function from outside its declaring library, and admits
inlining if and only if `requiresDelegateCallBoundary cand = false`. -/
structure LibraryCallInliningMetaSpec (cand : LibraryCallCandidate) : Prop where
  /-- Any `t_function_delegatecall*` callee is rejected with `externalLibraryCallDiagnostic`. -/
  rejects_delegatecall_tid :
    isDelegateCallTypeIdentifier cand.typeIdentifier = true →
      checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic
  /-- Any `public` or `external` library function called from outside its library is rejected. -/
  rejects_cross_library_public_or_external :
    cand.isLibraryDecl = true →
    cand.calledFromOutsideLibrary = true →
    isExternalOrPublicLibraryFunction cand.visibility = true →
      checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic
  /-- Exact characterization: inlining is allowed iff no `DELEGATECALL` boundary is crossed. -/
  allow_inline_iff_no_delegatecall :
    checkLibraryCallInliningAllowed cand = .allowInline ↔
      requiresDelegateCallBoundary cand = false

/-- `@[simp]` normal form for `checkLibraryCallInliningAllowed` when `requiresDelegateCallBoundary` holds. -/
@[simp]
theorem checkLibraryCallInliningAllowed_of_requiresDelegateCallBoundary
    {cand : LibraryCallCandidate}
    (h : requiresDelegateCallBoundary cand = true) :
    checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic := by
  simp [checkLibraryCallInliningAllowed, h]

/-- `@[simp]` normal form for `checkLibraryCallInliningAllowed` when `requiresDelegateCallBoundary` is false. -/
@[simp]
theorem checkLibraryCallInliningAllowed_of_not_requiresDelegateCallBoundary
    {cand : LibraryCallCandidate}
    (h : requiresDelegateCallBoundary cand = false) :
    checkLibraryCallInliningAllowed cand = .allowInline := by
  simp [checkLibraryCallInliningAllowed, h]

/-- **Universal Theorem 1 (`libraryCallInlining_satisfies_metaSpec`)**:
Every `LibraryCallCandidate` satisfies `LibraryCallInliningMetaSpec`. -/
theorem libraryCallInlining_satisfies_metaSpec (cand : LibraryCallCandidate) :
    LibraryCallInliningMetaSpec cand where
  rejects_delegatecall_tid hTid := by
    simp [checkLibraryCallInliningAllowed, requiresDelegateCallBoundary, hTid]
  rejects_cross_library_public_or_external hLib hOut hVis := by
    simp [checkLibraryCallInliningAllowed, requiresDelegateCallBoundary, hLib, hOut, hVis]
  allow_inline_iff_no_delegatecall := by
    unfold checkLibraryCallInliningAllowed
    cases requiresDelegateCallBoundary cand <;> simp

/-- **Layer I Meta-Spec 2 (`InitTranscriptionMetaSpec`)**:
Certifies that `transcribeInitHelperStep` preserves all persistent storage slots
outside `desc.modifiesSlot`, leaves all slots untouched for internal `String`
helpers, and monotonically advances the free-memory pointer and deployed count. -/
structure InitTranscriptionMetaSpec
    (desc : InitHelperDescriptor) (writeVal : Nat → Nat) (s : InitState) : Prop where
  /-- Every slot outside `desc.modifiesSlot` is preserved unchanged. -/
  unmodified_slot_preserved :
    ∀ slot, desc.modifiesSlot slot = false →
      (transcribeInitHelperStep desc writeVal s).persistentSlots slot = s.persistentSlots slot
  /-- Pure internal `String` helpers preserve all persistent storage slots. -/
  string_helper_preserves_storage :
    ∀ name len, desc = mkStringHelperDescriptor name len →
      ∀ slot, (transcribeInitHelperStep desc writeVal s).persistentSlots slot = s.persistentSlots slot
  /-- The free-memory pointer never decreases across initialization helper transcription. -/
  free_pointer_monotone :
    s.freeMemoryPtr ≤ (transcribeInitHelperStep desc writeVal s).freeMemoryPtr
  /-- The deployed contract counter never decreases across initialization helper transcription. -/
  deployed_count_monotone :
    s.deployedCount ≤ (transcribeInitHelperStep desc writeVal s).deployedCount

/-- **Universal Theorem 2 (`initTranscription_satisfies_metaSpec`)**:
Every `InitHelperDescriptor`, `writeVal`, and `InitState` satisfies `InitTranscriptionMetaSpec`. -/
theorem initTranscription_satisfies_metaSpec
    (desc : InitHelperDescriptor) (writeVal : Nat → Nat) (s : InitState) :
    InitTranscriptionMetaSpec desc writeVal s where
  unmodified_slot_preserved slot hFalse := by
    simp [transcribeInitHelperStep, hFalse]
  string_helper_preserves_storage name len hDesc slot := by
    subst hDesc
    rfl
  free_pointer_monotone := by
    simp [transcribeInitHelperStep]
  deployed_count_monotone := by
    simp [transcribeInitHelperStep]

/-! ## Layer II: 1–3 Line Projection Corollaries -/

/-- **Layer II Corollary 1**: No callee with a `t_function_delegatecall*` type identifier passes the inlining filter. -/
theorem no_delegatecall_type_identifier_inlined
    (cand : LibraryCallCandidate)
    (hTid : isDelegateCallTypeIdentifier cand.typeIdentifier = true) :
    checkLibraryCallInliningAllowed cand ≠ .allowInline := by
  rw [(libraryCallInlining_satisfies_metaSpec cand).rejects_delegatecall_tid hTid]
  decide

/-- **Layer II Corollary 2**: No `external` library function called from outside its library passes the inlining filter. -/
theorem no_external_library_call_inlined
    (cand : LibraryCallCandidate)
    (hLib : cand.isLibraryDecl = true)
    (hOut : cand.calledFromOutsideLibrary = true)
    (hVis : cand.visibility = .externalVis) :
    checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic :=
  (libraryCallInlining_satisfies_metaSpec cand).rejects_cross_library_public_or_external
    hLib hOut (by simp [isExternalOrPublicLibraryFunction, hVis])

/-- **Layer II Corollary 3**: No `public` library function called from outside its library passes the inlining filter. -/
theorem no_public_outside_library_call_inlined
    (cand : LibraryCallCandidate)
    (hLib : cand.isLibraryDecl = true)
    (hOut : cand.calledFromOutsideLibrary = true)
    (hVis : cand.visibility = .publicVis) :
    checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic :=
  (libraryCallInlining_satisfies_metaSpec cand).rejects_cross_library_public_or_external
    hLib hOut (by simp [isExternalOrPublicLibraryFunction, hVis])

/-- **Layer II Corollary 4**: An `internal` library function with an internal type identifier is admitted for inlining. -/
theorem internal_library_call_inlined
    (cand : LibraryCallCandidate)
    (hTid : isDelegateCallTypeIdentifier cand.typeIdentifier = false)
    (hVis : cand.visibility = .internal) :
    checkLibraryCallInliningAllowed cand = .allowInline := by
  apply (libraryCallInlining_satisfies_metaSpec cand).allow_inline_iff_no_delegatecall.mpr
  simp [requiresDelegateCallBoundary, isExternalOrPublicLibraryFunction, hTid, hVis]

/-- **Layer II Corollary 5**: A `public` library function called by unqualified name inside its own library is admitted for inlining. -/
theorem public_same_library_call_inlined
    (cand : LibraryCallCandidate)
    (hTid : isDelegateCallTypeIdentifier cand.typeIdentifier = false)
    (hInside : cand.calledFromOutsideLibrary = false) :
    checkLibraryCallInliningAllowed cand = .allowInline := by
  apply (libraryCallInlining_satisfies_metaSpec cand).allow_inline_iff_no_delegatecall.mpr
  simp [requiresDelegateCallBoundary, hTid, hInside]

/-- **Layer II Corollary 6**: Internal `String` initialization helpers preserve every persistent storage slot. -/
theorem string_init_helper_preserves_all_slots
    (name : String) (byteLength : Nat) (writeVal : Nat → Nat) (s : InitState) (slot : Nat) :
    (transcribeInitHelperStep (mkStringHelperDescriptor name byteLength) writeVal s).persistentSlots slot =
      s.persistentSlots slot :=
  (initTranscription_satisfies_metaSpec (mkStringHelperDescriptor name byteLength) writeVal s).string_helper_preserves_storage
    name byteLength rfl slot

/-- **Layer II Corollary 7**: Contract-creation initialization helpers preserve every slot outside `initSlotWrites`. -/
theorem creation_init_helper_preserves_disjoint_slot
    (templateBytes : Nat) (initSlotWrites : List Nat) (writeVal : Nat → Nat)
    (s : InitState) (slot : Nat)
    (hDisjoint : initSlotWrites.contains slot = false) :
    (transcribeInitHelperStep (mkCreationInitDescriptor templateBytes initSlotWrites) writeVal s).persistentSlots slot =
      s.persistentSlots slot :=
  (initTranscription_satisfies_metaSpec (mkCreationInitDescriptor templateBytes initSlotWrites) writeVal s).unmodified_slot_preserved
    slot hDisjoint

/-! ## Layer III: Kernel-Checked Executable Witness Suite (`by decide`) -/

/-- Witness 1 (`public-stub` / `public-body`): `H.h(a, b)` calling a `public` library function from contract `C` is rejected. -/
theorem witness_reject_public_library_member_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .publicVis
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_delegatecall_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .rejectDelegateCall externalLibraryCallDiagnostic := by decide

/-- Witness 2 (`external-stub`): `H.h(a, b)` calling an `external` library function from contract `C` is rejected. -/
theorem witness_reject_external_library_member_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .externalVis
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_delegatecall_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .rejectDelegateCall externalLibraryCallDiagnostic := by decide

/-- Witness 3 (`using-for`): `a.h(b)` via `using H for bytes32` on a `public` library function is rejected. -/
theorem witness_reject_using_for_public_library_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .publicVis
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_attached_to$_t_bytes32_$delegatecall_pure" } =
      .rejectDelegateCall externalLibraryCallDiagnostic := by decide

/-- Witness 4 (`internal-member`): `H.h(a, b)` calling an `internal` library function is admitted for inlining. -/
theorem witness_allow_internal_library_member_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .internal
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_internal_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .allowInline := by decide

/-- Witness 5 (`public-by-name-inside-library`): `h(a, b)` called by name inside `library H` is admitted for inlining. -/
theorem witness_allow_public_inside_own_library_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .publicVis
        calledFromOutsideLibrary := false
        typeIdentifier := "t_function_internal_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .allowInline := by decide

/-- Witness 6 (`#2465` String init helper): `Strings.toString` reserves 64 bytes (32 length + 32 data) and writes 0 storage slots. -/
theorem witness_string_helper_descriptor_layout :
    let d := mkStringHelperDescriptor "Strings.toString" 20
    d.writesStorage = false ∧ d.memoryAdvanceBytes = 64 ∧ d.createdContracts = 0 := by decide

/-- Witness 7 (`#2465` Contract-creation init helper): 85-byte initcode template reserves 96 aligned bytes and tracks slot 0 vs slot 5. -/
theorem witness_creation_init_descriptor_layout :
    let d := mkCreationInitDescriptor 85 [0, 1]
    d.writesStorage = true ∧ d.memoryAdvanceBytes = 96 ∧
      d.modifiesSlot 0 = true ∧ d.modifiesSlot 5 = false ∧ d.createdContracts = 1 := by decide

end Compiler.CompilationModel.SolidityImport
