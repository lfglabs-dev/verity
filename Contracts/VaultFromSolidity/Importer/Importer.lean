import Lean
import Verity.Stdlib.Math
import Verity.Core.SolidityImportAttr
import Compiler.Sha256.Engine
import Contracts.VaultFromSolidity.Importer.Semantics

/-!
A proof-only Solidity frontend. This module invokes pinned `solc --standard-json`,
validates a closed typed-AST/storage-layout subset, parses it into the closed,
intrinsically typed inductive in `Syntax.lean`, and registers each entry point as
`Semantics.lean`'s `Fn.meaning` applied to that parsed term. The accepted subset is
a kernel-checked Lean value, so nothing is serialized, no intermediate IR is
materialised, and no Lean source is generated or written to disk.

Besides the executable model it elaborates a kernel-checked `Storage` structure
(the one use of the standard command elaborator in this frontend), registers
`view : ContractState → Storage` from the `<var>Slot` handles, tags imported
declarations into the `solidity_import` simp set, and registers a deterministic
entry-point relation `step`. Specs can then say `v.totalAssets` instead of naming
a raw slot number.
-/

open Lean Meta Elab Command

namespace SolidityImporter

/-- Release identity used in `sourceDigest`. Platform banners are not part of it. -/
private def solcVersionPin := "0.8.33+commit.64118f21"
/-- Official SHA-256 digests from binaries.soliditylang.org `<platform>/list.json`. -/
private def officialSolcSha256s : Array String := #[
  "1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468",
  "8324280591ce398d7e2722846bc10ecf1779b13a328ef97b687c92cd9c70801a"]
private def acceptedSolcVersionOutputs : Array String := #[
  s!"solc, the solidity compiler commandline interface\nVersion: {solcVersionPin}.Linux.g++",
  s!"solc, the solidity compiler commandline interface\nVersion: {solcVersionPin}.Darwin.appleclang"]
/-- Logical path × package-relative path. The digest covers this file, so adding
a source moves every imported `sourceDigest`. -/
private def registeredSources : List (String × String) := [
  ("Contracts/VaultFromSolidity/Vault.sol", "Contracts/VaultFromSolidity/Vault.sol"),
  ("Contracts/SolidityImportSmoke/Inheritance/Inheritance.sol",
    "Contracts/SolidityImportSmoke/Inheritance/Inheritance.sol")
]

private def field (j : Json) (key : String) : MetaM Json :=
  match j.getObjVal? key with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def field? (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

private def str (j : Json) : MetaM String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def nat (j : Json) : MetaM Nat :=
  match j.getNat? with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def int (j : Json) : MetaM Int :=
  match j.getInt? with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def bool (j : Json) : MetaM Bool :=
  match j.getBool? with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def arr (j : Json) : MetaM (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def objKeys (j : Json) : MetaM (List String) :=
  match j with
  | .obj o => pure <| o.foldl (fun keys key _ => key :: keys) []
  | _ => throwError "object expected"

private def requireKeys (j : Json) (allowed : List String) (what : String) : MetaM Unit := do
  for key in ← objKeys j do
    unless key ∈ allowed do throwError "unknown {what} field {key}"

private def nodeKind (j : Json) : MetaM String := field j "nodeType" >>= str
private def nodeId (j : Json) : MetaM Nat := field j "id" >>= nat

private partial def collectAstIds (j : Json) : MetaM (List Nat) := do
  match j with
  | .obj o =>
      let self ← if (field? j "nodeType").isSome then do pure [← nodeId j] else pure []
      let mut ids := self
      for (_, value) in o.toList do ids := ids ++ (← collectAstIds value)
      pure ids
  | .arr xs =>
      let mut ids := []
      for value in xs do ids := ids ++ (← collectAstIds value)
      pure ids
  | _ => pure []

private def expect (ok : Bool) (message : String) : MetaM Unit :=
  unless ok do throwError message

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

private def sha256Hex (bytes : ByteArray) : String :=
  (Sha256Engine.sha256 bytes).data.foldl (init := "") fun acc byte =>
    acc.push (hexDigit (byte.toNat / 16)) |>.push (hexDigit (byte.toNat % 16))

private def verifyCompiler (compiler : System.FilePath) : MetaM Unit := do
  let output ←
    if System.Platform.isOSX then
      IO.Process.output { cmd := "/usr/bin/shasum", args := #["-a", "256", compiler.toString] }
    else
      IO.Process.output { cmd := "/usr/bin/sha256sum", args := #[compiler.toString] }
  unless output.exitCode == 0 && officialSolcSha256s.contains (output.stdout.take 64).toString do
    throwError "compiler checksum mismatch"

private structure SourceContext where
  path : System.FilePath
  logicalPath : String
  bytes : ByteArray
  sourceId : Nat

private def parseSpan (j : Json) : MetaM (Nat × Nat × Nat) := do
  let pieces := (← str (← field j "src")).splitOn ":"
  match pieces with
  | [a, b, c] =>
      let some start := a.toNat? | throwError "invalid source span"
      let some size := b.toNat? | throwError "invalid source span"
      let some sourceId := c.toNat? | throwError "invalid source span"
      pure (start, size, sourceId)
  | _ => throwError "invalid source span"

private def failAt (ctx : SourceContext) (j : Json) (why : String) : MetaM α := do
  let (start, size, _sourceId) ← parseSpan j
  let before := ctx.bytes.data.extract 0 (min start ctx.bytes.size)
  let (line, column) := before.foldl
    (fun (p : Nat × Nat) b => if b == 10 then (p.1 + 1, 1) else (p.1, p.2 + 1)) (1, 1)
  let excerptBytes : ByteArray := ⟨ctx.bytes.data.extract start (min (start + size) (min ctx.bytes.size (start + 100)))⟩
  let excerpt := String.fromUTF8? excerptBytes |>.getD "<invalid UTF-8>"
  let kind := (← nodeKind j)
  throwError "{ctx.logicalPath}:{line}:{column}: {kind}: {why}\n{excerpt}"

private def needAt (ctx : SourceContext) (j : Json) (ok : Bool) (why : String) : MetaM Unit :=
  unless ok do failAt ctx j why

private def commonFields := ["id", "src", "nodeType"]
private def expressionFields := ["isConstant", "isLValue", "isPure", "lValueRequested", "typeDescriptions"]

private def allowedNodeFields : String → Option (List String)
  | "SourceUnit" => some ["absolutePath", "exportedSymbols", "license", "nodes"]
  | "PragmaDirective" => some ["literals"]
  | "ContractDefinition" => some ["abstract", "baseContracts", "canonicalName", "contractDependencies",
      "contractKind", "documentation", "fullyImplemented", "linearizedBaseContracts", "name", "nameLocation",
      "nodes", "scope", "usedErrors", "usedEvents", "storageLayout"]
  | "StructuredDocumentation" => some ["text"]
  | "VariableDeclaration" => some ["constant", "functionSelector", "mutability", "name", "nameLocation", "scope",
      "stateVariable", "storageLocation", "typeDescriptions", "typeName", "visibility", "value"]
  | "ElementaryTypeName" => some ["name", "stateMutability", "typeDescriptions"]
  | "Mapping" => some ["keyName", "keyNameLocation", "keyType", "typeDescriptions", "valueName",
      "valueNameLocation", "valueType"]
  | "ErrorDefinition" => some ["errorSelector", "name", "nameLocation", "parameters"]
  | "FunctionDefinition" => some ["body", "functionSelector", "implemented", "kind", "modifiers", "name",
      "nameLocation", "parameters", "returnParameters", "scope", "stateMutability", "virtual", "visibility",
      "documentation", "overrides", "baseFunctions"]
  | "InheritanceSpecifier" => some ["baseName", "arguments"]
  | "IdentifierPath" => some ["name", "nameLocations", "referencedDeclaration"]
  | "OverrideSpecifier" => some ["overrides"]
  | "ParameterList" => some ["parameters"]
  | "Block" => some ["statements"]
  | "ExpressionStatement" => some ["expression"]
  | "Assignment" => some (expressionFields ++ ["leftHandSide", "operator", "rightHandSide"])
  | "BinaryOperation" => some (expressionFields ++ ["commonType", "leftExpression", "operator", "rightExpression", "function"])
  | "Identifier" => some ["argumentTypes", "name", "overloadedDeclarations", "referencedDeclaration", "typeDescriptions"]
  | "MemberAccess" => some (expressionFields ++ ["expression", "memberLocation", "memberName",
      "referencedDeclaration", "argumentTypes"])
  | "IndexAccess" => some (expressionFields ++ ["baseExpression", "indexExpression"])
  | "Literal" => some (expressionFields ++ ["hexValue", "kind", "subdenomination", "value"])
  | "FunctionCall" => some (expressionFields ++ ["arguments", "expression", "kind", "nameLocations", "names", "tryCall"])
  | "VariableDeclarationStatement" => some ["assignments", "declarations", "initialValue"]
  | "IfStatement" => some ["condition", "trueBody", "falseBody"]
  | "RevertStatement" => some ["errorCall"]
  | "Return" => some ["expression", "functionReturnParameters"]
  | _ => none

private def requiredNodeFields : String → List String
  | "SourceUnit" => ["absolutePath", "exportedSymbols", "license", "nodes"]
  | "PragmaDirective" => ["literals"]
  | "ContractDefinition" => ["abstract", "baseContracts", "canonicalName", "contractDependencies",
      "contractKind", "fullyImplemented", "linearizedBaseContracts", "name", "nameLocation", "nodes",
      "scope", "usedErrors", "usedEvents"]
  | "StructuredDocumentation" => ["text"]
  | "VariableDeclaration" => ["constant", "mutability", "name", "nameLocation", "scope", "stateVariable",
      "storageLocation", "typeDescriptions", "typeName", "visibility"]
  | "ElementaryTypeName" => ["name", "typeDescriptions"]
  | "Mapping" => ["keyName", "keyNameLocation", "keyType", "typeDescriptions", "valueName",
      "valueNameLocation", "valueType"]
  | "ErrorDefinition" => ["errorSelector", "name", "nameLocation", "parameters"]
  | "FunctionDefinition" => ["implemented", "kind", "modifiers", "name",
      "nameLocation", "parameters", "returnParameters", "scope", "stateMutability", "virtual", "visibility"]
  | "InheritanceSpecifier" => ["baseName"]
  | "IdentifierPath" => ["name", "nameLocations", "referencedDeclaration"]
  | "OverrideSpecifier" => ["overrides"]
  | "ParameterList" => ["parameters"]
  | "Block" => ["statements"]
  | "ExpressionStatement" => ["expression"]
  | "Assignment" => expressionFields ++ ["leftHandSide", "operator", "rightHandSide"]
  | "BinaryOperation" => expressionFields ++ ["commonType", "leftExpression", "operator", "rightExpression"]
  | "Identifier" => ["name", "overloadedDeclarations", "referencedDeclaration", "typeDescriptions"]
  | "MemberAccess" => expressionFields ++ ["expression", "memberLocation", "memberName", "typeDescriptions"]
  | "IndexAccess" => expressionFields ++ ["baseExpression", "indexExpression", "typeDescriptions"]
  | "Literal" => expressionFields ++ ["hexValue", "kind", "value", "typeDescriptions"]
  | "FunctionCall" => expressionFields ++ ["arguments", "expression", "kind", "nameLocations", "names",
      "tryCall", "typeDescriptions"]
  | "VariableDeclarationStatement" => ["assignments", "declarations", "initialValue"]
  | "IfStatement" => ["condition", "trueBody"]
  | "RevertStatement" => ["errorCall"]
  | "Return" => ["expression", "functionReturnParameters"]
  | _ => []

private def childFields : List String := ["nodes", "baseContracts", "parameters", "returnParameters", "body",
  "statements", "typeName", "keyType", "valueType", "modifiers", "overrides", "storageLayout", "leftHandSide",
  "rightHandSide", "leftExpression", "rightExpression", "expression", "baseExpression", "indexExpression",
  "arguments", "declarations", "initialValue", "condition", "trueBody", "falseBody", "errorCall", "baseName"]

private def validateTypeDescription (j : Json) : MetaM Unit := do
  requireKeys j ["typeIdentifier", "typeString"] "type description"
  let _ ← str (← field j "typeIdentifier")
  let _ ← str (← field j "typeString")

private def validateStringArray (j : Json) : MetaM Unit := do
  for value in ← arr j do let _ ← str value

private def validateNatArray (j : Json) : MetaM Unit := do
  for value in ← arr j do let _ ← nat value

private def validateAssignments (j : Json) : MetaM Unit := do
  for value in ← arr j do unless value.isNull do let _ ← nat value

private def validateExportedSymbols (j : Json) : MetaM Unit := do
  match j with
  | .obj entries => for (_, ids) in entries.toList do validateNatArray ids
  | _ => throwError "expected exported-symbol object"

private def validateMetadataField (ctx : SourceContext) (node : Json) (kind key : String) (value : Json) : MetaM Unit := do
  if ["absolutePath", "canonicalName", "contractKind", "text", "mutability", "name",
      "nameLocation", "scope", "storageLocation", "visibility", "stateMutability", "keyName",
      "keyNameLocation", "valueName", "valueNameLocation", "errorSelector", "kind", "operator",
      "memberLocation", "memberName", "hexValue", "value"].contains key then
    if key == "scope" then let _ ← nat value
    else let _ ← str value
  else if ["abstract", "fullyImplemented", "constant", "stateVariable", "indexed", "implemented",
      "virtual", "isConstant", "isLValue", "isPure", "lValueRequested", "tryCall"].contains key then
    let _ ← bool value
  else if key == "referencedDeclaration" then
    unless value.isNull do let _ ← int value
  else if key == "functionReturnParameters" then
    let _ ← nat value
  else if ["contractDependencies", "linearizedBaseContracts", "usedErrors", "usedEvents",
      "baseFunctions", "overloadedDeclarations"].contains key then
    validateNatArray value
  else if ["literals", "nameLocations", "names"].contains key then
    validateStringArray value
  else if key == "assignments" then validateAssignments value
  else if key == "exportedSymbols" then validateExportedSymbols value
  else if ["license", "functionSelector", "subdenomination"].contains key then
    unless value.isNull do let _ ← str value
  else
    failAt ctx node ("unvalidated AST metadata field " ++ kind ++ "." ++ key)

private partial def validateNode (ctx : SourceContext) (j : Json) : MetaM Unit := do
  let kind ← nodeKind j
  let some allowed := allowedNodeFields kind | failAt ctx j "unsupported AST node"
  let keys ← objKeys j
  needAt ctx j (keys.all fun key => commonFields.contains key || allowed.contains key)
    ("unexpected AST fields: " ++ String.intercalate ", " (keys.filter fun k => !(commonFields.contains k || allowed.contains k)))
  let missing := (requiredNodeFields kind).filter fun key => !(keys.contains key)
  needAt ctx j missing.isEmpty ("missing AST fields: " ++ String.intercalate ", " missing)
  let _ ← nodeId j
  let (start, size, sourceId) ← parseSpan j
  needAt ctx j (sourceId == ctx.sourceId && start <= ctx.bytes.size && size <= ctx.bytes.size - start)
    "source span outside registered source"
  if let some description := field? j "typeDescriptions" then
    validateTypeDescription description
  if let some common := field? j "commonType" then
    unless common.isNull do validateTypeDescription common
  if let some arguments := field? j "argumentTypes" then
    unless arguments.isNull do
      for description in ← arr arguments do validateTypeDescription description
  if let some documentation := field? j "documentation" then
    if documentation.isNull then pure ()
    else match documentation with
      | .str _ => pure ()
      | .obj _ =>
          needAt ctx j ((← nodeKind documentation) == "StructuredDocumentation") "invalid documentation"
          validateNode ctx documentation
      | _ => failAt ctx j "invalid documentation"
  for key in keys do
    unless commonFields.contains key || childFields.contains key ||
        ["typeDescriptions", "commonType", "argumentTypes", "documentation"].contains key ||
        (kind == "VariableDeclaration" && key == "value") do
      try validateMetadataField ctx j kind key (← field j key)
      catch _ => failAt ctx j ("invalid AST metadata field " ++ kind ++ "." ++ key)
  if kind == "ContractDefinition" then
    needAt ctx j ((field? j "storageLayout").all Json.isNull) "contract layout at specifier unsupported"
  if kind == "VariableDeclaration" then
    needAt ctx j ((field? j "value").all Json.isNull && (field? j "overrides").all Json.isNull)
      "initializer/override unsupported"
  if kind == "BinaryOperation" then
    needAt ctx j ((field? j "function").all Json.isNull) "user-defined operator unsupported"
  if kind == "FunctionCall" then
    needAt ctx j ((← str (← field j "kind")) == "functionCall" && !(← bool (← field j "tryCall")) &&
      (← arr (← field j "names")).isEmpty) "unsupported call surface"
  for key in childFields do
    if let some value := field? j key then
      if key == "storageLayout" && kind == "ContractDefinition" then pure ()
      else if value.isNull then pure ()
      else match value with
        | .arr values => for child in values do validateNode ctx child
        | .obj _ => validateNode ctx value
        | _ => failAt ctx j ("invalid AST child: " ++ key)
  let requireKind (key : String) (kinds : List String) : MetaM Unit := do
    let child ← field j key
    needAt ctx j (kinds.contains (← nodeKind child)) ("unexpected child kind: " ++ key)
  match kind with
  | "SourceUnit" =>
      let _ ← arr (← field j "nodes")
  | "ContractDefinition" =>
      let _ ← arr (← field j "nodes"); let _ ← arr (← field j "baseContracts")
  | "InheritanceSpecifier" =>
      requireKind "baseName" ["IdentifierPath"]
      if let some arguments := field? j "arguments" then
        needAt ctx j ((← arr arguments).isEmpty) "constructor arguments unsupported"
  | "OverrideSpecifier" =>
      let _ ← arr (← field j "overrides")
  | "FunctionDefinition" =>
      match field? j "body" with
      | none =>
          needAt ctx j (!(← bool (← field j "implemented")) && (← bool (← field j "virtual")))
            "unimplemented function must be virtual"
      | some body =>
          if body.isNull then
            needAt ctx j (!(← bool (← field j "implemented")) && (← bool (← field j "virtual")))
              "unimplemented function must be virtual"
          else requireKind "body" ["Block"]
      requireKind "parameters" ["ParameterList"]
      requireKind "returnParameters" ["ParameterList"]
      let _ ← arr (← field j "modifiers")
  | "ParameterList" =>
      for p in (← arr (← field j "parameters")) do
        needAt ctx j ((← nodeKind p) == "VariableDeclaration") "invalid parameter declaration"
  | "Block" => let _ ← arr (← field j "statements")
  | "VariableDeclaration" => requireKind "typeName" ["ElementaryTypeName", "Mapping"]
  | "Mapping" => requireKind "keyType" ["ElementaryTypeName"]; requireKind "valueType" ["ElementaryTypeName"]
  | "ExpressionStatement" => let _ ← field j "expression"
  | "Assignment" => let _ ← field j "leftHandSide"; let _ ← field j "rightHandSide"
  | "BinaryOperation" => let _ ← field j "leftExpression"; let _ ← field j "rightExpression"
  | "MemberAccess" => let _ ← field j "expression"
  | "IndexAccess" => let _ ← field j "baseExpression"; let _ ← field j "indexExpression"
  | "FunctionCall" => let _ ← field j "expression"; let _ ← arr (← field j "arguments")
  | "VariableDeclarationStatement" =>
      for d in (← arr (← field j "declarations")) do
        needAt ctx j ((← nodeKind d) == "VariableDeclaration") "invalid local declaration"
      let _ ← field j "initialValue"
  | "IfStatement" => requireKind "trueBody" ["Block"]
  | "RevertStatement" => requireKind "errorCall" ["FunctionCall"]
  | "Return" => let _ ← field j "expression"
  | "ErrorDefinition" => requireKind "parameters" ["ParameterList"]
  | _ => pure ()

private structure FieldInfo where
  id : Nat
  var : String
  name : String
  getter : Option String
  slot : Nat
  sty : Sol.StorageTy

private structure OpaqueField where
  id : Nat
  label : String
  slot : Nat
  typeLabel : String

private structure FnInfo where
  id : Nat
  contractId : Nat
  contractName : String
  name : String
  visibility : String
  mutability : String
  virtual : Bool
  implemented : Bool
  isTarget : Bool
  paramTys : List Sol.Ty
  paramIds : List (Nat × Sol.Ty × String)
  rets : List Sol.Ty
  namedReturn : Option (Nat × String)
  node : Json

private def FnInfo.sig (f : FnInfo) : Sol.Sig := ⟨f.paramTys.reverse, f.rets⟩

private def FnInfo.leanIdent (f : FnInfo) : String :=
  if f.isTarget && (f.visibility == "public" || f.visibility == "external") then f.name
  else f.contractName ++ "_" ++ f.name

private def FnInfo.isEntry (f : FnInfo) : Bool :=
  f.implemented && (f.visibility == "public" || f.visibility == "external")

/-- `view`/`pure` may appear in expression position. Nonpayable internals are
statement-only (`Stmt.callStmt`): pinned solc 0.8.x legacy codegen evaluates
an effectful call before the other operand / `+=` old-read. -/
private def FnInfo.viewOrPure (f : FnInfo) : Bool :=
  f.mutability == "view" || f.mutability == "pure"

private structure Frontend where
  source : SourceContext
  ast : Json
  targetName : String
  targetId : Nat
  linearization : List Nat
  contractById : List (Nat × String × Json)
  fields : List FieldInfo
  opaqueEntries : List OpaqueField
  errors : List (Nat × String)
  allFns : List FnInfo
  functions : List FnInfo
  digest : String

private def validName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && (c.isAlpha || cs.any (·.isAlpha)) &&
      cs.all (fun c => c.isAlphanum || c == '_') &&
      !["sourceDigest", "Storage", "view", "step", "opaqueFields", "registeredSources"].contains name

private def identifier (ctx : SourceContext) (j : Json) : MetaM String := do
  let name ← str (← field j "name")
  needAt ctx j (validName name) "unsupported/reserved name"
  pure name

private def typeString (j : Json) : MetaM String :=
  field j "typeDescriptions" >>= (field · "typeString") >>= str

private def parseValueTy (ctx : SourceContext) (j : Json) : MetaM Sol.Ty := do
  let typ ← typeString j
  match typ with
  | "uint256" => pure .uint
  | "address" => pure .addr
  | _ => failAt ctx j "unsupported value type"

private def parseFnInfo (ctx : SourceContext) (contractId : Nat) (contractName : String)
    (isTarget : Bool) (node : Json) : MetaM FnInfo := do
  let name ← identifier ctx node
  let mutability ← str (← field node "stateMutability")
  needAt ctx node ((← str (← field node "kind")) == "function" &&
    (← arr (← field node "modifiers")).isEmpty &&
    ["internal", "public", "external", "private"].contains (← str (← field node "visibility")) &&
    ["nonpayable", "view", "pure"].contains mutability)
    "unsupported function surface"
  let implemented ← bool (← field node "implemented")
  let virt ← bool (← field node "virtual")
  if implemented then
    needAt ctx node ((field? node "body").any fun b => !b.isNull) "implemented function missing body"
  else
    needAt ctx node virt "unimplemented function must be virtual"
  let mut paramTys : List Sol.Ty := []
  let mut paramIds : List (Nat × Sol.Ty × String) := []
  for p in (← arr (← field (← field node "parameters") "parameters")) do
    needAt ctx node (!(← bool (← field p "stateVariable")) &&
      !(← bool (← field p "constant")) &&
      (← str (← field p "mutability")) == "mutable" &&
      (← str (← field p "storageLocation")) == "default" &&
      (← str (← field p "visibility")) == "internal" &&
      (field? p "value").all Json.isNull) "unsupported parameter declaration"
    let ty ← parseValueTy ctx p
    let pname ← identifier ctx p
    paramTys := paramTys ++ [ty]
    paramIds := paramIds ++ [(← nodeId p, ty, pname)]
  let rs ← arr (← field (← field node "returnParameters") "parameters")
  needAt ctx node (rs.size <= 1) "unsupported signature"
  let mut rets : List Sol.Ty := []
  let mut namedReturn : Option (Nat × String) := none
  for r in rs do
    needAt ctx node (!(← bool (← field r "stateVariable")) &&
      !(← bool (← field r "constant")) &&
      (← str (← field r "mutability")) == "mutable" &&
      (← str (← field r "storageLocation")) == "default" &&
      (← str (← field r "visibility")) == "internal" &&
      (field? r "value").all Json.isNull) "unsupported parameter declaration"
    needAt ctx node ((← typeString r) == "uint256") "unsupported return type"
    rets := [.uint]
    let rname ← str (← field r "name")
    if !rname.isEmpty then
      needAt ctx node (validName rname) "unsupported/reserved name"
      namedReturn := some (← nodeId r, rname)
  pure {
    id := ← nodeId node, contractId, contractName, name,
    visibility := ← str (← field node "visibility"),
    mutability, virtual := virt, implemented, isTarget, paramTys, paramIds, rets, namedReturn, node
  }

set_option maxRecDepth 2048 in
private def parseCompilerOutput (sourcePath : System.FilePath) (logicalPath : String)
    (raw : ByteArray) (outputText importerText : String) (targetName? : Option String) :
    MetaM Frontend := do
  let output ← match Json.parse outputText with
    | .ok j => pure j
    | .error e => throwError "invalid solc standard JSON: {e}"
  requireKeys output ["contracts", "sources", "errors"] "solc output"
  if let some errors := field? output "errors" then
    for e in (← arr errors) do
      -- Compiler diagnostics may grow extra locator fields; only the fields we
      -- read are required. Unknown *AST* fields still fail closed.
      let keys ← objKeys e
      for need in ["formattedMessage", "message", "severity"] do
        unless keys.contains need do throwError "missing compiler diagnostic field {need}"
      if (← str (← field e "severity")) == "error" then
        throwError "{← str (← field e "formattedMessage")}"
  let sources ← field output "sources"
  let sourceKeys ← objKeys sources
  expect (sourceKeys == [logicalPath]) "unexpected compiler sources"
  let sourceOut ← field sources logicalPath
  requireKeys sourceOut ["ast", "id"] "source output"
  let sourceId ← nat (← field sourceOut "id")
  let ast ← field sourceOut "ast"
  let ctx := { path := sourcePath, logicalPath, bytes := raw, sourceId }
  needAt ctx ast ((← nodeKind ast) == "SourceUnit") "root must be SourceUnit"
  validateNode ctx ast
  needAt ctx ast ((← str (← field ast "absolutePath")) == logicalPath)
    "source-unit path mismatch"
  let ids ← collectAstIds ast
  needAt ctx ast (ids.length == ids.eraseDups.length) "duplicate Solidity AST node ID"
  let mut contracts : List Json := []
  for node in (← arr (← field ast "nodes")) do
    match ← nodeKind node with
    | "PragmaDirective" =>
      let literals ← arr (← field node "literals")
      needAt ctx node (literals.size == 4 && (← str literals[0]!) == "solidity" &&
        (← str literals[1]!) == "^" && (← str literals[2]!) == "0.8" &&
        (← str literals[3]!) == ".33") "unsupported pragma"
    | "ContractDefinition" => contracts := contracts ++ [node]
    | _ => failAt ctx node "unsupported source declaration"
  needAt ctx ast (!contracts.isEmpty) "exactly one concrete contract required"
  let mut concrete : List Json := []
  for c in contracts do
    unless (← bool (← field c "abstract")) do concrete := concrete ++ [c]
  let target ← match targetName? with
    | none =>
      needAt ctx ast (concrete.length == 1) "exactly one concrete contract required"
      pure concrete.head!
    | some name =>
      let some c := contracts.find? fun n => (field? n "name").bind (·.getStr?.toOption) == some name
        | throwError "unknown contract {name}"
      needAt ctx c (!(← bool (← field c "abstract")) && (← bool (← field c "fullyImplemented")))
        "target contract must be fully implemented"
      pure c
  let targetId ← nodeId target
  let targetName ← str (← field target "name")
  needAt ctx target ((← str (← field target "contractKind")) == "contract" &&
    !(← bool (← field target "abstract")) && (← bool (← field target "fullyImplemented")) &&
    (← arr (← field target "usedEvents")).isEmpty)
    "inheritance/abstract contract unsupported"
  let mut contractById : List (Nat × String × Json) := []
  let mut contractIds : List Nat := []
  for c in contracts do
    needAt ctx c ((← str (← field c "contractKind")) == "contract") "unsupported contract kind"
    needAt ctx c ((← str (← field c "canonicalName")) == (← str (← field c "name")) &&
      (← nat (← field c "scope")) == (← nodeId ast)) "contract identity mismatch"
    let cid ← nodeId c
    contractById := contractById ++ [(cid, ← str (← field c "name"), c)]
    contractIds := contractIds ++ [cid]
  for c in contracts do
    for dep in (← arr (← field c "contractDependencies")) do
      needAt ctx c (contractIds.contains (← nat dep)) "is referencing a contract from another file"
    for b in (← arr (← field c "baseContracts")) do
      let baseName ← field b "baseName"
      let rid ← int (← field baseName "referencedDeclaration")
      needAt ctx b (rid >= 0 && contractIds.contains rid.toNat)
        "is referencing a contract from another file"
  let linearized ← arr (← field target "linearizedBaseContracts")
  needAt ctx target (linearized.size >= 1 && (← nat linearized[0]!) == targetId)
    "invalid contract linearization"
  let mut linearization : List Nat := []
  for idj in linearized do
    let id ← nat idj
    needAt ctx target (contractIds.contains id) "invalid contract linearization"
    linearization := linearization ++ [id]
  let exports ← field ast "exportedSymbols"
  needAt ctx ast ((← objKeys exports).contains targetName) "exported symbol mismatch"
  let exportedIds ← arr (← field exports targetName)
  needAt ctx ast (exportedIds.any fun id => (id.getNat?.toOption == some targetId))
    "exported symbol mismatch"
  let compilerContracts ← field output "contracts"
  expect ((← objKeys compilerContracts) == [logicalPath]) "unexpected compiler contract sources"
  let sourceContracts ← field compilerContracts logicalPath
  expect ((← objKeys sourceContracts).contains targetName) "unexpected compiler contracts"
  let contractOut ← field sourceContracts targetName
  requireKeys contractOut ["storageLayout"] "contract output"
  let layout ← field contractOut "storageLayout"
  requireKeys layout ["storage", "types"] "storage layout"
  let storage ← arr (← field layout "storage")
  let layoutTypes ← field layout "types"
  let mut fields : List FieldInfo := []
  let mut opaqueEntries : List OpaqueField := []
  let mut errors : List (Nat × String) := []
  let mut allFns : List FnInfo := []
  for cid in linearization do
    let some (_, cname, cnode) := contractById.find? (·.1 == cid)
      | failAt ctx target "invalid contract linearization"
    for node in (← arr (← field cnode "nodes")) do
      match ← nodeKind node with
      | "VariableDeclaration" =>
          needAt ctx node ((← bool (← field node "stateVariable")) &&
            !(← bool (← field node "constant")) &&
            (← str (← field node "mutability")) == "mutable" &&
            (field? node "value").all Json.isNull &&
            (← str (← field node "storageLocation")) == "default" &&
            (← nat (← field node "scope")) == cid) "initializer/constant/transient field unsupported"
          let id ← nodeId node
          let some entry := storage.find? fun e => (field? e "astId").bind (·.getNat?.toOption) == some id
            | failAt ctx node "missing storage layout"
          requireKeys entry ["astId", "contract", "label", "offset", "slot", "type"] "storage entry"
          let label ← str (← field entry "label")
          needAt ctx node ((← str (← field entry "contract")) == s!"{logicalPath}:{targetName}" &&
            (← str (← field node "name")) == label) "storage declaration mismatch"
          needAt ctx node ((← nat (← field entry "offset")) == 0) "missing/packed layout"
          let typ ← typeString node
          let typeId ← str (← field entry "type")
          let layoutType ← field layoutTypes typeId
          let slotText ← str (← field entry "slot")
          let some slot := slotText.toNat? | failAt ctx node "invalid storage slot"
          if typ == "uint256" || typ == "mapping(address => uint256)" || typ == "address" then
            let name ← identifier ctx node
            let sty : Sol.StorageTy :=
              if typ == "mapping(address => uint256)" then .mapping
              else if typ == "address" then .addr else .scalar
            let expectedTypeKeys :=
              if sty == .mapping then ["encoding", "key", "label", "numberOfBytes", "value"]
              else ["encoding", "label", "numberOfBytes"]
            requireKeys layoutType expectedTypeKeys "storage type"
            match sty with
            | .scalar =>
                needAt ctx node ((← str (← field layoutType "numberOfBytes")) == "32" &&
                  (← str (← field layoutType "encoding")) == "inplace" &&
                  (← str (← field layoutType "label")) == "uint256") "bad scalar layout"
            | .addr =>
                needAt ctx node ((← str (← field layoutType "numberOfBytes")) == "20" &&
                  (← str (← field layoutType "encoding")) == "inplace" &&
                  (← str (← field layoutType "label")) == "address") "bad scalar layout"
            | .mapping =>
                needAt ctx node ((← str (← field layoutType "numberOfBytes")) == "32") "nonword layout"
                let keyType ← field layoutTypes (← str (← field layoutType "key"))
                let valueType ← field layoutTypes (← str (← field layoutType "value"))
                requireKeys keyType ["encoding", "label", "numberOfBytes"] "mapping key type"
                requireKeys valueType ["encoding", "label", "numberOfBytes"] "mapping value type"
                needAt ctx node ((← str (← field layoutType "encoding")) == "mapping" &&
                  (← str (← field keyType "encoding")) == "inplace" &&
                  (← str (← field keyType "label")) == "address" &&
                  (← str (← field keyType "numberOfBytes")) == "20" &&
                  (← str (← field valueType "encoding")) == "inplace" &&
                  (← str (← field valueType "label")) == "uint256" &&
                  (← str (← field valueType "numberOfBytes")) == "32") "bad mapping layout"
            let vis ← str (← field node "visibility")
            let getter := if vis == "public" then some name else none
            fields := fields ++ [FieldInfo.mk id name (name ++ "Slot") getter slot sty]
          else
            let vis ← str (← field node "visibility")
            needAt ctx node (vis != "public") "opaque public getter unsupported"
            let typeLabel ← str (← field layoutType "label")
            opaqueEntries := opaqueEntries ++ [OpaqueField.mk id label slot typeLabel]
      | "ErrorDefinition" =>
          let ps ← arr (← field (← field node "parameters") "parameters")
          needAt ctx node ps.isEmpty "only zero-argument custom errors"
          errors := errors ++ [((← nodeId node), (← identifier ctx node))]
      | "FunctionDefinition" =>
          needAt ctx node ((← nat (← field node "scope")) == cid) "function scope mismatch"
          allFns := allFns ++ [← parseFnInfo ctx cid cname (cid == targetId) node]
      | _ => failAt ctx node "unsupported contract declaration"
  needAt ctx target (storage.size == fields.length + opaqueEntries.length &&
    storage.all fun e => (field? e "astId").bind (·.getNat?.toOption) |>.any fun id =>
      fields.any (·.id == id) || opaqueEntries.any (·.id == id)) "unaccounted layout field"
  let names := fields.flatMap fun f => f.name :: f.getter.toList
  needAt ctx target (names.length == names.eraseDups.length) "storage/generated name collision"
  let slots := (fields.map (·.slot)) ++ (opaqueEntries.map (·.slot))
  needAt ctx target (slots.length == slots.eraseDups.length) "storage slot collision"
  let mut usedErrorIds : List Nat := []
  for cid in linearization do
    let some (_, _, cnode) := contractById.find? (·.1 == cid) | failAt ctx target "invalid contract linearization"
    for errorId in (← arr (← field cnode "usedErrors")) do
      usedErrorIds := usedErrorIds ++ [← nat errorId]
  needAt ctx target (usedErrorIds.all fun id => errors.any (·.1 == id)) "custom error reference mismatch"
  for f in allFns do
    for g in allFns do
      needAt ctx f.node (!(f.name == g.name && f.paramTys != g.paramTys))
        "function overloading by parameter type unsupported"
  let functions := allFns.filter (·.implemented)
  let sourceText := String.fromUTF8? raw |>.getD ""
  let digest := sha256Hex (sourceText ++ outputText ++ importerText ++ solcVersionPin).toUTF8
  pure {
    source := ctx, ast, targetName, targetId, linearization, contractById,
    fields, opaqueEntries, errors, allFns, functions, digest
  }

private def uint := mkConst ``Verity.Core.Uint256
private def address := mkConst ``Verity.Core.Address

private def register (name : Name) (value : Expr) (type? : Option Expr := none)
    (simp : Bool := true) : MetaM Unit := do
  if (← getEnv).contains name then throwError "declaration collision: {name}"
  let value ← instantiateMVars value
  let type ← instantiateMVars (← type?.getDM (inferType value))
  if value.hasMVar || value.hasFVar || type.hasMVar || type.hasFVar then
    throwError "unclosed imported declaration {name}"
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
    (forceExpose := true)
  compileDecls #[name] (logErrors := false)
  if simp then
    let some ext ← getSimpExtension? `solidity_import
      | throwError "solidity_import simp set is not registered"
    ext.add (SimpEntry.toUnfold name) AttributeKind.global

private def requireType (frontend : Frontend) (j : Json) (expected : String) : MetaM Unit := do
  let actual ← typeString j
  let identifier ← str (← field (← field j "typeDescriptions") "typeIdentifier")
  let expectedIdentifier := match expected with
    | "uint256" => "t_uint256"
    | "address" => "t_address"
    | "mapping(address => uint256)" => "t_mapping$_t_address_$_t_uint256_$"
    | "msg" => "t_magic_message"
    | "bool" => "t_bool"
    | "tuple()" => "t_tuple$__$"
    | _ => ""
  needAt frontend.source j (actual == expected && identifier == expectedIdentifier) ("expected " ++ expected)

private def valueType : Sol.Ty → Expr
  | .uint => uint
  | .addr => address

private def typeName : Sol.Ty → String
  | .uint => "uint256"
  | .addr => "address"

private def resultType : List Sol.Ty → Expr
  | [] => mkConst ``Unit
  | [t] => valueType t
  | _ => mkConst ``Unit

private def layoutOf (fields : List FieldInfo) : Sol.Layout := fields.map (·.sty)

private def fieldIndex (fields : List FieldInfo) (id : Nat) : Option Nat :=
  go fields 0
where
  go : List FieldInfo → Nat → Option Nat
    | [], _ => none
    | f :: fs, i => if f.id == id then some i else go fs (i + 1)

private def svar (frontend : Frontend) (L : Sol.Layout) (id : Nat) (s : Sol.StorageTy)
    (j : Json) : MetaM (Sol.SVar L s) := do
  let some i := fieldIndex frontend.fields id | failAt frontend.source j "unresolved declaration id"
  let some entry := Sol.SVar.ofIndex L i | failAt frontend.source j "unresolved declaration id"
  if h : entry.1 = s then pure (h ▸ entry.2) else failAt frontend.source j "storage type mismatch"

private structure Scope (Γ : Sol.Ctx) where
  vars : List (Nat × Σ t, Sol.Var Γ t)

private def Scope.push (sc : Scope Γ) (id : Nat) (t : Sol.Ty) : Scope (t :: Γ) :=
  ⟨(id, ⟨t, .here⟩) :: sc.vars.map fun v => (v.1, ⟨v.2.1, .there v.2.2⟩)⟩

private def Scope.find? (sc : Scope Γ) (id : Nat) : Option (Σ t, Sol.Var Γ t) :=
  (sc.vars.find? fun v => v.1 == id).map (·.2)

private def varHandles : (Γ : Sol.Ctx) → List (Σ t, Sol.Var Γ t)
  | [] => []
  | t :: ts => ⟨t, .here⟩ :: (varHandles ts).map fun v => ⟨v.1, .there v.2⟩

private def scopeOf (params : List (Nat × Sol.Ty × String)) (Γ : Sol.Ctx) : Scope Γ :=
  ⟨(varHandles Γ).zip params.reverse |>.map fun entry => (entry.2.1, entry.1)⟩

private def slotsTerm : (handles : List (Sol.StorageTy × Expr)) → MetaM Expr
  | [] => pure (mkConst ``Sol.Slots.nil)
  | (st, h) :: rest => do
      let restE ← slotsTerm rest
      let tail : Sol.Layout := rest.map (·.1)
      mkAppOptM ``Sol.Slots.cons #[some (toExpr tail), some (toExpr st), some h, some restE]

private def envTerm : (xs : List (Expr × Sol.Ty)) → MetaM Expr
  | [] => pure (mkConst ``Sol.Env.nil)
  | (x, t) :: rest => do
      let restE ← envTerm rest
      let tail : Sol.Ctx := rest.map (·.2)
      mkAppOptM ``Sol.Env.cons #[some (toExpr tail), some (toExpr t), some x, some restE]

private partial def withParams (ps : List (Nat × Sol.Ty × String)) (acc : List (Expr × Sol.Ty))
    (k : List (Expr × Sol.Ty) → MetaM Expr) : MetaM Expr := do
  match ps with
  | [] => k acc
  | p :: rest =>
      withLocalDeclD (Name.mkSimple p.2.2) (valueType p.2.1) fun x => do
        mkLambdaFVars #[x] (← withParams rest ((x, p.2.1) :: acc) k)

private def familyOf (frontend : Frontend) (name : String) (paramTys : List Sol.Ty) : List FnInfo :=
  frontend.allFns.filter fun f => f.name == name && f.paramTys == paramTys

private def mostDerived (frontend : Frontend) (name : String) (paramTys : List Sol.Ty) : Option FnInfo :=
  Id.run do
    for cid in frontend.linearization do
      if let some f := (familyOf frontend name paramTys).find? (fun g => g.contractId == cid && g.implemented) then
        return some f
    none

private def superTarget (frontend : Frontend) (definingId : Nat) (name : String)
    (paramTys : List Sol.Ty) : Option FnInfo :=
  Id.run do
    let mut seen := false
    for cid in frontend.linearization do
      if cid == definingId then seen := true
      else if seen then
        if let some f := (familyOf frontend name paramTys).find? (fun g => g.contractId == cid && g.implemented) then
          return some f
    none

private def lookupFn (frontend : Frontend) (id : Nat) : Option FnInfo :=
  frontend.allFns.find? (·.id == id)

private def isErrorRef (frontend : Frontend) (id : Nat) : Bool :=
  frontend.errors.any (·.1 == id)

private def resolveCall (frontend : Frontend) (current : FnInfo) (call : Json) : MetaM FnInfo := do
  let callee ← field call "expression"
  match ← nodeKind callee with
  | "Identifier" =>
      let rid ← int (← field callee "referencedDeclaration")
      needAt frontend.source callee (rid >= 0) "unresolved builtin identifier"
      let id := rid.toNat
      if isErrorRef frontend id then failAt frontend.source call "unsupported revert"
      let some static := lookupFn frontend id | failAt frontend.source call "unresolved function reference"
      needAt frontend.source call ((familyOf frontend static.name static.paramTys).any (·.id == id))
        "virtual dispatch disagrees with AST"
      let some resolved := mostDerived frontend static.name static.paramTys
        | failAt frontend.source call "unimplemented virtual"
      pure resolved
  | "MemberAccess" =>
      let base ← field callee "expression"
      needAt frontend.source callee ((← nodeKind base) == "Identifier" &&
        (← str (← field base "name")) == "super" &&
        (← int (← field base "referencedDeclaration")) == -25)
        "only super.f() member calls supported"
      let rid ← int (← field callee "referencedDeclaration")
      needAt frontend.source callee (rid >= 0) "unresolved super target"
      let some static := lookupFn frontend rid.toNat
        | failAt frontend.source call "unresolved function reference"
      -- solc's AST `referencedDeclaration` on `super.f` is the next override in
      -- the *defining* contract's linearization. Runtime (and this importer)
      -- use the *target* contract's C3 (`linearizedBaseContracts`), which
      -- disagrees on diamonds. Follow `superTarget`; only require the AST id
      -- to name a member of the same virtual family.
      needAt frontend.source callee
        ((familyOf frontend static.name static.paramTys).any (·.id == rid.toNat))
        "super dispatch family mismatch"
      let some resolved := superTarget frontend current.contractId static.name static.paramTys
        | failAt frontend.source call "unresolved super target"
      pure resolved
  | _ => failAt frontend.source call "unsupported call surface"

private partial def collectCallIds (frontend : Frontend) (current : FnInfo) (j : Json) :
    MetaM (List Nat) := do
  match j with
  | .obj o =>
      let walkChildren : MetaM (List Nat) := do
        let rest ← o.toList.mapM fun (_, v) => collectCallIds frontend current v
        pure rest.flatten
      match field? j "nodeType" with
      | some nt =>
          if (← str nt) == "FunctionCall" then
            let callee ← field j "expression"
            let skip ← match ← nodeKind callee with
              | "Identifier" =>
                  let rid ← int (← field callee "referencedDeclaration")
                  pure (rid >= 0 && isErrorRef frontend rid.toNat)
              | _ => pure false
            let restIds ← walkChildren
            if skip then pure restIds
            else
              let resolved ← resolveCall frontend current j
              pure (resolved.id :: restIds)
          else walkChildren
      | none => walkChildren
  | .arr xs =>
      let rest ← xs.toList.mapM (collectCallIds frontend current)
      pure rest.flatten
  | _ => pure []

private def topoSort (frontend : Frontend) : MetaM (List FnInfo) := do
  let mut deps : List (Nat × List Nat) := []
  for f in frontend.functions do
    let body := field? f.node "body" |>.getD Json.null
    let callees := (← collectCallIds frontend f body).eraseDups
    deps := deps ++ [(f.id, callees)]
  let mut remaining := frontend.functions
  let mut order : List FnInfo := []
  for _ in List.range (frontend.functions.length + 1) do
    if remaining.isEmpty then return order
    match remaining.find? fun f =>
        ((deps.find? (·.1 == f.id)).map (·.2) |>.getD []).all fun c =>
          order.any (·.id == c) with
    | some next =>
        order := order ++ [next]
        remaining := remaining.filter (fun g => g.id != next.id)
    | none =>
        failAt frontend.source frontend.ast
          s!"direct and mutual recursion unsupported ({String.intercalate ", " (remaining.map (·.leanIdent))})"
  failAt frontend.source frontend.ast "direct and mutual recursion unsupported"

private structure ParseCtx where
  frontend : Frontend
  L : Sol.Layout
  F : Sol.Fns
  registered : List FnInfo
  current : FnInfo

private def indexOfFn : List FnInfo → Nat → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, id, i => if x.id == id then some i else indexOfFn xs id (i + 1)

private def fvarOf (ctx : ParseCtx) (resolved : FnInfo) (j : Json) : MetaM (Σ σ, Sol.FVar ctx.F σ) := do
  let some idx := indexOfFn ctx.registered resolved.id 0
    | failAt ctx.frontend.source j "direct and mutual recursion unsupported"
  let some entry := Sol.FVar.ofIndex ctx.F idx
    | failAt ctx.frontend.source j "unresolved function reference"
  unless entry.1 == resolved.sig do failAt ctx.frontend.source j "function signature mismatch"
  pure entry

mutual
private partial def parseExpr (ctx : ParseCtx) {Γ : Sol.Ctx} (sc : Scope Γ) (t : Sol.Ty)
    (j : Json) : MetaM (Sol.Expr ctx.L ctx.F Γ t) := do
  match ← nodeKind j with
  | "Identifier" =>
      let rid ← int (← field j "referencedDeclaration")
      if rid < 0 then failAt ctx.frontend.source j "unresolved builtin identifier"
      let id := rid.toNat
      if let some v := sc.find? id then
        requireType ctx.frontend j (typeName v.1)
        if h : v.1 = t then pure (.var (h ▸ v.2)) else failAt ctx.frontend.source j "local type mismatch"
      else if let some info := ctx.frontend.fields.find? (·.id == id) then
        match info.sty, t with
        | .scalar, .uint =>
            requireType ctx.frontend j "uint256"
            pure (.load (← svar ctx.frontend ctx.L id .scalar j))
        | .addr, .addr =>
            requireType ctx.frontend j "address"
            pure (.loadAddr (← svar ctx.frontend ctx.L id .addr j))
        | .mapping, _ => failAt ctx.frontend.source j "mapping requires index access"
        | _, _ => failAt ctx.frontend.source j "storage type mismatch"
      else if ctx.frontend.opaqueEntries.any (·.id == id) then
        failAt ctx.frontend.source j "opaque field"
      else failAt ctx.frontend.source j "unresolved declaration reference"
  | "MemberAccess" =>
      let base ← field j "expression"
      needAt ctx.frontend.source j ((← str (← field j "memberName")) == "sender" &&
        (← nodeKind base) == "Identifier" && (← str (← field base "name")) == "msg" &&
        (← int (← field base "referencedDeclaration")) == -15 &&
        (field? j "referencedDeclaration").all fun v => v.isNull) "only builtin msg.sender supported"
      requireType ctx.frontend base "msg"
      requireType ctx.frontend j "address"
      match t with
      | .addr => pure .sender
      | .uint => failAt ctx.frontend.source j "address expression in uint256 position"
  | "IndexAccess" =>
      let base ← field j "baseExpression"
      needAt ctx.frontend.source j ((← nodeKind base) == "Identifier") "unsupported index base"
      let rid ← int (← field base "referencedDeclaration")
      if rid < 0 then failAt ctx.frontend.source j "unsupported index base"
      if ctx.frontend.opaqueEntries.any (·.id == rid.toNat) then failAt ctx.frontend.source j "opaque field"
      let some info := ctx.frontend.fields.find? (·.id == rid.toNat)
        | failAt ctx.frontend.source j "unsupported index base"
      needAt ctx.frontend.source j (info.sty == .mapping) "unsupported index base"
      requireType ctx.frontend base "mapping(address => uint256)"
      let index ← field j "indexExpression"
      requireType ctx.frontend index "address"
      requireType ctx.frontend j "uint256"
      let key ← parseExpr ctx sc .addr index
      match t with
      | .uint => pure (.index (← svar ctx.frontend ctx.L info.id .mapping j) key)
      | .addr => failAt ctx.frontend.source j "uint256 expression in address position"
  | "Literal" =>
      let value ← str (← field j "value")
      let some n := value.toNat? | failAt ctx.frontend.source j "unsupported literal"
      needAt ctx.frontend.source j ((← str (← field j "kind")) == "number" &&
        (field? j "subdenomination").all Json.isNull && n < 2^256) "unsupported literal"
      needAt ctx.frontend.source j ((← typeString j).startsWith "int_const ") "unsupported literal type"
      match t with
      | .uint => pure (.lit n)
      | .addr => failAt ctx.frontend.source j "uint256 expression in address position"
  | "BinaryOperation" =>
      let op ← str (← field j "operator")
      needAt ctx.frontend.source j (op == "+" || op == "-") "unsupported binary operation/types"
      requireType ctx.frontend j "uint256"
      let left ← field j "leftExpression"
      let right ← field j "rightExpression"
      requireType ctx.frontend left "uint256"; requireType ctx.frontend right "uint256"
      let a ← parseExpr ctx sc .uint left
      let b ← parseExpr ctx sc .uint right
      let aop : Sol.ArithOp := if op == "+" then .add else .sub
      match t with
      | .uint => pure (.arith aop a b)
      | .addr => failAt ctx.frontend.source j "uint256 expression in address position"
  | "FunctionCall" =>
      requireType ctx.frontend j (typeName t)
      let resolved ← resolveCall ctx.frontend ctx.current j
      needAt ctx.frontend.source j resolved.viewOrPure
        "effectful internal call in expression position"
      needAt ctx.frontend.source j (resolved.rets == [t]) "function does not return the expected type"
      let ⟨σ, fv⟩ ← fvarOf ctx resolved j
      let argsJ := (← arr (← field j "arguments")).toList
      let args ← parseArgs ctx sc resolved.paramTys argsJ j
      if h : σ = ⟨resolved.paramTys.reverse, [t]⟩ then
        pure (.call (h ▸ fv) args)
      else failAt ctx.frontend.source j "function signature mismatch"
  | _ => failAt ctx.frontend.source j "unsupported expression"

private partial def parseArgs (ctx : ParseCtx) {Γ : Sol.Ctx} (sc : Scope Γ) (ts : List Sol.Ty)
    (js : List Json) (origin : Json) : MetaM (Sol.Args ctx.L ctx.F Γ ts) := do
  match ts, js with
  | [], [] => pure .nil
  | t :: ts, j :: js =>
      let e ← parseExpr ctx sc t j
      let rest ← parseArgs ctx sc ts js origin
      pure (.cons e rest)
  | _, _ => failAt ctx.frontend.source origin "argument count mismatch"

private partial def parseLValue (ctx : ParseCtx) {Γ : Sol.Ctx} (sc : Scope Γ) (j : Json) :
    MetaM (Sol.LVal ctx.L ctx.F Γ) := do
  match ← nodeKind j with
  | "Identifier" =>
      let rid ← int (← field j "referencedDeclaration")
      if rid < 0 then failAt ctx.frontend.source j "unsupported storage lvalue"
      if ctx.frontend.opaqueEntries.any (·.id == rid.toNat) then failAt ctx.frontend.source j "opaque field"
      let some info := ctx.frontend.fields.find? (·.id == rid.toNat)
        | failAt ctx.frontend.source j "unsupported storage lvalue"
      needAt ctx.frontend.source j (info.sty == .scalar) "mapping requires index access"
      requireType ctx.frontend j "uint256"
      pure (.scalar (← svar ctx.frontend ctx.L info.id .scalar j))
  | "IndexAccess" =>
      let base ← field j "baseExpression"
      needAt ctx.frontend.source j ((← nodeKind base) == "Identifier") "unsupported index base"
      let rid ← int (← field base "referencedDeclaration")
      if rid < 0 then failAt ctx.frontend.source j "unsupported index base"
      if ctx.frontend.opaqueEntries.any (·.id == rid.toNat) then failAt ctx.frontend.source j "opaque field"
      let some info := ctx.frontend.fields.find? (·.id == rid.toNat)
        | failAt ctx.frontend.source j "unsupported index base"
      needAt ctx.frontend.source j (info.sty == .mapping) "unsupported index base"
      requireType ctx.frontend base "mapping(address => uint256)"
      let index ← field j "indexExpression"
      requireType ctx.frontend index "address"
      requireType ctx.frontend j "uint256"
      let key ← parseExpr ctx sc .addr index
      pure (.mapping (← svar ctx.frontend ctx.L info.id .mapping j) key)
  | _ => failAt ctx.frontend.source j "only storage assignment supported"

private partial def parseStmts (ctx : ParseCtx) {Γ : Sol.Ctx} (sc : Scope Γ) (r : Sol.Ret)
    (namedReturn : Option Nat) (nodes : List Json) : MetaM (Sol.Stmt ctx.L ctx.F Γ r) := do
  match nodes with
  | [] =>
      match r with
      | [] => pure .done
      | [t] =>
          match namedReturn with
          | some id =>
              let some v := sc.find? id | throwError "missing named return"
              if h : v.1 = t then pure (.ret (.var (h ▸ v.2)))
              else throwError "named return type mismatch"
          | none => throwError "missing terminal return"
      | _ => throwError "missing terminal return"
  | node :: rest =>
      match ← nodeKind node with
      | "ExpressionStatement" =>
          let expr ← field node "expression"
          match ← nodeKind expr with
          | "Assignment" =>
              let op ← str (← field expr "operator")
              let lhs ← field expr "leftHandSide"
              if (← nodeKind lhs) == "Identifier" then
                let rid ← int (← field lhs "referencedDeclaration")
                if rid >= 0 && ctx.frontend.opaqueEntries.any (·.id == rid.toNat) then
                  failAt ctx.frontend.source node "opaque field"
                if rid >= 0 then
                  if let some info := ctx.frontend.fields.find? (·.id == rid.toNat) then
                    if info.sty == .addr then
                      needAt ctx.frontend.source expr (op == "=") "unsupported assignment"
                      requireType ctx.frontend expr "address"
                      let rhs ← parseExpr ctx sc .addr (← field expr "rightHandSide")
                      let sv ← svar ctx.frontend ctx.L info.id .addr lhs
                      return .assignAddr sv rhs (← parseStmts ctx sc r namedReturn rest)
              requireType ctx.frontend expr "uint256"
              needAt ctx.frontend.source expr (op == "=" || op == "+=" || op == "-=") "unsupported assignment"
              let lv ← parseLValue ctx sc lhs
              let rhs ← parseExpr ctx sc .uint (← field expr "rightHandSide")
              let aop : Sol.AssignOp := if op == "=" then .set else if op == "+=" then .add else .sub
              pure (.assign lv aop rhs (← parseStmts ctx sc r namedReturn rest))
          | "FunctionCall" =>
              requireType ctx.frontend expr "tuple()"
              let resolved ← resolveCall ctx.frontend ctx.current expr
              needAt ctx.frontend.source expr resolved.rets.isEmpty "function does not return the expected type"
              let ⟨σ, fv⟩ ← fvarOf ctx resolved expr
              let argsJ := (← arr (← field expr "arguments")).toList
              let args ← parseArgs ctx sc resolved.paramTys argsJ expr
              let restS ← parseStmts ctx sc r namedReturn rest
              if h : σ = ⟨resolved.paramTys.reverse, []⟩ then
                pure (.callStmt (h ▸ fv) args restS)
              else failAt ctx.frontend.source expr "function signature mismatch"
          | _ => failAt ctx.frontend.source node "unsupported expression statement"
      | "VariableDeclarationStatement" =>
          let declarations ← arr (← field node "declarations")
          needAt ctx.frontend.source node (declarations.size == 1) "unsupported locals"
          let declaration := declarations[0]!
          needAt ctx.frontend.source declaration (!(← bool (← field declaration "stateVariable")) &&
            !(← bool (← field declaration "constant")) &&
            (← str (← field declaration "mutability")) == "mutable" &&
            (← str (← field declaration "storageLocation")) == "default" &&
            (← str (← field declaration "visibility")) == "internal") "unsupported local declaration"
          requireType ctx.frontend declaration "uint256"
          let id ← nodeId declaration
          let _ ← identifier ctx.frontend.source declaration
          let value ← parseExpr ctx sc .uint (← field node "initialValue")
          pure (.local_ value (← parseStmts ctx (sc.push id .uint) r namedReturn rest))
      | "IfStatement" =>
          let falseBody := field? node "falseBody"
          let trueBody ← field node "trueBody"
          let statements ← arr (← field trueBody "statements")
          needAt ctx.frontend.source node (falseBody.all Json.isNull && statements.size == 1 &&
            (← nodeKind statements[0]!) == "RevertStatement") "only if/revert guard supported"
          let call ← field statements[0]! "errorCall"
          let callee ← field call "expression"
          let rid ← int (← field callee "referencedDeclaration")
          let some errorName := if rid < 0 then none else ctx.frontend.errors.lookup rid.toNat
            | failAt ctx.frontend.source node "unsupported revert"
          needAt ctx.frontend.source node ((← nodeKind callee) == "Identifier" &&
            (← arr (← field call "arguments")).isEmpty) "unsupported revert"
          let condition ← field node "condition"
          needAt ctx.frontend.source condition ((← nodeKind condition) == "BinaryOperation" &&
            (← str (← field condition "operator")) == "<") "only uint256 comparison guard supported"
          requireType ctx.frontend condition "bool"
          let commonType ← field condition "commonType"
          needAt ctx.frontend.source condition ((← str (← field commonType "typeString")) == "uint256" &&
            (← str (← field commonType "typeIdentifier")) == "t_uint256") "unsupported comparison type"
          let left ← field condition "leftExpression"
          let right ← field condition "rightExpression"
          requireType ctx.frontend left "uint256"; requireType ctx.frontend right "uint256"
          let a ← parseExpr ctx sc .uint left
          let b ← parseExpr ctx sc .uint right
          pure (.guard a b (errorName ++ "()") (← parseStmts ctx sc r namedReturn rest))
      | "Return" =>
          match r with
          | [t] =>
              needAt ctx.frontend.source node rest.isEmpty "only terminal scalar return"
              let e ← parseExpr ctx sc t (← field node "expression")
              pure (.ret e)
          | _ => failAt ctx.frontend.source node "only terminal scalar return"
      | _ => failAt ctx.frontend.source node "unsupported statement"
end

private def checkCollisions (ns : Name) (frontend : Frontend) (order : List FnInfo) : MetaM Unit := do
  let mut names := #[
    ns ++ `sourceDigest, ns ++ `Storage, ns ++ `view, ns ++ `step,
    ns ++ `Storage ++ `mk, ns ++ `opaqueFields, ns ++ `registeredSources]
  for f in frontend.fields do
    names := names.push (ns ++ Name.mkSimple f.name)
    names := names.push (ns ++ `Storage ++ Name.mkSimple f.var)
    if let some getter := f.getter then names := names.push (ns ++ Name.mkSimple getter)
  for fn in order do
    names := names.push (ns ++ Name.mkSimple fn.leanIdent)
  for i in [:names.size] do
    if (← getEnv).contains names[i]! || (names.extract 0 i).contains names[i]! then
      throwError "declaration collision: {names[i]!}"

private def storageStructure (alias : Name) (frontend : Frontend) : CommandElabM Syntax := do
  let declId := mkIdent (alias ++ `Storage)
  let binders : TSyntaxArray ``Parser.Command.structExplicitBinder ←
    frontend.fields.toArray.mapM fun f => do
      let fieldId := mkIdent (Name.mkSimple f.var)
      let ty : Term ← match f.sty with
        | .mapping => `(Verity.Address → Verity.Uint256)
        | .addr => `(Verity.Address)
        | .scalar => `(Verity.Uint256)
      `(Parser.Command.structExplicitBinder| ($fieldId:ident : $ty))
  `(command| structure $declId where $binders:structExplicitBinder*)

private def mkEntryDisjunct (s s' : Expr) (name : Name) (binders : List (Name × Expr)) : MetaM Expr :=
  go binders #[]
where
  go : List (Name × Expr) → Array Expr → MetaM Expr
    | [], xs => do
        let run ← mkAppM ``Verity.Contract.run #[mkAppN (mkConst name) xs, s]
        let snd ← mkAppM ``Verity.ContractResult.snd #[run]
        mkEq s' snd
    | (n, dom) :: rest, xs =>
        withLocalDeclD n dom fun x => do
          let inner ← go rest (xs.push x)
          mkAppOptM ``Exists #[some dom, some (← mkLambdaFVars #[x] inner)]

private def envApply (σ : Sol.Sig) (fn : Expr) : MetaM Expr := do
  let envTy ← mkAppM ``Sol.Env #[toExpr σ.params]
  withLocalDeclD `env envTy fun env => do
    let mut app := fn
    let n := σ.params.length
    for i in [:n] do
      let dbIndex := n - 1 - i
      let some v := Sol.Var.ofIndex σ.params dbIndex | throwError "envApply: missing binder"
      let getter ← mkAppOptM ``Sol.Env.get
        #[some (toExpr σ.params), some (toExpr v.1), some env, some (toExpr v.2)]
      app := mkApp app getter
    mkLambdaFVars #[env] app

private def fnsTerm : (handles : List (Sol.Sig × Expr)) → MetaM Expr
  | [] => pure (mkConst ``Sol.FnEnv.nil)
  | (σ, h) :: rest => do
      let restE ← fnsTerm rest
      let apply ← envApply σ h
      let envTy ← mkAppM ``Sol.Env #[toExpr σ.params]
      let retTy ← mkAppM ``Sol.Ret.denote #[toExpr σ.rets]
      let contractTy ← mkAppM ``Verity.Contract #[retTy]
      let applyTy ← mkArrow envTy contractTy
      let apply ← mkExpectedTypeHint apply applyTy
      let tail : Sol.Fns := rest.map (·.1)
      -- `FnEnv.cons` implicits are `{F : Fns}` then `{σ : Sig}`.
      pure (mkAppN (mkConst ``Sol.FnEnv.cons) #[toExpr tail, toExpr σ, apply, restE])

private def parseBody (ctx : ParseCtx) (fn : FnInfo) : MetaM Expr := do
  let Γ : Sol.Ctx := fn.paramIds.reverse.map fun p => p.2.1
  let sc0 := scopeOf fn.paramIds Γ
  let statements :=
    match field? fn.node "body" with
    | some body => (field? body "statements").bind (·.getArr?.toOption) |>.getD #[]
    | none => #[]
  match fn.namedReturn with
  | some (id, _) =>
      let sc := sc0.push id .uint
      let inner ← parseStmts ctx sc fn.rets (some id) statements.toList
      let wrapped : Sol.Stmt ctx.L ctx.F Γ fn.rets := .local_ (.lit 0) inner
      pure (toExpr wrapped)
  | none =>
      let body ← parseStmts ctx sc0 fn.rets none statements.toList
      pure (toExpr body)

private def importFrontend (ns : Name) (frontend : Frontend) : MetaM Unit := do
  let L := layoutOf frontend.fields
  let order ← topoSort frontend
  let mut registered : List (FieldInfo × Expr) := []
  for f in frontend.fields do
    let ty ← match f.sty with
      | .mapping => mkArrow address uint
      | .addr => pure address
      | .scalar => pure uint
    let slot ← mkAppOptM ``Verity.StorageSlot.mk #[some ty, some (mkNatLit f.slot)]
    let name := ns ++ Name.mkSimple f.name
    register name slot
    registered := registered ++ [(f, mkConst name)]
  let slotsE ← slotsTerm (registered.map fun h => (h.1.sty, h.2))
  let state := mkConst ``Verity.ContractState
  let storageView := mkConst (ns ++ `Storage)
  let view ← withLocalDeclD `s state fun s => do
    let mut args : Array Expr := #[]
    for h in registered do
      let slot ← mkAppM ``Verity.StorageSlot.slot #[h.2]
      match h.1.sty with
      | .mapping =>
          let reader ← withLocalDeclD `k address fun k =>
            mkLambdaFVars #[k] (mkAppN (mkConst ``Verity.ContractState.readMap) #[s, slot, k])
          args := args.push reader
      | .addr =>
          args := args.push (mkAppN (mkConst ``Verity.ContractState.readAddrSlot) #[s, slot])
      | .scalar =>
          args := args.push (mkAppN (mkConst ``Verity.ContractState.readSlot) #[s, slot])
    mkLambdaFVars #[s] (← mkAppM (ns ++ `Storage ++ `mk) args)
  register (ns ++ `view) view (some (← mkArrow state storageView))
  let opaqueVal : List (String × Nat × String) :=
    frontend.opaqueEntries.map fun o => (o.label, o.slot, o.typeLabel)
  register (ns ++ `opaqueFields) (toExpr opaqueVal) (simp := false)
  register (ns ++ `registeredSources) (toExpr registeredSources) (simp := false)
  let mut getterEntries : Array (Name × List (Name × Expr)) := #[]
  for h in registered do
    if let some getter := h.1.getter then
      let gname := ns ++ Name.mkSimple getter
      match h.1.sty with
      | .mapping =>
          let value ← withLocalDeclD `account address fun account => do
            let getterFn ← mkAppM ``Verity.getMapping #[h.2, account]
            mkLambdaFVars #[account] (← mkAppM ``Sol.nonpayable #[getterFn])
          register gname value
          getterEntries := getterEntries.push (gname, [(`account, address)])
      | .addr =>
          let value ← mkAppM ``Sol.nonpayable #[← mkAppM ``Verity.getStorageAddr #[h.2]]
          register gname value
          getterEntries := getterEntries.push (gname, [])
      | .scalar =>
          let value ← mkAppM ``Sol.nonpayable #[← mkAppM ``Verity.getStorage #[h.2]]
          register gname value
          getterEntries := getterEntries.push (gname, [])
  let mut fnHandles : List (Sol.Sig × Expr) := []
  let mut fnInfos : List FnInfo := []
  let mut functionEntries : Array (Name × List (Name × Expr)) := #[]
  for fn in order do
    let F : Sol.Fns := fnHandles.map (·.1)
    let fnsE ← fnsTerm fnHandles
    let ctx : ParseCtx := { frontend, L, F, registered := fnInfos, current := fn }
    let Γ : Sol.Ctx := fn.paramIds.reverse.map fun p => p.2.1
    let bodyE ← parseBody ctx fn
    let meaningHead :=
      if fn.isEntry then mkConst ``Sol.Fn.meaning else mkConst ``Sol.Fn.bodyMeaning
    let value ← withParams fn.paramIds [] fun xs => do
      let envE ← envTerm xs
      pure (mkAppN meaningHead
        #[toExpr L, toExpr F, toExpr Γ, toExpr fn.rets, bodyE, slotsE, fnsE, envE])
    let mut type := ← mkAppM ``Verity.Contract #[resultType fn.rets]
    for p in fn.paramIds.reverse do
      type ← mkArrow (valueType p.2.1) type
    let fname := ns ++ Name.mkSimple fn.leanIdent
    register fname value (some type)
    let binders := fn.paramIds.map fun p => (Name.mkSimple p.2.2, valueType p.2.1)
    if fn.isEntry then
      if let some top := mostDerived frontend fn.name fn.paramTys then
        if top.id == fn.id then
          functionEntries := functionEntries.push (fname, binders)
    fnHandles := fnHandles ++ [(fn.sig, mkConst fname)]
    fnInfos := fnInfos ++ [fn]
  -- Entry-point order: target public/external in source order, then each base
  -- in linearization order, then getters in layout order.
  let mut orderedEntries : Array (Name × List (Name × Expr)) := #[]
  for cid in frontend.linearization do
    for fn in frontend.functions do
      if fn.contractId == cid && fn.isEntry then
        if let some top := mostDerived frontend fn.name fn.paramTys then
          if top.id == fn.id then
            let fname := ns ++ Name.mkSimple fn.leanIdent
            if let some entry := functionEntries.find? (·.1 == fname) then
              unless orderedEntries.any (fun e => e.1 == fname) do
                orderedEntries := orderedEntries.push entry
  let entries := orderedEntries ++ getterEntries
  let step ← withLocalDeclD `s state fun s =>
    withLocalDeclD `s' state fun s' => do
      let mut disjuncts : Array Expr := #[]
      for (ename, binders) in entries do
        disjuncts := disjuncts.push (← mkEntryDisjunct s s' ename binders)
      if disjuncts.isEmpty then throwError "imported contract has no entry points"
      let mut body := disjuncts.back!
      for i in (List.range (disjuncts.size - 1)).reverse do
        body := mkApp2 (mkConst ``Or) disjuncts[i]! body
      mkLambdaFVars #[s, s'] body
  let stepType ← mkArrow state (← mkArrow state (mkSort 0))
  register (ns ++ `step) step (some stepType) (simp := false)
  register (ns ++ `sourceDigest) (mkStrLit frontend.digest) (simp := false)

private def compileFrontend (root source : System.FilePath) (targetName? : Option String) : MetaM Frontend := do
  let canonicalRoot ← IO.FS.realPath root
  let canonicalSource ← IO.FS.realPath source
  unless canonicalSource.toString.startsWith (canonicalRoot.toString ++ "/") do
    throwError "source outside package"
  let mut matched : Option (String × String) := none
  for pair in registeredSources do
    let expected ← IO.FS.realPath (canonicalRoot / pair.2)
    if canonicalSource == expected then matched := some pair
  let some (logicalPath, _) := matched | throwError "unregistered source or source outside package"
  let compiler := canonicalRoot / ".lake/solidity-import/solc"
  verifyCompiler compiler
  let versionOut ← IO.Process.output { cmd := compiler.toString, args := #["--version"] }
  unless versionOut.exitCode == 0 &&
      acceptedSolcVersionOutputs.contains versionOut.stdout.trimAscii.toString do
    throwError "compiler version mismatch"
  verifyCompiler compiler
  let sourceBytes ← IO.FS.readBinFile canonicalSource
  let sourceText ← match String.fromUTF8? sourceBytes with
    | some text => pure text
    | none => throwError "Solidity source is not UTF-8"
  let settings := Json.mkObj [
    ("optimizer", Json.mkObj [("enabled", false)]),
    ("viaIR", false), ("evmVersion", "cancun"), ("remappings", Json.arr #[]),
    ("outputSelection", Json.mkObj [("*", Json.mkObj [
      ("", Json.arr #["ast"]), ("*", Json.arr #["storageLayout"])])])]
  let input := Json.mkObj [("language", "Solidity"),
    ("sources", Json.mkObj [(logicalPath, Json.mkObj [("content", sourceText)])]),
    ("settings", settings)]
  let output ← IO.Process.output
    { cmd := compiler.toString, args := #["--standard-json", "--no-import-callback"] }
    (some input.compress)
  unless output.exitCode == 0 do throwError "solc failed: {output.stderr}"
  verifyCompiler compiler
  let importerDir := canonicalRoot / "Contracts/VaultFromSolidity/Importer"
  let importerText ← IO.FS.readFile (importerDir / "Importer.lean")
  let syntaxText ← IO.FS.readFile (importerDir / "Syntax.lean")
  let semanticsText ← IO.FS.readFile (importerDir / "Semantics.lean")
  parseCompilerOutput canonicalSource logicalPath sourceBytes output.stdout
    (importerText ++ syntaxText ++ semanticsText) targetName?

syntax (name := solidityContract) "solidity_contract " ident " from " str : command
syntax (name := solidityContractNamed) "solidity_contract " ident " from " str " contract " str : command

private def elabSolidityContractCore (alias : Name) (rel : String) (targetName? : Option String)
    (_stx : Syntax) : CommandElabM Unit := do
  let saved ← getEnv
  try
    if debug.skipKernelTC.get (← getOptions) then throwError "kernel checking must be enabled"
    let authored ← IO.FS.realPath (← getFileName)
    let source := authored.parent.getD "." / rel
    let mut root := authored.parent.getD "."
    while !(← (root / "lakefile.lean").pathExists) do
      let some parent := root.parent | throwError "package root not found"
      if parent == root then throwError "package root not found"
      root := parent
    let frontend ← liftTermElabM <| compileFrontend root source targetName?
    let ns := (← getCurrNamespace) ++ alias
    let order ← liftTermElabM <| topoSort frontend
    liftTermElabM <| checkCollisions ns frontend order
    let storageStx ← storageStructure alias frontend
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      elabCommand storageStx
    if (← get).messages.hasErrors then
      throwError "storage view elaboration failed"
    liftTermElabM <| withOptions (Elab.async.set · false) (importFrontend ns frontend)
  catch e =>
    setEnv saved
    throw e

@[command_elab solidityContract] def elabSolidityContract : CommandElab := fun stx => do
  elabSolidityContractCore stx[1].getId stx[3].isStrLit?.get! none stx

@[command_elab solidityContractNamed] def elabSolidityContractNamed : CommandElab := fun stx => do
  elabSolidityContractCore stx[1].getId stx[3].isStrLit?.get! stx[5].isStrLit? stx

end SolidityImporter
