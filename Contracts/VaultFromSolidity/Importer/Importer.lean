import Lean
import Verity.Stdlib.Math
import Compiler.Sha256.Engine

/-!
A proof-only Solidity frontend. This module invokes pinned `solc --standard-json`,
validates a closed typed-AST/storage-layout subset, and directly registers safe,
transparent Verity definitions. It emits neither an intermediate IR nor Lean source.
-/

open Lean Meta Elab Command

namespace SolidityImporter

private def solcVersionOutput :=
  "solc, the solidity compiler commandline interface\nVersion: 0.8.33+commit.64118f21.Linux.g++"
private def solcSha256 := "1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468"
private def registeredSource := "Contracts/VaultFromSolidity/Vault.sol"

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
  let output ← IO.Process.output { cmd := "/usr/bin/sha256sum", args := #[compiler.toString] }
  unless output.exitCode == 0 && (output.stdout.take 64).toString == solcSha256 do
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
      "documentation"]
  | "ParameterList" => some ["parameters"]
  | "Block" => some ["statements"]
  | "ExpressionStatement" => some ["expression"]
  | "Assignment" => some (expressionFields ++ ["leftHandSide", "operator", "rightHandSide"])
  | "BinaryOperation" => some (expressionFields ++ ["commonType", "leftExpression", "operator", "rightExpression", "function"])
  | "Identifier" => some ["argumentTypes", "name", "overloadedDeclarations", "referencedDeclaration", "typeDescriptions"]
  | "MemberAccess" => some (expressionFields ++ ["expression", "memberLocation", "memberName"])
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
  | "FunctionDefinition" => ["body", "functionSelector", "implemented", "kind", "modifiers", "name",
      "nameLocation", "parameters", "returnParameters", "scope", "stateMutability", "virtual", "visibility"]
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
  "arguments", "declarations", "initialValue", "condition", "trueBody", "falseBody", "errorCall"]

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
    let _ ← int value
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
  | "FunctionDefinition" =>
      requireKind "body" ["Block"]
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
  name : String
  getter : Option String
  slot : Nat
  mapping : Bool

private structure Frontend where
  source : SourceContext
  ast : Json
  fields : List FieldInfo
  errors : List (Nat × String)
  functions : List Json
  digest : String

private def validName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: cs => c.isAlpha && cs.all (fun c => c.isAlphanum || c == '_') && name != "sourceDigest"

private def identifier (ctx : SourceContext) (j : Json) : MetaM String := do
  let name ← str (← field j "name")
  needAt ctx j (validName name) "unsupported/reserved name"
  pure name

private def typeString (j : Json) : MetaM String :=
  field j "typeDescriptions" >>= (field · "typeString") >>= str

set_option maxRecDepth 2048 in
private def parseCompilerOutput (sourcePath : System.FilePath) (logicalPath : String)
    (raw : ByteArray) (outputText version importerText : String) : MetaM Frontend := do
  let output ← match Json.parse outputText with
    | .ok j => pure j
    | .error e => throwError "invalid solc standard JSON: {e}"
  requireKeys output ["contracts", "sources", "errors"] "solc output"
  if let some errors := field? output "errors" then
    for e in (← arr errors) do
      requireKeys e ["component", "errorCode", "formattedMessage", "message", "severity",
        "sourceLocation", "type"] "compiler diagnostic"
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
    | "ContractDefinition" => contracts := node :: contracts
    | _ => failAt ctx node "unsupported source declaration"
  needAt ctx ast (contracts.length == 1) "exactly one concrete contract required"
  let contract := contracts.head!
  let contractId ← nodeId contract
  needAt ctx contract ((← str (← field contract "contractKind")) == "contract" &&
    !(← bool (← field contract "abstract")) && (← bool (← field contract "fullyImplemented")) &&
    (← arr (← field contract "baseContracts")).isEmpty &&
    (← arr (← field contract "contractDependencies")).isEmpty &&
    (← arr (← field contract "usedEvents")).isEmpty)
    "inheritance/abstract contract unsupported"
  let linearized ← arr (← field contract "linearizedBaseContracts")
  needAt ctx contract (linearized.size == 1 && (← nat linearized[0]!) == contractId)
    "invalid contract linearization"
  let contractName ← str (← field contract "name")
  needAt ctx contract ((← str (← field contract "canonicalName")) == contractName &&
    (← nat (← field contract "scope")) == (← nodeId ast)) "contract identity mismatch"
  let exports ← field ast "exportedSymbols"
  needAt ctx ast ((← objKeys exports) == [contractName]) "exported symbol mismatch"
  let exportedIds ← arr (← field exports contractName)
  needAt ctx ast (exportedIds.size == 1 && (← nat exportedIds[0]!) == contractId)
    "exported symbol mismatch"
  let compilerContracts ← field output "contracts"
  expect ((← objKeys compilerContracts) == [logicalPath]) "unexpected compiler contract sources"
  let sourceContracts ← field compilerContracts logicalPath
  expect ((← objKeys sourceContracts) == [contractName]) "unexpected compiler contracts"
  let contractOut ← field sourceContracts contractName
  requireKeys contractOut ["storageLayout"] "contract output"
  let layout ← field contractOut "storageLayout"
  requireKeys layout ["storage", "types"] "storage layout"
  let storage ← arr (← field layout "storage")
  let layoutTypes ← field layout "types"
  let layoutTypeKeys ← objKeys layoutTypes
  expect (layoutTypeKeys.length == 3 && layoutTypeKeys.all fun key =>
    ["t_address", "t_uint256", "t_mapping(t_address,t_uint256)"].contains key)
    "unexpected storage type table"
  let mut fields : List FieldInfo := []
  let mut errors : List (Nat × String) := []
  let mut functions : List Json := []
  for node in (← arr (← field contract "nodes")) do
    match ← nodeKind node with
    | "VariableDeclaration" =>
        let name ← identifier ctx node
        needAt ctx node ((← bool (← field node "stateVariable")) && !(← bool (← field node "constant")) &&
          (← str (← field node "mutability")) == "mutable" && (field? node "value").all Json.isNull &&
          (← str (← field node "storageLocation")) == "default" &&
          (← nat (← field node "scope")) == contractId) "initializer/constant/transient field unsupported"
        let typ ← typeString node
        needAt ctx node (typ == "uint256" || typ == "mapping(address => uint256)") "unsupported storage type"
        let id ← nodeId node
        let some entry := storage.find? fun e => (field? e "astId").bind (·.getNat?.toOption) == some id
          | failAt ctx node "missing storage layout"
        requireKeys entry ["astId", "contract", "label", "offset", "slot", "type"] "storage entry"
        needAt ctx node ((← str (← field entry "contract")) == s!"{logicalPath}:{contractName}" &&
          (← str (← field entry "label")) == name) "storage declaration mismatch"
        needAt ctx node ((← nat (← field entry "offset")) == 0) "missing/packed layout"
        let typeId ← str (← field entry "type")
        let layoutType ← field layoutTypes typeId
        let expectedTypeKeys := if typ == "uint256" then
          ["encoding", "label", "numberOfBytes"]
        else ["encoding", "key", "label", "numberOfBytes", "value"]
        requireKeys layoutType expectedTypeKeys "storage type"
        needAt ctx node ((← str (← field layoutType "numberOfBytes")) == "32") "nonword layout"
        if typ == "uint256" then
          needAt ctx node ((← str (← field layoutType "encoding")) == "inplace" &&
            (← str (← field layoutType "label")) == typ) "bad scalar layout"
        else
          let keyType ← field layoutTypes (← str (← field layoutType "key"))
          let valueType ← field layoutTypes (← str (← field layoutType "value"))
          requireKeys keyType ["encoding", "label", "numberOfBytes"] "mapping key type"
          requireKeys valueType ["encoding", "label", "numberOfBytes"] "mapping value type"
          let layoutEncoding ← str (← field layoutType "encoding")
          let keyEncoding ← str (← field keyType "encoding")
          let keyLabel ← str (← field keyType "label")
          let keyBytes ← str (← field keyType "numberOfBytes")
          let valueEncoding ← str (← field valueType "encoding")
          let valueLabel ← str (← field valueType "label")
          let valueBytes ← str (← field valueType "numberOfBytes")
          needAt ctx node (layoutEncoding == "mapping" && keyEncoding == "inplace" &&
            keyLabel == "address" && keyBytes == "20" && valueEncoding == "inplace" &&
            valueLabel == "uint256" && valueBytes == "32") "bad mapping layout"
        let getter := if (← str (← field node "visibility")) == "public" then some name else none
        let slotText ← str (← field entry "slot")
        let some slot := slotText.toNat? | failAt ctx node "invalid storage slot"
        fields := FieldInfo.mk id (name ++ "Slot") getter slot (typ.startsWith "mapping") :: fields
    | "ErrorDefinition" =>
        let ps ← arr (← field (← field node "parameters") "parameters")
        needAt ctx node ps.isEmpty "only zero-argument custom errors"
        errors := ((← nodeId node), (← identifier ctx node)) :: errors
    | "FunctionDefinition" =>
        needAt ctx node ((← nat (← field node "scope")) == contractId) "function scope mismatch"
        functions := node :: functions
    | _ => failAt ctx node "unsupported contract declaration"
  needAt ctx contract (storage.size == fields.length && storage.all fun e =>
    (field? e "astId").bind (·.getNat?.toOption) |>.any fun id => fields.any (·.id == id)) "unaccounted layout field"
  let names := fields.flatMap fun f => f.name :: f.getter.toList
  needAt ctx contract (names.length == names.eraseDups.length) "storage/generated name collision"
  let slots := fields.map (·.slot)
  needAt ctx contract (slots.length == slots.eraseDups.length) "storage slot collision"
  let usedErrors ← arr (← field contract "usedErrors")
  let mut usedErrorIds : List Nat := []
  for errorId in usedErrors do usedErrorIds := (← nat errorId) :: usedErrorIds
  let errorIds := errors.map (·.1)
  needAt ctx contract (usedErrorIds.length == errorIds.length &&
    usedErrorIds.all fun id => errorIds.contains id) "custom error reference mismatch"
  let sourceText := String.fromUTF8? raw |>.getD ""
  let digest := sha256Hex (sourceText ++ outputText ++ importerText ++ solcSha256 ++ version).toUTF8
  pure <| Frontend.mk ctx ast fields.reverse errors functions.reverse digest

private def uint := mkConst ``Verity.Core.Uint256
private def address := mkConst ``Verity.Core.Address
private def unit := mkConst ``Unit
private def valueType (s : String) : MetaM Expr :=
  match s with
  | "uint256" => pure uint
  | "address" => pure address
  | "unit" => pure unit
  | _ => throwError "unsupported type {s}"

private def ret (x : Expr) : MetaM Expr := mkAppM ``Verity.pure #[x]
private def seq (m t : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `value t fun x => do
    let next ← k x
    mkAppM ``Verity.bind #[m, ← mkLambdaFVars #[x] next]

private def register (name : Name) (value : Expr) : MetaM Unit := do
  if (← getEnv).contains name then throwError "declaration collision: {name}"
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if value.hasMVar || value.hasFVar || type.hasMVar || type.hasFVar then
    throwError "unclosed imported declaration {name}"
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
    (forceExpose := true)
  compileDecls #[name] (logErrors := false)

private abbrev Locals := List (Nat × String × Expr)
private abbrev Slots := List (Nat × Expr)

private def lookupLocal (locals : Locals) (id : Nat) : Option (String × Expr) :=
  (locals.find? fun x => x.1 == id).map fun x => (x.2.1, x.2.2)

private def lookupSlot (slots : Slots) (id : Nat) : MetaM Expr :=
  match slots.lookup id with
  | some e => pure e
  | none => throwError "unresolved declaration id {id}"

private def checked (op : String) (a b : Expr) : MetaM Expr := do
  let fn ← match op with
    | "+" | "+=" => pure ``Verity.Stdlib.Math.safeAdd
    | "-" | "-=" => pure ``Verity.Stdlib.Math.safeSub
    | _ => throwError "unsupported arithmetic {op}"
  mkAppM ``Verity.Stdlib.Math.requireSomeUint #[← mkAppM fn #[a, b], mkStrLit "Panic(0x11)"]

private def requireType (frontend : Frontend) (j : Json) (expected : String) : MetaM Unit := do
  let actual ← typeString j
  let identifier ← str (← field (← field j "typeDescriptions") "typeIdentifier")
  let expectedIdentifier := match expected with
    | "uint256" => "t_uint256"
    | "address" => "t_address"
    | "mapping(address => uint256)" => "t_mapping$_t_address_$_t_uint256_$"
    | "msg" => "t_magic_message"
    | "bool" => "t_bool"
    | _ => ""
  needAt frontend.source j (actual == expected && identifier == expectedIdentifier) ("expected " ++ expected)

private partial def translateExpr (frontend : Frontend) (slots : Slots) (locals : Locals) (j : Json)
    (k : Expr → MetaM Expr) : MetaM Expr := do
  match ← nodeKind j with
  | "Identifier" =>
      let rid ← int (← field j "referencedDeclaration")
      if rid < 0 then failAt frontend.source j "unresolved builtin identifier"
      let id := rid.toNat
      if let some (typ, value) := lookupLocal locals id then
        requireType frontend j typ
        k value
      else
        let some info := frontend.fields.find? (·.id == id)
          | failAt frontend.source j "unresolved declaration reference"
        needAt frontend.source j (!info.mapping) "mapping requires index access"
        requireType frontend j "uint256"
        seq (← mkAppM ``Verity.getStorage #[← lookupSlot slots id]) uint k
  | "MemberAccess" =>
      let base ← field j "expression"
      needAt frontend.source j ((← str (← field j "memberName")) == "sender" &&
        (← nodeKind base) == "Identifier" && (← str (← field base "name")) == "msg" &&
        (← int (← field base "referencedDeclaration")) == -15 &&
        (field? j "referencedDeclaration").all Json.isNull) "only builtin msg.sender supported"
      requireType frontend base "msg"
      requireType frontend j "address"
      seq (mkConst ``Verity.msgSender) address k
  | "IndexAccess" =>
      let base ← field j "baseExpression"
      needAt frontend.source j ((← nodeKind base) == "Identifier") "unsupported index base"
      let rid ← int (← field base "referencedDeclaration")
      let some info := if rid < 0 then none else frontend.fields.find? (·.id == rid.toNat)
        | failAt frontend.source j "unsupported index base"
      needAt frontend.source j info.mapping "unsupported index base"
      requireType frontend base "mapping(address => uint256)"
      let index ← field j "indexExpression"
      requireType frontend index "address"
      requireType frontend j "uint256"
      translateExpr frontend slots locals index fun key => do
        let slot ← lookupSlot slots info.id
        seq (← mkAppM ``Verity.getMapping #[slot, key]) uint k
  | "Literal" =>
      let value ← str (← field j "value")
      let some n := value.toNat? | failAt frontend.source j "unsupported literal"
      needAt frontend.source j ((← str (← field j "kind")) == "number" &&
        (field? j "subdenomination").all Json.isNull && n < 2^256) "unsupported literal"
      needAt frontend.source j ((← typeString j).startsWith "int_const ") "unsupported literal type"
      k (← mkAppM ``Verity.Core.Uint256.ofNat #[mkNatLit n])
  | "BinaryOperation" =>
      let op ← str (← field j "operator")
      needAt frontend.source j (op == "+" || op == "-") "unsupported binary operation/types"
      requireType frontend j "uint256"
      let left ← field j "leftExpression"
      let right ← field j "rightExpression"
      requireType frontend left "uint256"; requireType frontend right "uint256"
      translateExpr frontend slots locals left fun a => do
        translateExpr frontend slots locals right fun b => do
          seq (← checked op a b) uint k
  | _ => failAt frontend.source j "unsupported expression"

private def translateLValue (frontend : Frontend) (slots : Slots) (locals : Locals) (j : Json)
    (k : Expr → Option Expr → MetaM Expr) : MetaM Expr := do
  match ← nodeKind j with
  | "Identifier" =>
      let rid ← int (← field j "referencedDeclaration")
      let some info := if rid < 0 then none else frontend.fields.find? (·.id == rid.toNat)
        | failAt frontend.source j "unsupported storage lvalue"
      needAt frontend.source j (!info.mapping) "mapping requires index access"
      requireType frontend j "uint256"
      k (← lookupSlot slots info.id) none
  | "IndexAccess" =>
      let base ← field j "baseExpression"
      needAt frontend.source j ((← nodeKind base) == "Identifier") "unsupported index base"
      let rid ← int (← field base "referencedDeclaration")
      let some info := if rid < 0 then none else frontend.fields.find? (·.id == rid.toNat)
        | failAt frontend.source j "unsupported index base"
      needAt frontend.source j info.mapping "unsupported index base"
      requireType frontend base "mapping(address => uint256)"
      let index ← field j "indexExpression"
      requireType frontend index "address"
      requireType frontend j "uint256"
      translateExpr frontend slots locals index fun key => do
        k (← lookupSlot slots info.id) (some key)
  | _ => failAt frontend.source j "only storage assignment supported"

private partial def translateStmts (frontend : Frontend) (slots : Slots) (locals : Locals)
    (returns : String) (nodes : List Json) : MetaM Expr := do
  match nodes with
  | [] =>
      if returns == "unit" then ret (mkConst ``Unit.unit)
      else throwError "missing terminal return"
  | node :: rest =>
      match ← nodeKind node with
      | "ExpressionStatement" =>
          let assignment ← field node "expression"
          needAt frontend.source node ((← nodeKind assignment) == "Assignment") "unsupported expression statement"
          requireType frontend assignment "uint256"
          let op ← str (← field assignment "operator")
          needAt frontend.source assignment (op == "=" || op == "+=" || op == "-=") "unsupported assignment"
          translateLValue frontend slots locals (← field assignment "leftHandSide") fun slot key => do
            let write (value : Expr) : MetaM Expr := do
              let action ← match key with
                | none => mkAppM ``Verity.setStorage #[slot, value]
                | some index => mkAppM ``Verity.setMapping #[slot, index, value]
              seq action unit fun _ => translateStmts frontend slots locals returns rest
            let rhsNode ← field assignment "rightHandSide"
            if op == "=" then translateExpr frontend slots locals rhsNode write
            else
              let read ← match key with
                | none => mkAppM ``Verity.getStorage #[slot]
                | some index => mkAppM ``Verity.getMapping #[slot, index]
              seq read uint fun old => do
                translateExpr frontend slots locals rhsNode fun rhs => do
                  seq (← checked op old rhs) uint write
      | "VariableDeclarationStatement" =>
          let declarations ← arr (← field node "declarations")
          needAt frontend.source node (declarations.size == 1) "unsupported locals"
          let declaration := declarations[0]!
          needAt frontend.source declaration (!(← bool (← field declaration "stateVariable")) &&
            !(← bool (← field declaration "constant")) &&
            (← str (← field declaration "mutability")) == "mutable" &&
            (← str (← field declaration "storageLocation")) == "default" &&
            (← str (← field declaration "visibility")) == "internal") "unsupported local declaration"
          requireType frontend declaration "uint256"
          let id ← nodeId declaration
          let _ ← identifier frontend.source declaration
          let initialValue ← field node "initialValue"
          translateExpr frontend slots locals initialValue fun value =>
            translateStmts frontend slots ((id, "uint256", value) :: locals) returns rest
      | "IfStatement" =>
          let falseBody := field? node "falseBody"
          let trueBody ← field node "trueBody"
          let statements ← arr (← field trueBody "statements")
          needAt frontend.source node (falseBody.all Json.isNull && statements.size == 1 &&
            (← nodeKind statements[0]!) == "RevertStatement") "only if/revert guard supported"
          let call ← field statements[0]! "errorCall"
          let callee ← field call "expression"
          let rid ← int (← field callee "referencedDeclaration")
          let some errorName := if rid < 0 then none else frontend.errors.lookup rid.toNat
            | failAt frontend.source node "unsupported revert"
          needAt frontend.source node ((← nodeKind callee) == "Identifier" &&
            (← arr (← field call "arguments")).isEmpty) "unsupported revert"
          let condition ← field node "condition"
          needAt frontend.source condition ((← nodeKind condition) == "BinaryOperation" &&
            (← str (← field condition "operator")) == "<") "only uint256 comparison guard supported"
          requireType frontend condition "bool"
          let commonType ← field condition "commonType"
          needAt frontend.source condition ((← str (← field commonType "typeString")) == "uint256" &&
            (← str (← field commonType "typeIdentifier")) == "t_uint256") "unsupported comparison type"
          let left ← field condition "leftExpression"
          let right ← field condition "rightExpression"
          requireType frontend left "uint256"; requireType frontend right "uint256"
          translateExpr frontend slots locals left fun a =>
            translateExpr frontend slots locals right fun b => do
              let av ← mkAppM ``Verity.Core.Uint256.val #[a]
              let bv ← mkAppM ``Verity.Core.Uint256.val #[b]
              let allowed ← mkAppM ``Nat.ble #[bv, av]
              let guard ← mkAppM ``Verity.require #[allowed, mkStrLit (errorName ++ "()")]
              seq guard unit fun _ => translateStmts frontend slots locals returns rest
      | "Return" =>
          needAt frontend.source node (rest.isEmpty && returns == "uint256") "only terminal scalar return"
          translateExpr frontend slots locals (← field node "expression") ret
      | _ => failAt frontend.source node "unsupported statement"

private def nonpayable (m : Expr) : MetaM Expr :=
  seq (mkConst ``Verity.msgValue) uint fun value => do
    let n ← mkAppM ``Verity.Core.Uint256.val #[value]
    let zero ← mkAppM ``Nat.beq #[n, mkNatLit 0]
    let guard ← mkAppM ``Verity.require #[zero, mkStrLit "Nonpayable"]
    seq guard unit fun _ => pure m

private def validateValueDecl (frontend : Frontend) (p : Json) : MetaM Unit := do
  needAt frontend.source p (!(← bool (← field p "stateVariable")) &&
    !(← bool (← field p "constant")) &&
    (← str (← field p "mutability")) == "mutable" &&
    (← str (← field p "storageLocation")) == "default" &&
    (← str (← field p "visibility")) == "internal" &&
    (field? p "value").all Json.isNull) "unsupported parameter declaration"

private partial def translateParams (frontend : Frontend) (params : List Json) (locals : Locals)
    (k : Locals → MetaM Expr) : MetaM Expr := do
  match params with
  | [] => k locals
  | p :: ps =>
      validateValueDecl frontend p
      let typ ← typeString p
      needAt frontend.source p (typ == "uint256" || typ == "address") "unsupported value type"
      let name ← identifier frontend.source p
      let id ← nodeId p
      withLocalDeclD (Name.mkSimple name) (← valueType typ) fun x => do
        mkLambdaFVars #[x] (← translateParams frontend ps ((id, typ, x) :: locals) k)

private def importFrontend (ns : Name) (frontend : Frontend) : MetaM Unit := do
  if debug.skipKernelTC.get (← getOptions) then throwError "kernel checking must be enabled"
  let mut names := #[ns ++ `sourceDigest]
  for f in frontend.fields do
    names := names.push (ns ++ Name.mkSimple f.name)
    if let some getter := f.getter then names := names.push (ns ++ Name.mkSimple getter)
  for fn in frontend.functions do
    let name ← identifier frontend.source fn
    names := names.push (ns ++ Name.mkSimple name)
  for i in [:names.size] do
    if (← getEnv).contains names[i]! || (names.extract 0 i).contains names[i]! then
      throwError "declaration collision: {names[i]!}"
  let mut slots : Slots := []
  for f in frontend.fields do
    let ty ← if f.mapping then mkArrow address uint else pure uint
    let slot ← mkAppOptM ``Verity.StorageSlot.mk #[some ty, some (mkNatLit f.slot)]
    let name := ns ++ Name.mkSimple f.name
    register name slot
    slots := (f.id, mkConst name) :: slots
  for f in frontend.fields do
    if let some getter := f.getter then
      let slot ← lookupSlot slots f.id
      let value ← if f.mapping then
          withLocalDeclD `account address fun account => do
            let getter ← mkAppM ``Verity.getMapping #[slot, account]
            mkLambdaFVars #[account] (← nonpayable getter)
        else nonpayable (← mkAppM ``Verity.getStorage #[slot])
      register (ns ++ Name.mkSimple getter) value
  for fn in frontend.functions do
    let name ← identifier frontend.source fn
    needAt frontend.source fn ((← str (← field fn "kind")) == "function" &&
      (← bool (← field fn "implemented")) && (← arr (← field fn "modifiers")).isEmpty &&
      !(← bool (← field fn "virtual")) && (field? fn "overrides").all Json.isNull &&
      ["external", "public"].contains (← str (← field fn "visibility")) &&
      ["nonpayable", "view"].contains (← str (← field fn "stateMutability"))) "unsupported function surface"
    let ps ← arr (← field (← field fn "parameters") "parameters")
    let rs ← arr (← field (← field fn "returnParameters") "parameters")
    needAt frontend.source fn (ps.size <= 1 && rs.size <= 1) "unsupported signature"
    for r in rs do
      validateValueDecl frontend r
      needAt frontend.source r ((← str (← field r "name")).isEmpty && (← typeString r) == "uint256")
        "unsupported return type"
    let returns := if rs.isEmpty then "unit" else "uint256"
    let value ← translateParams frontend ps.toList [] fun locals => do
      let code ← translateStmts frontend slots locals returns
        (← arr (← field (← field fn "body") "statements")).toList
      let expected ← mkAppM ``Verity.Contract #[← valueType returns]
      unless ← isDefEq (← inferType code) expected do
        throwError "imported body does not match typed AST return signature"
      nonpayable code
    register (ns ++ Name.mkSimple name) value
  register (ns ++ `sourceDigest) (mkStrLit frontend.digest)

private def compileFrontend (root source : System.FilePath) : MetaM Frontend := do
  let canonicalRoot ← IO.FS.realPath root
  let canonicalSource ← IO.FS.realPath source
  unless canonicalSource.toString.startsWith (canonicalRoot.toString ++ "/") do
    throwError "source outside package"
  let expected ← IO.FS.realPath (canonicalRoot / registeredSource)
  unless canonicalSource == expected do throwError "unregistered source or source outside package"
  let compiler := canonicalRoot / ".lake/solidity-import/solc"
  verifyCompiler compiler
  let versionOut ← IO.Process.output { cmd := compiler.toString, args := #["--version"] }
  unless versionOut.exitCode == 0 && versionOut.stdout.trimAscii.toString == solcVersionOutput do
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
    ("sources", Json.mkObj [(registeredSource, Json.mkObj [("content", sourceText)])]),
    ("settings", settings)]
  let output ← IO.Process.output
    { cmd := compiler.toString, args := #["--standard-json", "--no-import-callback"] }
    (some input.compress)
  unless output.exitCode == 0 do throwError "solc failed: {output.stderr}"
  verifyCompiler compiler
  let importerText ← IO.FS.readFile
    (canonicalRoot / "Contracts/VaultFromSolidity/Importer/Importer.lean")
  parseCompilerOutput canonicalSource registeredSource sourceBytes output.stdout versionOut.stdout importerText

syntax (name := solidityContract) "solidity_contract " ident " from " str : command

@[command_elab solidityContract] def elabSolidityContract : CommandElab := fun stx => do
  let saved ← getEnv
  try
    let authored ← IO.FS.realPath (← getFileName)
    let source := authored.parent.getD "." / stx[3].isStrLit?.get!
    let mut root := authored.parent.getD "."
    while !(← (root / "lakefile.lean").pathExists) do
      let some parent := root.parent | throwError "package root not found"
      if parent == root then throwError "package root not found"
      root := parent
    let frontend ← liftTermElabM <| compileFrontend root source
    let ns := (← getCurrNamespace) ++ stx[1].getId
    liftTermElabM <| withOptions (Elab.async.set · false) (importFrontend ns frontend)
  catch e =>
    setEnv saved
    throw e

end SolidityImporter
