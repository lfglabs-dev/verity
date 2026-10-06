import Lean
import Compiler.Sha256.Engine
import Compiler.Hex
import Compiler.SolidityImport.Access
import Compiler.SolidityImport.Profile
import Compiler.SolidityImport.Quote
import Compiler.SolidityImport.Report
import Compiler.SolidityImport.AbiRootLowering
import Compiler.SolidityImport.AbiEncoding

/-!
Solidity importer. Pinned `solc --standard-json` supplies the AST, declaration
ids, and `storageLayout`. The `solidity_import` command selects a function,
closes over the definitions that resolution actually reaches, and elaborates a
`CompilationModel`. It does not interpret that model: execution is
`Denote.execStmt`, restricted by `stmtListCovered`.

```lean
solidity_import midnight from "vendor/midnight" entry "src/Midnight.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract Midnight
  function updatePositionView(Market, bytes32, address)
```

This defines `midnight.model`, `midnight.report`, `midnight.sourceDigest`, the
theorem `midnight.covered`, and typed accessors: `midnight.updatePositionView`
for each imported function and `midnight.position.credit` for each storage
struct member.

The frontend is in the trust base. A covered model is not, by itself, a proof
that the model matches the Solidity source or solc's bytecode.
-/

open Lean Meta Elab Command

namespace Compiler.CompilationModel.SolidityImport

def importerVersion : String := "solidity-import-1"

private def solcLongVersion := "0.8.34+commit.80d5c536"

private def officialSolcSha256s : Array String := #[
  "d40adc6f9fdbb22a97d32a02fa05688bf2ee7886affc48c9851b0afd4a726b39",
  "0a2829292697dda542e4e365bb63fbd6d3ed51537140222a880ab760cffa7746"]

private def acceptedSolcBanners : Array String := #[
  s!"solc, the solidity compiler commandline interface\nVersion: {solcLongVersion}.Linux.g++",
  s!"solc, the solidity compiler commandline interface\nVersion: {solcLongVersion}.Darwin.appleclang"]

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

private def arr (j : Json) : MetaM (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def bool (j : Json) : MetaM Bool :=
  match j.getBool? with
  | .ok v => pure v
  | .error e => throwError "{e}"

private def flexNat (j : Json) : MetaM Nat := do
  match j.getNat? with
  | .ok n => pure n
  | .error _ =>
      match j.getStr? with
      | .ok s =>
          match s.toNat? with
          | some n => pure n
          | none => throwError "not a nat: {s}"
      | .error e => throwError "{e}"

private def nodeKind (j : Json) : MetaM String := do
  str (← field j "nodeType")

private def typeString (j : Json) : MetaM String := do
  str (← field (← field j "typeDescriptions") "typeString")

private def optStr (j : Json) (key : String) : Option String :=
  match field? j key with
  | some v => v.getStr?.toOption
  | none => none

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

private def sha256Hex (bytes : ByteArray) : String :=
  (Sha256Engine.sha256 bytes).data.foldl (init := "") fun acc byte =>
    acc.push (hexDigit (byte.toNat / 16)) |>.push (hexDigit (byte.toNat % 16))

/-- A lowered expression and the statements that must run before it. -/
private structure Val where
  pre : Array Stmt
  expr : Expr

private structure EncodedBytes where
  pre : Array Stmt
  pointer : Expr
  size : Expr

private inductive SPath where
  | one (field : String) (key : Expr)
  | two (field : String) (k1 k2 : Expr)
  | outer (field : String) (k1 : Expr)

private inductive Ref where
  | expr (v : Val)
  | path (pre : Array Stmt) (p : SPath)
  | fixedElement (pre : Array Stmt) (path : SPath) (index : Expr)
  | snapshot (elements : Array Expr)
  | mem (id : Nat) (pre : Array Stmt)
  | abiArray (id memberIndex : Nat) (pre : Array Stmt)
  | abiElement (id memberIndex : Nat) (pointer : Expr) (pre : Array Stmt)
  | state (name : String) (pre : Array Stmt)

private structure MemParam where
  structId : Nat
  param : String
  structName : String
  members : Array (String × String)
  staticTypes : Option (List ParamType) := none
  calldataLocation : Bool := false
  headBinding : String := ""
  schema : Option (List AbiSchema.Member) := none
  abiStem : String := ""

private inductive CallArg where
  | scalar (value : Val)
  | memory (descriptor : MemParam) (pre : Array Stmt)

private structure FieldInfo where
  slot : Nat
  field : Field
  keyCount : Nat
  memberNames : Array String
  opaqueNames : Array String
  scalarMapping : Bool := false
  booleanMapping : Bool := false
  fixedArrayLength : Option Nat := none
  fixedArrayType : String := ""

private structure FnRec where
  contract : String
  name : String
  declId : Nat
  paramTypes : Array String

private structure ProjRec where
  parameter : String
  member : String
  structName : String
  headWord : Nat
  modelParam : String

private structure OpaqRec where
  field : String
  name : String
  solcType : String
  wordOffset : Nat
  byteOffset : Nat

private structure SrcParam where
  name : String
  id : Nat

private structure Env where
  sourceNames : List String
  nodeFile : RBMap Nat String compare
  files : RBMap String ByteArray compare
  funs : RBMap Nat Json compare
  funContract : RBMap Nat String compare
  structs : RBMap Nat Json compare
  eventDecls : RBMap Nat Json compare
  usedEvents : List (Nat × EventDef)
  errorDecls : RBMap Nat Json compare
  usedErrors : List ErrorDef
  stateVars : RBMap Nat Json compare
  numericConstants : RBMap Nat Json compare := RBMap.empty
  constantStack : List Nat := []
  values : RBMap Nat Expr compare
  paths : RBMap Nat SPath compare
  snapshots : RBMap Nat (Array Expr) compare := RBMap.empty
  mems : RBMap Nat MemParam compare
  fieldsByName : RBMap String FieldInfo compare
  layoutItems : RBMap String Json compare
  layoutTypes : Json
  included : Array FnRec
  projections : Array ProjRec
  opaqueMembers : Array OpaqRec
  referenced : Array String
  scalarTy : RBMap Nat ParamType compare
  writableLocals : RBMap Nat String compare := RBMap.empty
  rawBindings : RBMap Nat String compare := RBMap.empty
  encodingMemory : Bool := false
  explicitAbi : Bool := false
  next : Nat
  /-- Every binding name allocated in the current root, including its parameters. -/
  bound : List String
  stack : List Nat
  yulNames : RBMap String Expr compare
  currentFile : String

private def Env.init : Env where
  sourceNames := []
  nodeFile := RBMap.empty
  files := RBMap.empty
  funs := RBMap.empty
  funContract := RBMap.empty
  structs := RBMap.empty
  eventDecls := RBMap.empty
  usedEvents := []
  errorDecls := RBMap.empty
  usedErrors := []
  stateVars := RBMap.empty
  values := RBMap.empty
  paths := RBMap.empty
  mems := RBMap.empty
  fieldsByName := RBMap.empty
  layoutItems := RBMap.empty
  layoutTypes := Json.null
  included := #[]
  projections := #[]
  opaqueMembers := #[]
  referenced := #[]
  scalarTy := RBMap.empty
  next := 0
  bound := []
  stack := []
  yulNames := RBMap.empty
  currentFile := ""

private abbrev M := StateT Env MetaM

private def mField (j : Json) (key : String) : M Json := liftM (field j key)
private def mStr (j : Json) : M String := liftM (str j)
private def mArr (j : Json) : M (Array Json) := liftM (arr j)
private def mBool (j : Json) : M Bool := liftM (bool j)
private def mNat (j : Json) : M Nat := liftM (flexNat j)
private def mKind (j : Json) : M String := liftM (nodeKind j)
private def mType (j : Json) : M String := liftM (typeString j)

private def failAt (j : Json) (why : String) : M α := do
  let env ← get
  let frames := env.stack.reverse.map fun id =>
    let owner := env.funContract.find? id |>.getD "<free>"
    let name := (env.funs.find? id).bind (fun fn => optStr fn "name") |>.getD s!"decl#{id}"
    s!"{owner}.{name}"
  let why := s!"[solidity-import:unsupported] {why}\nclosure: {String.intercalate " -> " frames}"
  let file :=
    match (field? j "id").bind (fun id => id.getNat?.toOption) with
    | some id => env.nodeFile.find? id |>.getD env.currentFile
    | none => env.currentFile
  let some bytes := env.files.find? file | throwError "{file}: {why}"
  let some src := (field? j "src").bind (fun s => s.getStr?.toOption)
    | throwError "{file}: {why}"
  let pieces := src.splitOn ":"
  let some start := pieces[0]?.bind (·.toNat?) | throwError "{file}: {why}"
  let some size := pieces[1]?.bind (·.toNat?) | throwError "{file}: {why}"
  let before := bytes.data.extract 0 (min start bytes.size)
  let (line, column) := before.foldl
    (fun (p : Nat × Nat) b => if b == 10 then (p.1 + 1, 1) else (p.1, p.2 + 1)) (1, 1)
  let excerptBytes : ByteArray :=
    ⟨bytes.data.extract start (min (start + size) (min bytes.size (start + 120)))⟩
  let excerpt := String.fromUTF8? excerptBytes |>.getD "<invalid UTF-8>"
  let kind := (field? j "nodeType").bind (fun k => k.getStr?.toOption) |>.getD "node"
  throwError "{file}:{line}:{column}: {kind}: {why}\n{excerpt}"

private def refInt (j : Json) : M Int := do
  match field? j "overloadedDeclarations" with
  | some over =>
      let xs ← mArr over
      if xs.size ≠ 0 then failAt j "ambiguous declaration"
  | none => pure ()
  let some declaration := field? j "referencedDeclaration"
    | failAt j "expression has no supported declaration reference"
  match declaration.getInt? with
  | .ok i => pure i
  | .error e => failAt j e

private def fresh : M String := do
  let env ← get
  let projected := env.mems.toList.flatMap fun (_, p) =>
    p.members.toList.map (fun (member, _) => s!"{p.param}_{member}")
  let reserved := env.sourceNames ++ projected ++ env.bound
  -- The prefix is a valid compiler identifier, but is not assumed reserved by
  -- Solidity. Check every source name and every potential scalar projection.
  for _ in [:reserved.length + 1] do
    let n := (← get).next
    modify fun e => { e with next := e.next + 1 }
    let candidate := s!"_verity_slice_tmp_{n}"
    unless reserved.contains candidate do
      modify fun e => { e with bound := candidate :: e.bound }
      return candidate
  throwError "unable to allocate a hygienic slice binding"

private def yulKeywords : List String :=
  ["let", "if", "switch", "case", "default", "for", "break", "continue", "leave",
   "function", "true", "false"]

/-- Binding for the Solidity local `name`: the source name itself when it is
free, so that proofs can refer to it, else `name_1`, `name_2`, ... Names that
the compiler reserves or Yul forbids fall back to `fresh`. -/
private def freshFor (name : String) : M String := do
  if name.startsWith "__" || name.startsWith "_verity_slice_tmp" then return ← fresh
  let env ← get
  let projected := env.mems.toList.flatMap fun (_, p) =>
    p.members.toList.map (fun (member, _) => s!"{p.param}_{member}")
  let usable (candidate : String) : Bool :=
    !(env.bound.contains candidate || projected.contains candidate ||
      yulKeywords.contains candidate || (Verity.Core.Intrinsics.yulBuiltinArity? candidate).isSome)
  let mut chosen := none
  if usable name then chosen := some name
  else
    for k in [1:env.bound.length + 2] do
      let candidate := s!"{name}_{k}"
      if chosen.isNone && usable candidate && !env.sourceNames.contains candidate then
        chosen := some candidate
  let some binding := chosen | fresh
  modify fun e => { e with bound := binding :: e.bound }
  pure binding

/-- Reserve every generated ABI name, not just the root prefix. -/
private def freshAbiStem (schema : List AbiSchema.Member) (inMemory : Bool) : M String := do
  let budget := (← get).sourceNames.length + (← get).bound.length + 1
  for _ in [:budget] do
    let stem ← fresh
    let names := (AbiRootLowering.root stem 0 0 schema inMemory).names
    let reserved := (← get).sourceNames ++ (← get).bound
    unless names.any reserved.contains do
      modify fun e => { e with bound := names ++ e.bound }
      return stem
  throwError "unable to allocate hygienic ABI bindings"

private def isAtom : Expr → Bool
  | .literal _ | .localVar _ | .param _ | .blockTimestamp | .blockNumber
  | .caller | .contractAddress | .chainid => true
  | _ => false

/-- Includes nested loop step writes; callers pass only the current loop body. -/
private partial def bodyAssignedIds (j : Json) : List Nat :=
  match j with
  | .arr xs => xs.toList.flatMap bodyAssignedIds
  | .obj o =>
      let kind := optStr j "nodeType"
      let operator := optStr j "operator" |>.getD ""
      let target :=
        if kind == some "Assignment" then field? j "leftHandSide"
        else if kind == some "UnaryOperation" && ["++", "--", "delete"].contains operator then
          field? j "subExpression"
        else none
      let own := match target with
        | some t =>
            if optStr t "nodeType" == some "Identifier" then
              match (field? t "referencedDeclaration").bind (fun v => v.getNat?.toOption) with
              | some n => [n]
              | none => []
            else []
        | none => []
      o.foldl (fun acc _ v => acc ++ bodyAssignedIds v) own
  | _ => []

/-- Stateful calls in sibling expressions need an independently validated order.
    A non-view declaration is conservatively treated as stateful even when its
    current body happens not to write. Unknown calls retain their usual rejection. -/
private partial def statefulCallIn (j : Json) (env : Env) : Bool :=
  match j with
  | .arr xs => xs.any (fun child => statefulCallIn child env)
  | .obj o =>
      let own := if optStr j "nodeType" == some "FunctionCall" &&
          optStr j "kind" == some "functionCall" then
        match (field? j "expression").bind (fun callee =>
            (field? callee "referencedDeclaration").bind (fun id => id.getNat?.toOption)) with
        | some id => match env.funs.find? id with
          | some fn => ![some "pure", some "view"].contains (optStr fn "stateMutability")
          | none => false
        | none => false
      else false
      o.foldl (fun found _ child => found || statefulCallIn child env) own
  | _ => false

private def atom (v : Val) : M Val := do
  if v.pre.isEmpty && isAtom v.expr then
    pure v
  else
    let n ← fresh
    pure { pre := v.pre.push (.letVar n v.expr), expr := .localVar n }

private def bitsOf (ty : String) : Option Nat :=
  if ty == "uint256" || ty == "uint" then some 256
  else if ty == "bytes32" then some 256
  else if ty == "address" then some 160
  else if ty.startsWith "uint" then (ty.drop 4).toNat?
  else none

private def paramType (ty : String) : Option ParamType :=
  match ty with
  | "uint256" | "uint" => some .uint256
  | "address" => some .address
  | "bytes32" => some .bytes32
  | "bool" => some .bool
  | _ =>
      match bitsOf ty with
      | some n => if n != 256 && ty.startsWith "uint" then some (.uintN n) else none
      | none => none

/-- Resolve the actual CompilationModel parameter type, including projected
struct members. A helper's Solidity return type need not be the type of the
root parameter expression that survives inlining. -/
private def rootParamType? (env : Env) (name : String) : Option ParamType := do
  for (id, expression) in env.values do
    match expression with
    | .param candidate =>
        if candidate == name then
          if let some ty := env.scalarTy.find? id then return ty
    | _ => pure ()
  for (_, memory) in env.mems do
    for (member, ty) in memory.members do
      if s!"{memory.param}_{member}" == name then return ← paramType ty
  none

private def noteFn (fn : Json) : M Unit := do
  let id ← mNat (← mField fn "id")
  let env ← get
  unless env.included.any (·.declId == id) do
    let name ← mStr (← mField fn "name")
    let params ← mArr (← mField (← mField fn "parameters") "parameters")
    let mut tys : Array String := #[]
    for p in params do
      tys := tys.push (← mType p)
    let contract := env.funContract.find? id |>.getD "<free>"
    modify fun e =>
      let added := e.included.push ⟨contract, name, id, tys⟩
      { e with included := added }

private def markField (name : String) : M Unit := do
  let env ← get
  unless env.referenced.contains name do
    modify fun e => { e with referenced := e.referenced.push name }

private def mappingKey (ty : String) : MetaM MappingKeyType :=
  match ty with
  | "t_bytes32" => pure .bytes32
  | "t_address" => pure .address
  | "t_uint256" => pure .uint256
  | _ => throwError "unsupported mapping key {ty}"

private def layoutType (types : Json) (id : String) : MetaM Json :=
  field types id

/-- Solidity names of the mapping keys of the state variable `name`
(`mapping(bytes32 id => ...)`), outermost first; `""` when unnamed. -/
private def mappingKeyNames (env : Env) (name : String) : List String :=
  let decl := env.stateVars.toList.find? fun (_, j) => optStr j "name" == some name
  let rec go (fuel : Nat) (ty : Json) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if optStr ty "nodeType" == some "Mapping" then
        (optStr ty "keyName" |>.getD "") :: (match field? ty "valueType" with
          | some v => go fuel v
          | none => [])
      else []
  match decl.bind (fun (_, j) => field? j "typeName") with
  | some ty => go 8 ty
  | none => []

private def buildField (types item : Json) : M FieldInfo := do
  let name ← mStr (← mField item "label")
  let slot ← mNat (← mField item "slot")
  let typeId ← mStr (← mField item "type")
  let top ← liftM (layoutType types typeId)
  let encoding ← mStr (← mField top "encoding")
  if encoding == "inplace" then
    let width ←
      if typeId == "t_address" || typeId == "t_address_payable" then pure 160
      else if typeId == "t_bytes32" then pure 256
      else if typeId.startsWith "t_uint" then
        let some bits := (typeId.drop 6).toNat? | throwError "invalid scalar uint layout {typeId}"
        unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
          throwError "invalid scalar uint width {bits}"
        pure bits
      else throwError "unsupported scalar storage type {typeId}"
    let offset := (← mNat (← mField item "offset")) * 8
    unless offset + width ≤ 256 do throwError "scalar storage field {name} crosses a word boundary"
    let packedBits : Option PackedBits :=
      if offset == 0 && width == 256 then none else some { offset, width }
    -- Exact physical words; source types still govern conversions and ABI.
    let field : Field := { name, ty := .uint256, slot := some slot, packedBits }
    return { slot, field, keyCount := 0, memberNames := #[], opaqueNames := #[] }
  unless encoding == "mapping" do
    throwError "unsupported storage encoding {encoding} for {name}"
  let key1 ← liftM (mappingKey (← mStr (← mField top "key")))
  let valueId ← mStr (← mField top "value")
  let value ← liftM (layoutType types valueId)
  let encoding ← mStr (← mField value "encoding")
  let (key2, structTy) ←
    if encoding == "mapping" then
      let key2 ← liftM (mappingKey (← mStr (← mField value "key")))
      let innerId ← mStr (← mField value "value")
      pure (some key2, ← liftM (layoutType types innerId))
    else if encoding == "inplace" then
      pure (none, value)
    else
      throwError "unsupported mapping value encoding {encoding} for {name}"
  -- Fixed arrays have finite elements, not an extra mapping key. Solidity
  -- packs floor(256/width) elements per word, leaving any remainder unused.
  if let some baseId := optStr structTy "base" then
    unless (← mStr (← mField structTy "encoding")) == "inplace" do
      throwError "only fixed inplace mapping arrays are supported for {name}"
    let label ← mStr (← mField structTy "label")
    let [elementLabel, suffix] := label.splitOn "["
      | throwError "mapping arrays require exactly one fixed dimension: {label}"
    unless suffix.endsWith "]" do throwError "invalid fixed array layout {label}"
    let some length := (suffix.dropEnd 1).toNat?
      | throwError "mapping arrays require a resolved fixed length: {label}"
    unless length > 0 do throwError "fixed mapping array length must be positive"
    let base ← liftM (layoutType types baseId)
    let baseLabel ← mStr (← mField base "label")
    unless elementLabel == baseLabel && baseLabel.startsWith "uint" do
      throwError "fixed mapping arrays require unsigned scalar elements: {label}"
    let some width := bitsOf baseLabel
      | throwError "invalid fixed mapping array element width: {baseLabel}"
    unless width > 0 && width ≤ 256 && width % 8 == 0 do
      throwError "invalid fixed mapping array element width: {width}"
    unless (← mStr (← mField base "encoding")) == "inplace" &&
        (← mNat (← mField base "numberOfBytes")) * 8 == width do
      throwError "fixed mapping array base layout disagrees with {baseLabel}"
    let perWord := 256 / width
    let words := (length + perWord - 1) / perWord
    unless (← mNat (← mField structTy "numberOfBytes")) == words * 32 do
      throwError "fixed mapping array footprint disagrees with {label}"
    let mut members : Array StructMember := #[]
    for index in [:length] do
      let offset := (index % perWord) * width
      let packed : Option PackedBits :=
        if width == 256 then none else some { offset := offset, width := width }
      let member : StructMember := { name := s!"__solidity_element_{index}", ty := .uint256, wordOffset := index / perWord, packed }
      members := members.push member
    let ty : FieldType := match key2 with
      | some k2 => .mappingStruct2 key1 k2 members.toList
      | none => .mappingStruct key1 members.toList
    return { slot, field := { name, ty, slot := some slot },
             keyCount := if key2.isSome then 2 else 1, memberNames := #[],
             opaqueNames := #[], fixedArrayLength := some length, fixedArrayType := label }
  -- A scalar mapping value occupies a word just like a one-member mapping
  -- struct. Keep narrow writes as read/modify/write operations, including the
  -- one-byte Solidity bool representation, rather than clearing upper bits.
  if (field? structTy "members").isNone then
    let leafEncoding ← mStr (← mField structTy "encoding")
    unless leafEncoding == "inplace" do
      throwError "unsupported scalar mapping value encoding {leafEncoding} for {name}"
    let leafType ← mStr (← mField structTy "label")
    let width ←
      if leafType == "bool" then pure 8
      else if leafType == "address" || leafType == "address payable" then pure 160
      else if leafType == "bytes32" then pure 256
      else if leafType.startsWith "uint" then
        let some bits := (leafType.drop 4).toNat? | throwError "invalid mapping uint layout {leafType}"
        unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
          throwError "invalid mapping uint width {bits}"
        pure bits
      else throwError "unsupported scalar mapping value type {leafType}"
    let bytes ← mNat (← mField structTy "numberOfBytes")
    unless bytes * 8 == width do
      throwError "scalar mapping value size disagrees with type {leafType}"
    let packed : Option PackedBits :=
      if width == 256 then none else some { offset := 0, width }
    let member : StructMember :=
      { name := "__solidity_value", ty := .uint256, wordOffset := 0, packed }
    let ty : FieldType := match key2 with
      | some k2 => .mappingStruct2 key1 k2 [member]
      | none => .mappingStruct key1 [member]
    let field : Field := { name, ty, slot := some slot }
    return { slot, field, keyCount := if key2.isSome then 2 else 1,
             memberNames := #[], opaqueNames := #[], scalarMapping := true,
             booleanMapping := leafType == "bool" }
  let members ← mArr (← mField structTy "members")
  let mut members' : Array StructMember := #[]
  let mut names : Array String := #[]
  let mut skipped : Array String := #[]
  for m in members do
    let label ← mStr (← mField m "label")
    let solcType ← mStr (← mField m "type")
    let word ← mNat (← mField m "slot")
    let byteOff ← mNat (← mField m "offset")
    if solcType.startsWith "t_array" || solcType.startsWith "t_mapping" then
      skipped := skipped.push label
      modify fun e =>
        let item : OpaqRec := ⟨name, label, solcType, word, byteOff⟩
        { e with opaqueMembers := e.opaqueMembers.push item }
    else if solcType.startsWith "t_uint" then
      let some bits := (solcType.drop 6).toNat? | throwError "bad uint {solcType}"
      let bitOff := byteOff * 8
      unless bitOff + bits ≤ 256 do throwError "packed field {label} does not fit in a word"
      let packed : Option PackedBits :=
        if bits == 256 && bitOff == 0 then none else some { offset := bitOff, width := bits }
      let ty : StructMemberType := if bits == 16 then .uint16 else .uint256
      members' := members'.push { name := label, ty, wordOffset := word, packed }
      names := names.push label
    else
      throwError "unsupported layout member {label} : {solcType}"
  let ty : FieldType :=
    match key2 with
    | some k2 => .mappingStruct2 key1 k2 members'.toList
    | none => .mappingStruct key1 members'.toList
  let field : Field := { name, ty, slot := some slot }
  pure { slot, field, keyCount := if key2.isSome then 2 else 1,
         memberNames := names, opaqueNames := skipped }

/-- Resolve only reached fields: an unrelated unsupported layout must not
prevent importing a supported function closure. -/
private def resolveField (name : String) (at_ : Json) : M FieldInfo := do
  if let some info := (← get).fieldsByName.find? name then return info
  let env ← get
  let some item := env.layoutItems.find? name | failAt at_ s!"no storage layout for {name}"
  let info ← try buildField env.layoutTypes item catch ex =>
    failAt at_ (← ex.toMessageData.toString)
  modify fun e => { e with fieldsByName := e.fieldsByName.insert name info }
  return info

private def memberRead (pre : Array Stmt) (path : SPath) (member : String) (at_ : Json) : M Val := do
  let (fieldName, read) ← match path with
    | .one field key => pure (field, Expr.structMember field key member)
    | .two field k1 k2 => pure (field, Expr.structMember2 field k1 k2 member)
    | .outer _ _ => failAt at_ "member access on an incomplete mapping"
  let some info := (← get).fieldsByName.find? fieldName
    | failAt at_ s!"no storage layout for {fieldName}"
  if info.opaqueNames.contains member then
    failAt at_ s!"member {member} is opaque in this slice"
  unless info.memberNames.contains member do
    failAt at_ s!"member {member} is not a layout member of {fieldName}"
  markField fieldName
  pure { pre, expr := read }

private def scalarMappingRead (pre : Array Stmt) (path : SPath) (at_ : Json) : M Val := do
  let (name, count, read) ← match path with
    | .one field key => pure (field, 1, Expr.structMember field key "__solidity_value")
    | .two field key1 key2 => pure (field, 2, Expr.structMember2 field key1 key2 "__solidity_value")
    | .outer _ _ => failAt at_ "scalar mapping read requires both keys"
  let info ← resolveField name at_
  unless info.scalarMapping && info.keyCount == count do
    failAt at_ "storage or memory path used as a value"
  markField name
  -- Solidity cleans a storage bool by testing the loaded byte for nonzero.
  let expr := if info.booleanMapping then Expr.logicalNot (.logicalNot read) else read
  pure { pre, expr }

/-- `if cond then [yes] else [no]` with single-statement branches. -/
private def iteStmt (cond : Expr) (yes no : Stmt) : Stmt :=
  .ite cond [yes] [no]

private def overflowPanic : Stmt := .panic .arithmeticOverflow

private def divPanic : Stmt := .panic .divisionByZero

/-- Decimal/scientific literal value as an exact natural rational. -/
private def numericLiteralRatio (raw : String) : Option (Nat × Nat) := do
  let raw := raw.replace "_" ""
  if let some n := Compiler.Hex.parseHexNat? raw then return (n, 1)
  let (mantissa, exponent, negative) ← match (raw.replace "E" "e").splitOn "e" with
    | [m] => some (m, 0, false)
    | [m, e] => do
        let negative := e.startsWith "-"
        let digits := if negative || e.startsWith "+" then (e.drop 1).toString else e
        let exponent ← digits.toNat?
        some (m, exponent, negative)
    | _ => none
  let (numerator, denominator) ← match mantissa.splitOn "." with
    | [digits] => do
        let n ← digits.toNat?
        some (n, 1)
    | [whole, fraction] => do
        let w ← if whole.isEmpty then some 0 else whole.toNat?
        let f ← fraction.toNat?
        let scale := 10 ^ fraction.length
        some (w * scale + f, scale)
    | _ => none
  if negative then return (numerator, denominator * 10 ^ exponent)
  else return (numerator * 10 ^ exponent, denominator)

private def literalUnitScale : String → Option Nat
  | "seconds" | "wei" => some 1
  | "minutes" => some 60
  | "hours" => some 3600
  | "days" => some 86400
  | "weeks" => some 604800
  | "gwei" => some (10 ^ 9)
  | "ether" => some (10 ^ 18)
  | _ => none

mutual

private partial def lowerYul (j : Json) : M Expr := do
  match ← mKind j with
  | "YulIdentifier" =>
      let name ← mStr (← mField j "name")
      match (← get).yulNames.find? name with
      | some expr => pure expr
      | none => failAt j s!"unbound Yul identifier {name}"
  | "YulFunctionCall" =>
      let fname ← mStr (← mField (← mField j "functionName") "name")
      let args ← mArr (← mField j "arguments")
      let mut xs : Array Expr := #[]
      for arg in args do
        xs := xs.push (← lowerYul arg)
      match fname, xs with
      | "xor", #[a, b] => pure (.bitXor a b)
      | "mul", #[a, b] => pure (.mul a b)
      | "lt", #[a, b] => pure (.lt a b)
      | _, _ => failAt j s!"unsupported Yul builtin {fname}"
  | kind => failAt j s!"unsupported Yul node {kind}"

private partial def lowerExpr (j : Json) : M Val := do
  match ← mKind j with
  | "Literal" =>
      let raw := optStr j "value" |>.getD ""
      if optStr j "kind" == some "bool" then
        unless (← mType j) == "bool" do failAt j "boolean literal has inconsistent type"
        let value ← match raw with
          | "true" => pure 1
          | "false" => pure 0
          | _ => failAt j "invalid boolean literal"
        return { pre := #[], expr := .literal value }
      unless optStr j "kind" == some "number" do failAt j "unsupported non-numeric literal"
      let multiplier ← match optStr j "subdenomination" with
        | none => pure 1
        | some denomination =>
            let some scale := literalUnitScale denomination
              | failAt j s!"unsupported literal denomination {denomination}"
            pure scale
      let some (numerator, denominator) := numericLiteralRatio raw
        | failAt j s!"unsupported literal {raw}"
      let scaled := numerator * multiplier
      unless scaled % denominator == 0 do
        failAt j "fractional numeric literal requires exact constant-expression lowering"
      let n := scaled / denominator
      unless n < 2 ^ 256 do failAt j "numeric literal exceeds an EVM word"
      pure { pre := #[], expr := .literal n }
  | "TupleExpression" =>
      if ← mBool (← mField j "isInlineArray") then failAt j "inline arrays are outside this slice"
      let cs ← mArr (← mField j "components")
      if cs.size == 1 then
        if cs[0]!.isNull then failAt j "empty tuple component"
        lowerExpr cs[0]!
      else
        failAt j "a multi-value expression is only valid as a return"
  | "BinaryOperation" => lowerBinary j
  | "Conditional" => lowerConditional j
  | "FunctionCall" => lowerCall j
  | "Identifier" | "MemberAccess" | "IndexAccess" =>
      match ← lowerRef j with
      | .expr v => pure v
      | .state name pre =>
          let info ← resolveField name j
          unless info.keyCount == 0 do failAt j "mapping used as a scalar value"
          markField name
          pure { pre, expr := .storage name }
      | .path pre path => scalarMappingRead pre path j
      | .fixedElement pre path index =>
          let (name, count, read) ← match path with
            | .one name key => pure (name, 1, fun member => Expr.structMember name key member)
            | .two name key1 key2 => pure (name, 2, fun member => Expr.structMember2 name key1 key2 member)
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
          let info ← resolveField name j
          let some length := info.fixedArrayLength | failAt j "missing fixed array layout"
          unless info.keyCount == count do failAt j "fixed array mapping key count differs"
          let dest ← fresh
          let mut pre := pre.push (.ite (.lt index (.literal length))
            [] [.panicCode (.literal 0x32)]) |>.push (.letVar dest (.literal 0))
          for i in [:length] do
            pre := pre.push (.ite (.eq index (.literal i))
              [.assignVar dest (read s!"__solidity_element_{i}")] [])
          markField name
          pure { pre, expr := .localVar dest }
      | _ => failAt j "storage or memory path used as a value"
  | kind => failAt j s!"unsupported expression {kind}"

private partial def lowerRef (j : Json) : M Ref := do
  match ← mKind j with
  | "Identifier" =>
      let id ← refInt j
      if id < 0 then failAt j "unresolved builtin identifier"
      let n := id.toNat
      let env ← get
      if let some expr := env.values.find? n then
        pure (.expr { pre := #[], expr })
      else if let some path := env.paths.find? n then
        pure (.path #[] path)
      else if let some elements := env.snapshots.find? n then
        pure (.snapshot elements)
      else if env.mems.contains n then
        pure (.mem n #[])
      else if let some decl := env.numericConstants.find? n then
        if env.constantStack.contains n then failAt j "cyclic constant initializer"
        let declared ← mType decl
        unless (declared.startsWith "uint" && (bitsOf declared).isSome) || declared == "bool" do
          failAt j s!"unsupported numeric constant type {declared}"
        let initializer ← mField decl "value"
        modify fun e => { e with constantStack := n :: e.constantStack }
        let value ← lowerExpr initializer
        modify fun e => { e with constantStack := env.constantStack }
        pure (.expr value)
      else if let some decl := env.stateVars.find? n then
        let name ← mStr (← mField decl "name")
        if let some item := env.layoutItems.find? name then
          unless (← mNat (← mField item "astId")) == n do
            failAt j s!"shadowed storage declaration {name} is outside this slice"
        pure (.state name #[])
      else
        failAt j s!"unresolved identifier {id}"
  | "IndexAccess" =>
      let baseExpression ← mField j "baseExpression"
      if (← mKind baseExpression) == "TupleExpression" then
        if ← mBool (← mField baseExpression "isInlineArray") then
          let components ← mArr (← mField baseExpression "components")
          unless components.size > 0 do failAt baseExpression "empty inline constant array"
          let arrayType ← mType baseExpression
          let elementType := (arrayType.splitOn "[").head!
          unless elementType.startsWith "uint" do
            failAt baseExpression "inline constant arrays require unsigned scalar elements"
          let some bits := bitsOf elementType
            | failAt baseExpression "unsupported inline constant array element type"
          let mut constants : Array Nat := #[]
          for component in components do
            let value ← lowerExpr component
            unless value.pre.isEmpty do
              failAt component "inline array elements must be exact natural constants"
            let .literal n := value.expr
              | failAt component "inline array elements must be exact natural constants"
            unless n < 2 ^ bits do failAt component "inline array constant exceeds element width"
            constants := constants.push n
          let indexExpression ← mField j "indexExpression"
          let indexType ← mType indexExpression
          unless indexType.startsWith "uint" || indexType.startsWith "int_const" do
            failAt indexExpression "inline constant array index must be unsigned"
          let key ← atom (← lowerExpr indexExpression)
          let dest ← fresh
          let mut pre := key.pre.push (.ite (.lt key.expr (.literal constants.size))
            [] [.panicCode (.literal 0x32)]) |>.push (.letVar dest (.literal 0))
          for index in [:constants.size] do
            pre := pre.push (.ite (.eq key.expr (.literal index))
              [.assignVar dest (.literal constants[index]!)] [])
          return .expr { pre, expr := .localVar dest }
      let base ← lowerRef baseExpression
      let key ← atom (← lowerExpr (← mField j "indexExpression"))
      match base with
      | .state name pre =>
          let info ← resolveField name j
          markField name
          if info.keyCount == 2 then
            pure (.path (pre ++ key.pre) (.outer name key.expr))
          else
            pure (.path (pre ++ key.pre) (.one name key.expr))
      | .path pre (.outer field k1) =>
          pure (.path (pre ++ key.pre) (.two field k1 key.expr))
      | .path pre path =>
          let name ← match path with
            | .one name _ | .two name _ _ => pure name
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
          let info ← resolveField name j
          unless info.fixedArrayLength.isSome do
            failAt j "index of a storage value requires a fixed array layout"
          let ty ← mType (← mField j "indexExpression")
          unless ty.startsWith "uint" || ty.startsWith "int_const" do
            failAt j "fixed storage array index must be unsigned"
          let captured ← fresh
          pure (.fixedElement ((pre ++ key.pre).push (.letVar captured key.expr))
            path (.localVar captured))
      | .snapshot elements =>
          let ty ← mType (← mField j "indexExpression")
          unless ty.startsWith "uint" || ty.startsWith "int_const" do
            failAt j "fixed memory array index must be unsigned"
          let dest ← fresh
          let mut pre := key.pre.push (.ite (.lt key.expr (.literal elements.size))
            [] [.panicCode (.literal 0x32)]) |>.push (.letVar dest (.literal 0))
          for i in [:elements.size] do
            let some element := elements[i]? | failAt j "missing fixed array snapshot element"
            pre := pre.push (.ite (.eq key.expr (.literal i))
              [.assignVar dest element] [])
          pure (.expr { pre, expr := .localVar dest })
      | .abiArray id memberIndex pre =>
          unless key.pre.isEmpty do
            failAt j "computed struct-array indices require explicit evaluation-order lowering"
          let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
          let some schema := mem.schema | failAt j "missing ABI schema"
          if let some (.scalarArray field) := schema[memberIndex]? then
            if mem.calldataLocation then
              let header ← fresh
              let length ← fresh
              let data ← fresh
              let checks := AbiLowering.staticArrayHead (.localVar (mem.abiStem ++ "_calldata"))
                memberIndex 1 header length data
              let pre := pre ++ checks.toArray ++ #[.ite (.lt key.expr (.localVar length))
                [] [.panicCode (.literal 0x32)]]
              let value := Expr.calldataload (.add (.localVar data) (.mul key.expr (.literal 32)))
              let bound := SolidityAbi.scalarBound field.kind
              let pre := if bound < 2^256 then
                pre.push (AbiLowering.guard (.lt value (.literal bound))) else pre
              return .expr { pre, expr := value }
            else
              let array := Expr.mload (.add (.localVar (mem.abiStem ++ "_memory"))
                (.literal (32*memberIndex)))
              let pre := pre.push (.ite (.lt key.expr (.mload array)) [] [.panicCode (.literal 0x32)])
              let value := Expr.mload (.add (.add array (.literal 32)) (.mul key.expr (.literal 32)))
              return .expr { pre, expr := value }
          let some (.structArray _ fields) := schema[memberIndex]?
            | failAt j "index requires a struct-array member"
          if mem.calldataLocation then
            let header ← fresh
            let length ← fresh
            let data ← fresh
            let checks := AbiLowering.staticArrayHead (.localVar (mem.abiStem ++ "_calldata"))
              memberIndex fields.length header length data
            let pre := pre ++ checks.toArray ++ #[.ite (.lt key.expr (.localVar length))
              [] [.panicCode (.literal 0x32)]]
            pure (.abiElement id memberIndex
              (.add (.localVar data) (.mul key.expr (.literal (32*fields.length)))) pre)
          else
            let array := Expr.mload (.add (.localVar (mem.abiStem ++ "_memory"))
              (.literal (32*memberIndex)))
            let pre := pre.push (.ite (.lt key.expr (.mload array)) [] [.panicCode (.literal 0x32)])
            pure (.abiElement id memberIndex
              (.mload (.add (.add array (.literal 32)) (.mul key.expr (.literal 32)))) pre)
      | _ => failAt j "index of a non-mapping or unsupported ABI value"
  | "MemberAccess" =>
      let member ← mStr (← mField j "memberName")
      let base ← mField j "expression"
      if (← mKind base) == "Identifier" &&
          optStr base "name" == some "block" &&
          optStr ((field? base "typeDescriptions").getD Json.null) "typeIdentifier" == some "t_magic_block" then
        unless (← refInt base) == -4 do failAt base "block does not resolve to the Solidity builtin"
        let expression ← match member with
          | "timestamp" => pure Expr.blockTimestamp
          | "number" => pure Expr.blockNumber
          | "chainid" => pure Expr.chainid
          | _ => failAt j s!"unsupported block context member {member}"
        pure (.expr { pre := #[], expr := expression })
      else if (← mKind base) == "Identifier" && optStr base "name" == some "msg" &&
          optStr ((field? base "typeDescriptions").getD Json.null) "typeIdentifier" == some "t_magic_message" then
        unless (← refInt base) == -15 do failAt base "msg does not resolve to the Solidity builtin"
        unless member == "sender" do failAt j s!"unsupported message context member {member}"
        pure (.expr { pre := #[], expr := .caller })
      else if member == "max" then
        lowerTypeMax j base
      else
        match ← lowerRef base with
        | .path pre path =>
            pure (.expr (← memberRead pre path member j))
        | .mem id pre =>
            let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
            if let some schema := mem.schema then
              if let some i := mem.members.findIdx? (fun p => p.1 == member) then
                if let some (.structArray _ _) := schema[i]? then
                  return .abiArray id i pre
                if let some (.scalarArray _) := schema[i]? then
                  return .abiArray id i pre
            pure (.expr (← readAbiMember id pre member j))
        | .abiArray id memberIndex pre =>
            unless member == "length" do failAt j s!"unsupported array member {member}"
            let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
            let some schema := mem.schema | failAt j "missing ABI schema"
            let elementWords ← match schema[memberIndex]? with
              | some (.scalarArray _) => pure 1
              | some (.structArray _ fields) => pure fields.length
              | _ => failAt j "length requires a schema-checked ABI array"
            if mem.calldataLocation then
              let header ← fresh
              let length ← fresh
              let data ← fresh
              let checks := AbiLowering.staticArrayHead
                (.localVar (mem.abiStem ++ "_calldata")) memberIndex elementWords header length data
              return .expr { pre := pre ++ checks.toArray, expr := .localVar length }
            else
              let array := Expr.mload (.add (.localVar (mem.abiStem ++ "_memory"))
                (.literal (32*memberIndex)))
              return .expr { pre, expr := .mload array }
        | .abiElement id memberIndex pointer pre =>
            let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
            let some schema := mem.schema | failAt j "missing ABI schema"
            let some (.structArray _ fields) := schema[memberIndex]?
              | failAt j "expected a struct-array element"
            let some i := fields.findIdx? (fun f => f.name == member)
              | failAt j s!"unknown struct-array member {member}"
            let some field := fields[i]? | failAt j "missing struct-array field"
            let offset := Expr.add pointer (.literal (32*i))
            let value := if mem.calldataLocation then Expr.calldataload offset else Expr.mload offset
            let bound := SolidityAbi.scalarBound field.kind
            let pre := if mem.calldataLocation && bound < 2^256 then
              pre.push (AbiLowering.guard (.lt value (.literal bound))) else pre
            pure (.expr { pre, expr := value })
        | _ => failAt j s!"unsupported member {member}"
  | kind => failAt j s!"unsupported reference {kind}"

private partial def lowerTypeMax (at_ base : Json) : M Ref := do
  unless (← mKind base) == "FunctionCall" do
    failAt at_ "max is only supported on type(T)"
  let callee ← mField base "expression"
  unless (← mKind callee) == "Identifier" && optStr callee "name" == some "type" do
    failAt at_ "max is only supported on type(T)"
  let args ← mArr (← mField base "arguments")
  unless args.size == 1 do failAt at_ "type() expects one argument"
  let arg := args[0]!
  unless (← mKind arg) == "ElementaryTypeNameExpression" do
    failAt at_ "type() expects an elementary type"
  let tname ← mStr (← mField (← mField arg "typeName") "name")
  let some bits := bitsOf tname | failAt at_ s!"unsupported type().max {tname}"
  pure (.expr { pre := #[], expr := .literal (2 ^ bits - 1) })

private partial def readAbiMember (id : Nat) (pre : Array Stmt) (member : String) (at_ : Json) : M Val := do
  let some mem := (← get).mems.find? id | failAt at_ "unknown memory parameter"
  let some idx := mem.members.findIdx? (fun p => p.1 == member)
    | failAt at_ s!"{member} is not a member of {mem.structName}"
  if let some schema := mem.schema then
    let some (.scalar field) := schema[idx]? | failAt at_ "struct array used as a scalar"
    let plan := AbiRootLowering.root mem.abiStem 0 0 schema (!mem.calldataLocation)
    let (checks, expr) := AbiRootLowering.scalarRead plan (!mem.calldataLocation) idx field.kind
    return { pre := pre ++ checks.toArray, expr }
  if let some types := mem.staticTypes then
    let modelParam := s!"{mem.param}_{idx}"
    let some ty := types[idx]? | failAt at_ "missing static tuple member type"
    let limit := match ty with
      | .uintN bits => if bits < 256 then some (2^bits) else none
      | .address => some (2^160)
      | .bool => some 2
      | _ => none
    let mut pre := pre
    if mem.calldataLocation then
      if let some bound := limit then
        pre := pre.push (.ite
          (.lt (.calldataload (.add (.localVar mem.headBinding) (.literal (32*idx))))
            (.literal bound)) [] [.revertReturndata])
    return { pre, expr := .param modelParam }
  failAt at_ "struct member has no supported complete ABI schema"

private partial def lowerBinary (j : Json) : M Val := do
  let op ← mStr (← mField j "operator")
  unless op == "&&" || op == "||" do
    let env ← get
    if statefulCallIn (← mField j "leftExpression") env ||
        statefulCallIn (← mField j "rightExpression") env then
      failAt j "stateful helper operands require explicit evaluation-order support"
  let left ← lowerExpr (← mField j "leftExpression")
  let right ← lowerExpr (← mField j "rightExpression")
  let common ← mStr (← mField (← mField j "commonType") "typeString")
  -- Solidity folds literal sums in unbounded integer arithmetic. Admit only
  -- exact natural literals whose sum remains representable as an EVM word.
  if common.startsWith "int_const" && op == "+" then
    if left.pre.isEmpty && right.pre.isEmpty then
      if let .literal a := left.expr then
        if let .literal b := right.expr then
          let sum := a + b
          if sum < 2 ^ 256 then return { pre := #[], expr := .literal sum }
    failAt j "unsupported integer constant sum"
  -- Products of exact natural literals use Solidity's unbounded constant arithmetic.
  if common.startsWith "int_const" && op == "*" then
    if left.pre.isEmpty && right.pre.isEmpty then
      if let .literal a := left.expr then
        if let .literal b := right.expr then
          let product := a * b
          if product < 2 ^ 256 then return { pre := #[], expr := .literal product }
    failAt j "unsupported integer constant product"
  unless (bitsOf common).isSome || common == "bool" do
    failAt j s!"unsupported operand type {common}"
  match op with
  | "&&" | "||" =>
      unless common == "bool" do failAt j s!"unsupported logical operand type {common}"
      let a ← atom left
      let dest ← fresh
      -- Solidity evaluates the RHS only when the LHS does not determine the
      -- result. Keep its guards and helper prelude inside the selected branch.
      let rhs := right.pre.push (.assignVar dest right.expr)
      let branch := if op == "&&" then Stmt.ite a.expr rhs.toList []
        else Stmt.ite a.expr [] rhs.toList
      pure { pre := a.pre.push (.letVar dest a.expr) |>.push branch,
             expr := .localVar dest }
  | "+" =>
      let some bits := bitsOf common | failAt j s!"unsupported add type {common}"
      checkedAdd bits left right
  | "-" => checkedSub left right
  | "*" =>
      let some bits := bitsOf common | failAt j s!"unsupported mul type {common}"
      checkedMul bits left right
  | "/" => checkedDiv left right
  | "%" =>
      unless common.startsWith "uint" do failAt j "modulo requires unsigned scalar operands"
      checkedModulo left right
  | "<" => cmp .lt left right
  | ">" => cmp .gt left right
  | "<=" => cmp .le left right
  | ">=" => cmp .ge left right
  | "==" => cmp .eq left right
  | "!=" =>
      let v ← cmp .eq left right
      pure { v with expr := .logicalNot v.expr }
  | _ => failAt j s!"unsupported operator {op}"

private partial def checkedSub (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let ok := Stmt.assignVar dest (.sub a.expr b.expr)
  let ite := iteStmt (.lt a.expr b.expr) overflowPanic ok
  pure { pre := a.pre ++ b.pre |>.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }

private partial def checkedDiv (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let ok := Stmt.assignVar dest (.div a.expr b.expr)
  let ite := iteStmt (.eq b.expr (.literal 0)) divPanic ok
  pure { pre := a.pre ++ b.pre |>.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }

private partial def checkedModulo (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let moduloResult := Stmt.assignVar dest (.mod a.expr b.expr)
  let moduloGuard := iteStmt (.eq b.expr (.literal 0)) divPanic moduloResult
  pure { pre := a.pre ++ b.pre |>.push (.letVar dest (.literal 0)) |>.push moduloGuard,
         expr := .localVar dest }

private partial def checkedAdd (bits : Nat) (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let sum := Expr.add a.expr b.expr
  let ok := Stmt.assignVar dest sum
  let cond :=
    if bits == 256 then Expr.lt sum a.expr
    else Expr.lt (.literal (2 ^ bits - 1)) sum
  pure { pre := a.pre ++ b.pre |>.push (.letVar dest (.literal 0)) |>.push (iteStmt cond overflowPanic ok),
         expr := .localVar dest }

private partial def checkedMul (bits : Nat) (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let prod := Expr.mul a.expr b.expr
  let ok := Stmt.assignVar dest prod
  -- Check the EVM-width product before the Solidity-width bound. For e.g.
  -- uint248, an overflowing 256-bit product can wrap below the uint248 bound.
  let bounded := if bits == 256 then ok
    else iteStmt (.lt (.literal (2 ^ bits - 1)) prod) overflowPanic ok
  let inner := iteStmt (.eq (.div prod a.expr) b.expr) bounded overflowPanic
  let ite := iteStmt (.eq a.expr (.literal 0)) bounded inner
  pure { pre := a.pre ++ b.pre |>.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }

private partial def cmp (op : Expr → Expr → Expr) (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  pure { pre := a.pre ++ b.pre, expr := op a.expr b.expr }

private partial def lowerConditional (j : Json) : M Val := do
  let cond ← atom (← lowerExpr (← mField j "condition"))
  let yes ← lowerExpr (← mField j "trueExpression")
  let no ← lowerExpr (← mField j "falseExpression")
  let dest ← fresh
  let thenB := yes.pre.push (.assignVar dest yes.expr)
  let elseB := no.pre.push (.assignVar dest no.expr)
  let ite := Stmt.ite cond.expr thenB.toList elseB.toList
  pure { pre := cond.pre.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }

private partial def lowerCast (j : Json) : M Val := do
  let targetExpr ← mField j "expression"
  unless (← mKind targetExpr) == "ElementaryTypeNameExpression" do
    failAt j "unsupported cast"
  let tname ← mStr (← mField (← mField targetExpr "typeName") "name")
  let some bits := bitsOf tname | failAt j s!"unsupported cast target {tname}"
  let args ← mArr (← mField j "arguments")
  unless args.size == 1 do failAt j "cast expects one argument"
  let v ← lowerExpr args[0]!
  let src := ← mType args[0]!
  let narrow : Bool :=
    match bitsOf src with
    | some sb => decide (sb > bits)
    | none => decide (bits < 256) && !src.startsWith "int_const"
  if narrow then
    let a ← atom v
    let dest ← fresh
    let bound := Stmt.letVar dest (.bitAnd a.expr (.literal (2 ^ bits - 1)))
    pure { pre := a.pre.push bound, expr := .localVar dest }
  else
    pure v

/-- Restrict the entire argument tree, not merely its outer cast. This keeps
custom reverts or effects hidden beneath a cast out of the admitted fragment. -/
private partial def checkEncodingScalar (j : Json) : M Unit := do
  match ← mKind j with
  | "Identifier" | "Literal" => pure ()
  | "MemberAccess" => checkEncodingScalar (← mField j "expression")
  | "FunctionCall" =>
      unless optStr j "kind" == some "typeConversion" do
        failAt j "effectful ABI encoding argument is unsupported"
      for arg in (← mArr (← mField j "arguments")) do checkEncodingScalar arg
  | _ => failAt j "effectful ABI encoding argument is unsupported"

/-- Encode one root tuple from its complete declaration schema. Array
payloads contain inline scalar words, even when source memory holds pointers
to the array's struct elements. Calldata is validated as it is consumed. -/
private partial def lowerEncodedRoot (arg : Json) : M EncodedBytes := do
  let .mem id effects ← lowerRef arg
    | failAt arg "ABI encoding requires a root struct reference"
  let some mem := (← get).mems.find? id | failAt arg "unknown encoding root"
  let pointer ← fresh
  let finish ← fresh
  modify fun env => { env with encodingMemory := true }
  if let some types := mem.staticTypes then
    let mut pre := effects
    let mut values := []
    for (name, _) in mem.members do
      let value ← atom (← readAbiMember id #[] name arg)
      pre := pre ++ value.pre
      values := values ++ [value.expr]
    unless values.length == types.length do failAt arg "static encoding schema mismatch"
    pre := pre ++ (AbiEncoding.staticWords pointer finish values).toArray
    return { pre, pointer := .localVar pointer, size := .literal (32 * values.length) }
  let some schema := mem.schema | failAt arg "missing full ABI encoding schema"
  let base := Expr.localVar pointer
  let tuple := Expr.add base (.literal 32)
  let mut pre := effects ++ (AbiEncoding.reserve pointer finish
    (.literal (32 * (schema.length + 1)))).toArray
  pre := pre.push (.mstore base (.literal 32))
  for (member, memberIndex) in schema.zipIdx do
    let destination := Expr.add tuple (.literal (32 * memberIndex))
    match member with
    | .scalar field =>
        let value ← atom (← readAbiMember id #[] field.name arg)
        pre := pre ++ value.pre
        pre := pre.push (.mstore destination value.expr)
    | .scalarArray _ | .structArray _ _ =>
        let kinds : List SolidityAbi.ScalarKind := match member with
          | .scalarArray field => [field.kind]
          | .structArray _ fields => fields.map (fun (field : AbiSchema.ScalarField) => field.kind)
          | .scalar _ => []
        let scalarArray := match member with
          | .scalarArray _ => true
          | _ => false
        let header ← fresh
        let length ← fresh
        let data ← fresh
        if mem.calldataLocation then
          pre := pre ++ (AbiLowering.staticArrayHead
            (.localVar (mem.abiStem ++ "_calldata")) memberIndex kinds.length
            header length data).toArray
        else
          pre := pre ++ #[
            .letVar header (.mload (.add (.localVar (mem.abiStem ++ "_memory"))
              (.literal (32 * memberIndex)))),
            .letVar length (.mload (.localVar header)),
            .letVar data (.add (.localVar header) (.literal 32))]
        let tail ← fresh
        let tailEnd ← fresh
        let payloadSize := Expr.mul (.localVar length) (.literal (32 * kinds.length))
        pre := pre ++ (AbiEncoding.reserve tail tailEnd
          (.add (.literal 32) payloadSize)).toArray
        pre := pre ++ #[.mstore destination (.sub (.localVar tail) tuple),
          .mstore (.localVar tail) (.localVar length)]
        let index ← fresh
        let source ← fresh
        let sourceAddress := if mem.calldataLocation || scalarArray then
          Expr.add (.localVar data) (.mul (.localVar index) (.literal (32 * kinds.length)))
          else Expr.mload (.add (.localVar data) (.mul (.localVar index) (.literal 32)))
        let mut body : List Stmt := [.letVar source sourceAddress]
        for (kind, fieldIndex) in kinds.zipIdx do
          let address := Expr.add (.localVar source) (.literal (32 * fieldIndex))
          let value := if mem.calldataLocation then Expr.calldataload address else Expr.mload address
          let bound := SolidityAbi.scalarBound kind
          if mem.calldataLocation && bound < 2^256 then
            body := body ++ [AbiLowering.guard (.lt value (.literal bound))]
          let offset := Expr.add (.literal (32 * fieldIndex))
            (.mul (.localVar index) (.literal (32 * kinds.length)))
          body := body ++ [.mstore (.add (.add (.localVar tail) (.literal 32)) offset) value]
        pre := pre.push (.forEach index (.localVar length) body)
  let size ← fresh
  pre := pre.push (.letVar size (.sub (.mload (.literal 64)) base))
  return { pre, pointer := base, size := .localVar size }

/-- Literal bytes are stored as right-zero-padded words; their logical size
excludes that padding. `hexValue` is solc's byte spelling, including UTF-8. -/
private partial def lowerLiteralBytes (j : Json) : M EncodedBytes := do
  let some hex := optStr j "hexValue" | failAt j "missing literal byte spelling"
  unless hex.length % 2 == 0 do failAt j "invalid literal byte spelling"
  let chars := hex.toList.toArray
  let mut words : List Expr := []
  let mut word := 0
  for index in [:chars.size] do
    let some digit := Compiler.Hex.hexCharToNat? chars[index]!
      | failAt j "invalid literal hex digit"
    word := word * 16 + digit
    if index % 64 == 63 then
      words := words ++ [.literal word]
      word := 0
  if chars.size % 64 != 0 then
    words := words ++ [.literal (word * 16^(64 - chars.size % 64))]
  let pointer ← fresh
  let finish ← fresh
  modify fun env => { env with encodingMemory := true }
  return { pre := (AbiEncoding.staticWords pointer finish words).toArray,
           pointer := .localVar pointer, size := .literal (hex.length / 2) }

private partial def lowerPackedArgument (j : Json) : M EncodedBytes := do
  let ty ← mType j
  if let some _ := paramType ty then
    -- Hash builtins consume only admitted byte buffers; other function calls
    -- remain rejected even if hidden beneath a scalar cast.
    let mut hashCall := false
    if (← mKind j) == "FunctionCall" then
      let callee ← mField j "expression"
      if (← mKind callee) == "Identifier" then
        hashCall := (← refInt callee) == -8
    unless hashCall do checkEncodingScalar j
    let value ← atom (← lowerExpr j)
    let size := if ty == "bool" then 1 else (bitsOf ty).getD 256 / 8
    let pointer ← fresh
    let finish ← fresh
    modify fun env => { env with encodingMemory := true }
    let padded := Expr.mul value.expr (.literal (2^(8*(32-size))))
    let pre := value.pre ++ (AbiEncoding.staticWords pointer finish [padded]).toArray
    return { pre, pointer := .localVar pointer, size := .literal size }
  lowerEncodedBytes j

private partial def lowerPacked (args : Array Json) : M EncodedBytes := do
  let mut buffers : List EncodedBytes := []
  let mut pre := #[]
  -- Pinned solc via-IR evaluates nested ABI arguments from right to left.
  -- Bind every input buffer before allocating or writing the output buffer.
  for arg in args.reverse do
    let buffer ← lowerPackedArgument arg
    pre := pre ++ buffer.pre
    buffers := buffer :: buffers
  let sizeName ← fresh
  let size := Expr.localVar sizeName
  let length := buffers.foldl (fun total buffer => Expr.add total buffer.size) (.literal 0)
  pre := pre.push (.letVar sizeName length)
  let pointer ← fresh
  let finish ← fresh
  let clearIndex ← fresh
  pre := pre ++ (AbiEncoding.packedBuffer pointer finish clearIndex size).toArray
  let start ← fresh
  pre := pre.push (.letVar start (.literal 0))
  for buffer in buffers do
    let index ← fresh
    let byteName ← fresh
    let address ← fresh
    pre := pre.push (AbiEncoding.copyBytes buffer.pointer (.localVar pointer)
      (.localVar start) buffer.size index byteName address)
    pre := pre.push (.assignVar start (.add (.localVar start) buffer.size))
  modify fun env => { env with encodingMemory := true }
  return { pre, pointer := .localVar pointer, size }

/-- Encode complete admitted byte schemas, without name-based library rules. -/
private partial def lowerEncodedBytes (j : Json) : M EncodedBytes := do
  if (← mKind j) == "Literal" then
    unless optStr j "kind" == some "hexString" || optStr j "kind" == some "string" ||
        optStr j "kind" == some "unicodeString" do
      failAt j "unsupported literal byte buffer"
    return ← lowerLiteralBytes j
  if (← mKind j) == "Identifier" then
    let id ← refInt j
    let some decl := (← get).stateVars.find? id.toNat
      | failAt j "only literal constants are supported as named byte buffers"
    unless (field? decl "constant").bind (fun value => value.getBool?.toOption) == some true do
      failAt j "mutable byte buffers are unsupported"
    let value ← mField decl "value"
    unless (← mKind value) == "Literal" do
      failAt value "byte constant must have a literal initializer"
    return ← lowerEncodedBytes value
  unless (← mKind j) == "FunctionCall" do
    failAt j "hash input must be a supported ABI encoding"
  let callee ← mField j "expression"
  unless (← mKind callee) == "MemberAccess" do
    failAt callee "hash input must be a supported ABI encoding"
  let base ← mField callee "expression"
  unless (← mKind base) == "Identifier" && optStr base "name" == some "abi" &&
      (← refInt base) == -1 do
    failAt callee "encoding does not resolve to the abi builtin"
  let args ← mArr (← mField j "arguments")
  if optStr callee "memberName" == some "encodePacked" then
    return ← lowerPacked args
  unless optStr callee "memberName" == some "encode" do
    failAt callee "unsupported ABI encoding builtin"
  if args.size == 1 then
    if (← mType args[0]!).startsWith "struct " then
      return ← lowerEncodedRoot args[0]!
  let mut pre := #[]
  let mut words := []
  for arg in args do
    let ty ← mType arg
    unless (paramType ty).isSome do
      failAt arg s!"unsupported ABI encoding argument type {ty}"
    -- Avoid assigning an evaluation order to multiple effectful arguments.
    -- Scalar paths and casts have no source-level writes or custom reverts.
    checkEncodingScalar arg
    let value ← atom (← lowerExpr arg)
    pre := pre ++ value.pre
    words := words ++ [value.expr]
  let pointer ← fresh
  let finish ← fresh
  modify fun env => { env with encodingMemory := true }
  pre := pre ++ (AbiEncoding.staticWords pointer finish words).toArray
  return { pre, pointer := .localVar pointer, size := .literal (32 * words.length) }

private partial def lowerCall (j : Json) : M Val := do
  let names ← mArr (← mField j "names")
  unless names.isEmpty do failAt j "named call arguments are outside this slice"
  let kind ← mStr (← mField j "kind")
  if kind == "typeConversion" then
    let args ← mArr (← mField j "arguments")
    if (← mType j) == "address" && args.size == 1 &&
        (← mKind args[0]!) == "Identifier" && optStr args[0]! "name" == some "this" then
      unless (← refInt args[0]!) == -28 do
        failAt args[0]! "this does not resolve to the current contract builtin"
      return { pre := #[], expr := .contractAddress }
    lowerCast j
  else if kind == "functionCall" then
    let callee ← mField j "expression"
    if (← mKind callee) == "Identifier" && (← refInt callee) == -8 then
      let args ← mArr (← mField j "arguments")
      unless args.size == 1 do failAt j "keccak256 requires one byte buffer"
      let bytes ← lowerEncodedBytes args[0]!
      return { pre := bytes.pre, expr := .keccak256 bytes.pointer bytes.size }
    let (fnId, receiver?) ← match ← mKind callee with
      | "MemberAccess" =>
          let id ← refInt callee
          if id < 0 then failAt callee "builtin call is outside this slice"
          let base ← mField callee "expression"
          let baseTy ← mType base
          if baseTy.startsWith "type(library " then
            pure (id.toNat, none)
          else
            pure (id.toNat, some base)
      | "Identifier" =>
          let id ← refInt callee
          if id < 0 then failAt callee "builtin call is outside this slice"
          pure (id.toNat, none)
      | _ => failAt callee "unsupported callee"
    let args ← mArr (← mField j "arguments")
    let nodes := match receiver? with
      | some recv => #[recv] ++ args
      | none => args
    let mut vals : Array CallArg := #[]
    for arg in nodes do
      if statefulCallIn arg (← get) then
        failAt arg "stateful helper call arguments require explicit evaluation-order support"
      if (← mType arg).startsWith "struct " then
        match ← lowerRef arg with
        | .mem id pre =>
            let some descriptor := (← get).mems.find? id
              | failAt arg "unknown reference argument"
            vals := vals.push (.memory descriptor pre)
        | _ => failAt arg "only root memory/calldata struct arguments are supported"
      else
        vals := vals.push (.scalar (← lowerExpr arg))
    inlineFn fnId vals j
  else
    failAt j s!"unsupported call kind {kind}"

private partial def inlineFn (fnId : Nat) (args : Array CallArg) (at_ : Json) : M Val := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  -- External library calls cross an ABI/delegatecall boundary. A root
  -- descriptor may only be shared with helpers in the same call frame.
  if optStr fn "visibility" == some "external" then
    for arg in args do
      match arg with
      | .memory _ _ => failAt at_ "external reference helper calls are unsupported"
      | .scalar _ => pure ()
  let saved := ← get
  let savedYul := saved.yulNames
  let savedFile := (← get).currentFile
  let frameFile := (← get).nodeFile.find? fnId |>.getD (← get).currentFile
  let frame := fnId :: (← get).stack
  modify fun e => { e with stack := frame, currentFile := frameFile }
  if (field? fn "virtual").bind (fun v => v.getBool?.toOption) == some true then
    failAt fn "virtual dispatch is outside this slice"
  let mods ← mArr (← mField fn "modifiers")
  unless mods.isEmpty do failAt fn "modifiers are outside this slice"
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "only single-value helpers are inlined"
  let retName ← mStr (← mField rets[0]! "name")
  let mut pre : Array Stmt := #[]
  let mut yul := savedYul
  for i in [:params.size] do
    let p := params[i]!
    let pname ← mStr (← mField p "name")
    let pid ← mNat (← mField p "id")
    let pty ← mType p
    let argNode ← argumentAt at_ i
    let argTy ← mType argNode
    let some arg := args[i]? | failAt at_ s!"missing argument {i}"
    match arg with
    | .scalar value =>
        let converted ← convert pty argTy value at_
        let bound ← atom converted
        pre := pre ++ bound.pre
        modify fun e => { e with values := e.values.insert pid bound.expr }
        if pname != "" then
          yul := yul.insert pname bound.expr
    | .memory descriptor effects =>
        unless pty.startsWith "struct " do
          failAt p "reference argument requires a struct parameter"
        let sid ← refInt (← mField p "typeName")
        unless sid >= 0 && sid.toNat == descriptor.structId do
          failAt p "reference argument struct declaration differs"
        let location := optStr p "storageLocation" |>.getD "default"
        let expected := if descriptor.calldataLocation then "calldata" else "memory"
        unless location == expected do
          failAt p "reference argument location conversion is unsupported"
        pre := pre ++ effects
        modify fun e => { e with mems := e.mems.insert pid descriptor }
        if pname != "" then
          yul := yul.erase pname
  modify fun e => { e with yulNames := yul }
  noteFn fn
  let body ← mField fn "body"
  let stmts ← mArr (← mField body "statements")
  let result ← lowerHelper stmts retName
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, currentFile := savedFile,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems }
  pure { pre := pre ++ result.pre, expr := result.expr }

private partial def argumentAt (call : Json) (i : Nat) : M Json := do
  -- `i` counts the receiver plus explicit arguments. The receiver is not in
  -- `arguments` when the call is `using for`.
  let callee ← mField call "expression"
  let args ← mArr (← mField call "arguments")
  let hasReceiver ← match ← mKind callee with
    | "MemberAccess" =>
        let base ← mField callee "expression"
        pure !(← mType base).startsWith "type(library "
    | _ => pure false
  if hasReceiver then
    if i == 0 then mField callee "expression" else pure args[i - 1]!
  else
    pure args[i]!

private partial def convert (paramTy argTy : String) (v : Val) (at_ : Json) : M Val := do
  match bitsOf paramTy, bitsOf argTy with
  | some pb, some sb =>
      if sb ≤ pb then pure v
      else failAt at_ s!"implicit narrowing from {argTy} to {paramTy}"
  | _, _ =>
      if argTy.startsWith "int_const" || argTy == paramTy then pure v
      else failAt at_ s!"unsupported implicit conversion from {argTy} to {paramTy}"

private partial def lowerHelper (stmts : Array Json) (retName : String) : M Val := do
  let (pre, result) ← lowerHelperFrom stmts.toList retName
  match result with
  | some expr => pure { pre, expr }
  | none => throwError "inlined helper did not return"

/-- Splits an `if` into its lowered boolean condition and branch statements.
    A branch that is not a block is a single statement. -/
private partial def ifParts (s : Json) : M (Val × Array Json × Array Json) := do
  let conditionNode ← mField s "condition"
  unless (← mType conditionNode) == "bool" do failAt conditionNode "if condition must be bool"
  let condition ← atom (← lowerExpr conditionNode)
  let branch (j : Json) : M (Array Json) := do
    if (← mKind j) == "Block" then mArr (← mField j "statements") else pure #[j]
  let yes ← branch (← mField s "trueBody")
  let no ← match field? s "falseBody" with
    | some j => if j.isNull then pure #[] else branch j
    | none => pure #[]
  pure (condition, yes, no)

/-- Syntactic definite return: every path through `s` ends in a helper result.
    Assembly results count because `lowerHelperFrom` treats them as results. -/
private partial def helperReturns (s : Json) : M Bool := do
  match ← mKind s with
  | "Return" | "InlineAssembly" => pure true
  | "Block" => ((← mArr (← mField s "statements")).back?.map helperReturns).getD (pure false)
  | "IfStatement" =>
      let yes ← helperReturns (← mField s "trueBody")
      let no ← match field? s "falseBody" with
        | some j => if j.isNull then pure false else helperReturns j
        | none => pure false
      pure (yes && no)
  | _ => pure false

private partial def helperListReturns (stmts : Array Json) : M Bool := do
  match stmts.back? with
  | some s => helperReturns s
  | none => pure false

/-- Shared exact loop checks; the caller supplies its own return semantics. -/
private partial def lowerFor (s : Json) (lowerBody : Json → M (Array Stmt)) : M (Array Stmt) := do
  -- Only `for (uint256 i = 0; i < n; i++)` with an invariant `n` and a
  -- counter the body never assigns: then solc's per-iteration `i < n`
  -- test is exactly `forEach i n`, and `i++` cannot overflow.
  let init ← mField s "initializationExpression"
  unless (← mKind init) == "VariableDeclarationStatement" do
    failAt s "a for loop must declare its counter"
  let decls ← mArr (← mField init "declarations")
  unless decls.size == 1 && !decls[0]!.isNull do
    failAt init "a for loop must declare exactly one counter"
  let d := decls[0]!
  let counter ← mNat (← mField d "id")
  let counterName ← mStr (← mField d "name")
  unless (← mType d) == "uint256" do failAt d "a for loop counter must be uint256"
  if let some start := (field? init "initialValue").filter (!·.isNull) then
    unless (← mType start) == "int_const 0" do failAt start "a for loop counter must start at 0"
  let body ← mField s "body"
  let writes := bodyAssignedIds body
  if writes.contains counter then
    failAt d "a for loop counter must not be assigned in the loop body"
  let isCounter (j : Json) : M Bool := do
    if (← mKind j) != "Identifier" then return false
    pure ((← refInt j) == counter)
  let step ← mField (← mField s "loopExpression") "expression"
  let stepOk ← match ← mKind step with
    | "UnaryOperation" =>
        pure (optStr step "operator" == some "++" && (← isCounter (← mField step "subExpression")))
    | "Assignment" =>
        pure (optStr step "operator" == some "+=" && (← isCounter (← mField step "leftHandSide")) &&
          (← mType (← mField step "rightHandSide")) == "int_const 1")
    | _ => pure false
  unless stepOk do failAt step "a for loop must increment its counter by one"
  let cond ← mField s "condition"
  unless (← mKind cond) == "BinaryOperation" && optStr cond "operator" == some "<" do
    failAt cond "a for loop condition must be counter < bound"
  unless ← isCounter (← mField cond "leftExpression") do
    failAt cond "a for loop condition must be counter < bound"
  let boundNode ← mField cond "rightExpression"
  let abiLength ← if (← mKind boundNode) == "MemberAccess" &&
      optStr boundNode "memberName" == some "length" then do
    match ← lowerRef (← mField boundNode "expression") with
    | .abiArray _ _ pre => pure pre.isEmpty
    | _ => pure false
  else pure false
  let bound ← lowerExpr boundNode
  let invariant ← match bound.expr with
    | .literal _ | .param _ => pure true
    | .localVar _ =>
        if (← mKind boundNode) == "Identifier" then
          pure (!writes.contains (← refInt boundNode).toNat)
        else pure false
    | _ => pure false
  unless abiLength || (bound.pre.isEmpty && invariant) do
    failAt boundNode "a for loop bound must be a literal, a parameter or an unassigned local"
  let binding ← freshFor counterName
  let saved ← get
  modify fun e =>
    { e with values := e.values.insert counter (.localVar binding),
             yulNames := e.yulNames.insert counterName (.localVar binding) }
  let bodyOut ← lowerBody body
  if abiLength && !abiHeaderPreservingList bodyOut.toList then
    failAt body "ABI-length loop body may write memory or call external code"
  modify fun e =>
    { e with values := saved.values, paths := saved.paths,
             snapshots := saved.snapshots, mems := saved.mems, scalarTy := saved.scalarTy,
             writableLocals := saved.writableLocals, yulNames := saved.yulNames }
  let mut out : Array Stmt := #[]
  if abiLength then
    let captured ← fresh
    out := out ++ bound.pre |>.push (.letVar captured bound.expr)
    out := out.push (.forEach binding (.localVar captured) bodyOut.toList)
  else
    out := out.push (.forEach binding bound.expr bodyOut.toList)
  pure out

private partial def lowerHelperLoopBody (body : Json) : M (Array Stmt) := do
  let statements ← if (← mKind body) == "Block" then mArr (← mField body "statements") else pure #[body]
  let mut out : Array Stmt := #[]
  for statement in statements do
    match ← mKind statement with
    | "Block" =>
        let saved ← get
        out := out ++ (← lowerHelperLoopBody statement)
        modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, scalarTy := saved.scalarTy, yulNames := saved.yulNames }
    | "VariableDeclarationStatement" => out := out ++ (← lowerLocal statement)
    | "ExpressionStatement" => out := out ++ (← lowerEffect statement)
    | "EmitStatement" => out := out ++ (← lowerEmit statement)
    | "ForStatement" => out := out ++ (← lowerFor statement lowerHelperLoopBody)
    | "IfStatement" =>
        let (condition, _yes, no) ← ifParts statement
        let saved ← get
        let restore : M Unit := modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, scalarTy := saved.scalarTy, yulNames := saved.yulNames }
        let yesOut ← lowerHelperLoopBody (← mField statement "trueBody")
        restore
        let noOut ← if no.isEmpty then pure #[] else lowerHelperLoopBody (← mField statement "falseBody")
        restore
        out := out ++ condition.pre |>.push (.ite condition.expr yesOut.toList noOut.toList)
    | "Return" => failAt statement "return inside an inlined helper loop is unsupported"
    | kind => failAt statement s!"unsupported helper loop statement {kind}"
  pure out

/-- Lowers helper statements to a prelude and, when the list returns, its
    result. A returning `if` branch ends the list; the continuation after the
    `if` is lowered once, inside the branch that falls through. -/
private partial def lowerHelperFrom (stmts : List Json) (retName : String) :
    M (Array Stmt × Option Expr) := do
  match stmts with
  | [] => pure (#[], none)
  | s :: rest =>
    match ← mKind s with
    | "VariableDeclarationStatement" =>
        let pre ← lowerLocal s
        let (tail, result) ← lowerHelperFrom rest retName
        pure (pre ++ tail, result)
    | "ExpressionStatement" =>
        -- Use the same exact assignment/delete and require rules as root bodies.
        -- The helper continuation still resumes only after these effects.
        let pre ← lowerEffect s
        let (tail, result) ← lowerHelperFrom rest retName
        pure (pre ++ tail, result)
    | "ForStatement" =>
        let pre ← lowerFor s lowerHelperLoopBody
        let (tail, result) ← lowerHelperFrom rest retName
        pure (pre ++ tail, result)
    | "Return" =>
        if let some next := rest.head? then failAt next "statement after helper result"
        let v ← lowerExpr (← mField s "expression")
        pure (v.pre, some v.expr)
    | "InlineAssembly" =>
        if let some next := rest.head? then failAt next "statement after helper result"
        let v ← lowerAssembly s retName
        pure (v.pre, some v.expr)
    | "IfStatement" =>
        let (condition, yes, no) ← ifParts s
        let yesReturns ← helperListReturns yes
        let noReturns ← helperListReturns no
        if yesReturns && noReturns then
          if let some next := rest.head? then failAt next "statement after helper result"
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames }
        if !yesReturns && !noReturns then
          -- Neither branch returns: branch-local declarations stay scoped and
          -- the continuation is lowered once after the conditional.
          let (yesPre, _) ← lowerHelperFrom yes.toList retName
          restore
          let (noPre, _) ← lowerHelperFrom no.toList retName
          restore
          let (tail, result) ← lowerHelperFrom rest retName
          pure (condition.pre.push (.ite condition.expr yesPre.toList noPre.toList) ++ tail, result)
        else
          let yesList := if yesReturns then yes.toList else yes.toList ++ rest
          let noList := if noReturns then no.toList else no.toList ++ rest
          let (yesPre, yesResult) ← lowerHelperFrom yesList retName
          restore
          let (noPre, noResult) ← lowerHelperFrom noList retName
          restore
          let dest ← fresh
          let assign (pre : Array Stmt) (result : Option Expr) : Array Stmt :=
            match result with
            | some expr => pre.push (.assignVar dest expr)
            | none => pre
          let branch := Stmt.ite condition.expr (assign yesPre yesResult).toList
            (assign noPre noResult).toList
          match yesResult, noResult with
          | some _, some _ =>
              pure (condition.pre.push (.letVar dest (.literal 0)) |>.push branch,
                some (.localVar dest))
          | _, _ => failAt s "inlined helper does not return on every path"
    | kind => failAt s s!"unsupported helper statement {kind}"

private partial def lowerEffect (statement : Json) : M (Array Stmt) := do
  let expression ← mField statement "expression"
  let kind ← mKind expression
  if kind == "FunctionCall" && optStr expression "kind" == some "functionCall" then
    let callee ← mField expression "expression"
    let reference ← refInt callee
    if reference ≥ 0 then
      if let some declaration := (← get).funs.find? reference.toNat then
        let visibility := optStr declaration "visibility" |>.getD ""
        unless visibility == "internal" || visibility == "private" do
          failAt callee "discarded helper calls require an internal or private declaration"
        -- Materialize even a discarded result: the final expression can itself
        -- read storage or fail. The helper's effect prelude remains ordered.
        let result ← atom (← lowerCall expression)
        return result.pre
  if kind != "Assignment" && kind != "UnaryOperation" then
    return ← lowerRequire statement
  let deleting := kind == "UnaryOperation"
  let operator ← mStr (← mField expression "operator")
  unless (deleting && operator == "delete") || (!deleting && operator == "=") do
    failAt expression "only scalar storage assignment and delete are supported"
  let target ← mField expression (if deleting then "subExpression" else "leftHandSide")
  if (← mKind target) == "Identifier" then
    let id ← refInt target
    if id ≥ 0 then
      if let some bound := (← get).values.find? id.toNat then
        let .localVar binding := bound
          | failAt target "only materialized scalar locals are writable"
        unless (← get).writableLocals.find? id.toNat == some binding do
          failAt target "only declaration-bound scalar locals are writable"
        let ty ← mType target
        unless (paramType ty).isSome do
          failAt target s!"unsupported scalar local assignment type {ty}"
        let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do
          let right ← mField expression "rightHandSide"
          atom (← convert ty (← mType right) (← lowerExpr right) right)
        return value.pre.push (.assignVar binding value.expr)
  if (← mKind target) == "MemberAccess" then
    let member ← mStr (← mField target "memberName")
    let .path pre path ← lowerRef (← mField target "expression")
      | failAt target "member assignment requires a mapping struct storage path"
    -- Ordering between effectful key and RHS evaluation needs a separate rule.
    unless pre.isEmpty do failAt target "member write key prelude is unsupported"
    let (name, count, write) ← match path with
      | .one field key => pure (field, 1, fun (value : Expr) => Stmt.setStructMember field key member value)
      | .two field key1 key2 => pure (field, 2, fun (value : Expr) => Stmt.setStructMember2 field key1 key2 member value)
      | .outer _ _ => failAt target "member assignment requires both mapping keys"
    let info ← resolveField name target
    if info.opaqueNames.contains member then failAt target s!"member {member} is opaque in this slice"
    unless !info.scalarMapping && info.keyCount == count && info.memberNames.contains member do
      failAt target "member assignment requires a supported layout member"
    let ty ← mType target
    unless ty.startsWith "uint" && (bitsOf ty).isSome do
      failAt target "member assignment requires an unsigned scalar member"
    markField name
    let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do
      let right ← mField expression "rightHandSide"
      atom (← convert ty (← mType right) (← lowerExpr right) right)
    return value.pre.push (write value.expr)
  if (← mKind target) == "IndexAccess" then
    let reference ← lowerRef target
    if let .fixedElement pre path index := reference then
      -- Under the pinned via-IR profile, assignment evaluates and captures
      -- the RHS before the LHS mapping keys and index, then checks bounds.
      -- lowerRef captures the keys/index in their recursive source order.
      let (name, count, write) ← match path with
        | .one name key => pure (name, 1, fun member value => Stmt.setStructMember name key member value)
        | .two name key1 key2 => pure (name, 2, fun member value => Stmt.setStructMember2 name key1 key2 member value)
        | .outer _ _ => failAt target "fixed array write requires both mapping keys"
      let info ← resolveField name target
      let some length := info.fixedArrayLength | failAt target "missing fixed array layout"
      unless info.keyCount == count do failAt target "fixed array mapping key count differs"
      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
        let right ← mField expression "rightHandSide"
        atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
      let capturedValue ← fresh
      let valuePre := value.pre.push (.letVar capturedValue value.expr)
      let mut result := (valuePre ++ pre).push (.ite (.lt index (.literal length))
        [] [.panicCode (.literal 0x32)])
      for i in [:length] do
        result := result.push (.ite (.eq index (.literal i))
          [write s!"__solidity_element_{i}" (.localVar capturedValue)] [])
      markField name
      return result
    let .path pre path := reference
      | failAt target "mapping assignment target is not a storage path"
    let (name, count, write) ← match path with
      | .one field key => pure (field, 1, fun (value : Expr) => Stmt.setStructMember field key "__solidity_value" value)
      | .two field key1 key2 => pure (field, 2, fun (value : Expr) => Stmt.setStructMember2 field key1 key2 "__solidity_value" value)
      | .outer _ _ => failAt target "mapping assignment requires both keys"
    let info ← resolveField name target
    unless info.scalarMapping && info.keyCount == count do
      failAt target "only scalar mapping values are writable"
    markField name
    let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
      let right ← mField expression "rightHandSide"
      atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
    let expr := if info.booleanMapping then Expr.logicalNot (.logicalNot value.expr) else value.expr
    return (pre ++ value.pre).push (write expr)
  unless (← mKind target) == "Identifier" do
    failAt target "only a resolved scalar storage identifier is writable"
  let .state name pre ← lowerRef target
    | failAt target "assignment target is not scalar storage"
  let info ← resolveField name target
  unless info.keyCount == 0 do failAt target "whole mapping assignment is unsupported"
  markField name
  let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do
    let right ← mField expression "rightHandSide"
    atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
  return (pre ++ value.pre).push (.setStorage name value.expr)

private partial def lowerRequire (statement : Json) : M (Array Stmt) := do
  let call ← mField statement "expression"
  unless (← mKind call) == "FunctionCall" do
    failAt call "only builtin require calls are supported as expression statements"
  let callee ← mField call "expression"
  unless (← mKind callee) == "Identifier" && optStr callee "name" == some "require" do
    failAt callee "only builtin require calls are supported as expression statements"
  -- solc 0.8.34 retains all three builtin overloads (-18) even after
  -- selecting the (bool,string) signature. Do not relax user-call refInt.
  let signature ← mType callee
  unless (← mField callee "referencedDeclaration").getInt?.toOption == some (-18) &&
      (signature == "function (bool,string memory) pure" || signature == "function (bool,error) pure") do
    failAt callee "require must resolve to a supported Solidity builtin signature"
  unless (← mArr (← mField callee "overloadedDeclarations")).all
      (fun declaration => declaration.getInt?.toOption == some (-18)) do
    failAt callee "require overload set contains a non-builtin declaration"
  unless optStr call "kind" == some "functionCall" do
    failAt call "require must be a function call"
  unless (← mArr (← mField call "names")).isEmpty do
    failAt call "named require arguments are unsupported"
  let args ← mArr (← mField call "arguments")
  unless args.size == 2 do failAt call "require currently needs a literal string message"
  let message := args[1]!
  if signature == "function (bool,error) pure" then
    let condition ← atom (← lowerExpr args[0]!)
    let (pre, name, values) ← lowerErrorArguments message
    return condition.pre ++ pre |>.push (.requireError condition.expr name values)
  unless (← mKind message) == "Literal" do
    failAt message "require currently needs a literal string message"
  let kind ← mStr (← mField message "kind")
  unless kind == "string" || kind == "unicodeString" do
    failAt message "require message must be a UTF-8 string literal"
  let some value := optStr message "value"
    | failAt message "require message bytes are not represented exactly by UTF-8"
  let actual ← mStr (← mField message "hexValue")
  let expected := value.toUTF8.data.foldl (init := "") fun acc byte =>
    acc.push (hexDigit (byte.toNat / 16)) |>.push (hexDigit (byte.toNat % 16))
  unless actual == expected do failAt message "require message bytes are not represented exactly by UTF-8"
  let condition ← atom (← lowerExpr args[0]!)
  return condition.pre.push (.require condition.expr value)

private partial def lowerEmit (statement : Json) : M (Array Stmt) := do
  let call ← mField statement "eventCall"
  unless (← mKind call) == "FunctionCall" && optStr call "kind" == some "functionCall" do
    failAt call "event must be a resolved declaration call"
  unless (← mArr (← mField call "names")).isEmpty do
    failAt call "named event arguments are unsupported"
  let callee ← mField call "expression"
  let id ← refInt callee
  let some declaration := (← get).eventDecls.find? id.toNat
    | failAt callee "event does not resolve to an event declaration"
  if ← mBool (← mField declaration "anonymous") then
    failAt declaration "anonymous events are unsupported"
  let name ← mStr (← mField declaration "name")
  let parameters ← mArr (← mField (← mField declaration "parameters") "parameters")
  let arguments ← mArr (← mField call "arguments")
  unless parameters.size == arguments.size do failAt call "event argument count differs"
  let mut params : List EventParam := []
  let mut values : List Expr := []
  let mut pre : Array Stmt := #[]
  for index in [:parameters.size] do
    let parameter := parameters[index]!
    let ty ← mType parameter
    let some modelType := paramType ty | failAt parameter s!"unsupported event parameter type {ty}"
    unless (Denote.errorScalarType modelType).isSome do
      failAt parameter s!"unsupported event parameter type {ty}"
    let indexed ← mBool (← mField parameter "indexed")
    let parameterName ← mStr (← mField parameter "name")
    let argument := arguments[index]!
    let mut value ← convert ty (← mType argument) (← lowerExpr argument) argument
    -- Total scalar reads/casts commute. Reject guards and effects rather than
    -- choosing an argument evaluation order for competing revert paths.
    unless value.pre.all (fun | .letVar _ _ => true | _ => false) do
      failAt argument "event arguments currently require total scalar expressions"
    match value.expr with
    | .param parameterName =>
        let some actualType := rootParamType? (← get) parameterName
          | failAt argument "unresolved event model parameter type"
        if actualType != modelType then
          match modelType with
          | .uintN _ => failAt argument "event direct parameter type differs from its declaration"
          | _ =>
              -- Materialize a converted value so a type-preserving word cast
              -- or unsigned widening does not masquerade as a typed parameter.
              let binding ← fresh
              value := { pre := value.pre.push (.letVar binding value.expr), expr := .localVar binding }
    | _ => pure ()
    match modelType with
    | .uintN _ =>
        unless (match value.expr with | .param _ => true | _ => false) && value.pre.isEmpty do
          failAt argument "narrow event arguments currently require a matching direct parameter"
    | _ => pure ()
    let boundValue ← atom value
    params := params ++ [{ name := parameterName, ty := modelType, kind := if indexed then .indexed else .unindexed }]
    values := values ++ [boundValue.expr]
    pre := pre ++ boundValue.pre
  unless (params.filter (·.kind == .indexed)).length ≤ 3 do
    failAt declaration "event has more than three indexed parameters"
  if let some previous := (← get).usedEvents.find? (fun pair => pair.2.name == name) then
    unless previous.1 == id.toNat do failAt callee "event name resolves to multiple declarations"
  else
    modify fun e => { e with usedEvents := e.usedEvents ++ [(id.toNat, { name, params })] }
  pure (pre.push (.emit name values))

private partial def lowerErrorArguments (call : Json) : M (Array Stmt × String × List Expr) := do
  unless (← mKind call) == "FunctionCall" && optStr call "kind" == some "functionCall" do
    failAt call "custom error must be a resolved constructor call"
  unless (← mArr (← mField call "names")).isEmpty do
    failAt call "named custom-error arguments are unsupported"
  let callee ← mField call "expression"
  let id ← refInt callee
  let some declaration := (← get).errorDecls.find? id.toNat
    | failAt callee "custom error does not resolve to an error declaration"
  let name ← mStr (← mField declaration "name")
  let parameters ← mArr (← mField (← mField declaration "parameters") "parameters")
  let arguments ← mArr (← mField call "arguments")
  unless parameters.size == arguments.size do failAt call "custom-error argument count differs"
  let mut types : List ParamType := []
  let mut values : List Expr := []
  let mut pre : Array Stmt := #[]
  for index in [:parameters.size] do
    let parameter := parameters[index]!
    let ty ← mType parameter
    let some modelType := paramType ty | failAt parameter s!"unsupported custom-error parameter type {ty}"
    unless (Denote.errorScalarType modelType).isSome do
      failAt parameter s!"unsupported custom-error parameter type {ty}"
    let argument := arguments[index]!
    -- Restrict this first slice to total scalar operands. General expressions
    -- need an evaluation-order argument, including competing panic paths.
    match ← mKind argument with
    | "Literal" => pure ()
    | "Identifier" =>
        let argumentId ← refInt argument
        unless (← get).values.contains argumentId.toNat do
          failAt argument "custom-error arguments currently require literals or scalar bindings"
    | _ => failAt argument "custom-error arguments currently require literals or scalar bindings"
    let value ← atom (← convert ty (← mType argument) (← lowerExpr argument) argument)
    types := types ++ [modelType]
    values := values ++ [value.expr]
    pre := pre ++ value.pre
  let definition : ErrorDef := { name, params := types }
  if let some previous := (← get).usedErrors.find? (·.name == name) then
    unless previous.params == types do failAt callee "custom-error name has multiple signatures"
  else
    modify fun e => { e with usedErrors := e.usedErrors ++ [definition] }
  return (pre, name, values)

private partial def lowerAssembly (j : Json) (retName : String) : M Val := do
  let ast ← mField j "AST"
  unless (← mKind ast) == "YulBlock" do failAt j "assembly is not a Yul block"
  let stmts ← mArr (← mField ast "statements")
  unless stmts.size == 1 do failAt j "only a single Yul assignment is supported"
  let asg := stmts[0]!
  unless (← mKind asg) == "YulAssignment" do failAt asg "only a Yul assignment is supported"
  let vars ← mArr (← mField asg "variableNames")
  unless vars.size == 1 do failAt asg "Yul assignment must have one target"
  let vname ← mStr (← mField vars[0]! "name")
  unless retName != "" && vname == retName do
    failAt asg s!"Yul assigns {vname}, not the return name {retName}"
  pure { pre := #[], expr := ← lowerYul (← mField asg "value") }

private partial def lowerLocal (s : Json) : M (Array Stmt) := do
  let decls ← mArr (← mField s "declarations")
  unless decls.size == 1 do failAt s "only a single declaration is supported"
  if decls[0]!.isNull then failAt s "empty declaration"
  let d := decls[0]!
  let name ← mStr (← mField d "name")
  unless name.all (fun c => c.isAlphanum || c == '_') && name != "" do
    failAt d s!"unsupported local name {name}"
  let id ← mNat (← mField d "id")
  let loc := optStr d "storageLocation" |>.getD "default"
  let init := field? s "initialValue" |>.getD Json.null
  if init.isNull then
    unless loc == "default" do
      failAt d "uninitialized reference locals are outside this slice"
    let ty ← mType d
    let some scalarType := paramType ty
      | failAt d s!"unsupported default local type {ty}"
    let binding ← freshFor name
    let expr := Expr.localVar binding
    modify fun e =>
      { e with values := e.values.insert id expr,
               scalarTy := e.scalarTy.insert id scalarType,
               yulNames := e.yulNames.insert name expr,
               writableLocals := e.writableLocals.insert id binding }
    return #[.letVar binding (.literal 0)]
  if loc == "memory" && (← mType d).contains '[' then
    if (← mKind init) == "TupleExpression" then
      if ← mBool (← mField init "isInlineArray") then
        failAt init "inline arrays are outside this slice"
    let .path pre path ← lowerRef init
      | failAt d "fixed memory array initialization requires a mapping storage array"
    let (field, count, read) ← match path with
      | .one field key => pure (field, 1, fun member => Expr.structMember field key member)
      | .two field key1 key2 => pure (field, 2, fun member => Expr.structMember2 field key1 key2 member)
      | .outer _ _ => failAt init "fixed array copy requires both mapping keys"
    let info ← resolveField field init
    let some length := info.fixedArrayLength
      | failAt init "fixed memory array initialization requires a fixed storage array"
    unless info.keyCount == count && ((← mType d).splitOn " ").head! == info.fixedArrayType do
      failAt d "fixed memory array copy type differs from storage layout"
    let mut result := pre
    let mut elements : Array Expr := #[]
    for i in [:length] do
      let binding ← fresh
      result := result.push (.letVar binding (read s!"__solidity_element_{i}"))
      elements := elements.push (.localVar binding)
    modify fun e => { e with snapshots := e.snapshots.insert id elements }
    markField field
    return result
  if loc == "storage" then
    match ← lowerRef init with
    | .path pre path =>
        -- A Solidity storage pointer fixes its address at declaration time.
        -- Freeze even simple local keys, since subsequent assignments may change them.
        let capture (key : Expr) : M (Array Stmt × Expr) := do
          let binding ← fresh
          pure (#[.letVar binding key], .localVar binding)
        let (keys, frozen) ← match path with
          | .one field key => do
              let (pre, key) ← capture key
              pure (pre, SPath.one field key)
          | .two field key1 key2 => do
              let (pre1, key1) ← capture key1
              let (pre2, key2) ← capture key2
              pure (pre1 ++ pre2, SPath.two field key1 key2)
          | .outer field key => do
              let (pre, key) ← capture key
              pure (pre, SPath.outer field key)
        modify fun e => { e with paths := e.paths.insert id frozen }
        pure (pre ++ keys)
    | _ => failAt s "storage local is not a resolved read path"
  else
    let v ← lowerExpr init
    let binding ← freshFor name
    let expr := Expr.localVar binding
    modify fun e =>
      { e with values := e.values.insert id expr, yulNames := e.yulNames.insert name expr,
               writableLocals := e.writableLocals.insert id binding }
    pure (v.pre.push (.letVar binding v.expr))

end

private def structMemberList (st : Json) : M (Array (String × String)) := do
  let ms ← mArr (← mField st "members")
  let mut out : Array (String × String) := #[]
  for m in ms do
    out := out.push (← mStr (← mField m "name"), ← mType m)
  pure out

private def bindRoot (fn : Json) : M (Array SrcParam) := do
  noteFn fn
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  let mut out : Array SrcParam := #[]
  for p in params do
    let name ← mStr (← mField p "name")
    let id ← mNat (← mField p "id")
    let ty ← mType p
    let loc := optStr p "storageLocation" |>.getD "default"
    out := out.push { name, id }
    modify fun e => { e with bound := name :: e.bound }
    if ty.startsWith "struct " && (loc == "memory" || loc == "calldata") then
      let typeName ← mField p "typeName"
      let sid ← refInt typeName
      if sid < 0 then failAt p "builtin struct"
      let some decl := (← get).structs.find? sid.toNat | failAt p s!"unresolved struct {ty}"
      let members ← structMemberList decl
      let sname ← mStr (← mField decl "name")
      let staticTypes := members.toList.mapM (fun (_, ty) => paramType ty)
      let schema ← if staticTypes.isSome then pure none else do
        let structs := (← get).structs
        match AbiSchema.root (fun id => structs.find? id) decl with
        | .ok schema => pure (some schema)
        | .error failure => failAt failure.node failure.message
      let abiStem ← match schema with
        | none => pure ""
        | some schema => freshAbiStem schema (loc == "memory")
      let headBinding ← if staticTypes.isSome then fresh else pure ""
      if staticTypes.isSome then
        for i in [:members.size] do
          let binding := s!"{name}_{i}"
          if (← get).sourceNames.contains binding then
            failAt p s!"static tuple binding collides with source name {binding}"
          modify fun e => { e with bound := binding :: e.bound }
      modify fun e =>
        let bound : MemParam :=
          { structId := sid.toNat
            param := name
            structName := sname
            members := members
            staticTypes := staticTypes
            calldataLocation := loc == "calldata"
            headBinding := headBinding
            schema := schema
            abiStem := abiStem }
        { e with mems := e.mems.insert id bound }
    else if ty.startsWith "struct " then
      failAt p s!"unsupported location {loc} for {ty}"
    else
      let some pty := paramType ty | failAt p s!"unsupported parameter type {ty}"
      modify fun e =>
        let values := e.values.insert id (.param name)
        let scalarTy := e.scalarTy.insert id pty
        { e with values, scalarTy }
  let explicitAbi := (← get).mems.toList.any (fun (_, mem) => mem.schema.isSome)
  modify fun e => { e with explicitAbi }
  if explicitAbi then
    for p in params do
      let id ← mNat (← mField p "id")
      if let some mem := (← get).mems.find? id then
        if mem.staticTypes.isSome then
          failAt p "mixed static and dynamic struct parameters require explicit static-root lowering"
      else
        let binding ← fresh
        modify fun e => { e with
          rawBindings := e.rawBindings.insert id binding
          values := e.values.insert id (.localVar binding) }
  pure out

private partial def lowerRootStatements (stmts : Array Json) : M (Array Stmt × Bool) := do
  let mut out : Array Stmt := #[]
  let mut returned := false
  for s in stmts do
    if returned then failAt s "statement after root return"
    match ← mKind s with
    | "Block" =>
        let saved ← get
        let (nested, nestedReturned) ← lowerRootStatements (← mArr (← mField s "statements"))
        -- Restore lexical lookup maps, but retain fresh names and discovered dependencies.
        modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, scalarTy := saved.scalarTy, yulNames := saved.yulNames }
        out := out ++ nested
        returned := nestedReturned
    | "VariableDeclarationStatement" =>
        out := out ++ (← lowerLocal s)
    | "ExpressionStatement" =>
        out := out ++ (← lowerEffect s)
    | "EmitStatement" =>
        out := out ++ (← lowerEmit s)
    | "ForStatement" =>
        out := out ++ (← lowerFor s fun body => do
          let statements ← if (← mKind body) == "Block" then mArr (← mField body "statements") else pure #[body]
          let (lowered, _) ← lowerRootStatements statements
          pure lowered)
    | "IfStatement" =>
        let (condition, yes, no) ← ifParts s
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames }
        -- A root return inside a branch stops execution, so the continuation
        -- stays after the conditional and runs only on fallthrough.
        let (yesOut, yesReturned) ← lowerRootStatements yes
        restore
        let (noOut, noReturned) ← lowerRootStatements no
        restore
        out := out ++ condition.pre |>.push (.ite condition.expr yesOut.toList noOut.toList)
        returned := yesReturned && noReturned
    | "Return" =>
        returned := true
        let some expr := field? s "expression"
          | failAt s "bare return requires explicit void-return lowering"
        if expr.isNull then failAt s "bare return requires explicit void-return lowering"
        if (← mKind expr) == "TupleExpression" then
          if ← mBool (← mField expr "isInlineArray") then
            failAt expr "inline arrays are outside this slice"
          let cs ← mArr (← mField expr "components")
          let mut pres : Array Stmt := #[]
          let mut exprs : Array Expr := #[]
          for c in cs do
            if c.isNull then failAt expr "empty return component"
            let v ← atom (← lowerExpr c)
            pres := pres ++ v.pre
            exprs := exprs.push v.expr
          out := out ++ pres |>.push (.returnValues exprs.toList)
        else
          let v ← atom (← lowerExpr expr)
          out := out ++ v.pre |>.push (.returnValues [v.expr])
    | kind => failAt s s!"unsupported statement {kind}"
  pure (out, returned)

private def lowerRoot (fn : Json) : M (Array Stmt × Array SrcParam) := do
  let rootId ← mNat (← mField fn "id")
  modify fun e => { e with stack := [rootId] }
  if optStr fn "stateMutability" == some "payable" then
    failAt fn "payable entry points require value-transfer semantics and are unsupported"
  let srcParams ← bindRoot fn
  if (field? fn "virtual").bind (fun v => v.getBool?.toOption) == some true then
    failAt fn "virtual dispatch is outside this slice"
  let mods ← mArr (← mField fn "modifiers")
  unless mods.isEmpty do failAt fn "modifiers are outside this slice"
  let some _ := field? fn "body" | failAt fn "function has no body"
  let stmts ← mArr (← mField (← mField fn "body") "statements")
  let (out, returned) ← lowerRootStatements stmts
  let mut out := out
  unless returned do
    let returns ← mArr (← mField (← mField fn "returnParameters") "parameters")
    unless returns.isEmpty do failAt fn "an explicit root return is required"
    out := out.push .stop
  pure (out, srcParams)

private partial def index (file : String) (contract? : Option String) (j : Json) : M Unit := do
  match j with
  | .obj o =>
      if let some name := optStr j "name" then
        modify fun e => { e with sourceNames := name :: e.sourceNames }
      if (field? j "nodeType").isSome then
        if let some idj := field? j "id" then
          let id ← mNat idj
          modify fun e => { e with nodeFile := e.nodeFile.insert id file }
          match ← mKind j with
          | "FunctionDefinition" =>
              modify fun e =>
                let funs := e.funs.insert id j
                let funContract := e.funContract.insert id (contract?.getD "<free>")
                { e with funs, funContract }
          | "StructDefinition" =>
              modify fun e => { e with structs := e.structs.insert id j }
          | "EventDefinition" =>
              modify fun e => { e with eventDecls := e.eventDecls.insert id j }
          | "ErrorDefinition" =>
              modify fun e => { e with errorDecls := e.errorDecls.insert id j }
          | "VariableDeclaration" =>
              let isState := match field? j "stateVariable" with
                | some b => match b.getBool? with | .ok v => v | _ => false
                | none => false
              if isState then
                modify fun e => { e with stateVars := e.stateVars.insert id j }
              let isConstant := (field? j "constant").bind (fun v => v.getBool?.toOption)
              if isConstant == some true then
                modify fun e => { e with numericConstants := e.numericConstants.insert id j }
          | _ => pure ()
      let next ← do
        if (field? j "nodeType") == some (Json.str "ContractDefinition") then
          let n ← mStr (← mField j "name")
          pure (some n)
        else
          pure contract?
      let children := o.foldl (fun acc _ v => v :: acc) []
      for child in children do
        index file next child
  | .arr xs =>
      for child in xs do
        index file contract? child
  | _ => pure ()

private def normalizePath (path : String) : Except String String := Id.run do
  let mut out : Array String := #[]
  for part in path.splitOn "/" do
    if part == "" || part == "." then
      pure ()
    else if part == ".." then
      if out.isEmpty then return .error s!"path escapes the project: {path}"
      out := out.pop
    else
      out := out.push part
  return .ok (String.intercalate "/" out.toList)

private def resolveSpec (origin spec : String) (remaps : Array (String × String)) : Except String String := do
  if spec.startsWith "." then
    let parent := String.intercalate "/" (origin.splitOn "/").dropLast
    normalizePath (parent ++ "/" ++ spec)
  else
    let mut best : Option (String × String) := none
    for pair in remaps do
      if spec.startsWith pair.1 then
        best := match best with
          | none => some pair
          | some prev => if pair.1.length > prev.1.length then some pair else some prev
    match best with
    | some (pre, tgt) => normalizePath (tgt ++ spec.drop pre.length)
    | none => normalizePath spec

private def importSpecs (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith "import" then
      let parts := t.splitOn "\""
      if parts.length ≥ 2 then
        out := out.push parts[1]!
  pure out

private def readRemappings (root : System.FilePath) : IO (Array (String × String)) := do
  let path := root / "remappings.txt"
  if !(← path.pathExists) then return #[]
  let text ← IO.FS.readFile path
  let mut out : Array (String × String) := #[]
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t == "" || t.startsWith "#" || t.startsWith "//" then continue
    let parts := t.splitOn "="
    if parts.length == 2 then
      out := out.push (parts[0]!, parts[1]!)
  pure out

private partial def collectSources
    (root : System.FilePath) (logical : String)
    (remaps : Array (String × String))
    (acc : RBMap String String compare) : MetaM (RBMap String String compare) := do
  if acc.contains logical then return acc
  let path := root / logical
  unless ← path.pathExists do throwError "missing Solidity source {logical}"
  let text ← IO.FS.readFile path
  let mut acc := acc.insert logical text
  for spec in importSpecs text do
    match resolveSpec logical spec remaps with
    | .error e => throwError "{logical}: {e}"
    | .ok next => acc ← collectSources root next remaps acc
  pure acc

private def verifyCompiler (compiler : System.FilePath) : MetaM String := do
  let output ←
    if System.Platform.isOSX then
      IO.Process.output { cmd := "/usr/bin/shasum", args := #["-a", "256", compiler.toString] }
    else
      IO.Process.output { cmd := "/usr/bin/sha256sum", args := #[compiler.toString] }
  unless output.exitCode == 0 && officialSolcSha256s.contains (output.stdout.take 64).toString do
    throwError "compiler checksum mismatch"
  return (output.stdout.take 64).toString

/-- Verity itself stores the importer next to its lakefile. A downstream package
stores that checkout at `.lake/packages/verity`. The digest must hash those
sources in either layout. -/
private def importerSourceRoot (pkgRoot : System.FilePath) : MetaM System.FilePath := do
  if ← (pkgRoot / "Compiler/SolidityImport/Import.lean").pathExists then
    return pkgRoot
  let dep := pkgRoot / ".lake/packages/verity"
  if ← (dep / "Compiler/SolidityImport/Import.lean").pathExists then
    return dep
  throwError "importer source missing: {pkgRoot / "Compiler/SolidityImport/Import.lean"}"

private def moduleText (pkgRoot : System.FilePath) (rel : String) : MetaM String := do
  let path := pkgRoot / rel
  unless ← path.pathExists do throwError "importer source missing: {path}"
  IO.FS.readFile path

private def FnRec.toImported (f : FnRec) : ImportedFunction :=
  { contract := f.contract, name := f.name, declId := f.declId, paramTypes := f.paramTypes.toList }

/-- Solidity spelling of a solc `typeString`: `struct Market memory` → `Market`. -/
private def sourceTypeName (typeString : String) : String := Id.run do
  let mut t := typeString
  for pre in ["struct ", "contract ", "enum "] do
    if t.startsWith pre then t := (t.drop pre.length).toString
  for suf in [" storage pointer", " storage ref", " memory", " calldata", " storage"] do
    if t.endsWith suf then t := (t.dropEnd suf.length).toString
  return t

/-- A written type matches its Solidity spelling, optionally qualified (`I.Market`). -/
private def typeMatches (written typeString : String) : Bool :=
  let t := sourceTypeName typeString
  t == written || t.endsWith ("." ++ written) || written.endsWith ("." ++ t)

/-- Select the function; also return its solc parameter type strings. -/
private def selectFunction (contract functionName : String) (written : Array String) :
    M (Json × Array String) := do
  let env ← get
  let mut hits : Array (Json × Array String) := #[]
  let mut described : Array String := #[]
  for (id, fn) in env.funs do
    let name ← mStr (← mField fn "name")
    let owner := env.funContract.find? id |>.getD "<free>"
    let params ← mArr (← mField (← mField fn "parameters") "parameters")
    let mut tys : Array String := #[]
    for p in params do
      tys := tys.push (← mType p)
    if owner == contract && name == functionName then
      described := described.push
        s!"{functionName}({String.intercalate ", " (tys.map sourceTypeName).toList})"
      if tys.size == written.size && (tys.zip written).all (fun (t, w) => typeMatches w t) then
        hits := hits.push (fn, tys)
  let sig := s!"{contract}.{functionName}({String.intercalate ", " written.toList})"
  if hits.size == 0 then
    throwError "no function {sig}; candidates: {described}"
  if hits.size > 1 then
    throwError "ambiguous function {sig}; qualify the parameter types"
  let (fn, tys) := hits[0]!
  let implemented ← match field? fn "implemented" with
    | some b => mBool b
    | none => pure true
  unless implemented do throwError "function is not implemented"
  pure (fn, tys)

private def importSlice
    (pkgRoot projectRoot : System.FilePath) (entry contract : String)
    (roots : Array (String × Array String)) (profile : Profile) :
    MetaM (CompilationModel × ImportReport) := do
  let compiler := pkgRoot / ".lake/solidity-import/solc-0.8.34"
  let solcSha ← verifyCompiler compiler
  let versionOut ← IO.Process.output { cmd := compiler.toString, args := #["--version"] }
  unless versionOut.exitCode == 0 &&
      acceptedSolcBanners.contains versionOut.stdout.trimAscii.toString do
    throwError "compiler version mismatch"
  unless (← verifyCompiler compiler) == solcSha do throwError "compiler changed during import"
  let remaps ← readRemappings projectRoot
  let sources ← collectSources projectRoot entry remaps RBMap.empty
  let mut fileBytes : RBMap String ByteArray compare := RBMap.empty
  let mut sourceObj : Array (String × Json) := #[]
  for (logical, text) in sources do
    fileBytes := fileBytes.insert logical (text.toUTF8)
    sourceObj := sourceObj.push (logical, Json.mkObj [("content", Json.str text)])
  let settings := Json.mkObj [
    ("evmVersion", Json.str profile.evmVersion),
    ("metadata", Json.mkObj [("bytecodeHash", Json.str profile.bytecodeHash)]),
    ("optimizer", Json.mkObj [("enabled", Json.bool profile.optimizerRuns.isSome),
      ("runs", profile.optimizerRuns.getD 200)]),
    ("outputSelection", Json.mkObj [("*", Json.mkObj [
      ("", Json.arr #[Json.str "ast"]),
      ("*", Json.arr #[Json.str "storageLayout"])])]),
    ("remappings", Json.arr (remaps.map fun p => Json.str s!"{p.1}={p.2}")),
    ("viaIR", Json.bool profile.viaIR)]
  let input := Json.mkObj [
    ("language", Json.str "Solidity"),
    ("settings", settings),
    ("sources", Json.mkObj sourceObj.toList)]
  let output ← IO.Process.output
    { cmd := compiler.toString, args := #["--standard-json", "--no-import-callback"] }
    (some input.compress)
  unless output.exitCode == 0 do throwError "solc failed: {output.stderr}"
  unless (← verifyCompiler compiler) == solcSha do throwError "compiler changed during import"
  let parsed ← match Json.parse output.stdout with
    | .ok v => pure v
    | .error e => throwError "solc output is not JSON: {e}"
  if let some errors := field? parsed "errors" then
    for err in ← arr errors do
      let severity := optStr err "severity" |>.getD ""
      if severity == "error" then
        throwError "solc: {optStr err "formattedMessage" |>.getD "error"}"
  let mut env := Env.init
  env := { env with files := fileBytes }
  let sourcesOut ← field parsed "sources"
  for (logical, _) in sources do
    let unit ← field sourcesOut logical
    let ast ← field unit "ast"
    ((), env) ← (index logical none ast).run env
  let contracts ← field parsed "contracts"
  let entryContracts ← field contracts entry
  let chosen ← field entryContracts contract
  let layout ← field chosen "storageLayout"
  let types ← field layout "types"
  let items ← arr (← field layout "storage")
  env := { env with layoutTypes := types }
  for item in items do
    let label ← str (← field item "label")
    env := { env with layoutItems := env.layoutItems.insert label item }
  let mut specs : Array FunctionSpec := #[]
  let mut projections : Array ParamProjection := #[]
  let mut signatures : Array Json := #[]
  let mut rootIds : Array Nat := #[]
  for (functionName, written) in roots do
    let (fn, paramTys) ← (selectFunction contract functionName written).run' env
    let rootId ← flexNat (← field fn "id")
    if rootIds.contains rootId then throwError "function {contract}.{functionName} is imported twice"
    rootIds := rootIds.push rootId
    signatures := signatures.push (Json.mkObj
      [("function", Json.str functionName), ("parameterTypes", Json.arr (paramTys.map Json.str))])
    -- Each root is lowered on its own: bindings, generated names and projections
    -- do not leak between functions. Field layouts and the closure are shared.
    env := { env with currentFile := entry, next := 0, bound := [], values := RBMap.empty, paths := RBMap.empty,
                      snapshots := RBMap.empty, mems := RBMap.empty, scalarTy := RBMap.empty, writableLocals := RBMap.empty, yulNames := RBMap.empty,
                      projections := #[], rawBindings := RBMap.empty, explicitAbi := false, encodingMemory := false }
    let ((body, srcParams), env2) ← (lowerRoot fn).run env
    env := env2
    let mut modelParams : Array Param := #[]
    let mut modelParamNames : Array String := #[]
    for p in srcParams do
      if env.mems.contains p.id then
        let some mem := env.mems.find? p.id | throwError "missing memory parameter {p.name}"
        if let some schema := mem.schema then
          if modelParamNames.contains p.name then
            (failAt fn s!"parameter name collision: {p.name}").run' env
          modelParamNames := modelParamNames.push p.name
          modelParams := modelParams.push { name := p.name, ty := AbiSchema.paramType schema }
          continue
        if let some types := mem.staticTypes then
          if modelParamNames.contains p.name then
            (failAt fn s!"parameter name collision: {p.name}").run' env
          modelParamNames := modelParamNames.push p.name
          modelParams := modelParams.push { name := p.name, ty := .tuple types }
          continue
        (failAt fn s!"struct parameter {p.name} has no supported complete ABI schema").run' env
      else
        let some pty := env.scalarTy.find? p.id | throwError "missing parameter type"
        if modelParamNames.contains p.name then (failAt fn s!"projected parameter name collision: {p.name}").run' env
        modelParamNames := modelParamNames.push p.name
        modelParams := modelParams.push { name := p.name, ty := pty }
    -- ABI cleanup is not validation: Solidity rejects noncanonical scalar
    -- words before executing the function. Inspect the original calldata word,
    -- since the model parameter loader has already masked/normalized it.
    let mut abiGuards : Array Stmt := if env.explicitAbi || env.encodingMemory then #[.mstore (.literal 64) (.literal 128)] else #[]
    let rootHeadWords := (modelParams.toList.foldl (fun n p => n + paramHeadSize p.ty) 0) / 32
    for p in srcParams do
      if let some mem := env.mems.find? p.id then
        if let some schema := mem.schema then
          let some i := modelParamNames.findIdx? (· == p.name)
            | throwError "missing full struct parameter"
          let headWord := (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0 / 32
          let plan := AbiRootLowering.root mem.abiStem rootHeadWords headWord schema (!mem.calldataLocation)
          abiGuards := abiGuards ++ plan.body.toArray
        if let some types := mem.staticTypes then
          let some i := modelParamNames.findIdx? (· == p.name)
            | throwError "missing tuple model parameter {p.name}"
          let offset := 4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0
          abiGuards := abiGuards.push (.letVar mem.headBinding (.literal offset))
          unless mem.calldataLocation do
            for (ty, j) in types.zipIdx do
              let limit := match ty with
                | .uintN bits => if bits < 256 then some (2^bits) else none
                | .address => some (2^160)
                | .bool => some 2
                | _ => none
              if let some bound := limit then
                abiGuards := abiGuards.push (.ite
                  (.lt (.calldataload (.literal (offset + 32*j))) (.literal bound))
                  [] [.revertReturndata])
      if let some ty := env.scalarTy.find? p.id then
        -- Static tuples occupy their complete inline head; dynamic tuples
        -- occupy one offset word. Compute scalar offsets from the full ABI.
        let some i := modelParamNames.findIdx? (· == p.name)
          | throwError "missing scalar model parameter {p.name}"
        let limit := match ty with
          | .uint8 => some (2^8)
          | .uint16 => some (2^16)
          | .uintN bits => if bits < 256 then some (2^bits) else none
          | .address => some (2^160)
          | .bool => some 2
          | _ => none
        if let some bound := limit then
          -- At entry the EVM return-data buffer is empty. This guard is placed
          -- before every source statement, so the rejection has empty bytes.
          abiGuards := abiGuards.push (.ite
            (.lt (.calldataload (.literal (4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0))) (.literal bound))
            [] [.revertReturndata])
        if let some binding := env.rawBindings.find? p.id then
          let some i := modelParamNames.findIdx? (· == p.name) | throwError "missing raw scalar parameter"
          let offset := 4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0
          abiGuards := abiGuards.push (.letVar binding (.calldataload (.literal offset)))
    let body := abiGuards ++ body
    let returns ← (do
      let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
      let mut out : Array ParamType := #[]
      for r in rets do
        let ty ← mType r
        let some pty := paramType ty | failAt r s!"unsupported return type {ty}"
        out := out.push pty
      pure out) |>.run' env
    let mutability ← str (← field fn "stateMutability")
    let isView := mutability == "view" || mutability == "pure"
    specs := specs.push
      { name := functionName, params := modelParams.toList, returnType := none,
        returns := returns.toList, isView, body := body.toList,
        abiDecoding := if env.explicitAbi then .explicitPrelude else .standard,
        localObligations := if abiGuards.isEmpty then [] else [{
          name := if env.explicitAbi then "solidity_explicit_abi" else "solidity_scalar_abi_entry"
          obligation := "Raw source scalar and memory-struct words are validated before source execution; calldata-struct fields are validated at their reads. Within this fragment without external calls the fresh EIP-211 returndata buffer stays empty, so failed guards revert with no bytes. The solc-to-model boundary is checked differentially, not proved."
          proofStatus := .unchecked }] }
    for proj in env.projections do
      let ignored :=
        match env.mems.toList.find? (fun pair => pair.2.param == proj.parameter) with
        | some (_, mem) => mem.members.filterMap fun (pair : String × String) =>
            if env.projections.any (fun q => q.parameter == proj.parameter && q.member == pair.1)
            then none else some pair.1
        | none => #[]
      projections := projections.push
        { function := functionName, parameter := proj.parameter, member := proj.member,
          structName := proj.structName, headWord := proj.headWord, modelParam := proj.modelParam,
          ignoredMembers := ignored.toList }
  let mut fields : Array (Nat × Field) := #[]
  for name in env.referenced do
    let some info := env.fieldsByName.find? name | throwError "missing field {name}"
    fields := fields.push (info.slot, info.field)
  let sortedFields := (fields.qsort (fun a b => a.1 < b.1)).map (·.2)
  let model : CompilationModel :=
    { name := contract, constructor := none, fields := sortedFields.toList,
      errors := env.usedErrors, events := env.usedEvents.map Prod.snd, functions := specs.toList }
  let mut excluded : Array FnRec := #[]
  for (id, decl) in env.funs do
    unless env.included.any (·.declId == id) do
      let name ← str (← field decl "name")
      let params ← arr (← field (← field decl "parameters") "parameters")
      let mut tys : Array String := #[]
      for p in params do
        tys := tys.push (← typeString p)
      excluded := excluded.push {
        contract := env.funContract.find? id |>.getD "<free>",
        name, declId := id, paramTypes := tys }
  let sortedExcluded := excluded.qsort (fun a b => a.declId < b.declId)
  let mut opaqueMembers : Array OpaqueMember := #[]
  for o in env.opaqueMembers do
    if env.referenced.contains o.field then
      opaqueMembers := opaqueMembers.push
        { field := o.field, name := o.name, solcType := o.solcType,
          wordOffset := o.wordOffset, byteOffset := o.byteOffset }
  let sourceRoot ← importerSourceRoot pkgRoot
  let importer ← moduleText sourceRoot "Compiler/SolidityImport/Import.lean"
  let coverage ← moduleText sourceRoot "Compiler/SolidityImport/Coverage.lean"
  let reportSrc ← moduleText sourceRoot "Compiler/SolidityImport/Report.lean"
  let quoteSrc ← moduleText sourceRoot "Compiler/SolidityImport/Quote.lean"
  let profileSrc ← moduleText sourceRoot "Compiler/SolidityImport/Profile.lean"
  -- JSON framing prevents distinct file/signature lists from sharing a
  -- concatenation merely because their text contains separator newlines.
  let digestInput := Json.mkObj [
    ("importerVersion", Json.str importerVersion),
    ("solcVersion", Json.str solcLongVersion),
    ("contract", Json.str contract),
    ("functions", Json.arr signatures),
    ("solcInput", input),
    ("importerSources", Json.mkObj [
      ("Import.lean", Json.str importer), ("Coverage.lean", Json.str coverage),
      ("Report.lean", Json.str reportSrc), ("Quote.lean", Json.str quoteSrc),
      ("Profile.lean", Json.str profileSrc)])]
  let digest := sha256Hex digestInput.compress.toUTF8
  let report : ImportReport :=
    { importerVersion, solcLongVersion, solcSha256 := solcSha, settingsJson := settings.compress,
      sourceDigest := digest, contract, roots := (roots.map (·.1)).toList,
      functions := specs.toList.map fun f =>
        { function := f.name, denoteCovered := executableStmtListCovered f.body,
          compilerProof := .unavailable noCompilerProofReason },
      includedFunctions := (env.included.map FnRec.toImported).toList,
      excludedFunctions := (sortedExcluded.map FnRec.toImported).toList,
      projections := projections.toList, storageFields := env.referenced.toList,
      storageKeys := env.referenced.toList.map fun name => (name, mappingKeyNames env name),
      opaqueMembers := opaqueMembers.toList, observesPanicPayload := true }
  pure (model, report)

/-- `solidity_profile osaka466 where evmVersion := "osaka" …` defines a named
`Profile`, reusable by several imports and printable with `#print`. -/
syntax (name := solidityProfileCmd) "solidity_profile " ident " where"
  sepByIndentSemicolon(Lean.Parser.Term.structInstField) : command

macro_rules
  | `(solidity_profile $id where $fields;*) => do
    let fields : Syntax.TSepArray `Lean.Parser.Term.structInstField ", " := fields.getElems
    `(def $id : Compiler.CompilationModel.SolidityImport.Profile := { $fields:structInstField,* })

/-- `function name(T₁, …, Tₙ)`: a function to import, with its Solidity parameter types. -/
syntax solidityRoot := &"function" ident "(" ident,* ")"

/-- Import Solidity functions as a `CompilationModel`; see the module docstring. -/
syntax (name := solidityImportCmd)
  "solidity_import " ident &"from" str &"entry" str " using " term:max
  &"contract" ident (ppLine solidityRoot)+ : command

private unsafe def evalProfileUnsafe (stx : Term) : TermElabM Profile := do
  let e ← Term.elabTermEnsuringType stx (mkConst ``Profile)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "the solc profile is not fully determined"
  Meta.evalExpr Profile (mkConst ``Profile) e

@[implemented_by evalProfileUnsafe]
private opaque evalProfile (stx : Term) : TermElabM Profile

private unsafe def evalModelUnsafe (n : Name) : TermElabM CompilationModel :=
  evalConstCheck CompilationModel ``CompilationModel n

@[implemented_by evalModelUnsafe]
private opaque evalModel (n : Name) : TermElabM CompilationModel

private unsafe def evalReportUnsafe (n : Name) : TermElabM ImportReport :=
  evalConstCheck ImportReport ``ImportReport n

@[implemented_by evalReportUnsafe]
private opaque evalReport (n : Name) : TermElabM ImportReport

/-- The directory holding the importing package's `lakefile.lean`. -/
private def packageRoot : CommandElabM System.FilePath := do
  let mut pkg := (← IO.FS.realPath (← getFileName)).parent.getD "."
  while !(← (pkg / "lakefile.lean").pathExists) do
    let some parent := pkg.parent | throwError "package root not found"
    if parent == pkg then throwError "package root not found"
    pkg := parent
  return pkg

/-! ## Typed accessors

For readable specifications, the import also defines, under its namespace, one
typed function per imported root (`midnight.updatePositionView`) and one typed
reader per storage struct member (`midnight.position.credit`). They only wrap
`runFunction` and `readMember` on the imported model. -/

private def keyTypeTerm : MappingKeyType → CommandElabM Term
  | .address => `(Verity.Core.Address)
  | .bytes32 => `(Verity.Core.BytesN 32)
  | .uint256 => `(Verity.Core.Uint256)

/-- Lean type of a scalar parameter or return value, when it has one. -/
private def paramTypeTerm? : ParamType → Option (CommandElabM Term)
  | .uint256 => some `(Verity.Core.Uint256)
  | .uintN bits => some `(Verity.Core.UIntN $(quote bits))
  | .uint8 => some `(Verity.Core.UIntN 8)
  | .uint16 => some `(Verity.Core.UIntN 16)
  | .address => some `(Verity.Core.Address)
  | .bytes32 => some `(Verity.Core.BytesN 32)
  | .bool => some `(Bool)
  | _ => none

private def docComment (text : String) : TSyntax ``Lean.Parser.Command.docComment :=
  ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (text ++ "-/")]⟩

/-- A binder name for `base` that no Solidity parameter uses. -/
private def freeBinder (taken : List String) (base : String) : Ident := Id.run do
  let mut name := base
  while taken.contains name do name := name ++ "'"
  pure (mkIdent (Name.mkSimple name))

private def elabStorageAccessors (ns : Name) (model : CompilationModel) (report : ImportReport) :
    CommandElabM (List Name) := do
  let mut names := []
  for field in model.fields do
    let (keys, members) ← match field.ty with
      | .mappingStruct k members => pure ([k], members)
      | .mappingStruct2 k1 k2 members => pure ([k1, k2], members)
      | _ => continue
    let solNames := (report.storageKeys.find? (·.1 == field.name)).map (·.2) |>.getD []
    let keyIdents := (List.range keys.length).map fun i =>
      let solName := solNames.getD i ""
      let usable := solName != "" && !["oracle", "world"].contains solName &&
        (solNames.filter (· == solName)).length == 1
      mkIdent (Name.mkSimple (if usable then solName else s!"key{i + 1}"))
    let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
    for (k, ident) in keys.zip keyIdents do
      binders := binders.push (← `(bracketedBinder| ($ident : $(← keyTypeTerm k))))
    let keyWords ← keyIdents.toArray.mapM fun ident => `(($ident).val)
    let path := String.join (keyIdents.map fun _ => "[..]")
    for member in members do
      let name := ns ++ Name.mkSimple field.name ++ Name.mkSimple member.name
      let valName := ns ++ Name.mkSimple field.name ++ Name.mkSimple (member.name ++ "_val")
      let read ← `(Compiler.CompilationModel.SolidityImport.readMember oracle $(mkIdent (`_root_ ++ ns ++ `model))
        world $(quote field.name) [$keyWords,*] $(quote member.name))
      let doc := docComment s!"`{field.name}{path}.{member.name}`, read with the imported storage layout. "
      match member.packed with
      | some packed =>
          elabCommand (← `($doc:docComment def $(mkIdent (`_root_ ++ name))
              (oracle : Compiler.CompilationModel.Denote.DenoteOracle) (world : Verity.ContractState)
              $binders* : Verity.Core.UIntN $(quote packed.width) :=
            Verity.Core.UIntN.ofNat $(quote packed.width) $read))
          elabCommand (← `(@[simp] theorem $(mkIdent (`_root_ ++ valName))
              (oracle : Compiler.CompilationModel.Denote.DenoteOracle) (world : Verity.ContractState)
              $binders* : ($(mkIdent (`_root_ ++ name)) oracle world $keyIdents.toArray*).val = $read :=
            Compiler.CompilationModel.SolidityImport.val_uintN_readMember _ _ _ _ _ _ (by decide)))
      | none =>
          elabCommand (← `($doc:docComment def $(mkIdent (`_root_ ++ name))
              (oracle : Compiler.CompilationModel.Denote.DenoteOracle) (world : Verity.ContractState)
              $binders* : Verity.Core.Uint256 :=
            Verity.Core.Uint256.ofNat $read))
          elabCommand (← `(@[simp] theorem $(mkIdent (`_root_ ++ valName))
              (oracle : Compiler.CompilationModel.Denote.DenoteOracle) (world : Verity.ContractState)
              $binders* : ($(mkIdent (`_root_ ++ name)) oracle world $keyIdents.toArray*).val = $read :=
            Compiler.CompilationModel.SolidityImport.val_uint256_readMember _ _ _ _ _ _ (by decide)))
      names := name :: valName :: names
  pure names

private def elabFunctionCalls (ns : Name) (model : CompilationModel) : CommandElabM (List Name) := do
  let mut names := []
  for fn in model.functions do
    let taken := fn.params.map (·.name)
    let some paramTys := fn.params.mapM (paramTypeTerm? ·.ty) | continue
    let some returnTys := fn.returns.mapM paramTypeTerm? | continue
    let oracle := freeBinder taken "oracle"
    let world := freeBinder taken "world"
    let paramIdents := fn.params.map fun p => mkIdent (Name.mkSimple p.name)
    let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
    for (ident, ty) in paramIdents.zip paramTys do
      binders := binders.push (← `(bracketedBinder| ($ident : $(← ty))))
    let args ← (fn.params.zip paramIdents).toArray.mapM fun (p, ident) =>
      `(($(quote p.name), Compiler.CompilationModel.SolidityImport.Word.toWord $ident))
    let returnTys ← returnTys.mapM id
    let resultTy ← match returnTys.reverse with
      | [] => `(Unit)
      | last :: rest => rest.foldlM (fun acc ty => `($ty × $acc)) last
    let words := (List.range fn.returns.length).toArray.map fun i => mkIdent (Name.mkSimple s!"r{i}")
    let decoded ← words.mapM fun w => `(Compiler.CompilationModel.SolidityImport.Word.ofWord $w)
    let result ← match decoded.toList with
      | [] => `(())
      | [x] => pure x
      | x :: xs => `(($x, $(xs.toArray),*))
    let name := ns ++ Name.mkSimple fn.name
    let doc := docComment s!"Call `{fn.name}` on the imported model in `{world.getId}`; `none` means it reverts. "
    elabCommand (← `($doc:docComment def $(mkIdent (`_root_ ++ name))
        ($oracle : Compiler.CompilationModel.Denote.DenoteOracle) ($world : Verity.ContractState)
        $binders* : Option $resultTy :=
      match Compiler.CompilationModel.SolidityImport.runFunction $oracle $(mkIdent (`_root_ ++ ns ++ `model))
          $(quote fn.name) $world [$args,*] with
      | some [$words,*] => some $result
      | _ => none))
    names := name :: names
  pure names

@[command_elab solidityImportCmd]
def elabSolidityImport : CommandElab := fun stx => do
  let `(solidity_import $alias from $root entry $entry using $prof contract $contract
      $roots:solidityRoot*) := stx | throwUnsupportedSyntax
  let saved ← getEnv
  try
    if debug.skipKernelTC.get (← getOptions) then
      throwError "kernel checking must be enabled"
    let profile ← liftTermElabM <| evalProfile prof
    unless profile.solc == solcLongVersion do
      throwError "this importer is pinned to solc {solcLongVersion}, not {profile.solc}"
    let roots ← roots.mapM fun root => do
      let `(solidityRoot| function $fn ( $tys,* )) := root | throwUnsupportedSyntax
      pure (fn.getId.toString, tys.getElems.map (·.getId.toString (escape := false)))
    let pkg ← packageRoot
    let project := if root.getString.startsWith "/" then
      System.FilePath.mk root.getString else pkg / root.getString
    let (model, report) ← liftTermElabM <|
      importSlice pkg project entry.getString contract.getId.toString roots profile
    let ns := (← getCurrNamespace) ++ alias.getId
    let name (suffix : Name) := mkIdent (`_root_ ++ ns ++ suffix)
    elabCommand (← `(def $(name `model) : Compiler.CompilationModel.CompilationModel :=
      $(← quoteModel model)))
    elabCommand (← `(def $(name `report) : Compiler.CompilationModel.SolidityImport.ImportReport :=
      $(← quoteReport report)))
    elabCommand (← `(def $(name `sourceDigest) : String := $(quote report.sourceDigest)))
    elabCommand (← `(theorem $(name `covered) :
      Compiler.CompilationModel.SolidityImport.modelImportCovered $(name `model) = true := by decide))
    for fn in model.functions do
      if [`model, `report, `sourceDigest, `covered].contains (Name.mkSimple fn.name) then
        throwError "imported function {fn.name} collides with the generated {ns ++ Name.mkSimple fn.name}"
    let generated := (← elabFunctionCalls ns model) ++ (← elabStorageAccessors ns model report)
    if let some dup := generated.find? (fun n => (generated.filter (· == n)).length > 1) then
      throwError "generated accessor {dup} is defined twice"
    -- The quoted definitions must denote exactly the values the importer built.
    unless (← get).messages.hasErrors do
      let back ← liftTermElabM <| evalModel (ns ++ `model)
      unless toString (repr back) == toString (repr model) do
        throwError "internal: the elaborated model differs from the imported value"
      let backReport ← liftTermElabM <| evalReport (ns ++ `report)
      unless backReport == report do
        throwError "internal: the elaborated report differs from the imported value"
    if (← get).messages.hasErrors then
      throwError "Solidity import failed to check"
  catch e =>
    setEnv saved
    throw e

end Compiler.CompilationModel.SolidityImport
