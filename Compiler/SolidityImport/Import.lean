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

private structure SolcRelease where
  longVersion : String
  binaryName : String
  sha256s : Array String
  banners : Array String
  hasNoImportCallbackFlag : Bool
  supportedEvmVersions : Array String
  supportsViaIR : Bool

private def solcReleases : Array SolcRelease := #[
  { longVersion := "0.8.34+commit.80d5c536",
    binaryName := "solc-0.8.34",
    sha256s := #[
      "d40adc6f9fdbb22a97d32a02fa05688bf2ee7886affc48c9851b0afd4a726b39",
      "0a2829292697dda542e4e365bb63fbd6d3ed51537140222a880ab760cffa7746"],
    banners := #[
      "solc, the solidity compiler commandline interface\nVersion: 0.8.34+commit.80d5c536.Linux.g++",
      "solc, the solidity compiler commandline interface\nVersion: 0.8.34+commit.80d5c536.Darwin.appleclang"],
    hasNoImportCallbackFlag := true,
    supportedEvmVersions := #[
      "osaka", "prague", "cancun", "shanghai", "paris", "london", "berlin",
      "istanbul", "petersburg", "constantinople", "byzantium",
      "spuriousDragon", "tangerineWhistle", "homestead"],
    supportsViaIR := true },
  { longVersion := "0.8.10+commit.fc410830",
    binaryName := "solc-0.8.10",
    sha256s := #[
      "c7effacf28b9d64495f81b75228fbf4266ac0ec87e8f1adc489ddd8a4dd06d89",
      "a79fff23aeb35be856e446827c44a9cfa4c382f29babd2f6a405ef73d1e2a4cc"],
    banners := #[
      "solc, the solidity compiler commandline interface\nVersion: 0.8.10+commit.fc410830.Linux.g++",
      "solc, the solidity compiler commandline interface\nVersion: 0.8.10+commit.fc410830.Darwin.appleclang"],
    hasNoImportCallbackFlag := false,
    supportedEvmVersions := #[
      "london", "berlin", "istanbul", "petersburg", "constantinople",
      "byzantium", "spuriousDragon", "tangerineWhistle", "homestead"],
    supportsViaIR := false }]

private def resolveSolcRelease (profile : Profile) : MetaM SolcRelease := do
  let some release := solcReleases.find? (·.longVersion == profile.solc)
    | throwError "this importer is pinned to solc {String.intercalate " or " (solcReleases.map (·.longVersion)).toList}, not {profile.solc}"
  unless release.supportedEvmVersions.contains profile.evmVersion do
    throwError "evmVersion {profile.evmVersion} is not supported for solc {release.longVersion}"
  if profile.viaIR && !release.supportsViaIR then
    throwError "viaIR is not supported for solc {release.longVersion}"
  pure release

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
  | zero (field : String)
  | one (field : String) (key : Expr)
  | two (field : String) (k1 k2 : Expr)
  | outer (field : String) (k1 : Expr)
  | rawSlot (structId : Nat) (slot : Expr)
  | bytesSlot (field : String) (isString : Bool)

private structure StructFixedArrayInfo where
  member : String
  solcType : String
  wordOffset : Nat
  byteOffset : Nat
  length : Nat
  elementWidth : Nat
  arrayType : String

private structure StructMappingInfo where
  member : String
  solcType : String
  wordOffset : Nat
  keyType : MappingKeyType
  valueWidth : Nat
  booleanValue : Bool := false
  valueStructId : Option Nat := none

private structure StructDynamicArrayInfo where
  member : String
  solcType : String
  wordOffset : Nat
  elemType : String
  modelElemType : ParamType
  abiKind : SolidityAbi.ScalarKind
  elemStructId : Option Nat := none

private structure RawStructSubStructInfo where
  member : String
  structId : Nat
  wordOffset : Nat

private structure RawStructMemberInfo where
  member : String
  ty : String
  wordOffset : Nat
  byteOffset : Nat
  bitWidth : Nat
  isBool : Bool := false

private structure RawStructInfo where
  structId : Nat
  structName : String
  scalars : Array RawStructMemberInfo
  mappings : Array StructMappingInfo
  dynamicArrays : Array StructDynamicArrayInfo := #[]
  subStructs : Array RawStructSubStructInfo := #[]
  wordCount : Nat := 0

private structure FlatStructLocal where
  structId : Nat
  structName : String
  members : Array (String × String × String)

private inductive Ref where
  | expr (v : Val)
  | path (pre : Array Stmt) (p : SPath)
  | fixedElement (pre : Array Stmt) (path : SPath) (index : Expr)
  | structFixedArray (pre : Array Stmt) (path : SPath) (info : StructFixedArrayInfo)
  | structFixedElement (pre : Array Stmt) (path : SPath) (info : StructFixedArrayInfo) (index : Expr)
  | structMapping (pre : Array Stmt) (path : SPath) (info : StructMappingInfo)
  | structMappingElement (pre : Array Stmt) (path : SPath) (info : StructMappingInfo) (key : Expr)
  | structDynamicArray (pre : Array Stmt) (path : SPath) (info : StructDynamicArrayInfo)
  | structDynamicElement (pre : Array Stmt) (path : SPath) (info : StructDynamicArrayInfo) (index : Expr)
  | storageDynamicElement (pre : Array Stmt) (fieldName : String) (slotExpr : Expr) (elemTy : String) (index : Expr)
  | snapshot (elements : Array Expr)
  | mem (id : Nat) (pre : Array Stmt)
  | flatStruct (id : Nat)
  | abiArray (id memberIndex : Nat) (pre : Array Stmt)
  | abiBytesField (id memberIndex : Nat) (pre : Array Stmt)
  | abiElement (id memberIndex : Nat) (pointer : Expr) (inMemory : Bool) (pre : Array Stmt)
  | calldataBytes (id : Nat) (pre : Array Stmt)
  | scalarArray (id : Nat) (pre : Array Stmt)
  | state (name : String) (pre : Array Stmt)

private structure AbiElementLocal where
  rootId : Nat
  memberIndex : Nat
  pointer : Expr
  inMemory : Bool

private structure CalldataBytesParam where
  param : String
  offsetBinding : String
  headerBinding : String
  lengthBinding : String
  dataBinding : String
  isString : Bool := false
  inMemory : Bool := false
  memoryPointer : String := ""
  nextFreeBinding : String := ""
  copyIndexBinding : String := ""

private structure ScalarArrayParam where
  param : String
  elementType : String
  modelElementType : ParamType
  abiKind : SolidityAbi.ScalarKind
  inMemory : Bool
  offsetBinding : String := ""
  headerBinding : String := ""
  lengthBinding : String
  dataBinding : String := ""
  memoryPointer : String := ""
  nextFreeBinding : String := ""
  namePrefix : String := ""

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

private inductive FnPtr where
  | direct (fnId : Nat)
  | branch (cond : Expr) (trueFnId : Nat) (falseFnId : Nat)

private inductive CallArg where
  | scalar (value : Val)
  | memory (descriptor : MemParam) (pre : Array Stmt)
  | abiElement (bound : AbiElementLocal) (pre : Array Stmt)
  | scalarArray (descriptor : ScalarArrayParam) (pre : Array Stmt)
  | byteBuffer (buffer : EncodedBytes)
  | stringBuffer (buffer : EncodedBytes)
  | calldataBytes (descriptor : CalldataBytesParam) (pre : Array Stmt)
  | storagePath (structId : Nat) (path : SPath) (pre : Array Stmt)
  | flatStruct (structId : Nat) (structName : String) (members : Array (String × String × Expr)) (pre : Array Stmt)
  | storageBytes (fieldName : String) (isString : Bool)
  | storageDynamicArray (fieldName : String) (slotExpr : Expr) (elemTy : String) (elemStructId : Option Nat) (pre : Array Stmt)
  | fnPtr (ptr : FnPtr) (pre : Array Stmt)

private structure FieldInfo where
  slot : Nat
  field : Field
  keyCount : Nat
  memberNames : Array String
  opaqueNames : Array String
  booleanMembers : Array String := #[]
  structFixedArrays : Array StructFixedArrayInfo := #[]
  structMappings : Array StructMappingInfo := #[]
  structDynamicArrays : Array StructDynamicArrayInfo := #[]
  subStructs : Array (String × Nat) := #[]
  structMembers : Array StructMember := #[]
  booleanScalar : Bool := false
  scalarMapping : Bool := false
  booleanMapping : Bool := false
  bytesStorage : Bool := false
  stringStorage : Bool := false
  dynamicArrayElemType : Option (String × ParamType × SolidityAbi.ScalarKind) := none
  dynamicArrayStructId : Option Nat := none
  thirdKeyMapping : Option StructMappingInfo := none
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
  funContractId : RBMap Nat Nat compare := RBMap.empty
  funBases : RBMap Nat (Array Nat) compare := RBMap.empty
  contractNames : RBMap Nat String compare := RBMap.empty
  contractKinds : RBMap Nat String compare := RBMap.empty
  contractBases : RBMap Nat (Array Nat) compare := RBMap.empty
  contractFuns : RBMap Nat (Array Nat) compare := RBMap.empty
  contractPublicVars : RBMap Nat (Array Nat) compare := RBMap.empty
  contractNodes : RBMap Nat (Array Json) compare := RBMap.empty
  linearizedBases : Array Nat := #[]
  duplicateLayoutLabels : Array String := #[]
  structs : RBMap Nat Json compare
  enums : RBMap Nat (Array String) compare := RBMap.empty
  enumByType : RBMap String (Nat × Array String) compare := RBMap.empty
  userValueTypes : RBMap String String compare := RBMap.empty
  userValueTypeById : RBMap Nat String compare := RBMap.empty
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
  flatStructs : RBMap Nat FlatStructLocal compare := RBMap.empty
  abiElements : RBMap Nat AbiElementLocal compare := RBMap.empty
  calldataBytes : RBMap Nat CalldataBytesParam compare := RBMap.empty
  scalarArrays : RBMap Nat ScalarArrayParam compare := RBMap.empty
  byteBuffers : RBMap Nat EncodedBytes compare := RBMap.empty
  stringBuffers : RBMap Nat EncodedBytes compare := RBMap.empty
  storageBytesVars : RBMap Nat String compare := RBMap.empty
  storageDynamicArrayVars : RBMap Nat (String × Expr × String × Option Nat) compare := RBMap.empty
  fnPtrs : RBMap Nat FnPtr compare := RBMap.empty
  bodyAssigned : List Nat := []
  helperResult : Option (String × String) := none
  helperReturnId : Option Nat := none
  multiHelperResults : Option (Array (String × String × Bool)) := none
  flatStructHelperResult : Option (Nat × String × Array (String × String × String) × Bool) := none
  helperPost : Array Stmt := #[]
  rootIsVoid : Bool := false
  rootReturns : Array Expr := #[]
  rootReturnTypes : Array String := #[]
  rootNamedReturn : Option (Nat × String × String × String) := none
  rootFixedArrayReturn : Option (String × ParamType × Nat) := none
  rootFlatStructReturn : Option (Nat × String × Array (String × String × String) × Bool) := none
  rootMsgDataReturn : Bool := false
  rootDynamicBytesReturn : Option ParamType := none
  publicVarGetterReturns : Array ParamType := #[]
  rootPost : Array Stmt := #[]
  modifiers : RBMap Nat Json compare := RBMap.empty
  unchecked : Bool := false
  fieldsByName : RBMap String FieldInfo compare
  layoutItems : RBMap String Json compare
  layoutTypes : Json
  included : Array FnRec
  projections : Array ProjRec
  opaqueMembers : Array OpaqRec
  usedStructFixedArrays : Array (String × String) := #[]
  usedStructMappings : Array (String × String) := #[]
  usedStructDynamicArrays : Array (String × String) := #[]
  usedRawStorage : Bool := false
  referenced : Array String
  scalarTy : RBMap Nat ParamType compare
  enumBounds : RBMap Nat Nat compare := RBMap.empty
  bytes4Params : Array Nat := #[]
  writableLocals : RBMap Nat String compare := RBMap.empty
  zeroInitLocals : Array Nat := #[]
  rawBindings : RBMap Nat String compare := RBMap.empty
  encodingMemory : Bool := false
  explicitAbi : Bool := false
  next : Nat
  /-- Every binding name allocated in the current root, including its parameters. -/
  bound : List String
  stack : List Nat
  yulNames : RBMap String Expr compare
  yulMemoryArrays : RBMap String String compare := RBMap.empty
  yulScratch0 : Bool := false
  yulScratch32 : Bool := false
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
private def mType (j : Json) : M String := do
  let raw ← liftM (typeString j)
  let env ← get
  if let some u := env.userValueTypes.find? raw then
    return u
  let parts := raw.splitOn "["
  if let h :: t := parts then
    if let some u := env.userValueTypes.find? h then
      return String.intercalate "[" (u :: t)
  return raw

private def failAt (j : Json) (why : String) : M α := do
  let env ← get
  let frames := env.stack.reverse.map fun id =>
    let owner := env.funContract.find? id |>.getD "<free>"
    let name := (((env.funs.find? id).orElse (fun _ => env.modifiers.find? id)).orElse (fun _ => env.stateVars.find? id)).bind (fun fn => optStr fn "name") |>.getD s!"decl#{id}"
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

/-- Transitive closure of `fnId` under solc's `baseFunctions` relation,
    including `fnId` itself. Bounded by the number of indexed functions. -/
private def baseFunctionClosure (env : Env) (fnId : Nat) : Array Nat := Id.run do
  let mut visited : Array Nat := #[fnId]
  let mut queue : List Nat := [fnId]
  for _ in [:env.funs.size + env.stateVars.size + 1] do
    match queue with
    | [] => break
    | curr :: rest =>
        queue := rest
        for b in env.funBases.find? curr |>.getD #[] do
          unless visited.contains b do
            visited := visited.push b
            queue := queue ++ [b]
  return visited

/-- True when `candId` and `targetId` belong to the same virtual override family
    (they share at least one declaration in their transitive `baseFunctions` closures). -/
private def sameVirtualFamily (env : Env) (candId targetId : Nat) : Bool :=
  let candClosure := baseFunctionClosure env candId
  let targetClosure := baseFunctionClosure env targetId
  candClosure.any targetClosure.contains

/-- Resolve `targetFnId` across `searchContracts` (in C3 most-derived-first order),
    preferring the first implemented declaration in the same virtual family. -/
private def resolveInContracts (env : Env) (searchContracts : List Nat) (targetFnId : Nat) : Option Nat := Id.run do
  for cid in searchContracts do
    for candId in env.contractFuns.find? cid |>.getD #[] do
      if sameVirtualFamily env candId targetFnId then
        if let some candFn := env.funs.find? candId then
          let implemented := (field? candFn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
          let hasBody := match field? candFn "body" with
            | some b => !b.isNull
            | none => false
          if implemented && hasBody then
            return some candId
  for cid in searchContracts do
    for candId in env.contractFuns.find? cid |>.getD #[] do
      if sameVirtualFamily env candId targetFnId then
        return some candId
  return none

private def refInt (j : Json) : M Int := do
  let some declaration := field? j "referencedDeclaration"
    | failAt j "expression has no supported declaration reference"
  let i ← match declaration.getInt? with
    | .ok i => pure i
    | .error e => failAt j e
  match field? j "overloadedDeclarations" with
  | some over =>
      let xs ← mArr over
      if xs.size ≠ 0 then
        let env ← get
        let sameFamily ← if i ≥ 0 && env.funs.contains i.toNat then do
          let targetClosure := baseFunctionClosure env i.toNat
          let mut ok := true
          for x in xs do
            let xid ← mNat x
            let sharesOrigin := env.funs.contains xid &&
              (baseFunctionClosure env xid).any fun bx =>
                targetClosure.any fun bi =>
                  match env.funContractId.find? bx, env.funContractId.find? bi with
                  | some cx, some ci => cx == ci
                  | _, _ => false
            unless sameVirtualFamily env xid i.toNat || sharesOrigin do
              ok := false
          pure ok
        else
          pure false
        unless sameFamily do failAt j "ambiguous declaration"
  | none => pure ()
  pure i

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
  if !(name.all (fun c => c.isAlphanum || c == '_')) || name.startsWith "__" || name.startsWith "_verity_slice_tmp" || name.startsWith "_verity_memret_" || name.startsWith "_verity_raw_storage" || name.startsWith "_verity_struct_" then return ← fresh
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

private def freshAbiElementStem (fields : List AbiSchema.ScalarField) : M String := do
  let budget := (← get).sourceNames.length + (← get).bound.length + 1
  for _ in [:budget] do
    let stem ← fresh
    let (_, names, _) := AbiRootLowering.materializeElementFromCalldata (.literal 0) stem fields
    let reserved := (← get).sourceNames ++ (← get).bound
    unless names.any reserved.contains do
      modify fun e => { e with bound := names ++ e.bound }
      return stem
  throwError "unable to allocate hygienic ABI element bindings"

private def convertStructCalldataToMemory (descriptor : MemParam) (at_ : Json) :
    M (Array Stmt × MemParam) := do
  if let some schema := descriptor.schema then
    let copyStem ← freshAbiStem schema true
    let mat := AbiRootLowering.materializeFromCalldata (descriptor.abiStem ++ "_calldata") copyStem schema
    modify fun e => { e with encodingMemory := true }
    return (mat.body.toArray, { descriptor with calldataLocation := false, abiStem := copyStem })
  if let some types := descriptor.staticTypes then
    let mut checks : Array Stmt := #[]
    for (ty, j) in types.zipIdx do
      let limit := match ty with
        | .uintN bits => if bits < 256 then some (2^bits) else none
        | .address => some (2^160)
        | .bool => some 2
        | _ => none
      if let some bound := limit then
        checks := checks.push (.ite
          (.lt (.calldataload (.add (.localVar descriptor.headBinding) (.literal (32*j)))) (.literal bound))
          [] [.revertReturndata])
    return (checks, { descriptor with calldataLocation := false })
  failAt at_ "struct reference has no supported complete ABI schema"

private def isAtom : Expr → Bool
  | .literal _ | .localVar _ | .param _ | .blockTimestamp | .blockNumber
  | .caller | .contractAddress | .chainid | .selfBalance | .txOrigin => true
  | _ => false

private partial def targetAssignedIds (t : Json) : List Nat :=
  if optStr t "nodeType" == some "Identifier" then
    match (field? t "referencedDeclaration").bind (fun v => v.getNat?.toOption) with
    | some n => [n]
    | none => []
  else if optStr t "nodeType" == some "TupleExpression" then
    match (field? t "components").bind (fun c => c.getArr?.toOption) with
    | some cs => cs.toList.flatMap targetAssignedIds
    | none => []
  else []

private partial def yulAssignedSrcs (j : Json) : List String :=
  match j with
  | .arr xs => xs.toList.flatMap yulAssignedSrcs
  | .obj o =>
      let own :=
        if optStr j "nodeType" == some "YulAssignment" then
          match (field? j "variableNames").bind (fun v => v.getArr?.toOption) with
          | some vars => vars.toList.filterMap (fun v => optStr v "src")
          | none => []
        else []
      o.foldl (fun acc _ v => acc ++ yulAssignedSrcs v) own
  | _ => []

private def inlineAssemblyAssignedIds (j : Json) : List Nat :=
  let srcs := match field? j "AST" with
    | some ast => yulAssignedSrcs ast
    | none => []
  match (field? j "externalReferences").bind (fun v => v.getArr?.toOption) with
  | some refs =>
      refs.toList.filterMap fun ref =>
        match optStr ref "src", (field? ref "declaration").bind (fun d => d.getNat?.toOption) with
        | some s, some declId => if srcs.contains s then some declId else none
        | _, _ => none
  | none => []

private def yulOnlyAssignsDecl (j : Json) (declId : Nat) : Bool :=
  let srcs := match field? j "AST" with
    | some ast => yulAssignedSrcs ast
    | none => []
  match (field? j "externalReferences").bind (fun v => v.getArr?.toOption) with
  | some refs =>
      refs.toList.all fun ref =>
        match optStr ref "src", (field? ref "declaration").bind (fun d => d.getNat?.toOption) with
        | some s, some d => d != declId || srcs.contains s
        | _, some d => d != declId
        | _, none => true
  | none => true

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
        | some t => targetAssignedIds t
        | none =>
            if kind == some "InlineAssembly" then inlineAssemblyAssignedIds j
            else []
      o.foldl (fun acc _ v => acc ++ bodyAssignedIds v) own
  | _ => []

private def isCompoundAssignOp (operator : String) : Bool :=
  ["+=", "-=", "*=", "<<=", ">>=", "&=", "|=", "^=", "/=", "%="].contains operator

/-- Declarations modified by compound assignment (`+=`, `-=`, `*=`, `<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=`), `++`/`--`, or Yul assignment in `j`. -/
private partial def bodyCompoundAssignedIds (j : Json) : List Nat :=
  match j with
  | .arr xs => xs.toList.flatMap bodyCompoundAssignedIds
  | .obj o =>
      let kind := optStr j "nodeType"
      let operator := optStr j "operator" |>.getD ""
      let target :=
        if kind == some "Assignment" && isCompoundAssignOp operator then
          field? j "leftHandSide"
        else if kind == some "UnaryOperation" && ["++", "--"].contains operator then
          field? j "subExpression"
        else none
      let own := match target with
        | some t => targetAssignedIds t
        | none =>
            if kind == some "InlineAssembly" then inlineAssemblyAssignedIds j
            else []
      o.foldl (fun acc _ v => acc ++ bodyCompoundAssignedIds v) own
  | _ => []

/-- Declarations modified by direct `=` assignment in `j`. -/
private partial def bodyDirectAssignedIds (j : Json) : List Nat :=
  match j with
  | .arr xs => xs.toList.flatMap bodyDirectAssignedIds
  | .obj o =>
      let kind := optStr j "nodeType"
      let operator := optStr j "operator" |>.getD ""
      let target :=
        if kind == some "Assignment" && operator == "=" then
          field? j "leftHandSide"
        else none
      let own := match target with
        | some t => targetAssignedIds t
        | none => []
      o.foldl (fun acc _ v => acc ++ bodyDirectAssignedIds v) own
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
        | some id =>
          let isStateful (fid : Nat) : Bool :=
            match env.funs.find? fid with
            | some fn => ![some "pure", some "view"].contains (optStr fn "stateMutability")
            | none => false
          let ptrStateful : Bool :=
            match env.fnPtrs.find? id with
            | some (.direct fid) => isStateful fid
            | some (.branch _ tFid fFid) => isStateful tFid || isStateful fFid
            | none => false
          let targetId := resolveInContracts env env.linearizedBases.toList id |>.getD id
          ptrStateful || isStateful id || isStateful targetId
        | none => false
      else false
      o.foldl (fun found _ child => found || statefulCallIn child env) own
  | _ => false

mutual
  private partial def jsonHasCustomRevert (env : Env) (seen : List Nat) (j : Json) : Bool :=
    match j with
    | .arr xs => xs.any (jsonHasCustomRevert env seen)
    | .obj o =>
        let kind := optStr j "nodeType"
        let own :=
          if kind == some "RevertStatement" then true
          else if kind == some "YulFunctionCall" then
            let fname := optStr (field? j "functionName" |>.getD Json.null) "name"
            fname == some "revert" || fname == some "invalid"
          else if kind == some "FunctionCall" && optStr j "kind" == some "functionCall" then
            let callee := field? j "expression" |>.getD Json.null
            match (field? callee "referencedDeclaration").bind (fun v => v.getInt?.toOption) with
            | some (-18) | some (-19) | some (-20) | some (-3) => true
            | some id =>
                if id >= 0 then
                  let natId := id.toNat
                  let targetId := resolveInContracts env env.linearizedBases.toList natId |>.getD natId
                  fnHasCustomRevert env targetId seen
                else false
            | none => false
          else false
        o.foldl (fun found _ child => found || jsonHasCustomRevert env seen child) own
    | _ => false

  private partial def fnHasCustomRevert (env : Env) (fnId : Nat) (seen : List Nat := []) : Bool :=
    if seen.contains fnId then true
    else
      match env.funs.find? fnId with
      | none => true
      | some fn =>
          let isPureOrView := [some "pure", some "view"].contains (optStr fn "stateMutability")
          let noMods := ((field? fn "modifiers").bind (fun m => m.getArr?.toOption)).map (·.isEmpty) == some true
          let hasBody := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
          match (field? fn "body").filter (!·.isNull) with
          | none => true
          | some body =>
              !isPureOrView || !noMods || !hasBody || jsonHasCustomRevert env (fnId :: seen) body
end

private def isOrderIndependentSibling : Expr → Bool
  | .literal _ | .param _ | .blockTimestamp | .blockNumber
  | .caller | .contractAddress | .chainid | .selfBalance | .txOrigin => true
  | _ => false

private partial def assignmentIn (j : Json) : Bool :=
  match j with
  | .arr xs => xs.any assignmentIn
  | .obj o =>
      let kind := optStr j "nodeType"
      let op := optStr j "operator" |>.getD ""
      let own := kind == some "Assignment" ||
        (kind == some "UnaryOperation" && ["++", "--", "delete"].contains op)
      o.foldl (fun found _ child => found || assignmentIn child) own
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
  else if ty == "address" || ty == "address payable" || ty.startsWith "contract " then some 160
  else if ty.startsWith "enum " then some 8
  else if ty.startsWith "uint" then (ty.drop 4).toNat?
  else none

private def paramType (ty : String) : Option ParamType :=
  match ty with
  | "uint256" | "uint" => some .uint256
  | "int256" | "int" => some .int256
  | "address" | "address payable" => some .address
  | "bytes32" => some .bytes32
  | "bytes4" => some (.bytesN 4)
  | "bool" => some .bool
  | _ =>
      if ty.startsWith "contract " then some .address
      else if ty.startsWith "enum " then some (.uintN 8)
      else match bitsOf ty with
      | some n => if n != 256 && ty.startsWith "uint" then some (.uintN n) else none
      | none => none

private def scalarArrayElement? (ty : String) : Option (String × ParamType × SolidityAbi.ScalarKind) := do
  let ty := if ty.endsWith " calldata" then (ty.dropEnd 9).toString
    else if ty.endsWith " memory" then (ty.dropEnd 7).toString
    else if ty.endsWith " storage ref" then (ty.dropEnd 12).toString
    else if ty.endsWith " storage pointer" then (ty.dropEnd 16).toString
    else ty
  unless ty.endsWith "[]" do none
  let elemStr := (ty.dropEnd 2).toString
  if elemStr.contains '[' || elemStr == "bytes" || elemStr == "string" || elemStr.startsWith "enum " then
    none
  else
    let pty ← paramType elemStr
    let kind? : Option SolidityAbi.ScalarKind :=
      if elemStr == "address" || elemStr == "address payable" || elemStr.startsWith "contract " then
        some .address
      else if elemStr == "bool" then
        some .bool
      else if elemStr == "bytes32" || elemStr == "int256" || elemStr == "int" then
        some .bytes32
      else if elemStr == "uint" || elemStr == "uint256" then
        some (.uint ⟨31, by decide⟩)
      else if elemStr.startsWith "uint" then
        match (elemStr.drop 4).toNat? with
        | some width =>
            if 8 ≤ width && width ≤ 256 && width % 8 == 0 then
              let bytes := width / 8 - 1
              if hb : bytes < 32 then some (.uint ⟨bytes, hb⟩) else none
            else none
        | none => none
      else none
    let kind ← kind?
    some (elemStr, pty, kind)

private def resolveEnumMembers (j : Json) (ty : String) : M (Array String) := do
  let env ← get
  let byRef? : Option (Array String) :=
    match (field? j "typeName").bind (fun tn => (field? tn "referencedDeclaration").bind (fun v => v.getNat?.toOption)) with
    | some eid => env.enums.find? eid
    | none =>
        match (field? j "referencedDeclaration").bind (fun v => v.getNat?.toOption) with
        | some eid => env.enums.find? eid
        | none =>
            match (field? j "expression").bind (fun ex => (field? ex "referencedDeclaration").bind (fun v => v.getNat?.toOption)) with
            | some eid => env.enums.find? eid
            | none => (env.enumByType.find? ty).map Prod.snd
  let some ms := byRef?.orElse (fun _ => (env.enumByType.find? ty).map Prod.snd)
    | failAt j s!"unresolved enum {ty}"
  unless !ms.isEmpty && ms.size ≤ 256 do
    failAt j s!"invalid enum member count {ms.size} for {ty}"
  pure ms

private def validateEnumTypeIfNeeded (j : Json) (ty : String) : M (Option Nat) := do
  if ty.startsWith "enum " then
    pure (some (← resolveEnumMembers j ty).size)
  else
    pure none

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

private partial def publicVarGetterParamTypes (typeName : Json) : M (Array (String × Json) × Json) := do
  match ← mKind typeName with
  | "Mapping" =>
      let kNode ← mField typeName "keyType"
      let kTy ← liftM (typeString kNode)
      let vNode ← mField typeName "valueType"
      let (rest, leaf) ← publicVarGetterParamTypes vNode
      return (#[(kTy, kNode)] ++ rest, leaf)
  | "ArrayTypeName" =>
      let bNode ← mField typeName "baseType"
      let (rest, leaf) ← publicVarGetterParamTypes bNode
      return (#[("uint256", typeName)] ++ rest, leaf)
  | _ =>
      return (#[], typeName)

private def noteFn (fn : Json) : M Unit := do
  let id ← mNat (← mField fn "id")
  let env ← get
  unless env.included.any (·.declId == id) do
    let name ← mStr (← mField fn "name")
    let mut tys : Array String := #[]
    if (← mKind fn) == "VariableDeclaration" then
      let (paramSpecs, _) ← publicVarGetterParamTypes (← mField fn "typeName")
      tys := paramSpecs.map Prod.fst
    else
      let params ← mArr (← mField (← mField fn "parameters") "parameters")
      for p in params do
        tys := tys.push (← liftM (typeString p))
    let contract := env.funContract.find? id |>.getD "<free>"
    modify fun e =>
      let added := e.included.push ⟨contract, name, id, tys⟩
      { e with included := added }

private def rawStorageFieldName : String := "_verity_raw_storage"

private def topStructMemberFieldName (field member : String) : String :=
  let cleanMember := String.intercalate "__" (member.splitOn ".")
  s!"_verity_struct_{field}_{cleanMember}"

private def splitSPathField (raw : String) : String × String :=
  match raw.splitOn "::" with
  | [f, p] => (f, p)
  | _ => (raw, "")

private def qualifySPathMember (subPrefix member : String) : String :=
  if subPrefix == "" then member else s!"{subPrefix}.{member}"

private def appendSPathSub (path : SPath) (subMember : String) : SPath :=
  let ext (raw : String) : String :=
    let (f, p) := splitSPathField raw
    let p' := qualifySPathMember p subMember
    s!"{f}::{p'}"
  match path with
  | .zero raw => .zero (ext raw)
  | .one raw k1 => .one (ext raw) k1
  | .two raw k1 k2 => .two (ext raw) k1 k2
  | other => other

private def markField (name : String) : M Unit := do
  let env ← get
  unless env.referenced.contains name do
    modify fun e => { e with referenced := e.referenced.push name }

private def markStructFixedArray (fieldName memberName : String) : M Unit := do
  let env ← get
  unless env.usedStructFixedArrays.contains (fieldName, memberName) do
    modify fun e => { e with usedStructFixedArrays := e.usedStructFixedArrays.push (fieldName, memberName) }

private def markStructMapping (fieldName memberName : String) : M Unit := do
  let env ← get
  unless env.usedStructMappings.contains (fieldName, memberName) do
    modify fun e => { e with usedStructMappings := e.usedStructMappings.push (fieldName, memberName) }
  modify fun e => { e with usedRawStorage := true }

private def markStructDynamicArray (fieldName memberName : String) : M Unit := do
  let env ← get
  unless env.usedStructDynamicArrays.contains (fieldName, memberName) do
    modify fun e => { e with usedStructDynamicArrays := e.usedStructDynamicArrays.push (fieldName, memberName) }
  modify fun e => { e with usedRawStorage := true }

private def dynamicStorageArrayElement? (elemType : String) :
    Option (String × ParamType × SolidityAbi.ScalarKind) :=
  scalarArrayElement? (elemType ++ "[]")

private def dynamicStorageArrayElemLayout (elemTy : String) : (Nat × Nat × Bool) :=
  if elemTy == "bool" then (8, 32, true)
  else if elemTy == "int256" || elemTy == "int" || elemTy == "bytes32" then (256, 1, false)
  else if elemTy == "address" || elemTy == "address payable" || elemTy.startsWith "contract " then (160, 1, false)
  else
    let bits := (bitsOf elemTy).getD 256
    let byteWidth := max 1 (bits / 8)
    (bits, max 1 (32 / byteWidth), false)

private def resolveStructIdFromSolcType? (env : Env) (solcType : String) : Option Nat :=
  if solcType.startsWith "t_struct(" then
    let parts := solcType.splitOn ")"
    parts.getLast?.bind (fun s => (s.splitOn "_").head?.bind String.toNat?) |>.filter env.structs.contains
  else
    none

private def normalizeSolcLayoutType (env : Env) (solcType : String) : String :=
  if solcType.startsWith "t_userDefinedValueType(" then
    let parts := solcType.splitOn ")"
    let byId? := parts.getLast?.bind String.toNat? |>.bind env.userValueTypeById.find?
    let innerName := ((solcType.drop 23).toString.splitOn ")").headD ""
    let byName? := env.userValueTypes.find? innerName
    match byId? <|> byName? with
    | some u => "t_" ++ u
    | none => solcType
  else
    solcType

private def mappingKey (ty : String) : MetaM MappingKeyType :=
  match ty with
  | "t_bytes32" => pure .bytes32
  | "t_address" | "t_address_payable" => pure .address
  | "t_uint256" | "t_int256" | "t_bool" => pure .uint256
  | _ =>
      if ty.startsWith "t_contract(" then pure .address
      else if ty.startsWith "t_enum(" then pure .uint256
      else if ty.startsWith "t_uint" then do
        let some bits := (ty.drop 6).toNat? | throwError "unsupported mapping key {ty}"
        unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
          throwError "unsupported mapping key {ty}"
        pure .uint256
      else throwError "unsupported mapping key {ty}"

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

private partial def resolveRawStructInfo (structId : Nat) (at_ : Json) : M RawStructInfo := do
  let some sDecl := (← get).structs.find? structId
    | failAt at_ "unknown struct declaration"
  let sName ← mStr (← mField sDecl "name")
  let sMembers ← mArr (← mField sDecl "members")
  unless !sMembers.isEmpty do
    failAt sDecl s!"empty storage struct {sName} is unsupported"
  let mut currWord : Nat := 0
  let mut currByte : Nat := 0
  let mut scalars : Array RawStructMemberInfo := #[]
  let mut mappings : Array StructMappingInfo := #[]
  let mut dynamicArrays : Array StructDynamicArrayInfo := #[]
  let mut subStructs : Array RawStructSubStructInfo := #[]
  for mNode in sMembers do
    let mName ← mStr (← mField mNode "name")
    let mTy ← mType mNode
    let mTyNode ← mField mNode "typeName"
    if optStr mTyNode "nodeType" == some "Mapping" then
      let kNode ← mField mTyNode "keyType"
      let vNode ← mField mTyNode "valueType"
      let kTy ← mType kNode
      let vTy ← mType vNode
      let keyType ←
        if kTy == "address" || kTy == "address payable" || kTy.startsWith "contract " then
          pure MappingKeyType.address
        else if kTy == "uint256" || kTy == "uint" then
          pure MappingKeyType.uint256
        else if kTy == "bytes32" then
          pure MappingKeyType.bytes32
        else
          failAt mNode s!"unsupported struct mapping key type {kTy}"
      let (valueWidth, booleanValue, valueStructId?) ←
        if vTy.startsWith "uint" then
          match bitsOf vTy with
          | some w => pure (w, false, none)
          | none => failAt mNode s!"unsupported struct mapping value type {vTy}"
        else if vTy == "int256" || vTy == "int" || vTy == "bytes32" then
          pure (256, false, none)
        else if vTy == "address" || vTy == "address payable" || vTy.startsWith "contract " then
          pure (160, false, none)
        else if vTy == "bool" then
          pure (8, true, none)
        else if vTy.startsWith "struct " && !vTy.contains "[" then do
          let valSid ← refInt vNode
          unless valSid >= 0 && (← get).structs.contains valSid.toNat do
            failAt mNode s!"unsupported struct mapping value type {vTy}"
          let _ ← resolveRawStructInfo valSid.toNat mNode
          pure (256, false, some valSid.toNat)
        else
          failAt mNode s!"unsupported struct mapping value type {vTy}"
      if currByte > 0 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      currWord := currWord + 1
      mappings := mappings.push {
        member := mName
        solcType := mTy
        wordOffset
        keyType
        valueWidth
        booleanValue
        valueStructId := valueStructId?
      }
    else if optStr mTyNode "nodeType" == some "ArrayTypeName" && (field? mTyNode "length").isNone then
      let baseNode ← mField mTyNode "baseType"
      let baseTy ← mType baseNode
      let (elemTy, modelElemTy, abiKind, elemStructId?) ←
        if let some (eTy, mTy', aKind) := dynamicStorageArrayElement? baseTy then
          pure (eTy, mTy', aKind, none)
        else if baseTy.startsWith "struct " && !baseTy.contains "[" then do
          let elemSid ← refInt baseNode
          unless elemSid >= 0 && (← get).structs.contains elemSid.toNat do
            failAt mNode s!"unsupported storage struct dynamic array member {mName} : {mTy}"
          let elemInfo ← resolveRawStructInfo elemSid.toNat mNode
          unless elemInfo.mappings.isEmpty && elemInfo.dynamicArrays.isEmpty &&
              elemInfo.subStructs.isEmpty && !elemInfo.scalars.isEmpty && elemInfo.wordCount > 0 do
            failAt mNode s!"unsupported storage struct dynamic array member {mName} : {mTy}"
          pure (baseTy, ParamType.uint256, SolidityAbi.ScalarKind.bytes32, some elemSid.toNat)
        else
          failAt mNode s!"unsupported storage struct dynamic array member {mName} : {mTy}"
      if currByte > 0 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      currWord := currWord + 1
      dynamicArrays := dynamicArrays.push {
        member := mName
        solcType := mTy
        wordOffset
        elemType := elemTy
        modelElemType := modelElemTy
        abiKind
        elemStructId := elemStructId?
      }
    else if mTy.startsWith "struct " && !mTy.contains "[" then
      let subSid ← refInt mTyNode
      unless subSid >= 0 && (← get).structs.contains subSid.toNat do
        failAt mNode s!"unresolved nested storage struct member {mName} : {mTy}"
      let subInfo ← resolveRawStructInfo subSid.toNat mNode
      if currByte > 0 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      currWord := currWord + subInfo.wordCount
      subStructs := subStructs.push {
        member := mName
        structId := subSid.toNat
        wordOffset
      }
    else
      let (bitWidth, isBool) ←
        if mTy.startsWith "uint" then
          match bitsOf mTy with
          | some w => pure (w, false)
          | none => failAt mNode s!"unsupported storage struct member {mName} : {mTy}"
        else if mTy == "int256" || mTy == "int" || mTy == "bytes32" then
          pure (256, false)
        else if mTy == "address" || mTy == "address payable" || mTy.startsWith "contract " then
          pure (160, false)
        else if mTy == "bool" then
          pure (8, true)
        else
          failAt mNode s!"unsupported storage struct member {mName} : {mTy}"
      let byteWidth := bitWidth / 8
      if currByte + byteWidth > 32 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      let byteOffset := currByte
      currByte := currByte + byteWidth
      if currByte == 32 then
        currWord := currWord + 1
        currByte := 0
      scalars := scalars.push {
        member := mName
        ty := mTy
        wordOffset
        byteOffset
        bitWidth
        isBool
      }
  let wordCount := if currByte > 0 then currWord + 1 else currWord
  return { structId, structName := sName, scalars, mappings, dynamicArrays, subStructs, wordCount }

private partial def decodeStructLayoutMembers (name prefixStr : String) (baseWord : Nat) (types structTy : Json) :
    M (Array StructMember × Array String × Array String × Array String × Array StructFixedArrayInfo × Array StructMappingInfo × Array StructDynamicArrayInfo × Array (String × Nat)) := do
  let members ← mArr (← mField structTy "members")
  let mut members' : Array StructMember := #[]
  let mut names : Array String := #[]
  let mut skipped : Array String := #[]
  let mut booleanMembers : Array String := #[]
  let mut structFixedArrays : Array StructFixedArrayInfo := #[]
  let mut structMappings : Array StructMappingInfo := #[]
  let mut structDynamicArrays : Array StructDynamicArrayInfo := #[]
  let mut subStructs : Array (String × Nat) := #[]
  for m in members do
    let rawLabel ← mStr (← mField m "label")
    let qualLabel := if prefixStr == "" then rawLabel else s!"{prefixStr}.{rawLabel}"
    let rawSolcType ← mStr (← mField m "type")
    let solcType := normalizeSolcLayoutType (← get) rawSolcType
    let relWord ← mNat (← mField m "slot")
    let word := baseWord + relWord
    let byteOff ← mNat (← mField m "offset")
    if solcType.startsWith "t_struct(" then
      let some subTy := field? types rawSolcType
        | throwError "missing nested struct layout type {rawSolcType}"
      if byteOff == 0 && (← mStr (← mField subTy "encoding")) == "inplace" && (field? subTy "members").isSome then
        if let some sid := resolveStructIdFromSolcType? (← get) rawSolcType then
          subStructs := subStructs.push (qualLabel, sid)
          let (subMembers, subNames, subSkipped, subBools, subFixed, subMaps, subDyns, subSubs) ←
            decodeStructLayoutMembers name qualLabel word types subTy
          members' := members' ++ subMembers
          names := names ++ subNames
          skipped := skipped ++ subSkipped
          booleanMembers := booleanMembers ++ subBools
          structFixedArrays := structFixedArrays ++ subFixed
          structMappings := structMappings ++ subMaps
          structDynamicArrays := structDynamicArrays ++ subDyns
          subStructs := subStructs ++ subSubs
        else
          let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
          modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
          skipped := skipped.push qualLabel
      else
        let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
        modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
        skipped := skipped.push qualLabel
    else if solcType.startsWith "t_array" then
      let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
      modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
      let fixedInfo? : Option StructFixedArrayInfo ← (do
        let some arrTy := field? types rawSolcType | return none
        unless (← mStr (← mField arrTy "encoding")) == "inplace" && byteOff == 0 do
          return none
        let some baseKey := optStr arrTy "base" | return none
        let arrLabel ← mStr (← mField arrTy "label")
        let [elemLabel, suffix] := arrLabel.splitOn "["
          | return none
        unless suffix.endsWith "]" do return none
        let some length := (suffix.dropEnd 1).toNat? | return none
        unless length > 0 do return none
        let some base := field? types baseKey | return none
        let baseLabel ← mStr (← mField base "label")
        unless elemLabel == baseLabel && baseLabel.startsWith "uint" do
          return none
        let some width := bitsOf baseLabel | return none
        unless width > 0 && width ≤ 256 && width % 8 == 0 do
          return none
        unless (← mStr (← mField base "encoding")) == "inplace" &&
            (← mNat (← mField base "numberOfBytes")) * 8 == width do
          return none
        let perWord := 256 / width
        let words := (length + perWord - 1) / perWord
        unless (← mNat (← mField arrTy "numberOfBytes")) == words * 32 do
          return none
        return some {
          member := qualLabel
          solcType := rawSolcType
          wordOffset := word
          byteOffset := byteOff
          length
          elementWidth := width
          arrayType := arrLabel
        })
      let dynInfo? : Option StructDynamicArrayInfo ← (do
        let some arrTy := field? types rawSolcType | return none
        unless (← mStr (← mField arrTy "encoding")) == "dynamic_array" && byteOff == 0 &&
            (← mNat (← mField arrTy "numberOfBytes")) == 32 do
          return none
        let some baseKey := optStr arrTy "base" | return none
        let some base := field? types baseKey | return none
        unless (← mStr (← mField base "encoding")) == "inplace" do
          return none
        let rawBaseLabel ← mStr (← mField base "label")
        let baseLabel := (← get).userValueTypes.find? rawBaseLabel |>.getD rawBaseLabel
        if let some (elemTy, modelElemTy, abiKind) := dynamicStorageArrayElement? baseLabel then
          let (elemBits, _, _) := dynamicStorageArrayElemLayout elemTy
          unless (← mNat (← mField base "numberOfBytes")) * 8 == elemBits do
            return none
          return some {
            member := qualLabel
            solcType := rawSolcType
            wordOffset := word
            elemType := elemTy
            modelElemType := modelElemTy
            abiKind
          }
        if (normalizeSolcLayoutType (← get) baseKey).startsWith "t_struct(" then
          let some sid := resolveStructIdFromSolcType? (← get) baseKey | return none
          let rawInfo ← try resolveRawStructInfo sid Json.null catch _ => return none
          unless rawInfo.mappings.isEmpty && rawInfo.dynamicArrays.isEmpty &&
              rawInfo.subStructs.isEmpty && !rawInfo.scalars.isEmpty && rawInfo.wordCount > 0 do
            return none
          unless (← mNat (← mField base "numberOfBytes")) == rawInfo.wordCount * 32 do
            return none
          return some {
            member := qualLabel
            solcType := rawSolcType
            wordOffset := word
            elemType := rawBaseLabel
            modelElemType := .uint256
            abiKind := .bytes32
            elemStructId := some sid
          }
        return none)
      match fixedInfo?, dynInfo? with
      | some fixedInfo, _ => structFixedArrays := structFixedArrays.push fixedInfo
      | none, some dynInfo => structDynamicArrays := structDynamicArrays.push dynInfo
      | none, none => skipped := skipped.push qualLabel
    else if solcType.startsWith "t_mapping" then
      let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
      modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
      let mapInfo? : Option StructMappingInfo ← (do
        let some mapTy := field? types rawSolcType | return none
        unless (← mStr (← mField mapTy "encoding")) == "mapping" && byteOff == 0 &&
            (← mNat (← mField mapTy "numberOfBytes")) == 32 do
          return none
        let keyStr := normalizeSolcLayoutType (← get) (← mStr (← mField mapTy "key"))
        let keyType ← try liftM (mappingKey keyStr) catch _ => return none
        let valKey ← mStr (← mField mapTy "value")
        let some leafTy := field? types valKey | return none
        if (normalizeSolcLayoutType (← get) valKey).startsWith "t_struct(" then
          let some valSid := resolveStructIdFromSolcType? (← get) valKey | return none
          let _ ← try resolveRawStructInfo valSid Json.null catch _ => return none
          return some {
            member := qualLabel
            solcType := rawSolcType
            wordOffset := word
            keyType
            valueWidth := 256
            booleanValue := false
            valueStructId := some valSid
          }
        unless (field? leafTy "members").isNone && (optStr leafTy "base").isNone do
          return none
        unless (← mStr (← mField leafTy "encoding")) == "inplace" do
          return none
        let rawLeafLabel ← mStr (← mField leafTy "label")
        let leafLabel := (← get).userValueTypes.find? rawLeafLabel |>.getD rawLeafLabel
        let width? : Option Nat :=
          if leafLabel == "bool" then some 8
          else if leafLabel == "address" || leafLabel == "address payable" || leafLabel.startsWith "contract " then some 160
          else if leafLabel == "bytes32" || leafLabel == "int256" || leafLabel == "int" then some 256
          else if leafLabel.startsWith "uint" then
            match (leafLabel.drop 4).toNat? with
            | some bits => if bits > 0 && bits ≤ 256 && bits % 8 == 0 then some bits else none
            | none => none
          else none
        let some width := width? | return none
        unless (← mNat (← mField leafTy "numberOfBytes")) * 8 == width do
          return none
        return some {
          member := qualLabel
          solcType := rawSolcType
          wordOffset := word
          keyType
          valueWidth := width
          booleanValue := leafLabel == "bool"
        })
      match mapInfo? with
      | some mapInfo => structMappings := structMappings.push mapInfo
      | none => skipped := skipped.push qualLabel
    else if solcType == "t_bool" || solcType == "t_address" || solcType == "t_address_payable" ||
        solcType.startsWith "t_contract(" || solcType == "t_bytes32" || solcType == "t_int256" ||
        solcType.startsWith "t_uint" then
      let bits ←
        if solcType == "t_bool" then pure 8
        else if solcType == "t_address" || solcType == "t_address_payable" || solcType.startsWith "t_contract(" then pure 160
        else if solcType == "t_bytes32" || solcType == "t_int256" then pure 256
        else do
          let some b := (solcType.drop 6).toNat? | throwError "bad uint {solcType}"
          unless b > 0 && b ≤ 256 && b % 8 == 0 do throwError "bad uint {solcType}"
          pure b
      let bitOff := byteOff * 8
      unless bitOff + bits ≤ 256 do throwError "packed field {qualLabel} does not fit in a word"
      let packed : Option PackedBits :=
        if bits == 256 && bitOff == 0 then none else some { offset := bitOff, width := bits }
      let ty : StructMemberType := if bits == 16 then .uint16 else .uint256
      members' := members'.push { name := qualLabel, ty, wordOffset := word, packed }
      names := names.push qualLabel
      if solcType == "t_bool" then
        booleanMembers := booleanMembers.push qualLabel
    else
      throwError "unsupported layout member {qualLabel} : {rawSolcType}"
  pure (members', names, skipped, booleanMembers, structFixedArrays, structMappings, structDynamicArrays, subStructs)

private def buildField (types item : Json) : M FieldInfo := do
  let name ← mStr (← mField item "label")
  if name == rawStorageFieldName || name.startsWith "_verity_struct_" then
    throwError "state variable name {name} is reserved"
  let slot ← mNat (← mField item "slot")
  let rawTypeId ← mStr (← mField item "type")
  let top ← liftM (layoutType types rawTypeId)
  let typeId := normalizeSolcLayoutType (← get) rawTypeId
  let encoding ← mStr (← mField top "encoding")
  if encoding == "inplace" then
    if (field? top "members").isSome then
      unless (← mNat (← mField item "offset")) == 0 do
        throwError "top-level storage struct {name} must start at byte offset 0"
      let (members', names, skipped, booleanMembers, structFixedArrays, structMappings, structDynamicArrays, subStructs) ←
        decodeStructLayoutMembers name "" 0 types top
      let field : Field := { name, ty := .uint256, slot := some slot }
      return { slot, field, keyCount := 0, memberNames := names, opaqueNames := skipped,
               booleanMembers, structFixedArrays, structMappings, structDynamicArrays, subStructs,
               structMembers := members' }
    if let some baseId := optStr top "base" then
      unless (← mNat (← mField item "offset")) == 0 do
        throwError "top-level fixed storage array {name} must start at byte offset 0"
      let label ← mStr (← mField top "label")
      let [elementLabel, suffix] := label.splitOn "["
        | throwError "fixed storage arrays require exactly one fixed dimension: {label}"
      unless suffix.endsWith "]" do throwError "invalid fixed array layout {label}"
      let some length := (suffix.dropEnd 1).toNat?
        | throwError "fixed storage arrays require a resolved fixed length: {label}"
      unless length > 0 do throwError "fixed storage array length must be positive"
      let base ← liftM (layoutType types baseId)
      let baseLabel ← mStr (← mField base "label")
      unless elementLabel == baseLabel && baseLabel.startsWith "uint" do
        throwError "fixed storage arrays require unsigned scalar elements: {label}"
      let some width := bitsOf baseLabel
        | throwError "invalid fixed storage array element width: {baseLabel}"
      unless width > 0 && width ≤ 256 && width % 8 == 0 do
        throwError "invalid fixed storage array element width: {width}"
      unless (← mStr (← mField base "encoding")) == "inplace" &&
          (← mNat (← mField base "numberOfBytes")) * 8 == width do
        throwError "fixed storage array base layout disagrees with {baseLabel}"
      let perWord := 256 / width
      let words := (length + perWord - 1) / perWord
      unless (← mNat (← mField top "numberOfBytes")) == words * 32 do
        throwError "fixed storage array footprint disagrees with {label}"
      let mut members : Array StructMember := #[]
      for index in [:length] do
        let offset := (index % perWord) * width
        let packed : Option PackedBits :=
          if width == 256 then none else some { offset := offset, width := width }
        let member : StructMember :=
          { name := s!"__solidity_element_{index}", ty := .uint256, wordOffset := index / perWord, packed }
        members := members.push member
      let field : Field := { name, ty := .uint256, slot := some slot }
      return { slot, field, keyCount := 0, memberNames := #[], opaqueNames := #[],
               structMembers := members, fixedArrayLength := some length, fixedArrayType := label }
    let width ←
      if typeId == "t_bool" then pure 8
      else if typeId == "t_address" || typeId == "t_address_payable" || typeId.startsWith "t_contract(" then pure 160
      else if typeId == "t_bytes32" || typeId == "t_int256" then pure 256
      else if typeId.startsWith "t_uint" then
        let some bits := (typeId.drop 6).toNat? | throwError "invalid scalar uint layout {rawTypeId}"
        unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
          throwError "invalid scalar uint width {bits}"
        pure bits
      else throwError "unsupported scalar storage type {rawTypeId}"
    let bytes ← mNat (← mField top "numberOfBytes")
    unless bytes * 8 == width do
      throwError "scalar storage size disagrees with type {rawTypeId}"
    let offset := (← mNat (← mField item "offset")) * 8
    unless offset + width ≤ 256 do throwError "scalar storage field {name} crosses a word boundary"
    let packedBits : Option PackedBits :=
      if offset == 0 && width == 256 then none else some { offset, width }
    -- Exact physical words; source types still govern conversions and ABI.
    let field : Field := { name, ty := .uint256, slot := some slot, packedBits }
    return { slot, field, keyCount := 0, memberNames := #[], opaqueNames := #[],
             booleanScalar := typeId == "t_bool" }
  if encoding == "bytes" then
    unless typeId == "t_string_storage" || typeId == "t_bytes_storage" do
      throwError "unsupported bytes-encoded storage type {rawTypeId} for {name}"
    let bytes ← mNat (← mField top "numberOfBytes")
    let offset ← mNat (← mField item "offset")
    unless bytes == 32 && offset == 0 do
      throwError "bytes storage field {name} must occupy a full slot at offset 0"
    let field : Field := { name, ty := .uint256, slot := some slot }
    return { slot, field, keyCount := 0, memberNames := #[], opaqueNames := #[],
              bytesStorage := true, stringStorage := typeId == "t_string_storage" }
  if encoding == "dynamic_array" then
    let bytes ← mNat (← mField top "numberOfBytes")
    let offset ← mNat (← mField item "offset")
    unless bytes == 32 && offset == 0 do
      throwError "dynamic array storage field {name} must occupy a full slot at offset 0"
    let some baseKey := optStr top "base"
      | throwError "dynamic array storage field {name} is missing base type"
    let base ← liftM (layoutType types baseKey)
    unless (← mStr (← mField base "encoding")) == "inplace" do
      throwError "unsupported storage encoding {encoding} for {name}"
    let rawBaseLabel ← mStr (← mField base "label")
    let baseLabel := (← get).userValueTypes.find? rawBaseLabel |>.getD rawBaseLabel
    if let some elemSpec := dynamicStorageArrayElement? baseLabel then
      let (elemBits, _, _) := dynamicStorageArrayElemLayout elemSpec.1
      unless (← mNat (← mField base "numberOfBytes")) * 8 == elemBits do
        throwError "unsupported storage encoding {encoding} for {name}"
      let field : Field := { name, ty := .uint256, slot := some slot }
      return { slot, field, keyCount := 0, memberNames := #[], opaqueNames := #[],
               dynamicArrayElemType := some elemSpec }
    if (normalizeSolcLayoutType (← get) baseKey).startsWith "t_struct(" then
      let some sid := resolveStructIdFromSolcType? (← get) baseKey
        | throwError "unsupported storage encoding {encoding} for {name}"
      let rawInfo ← try resolveRawStructInfo sid Json.null catch _ =>
        throwError "unsupported storage encoding {encoding} for {name}"
      unless rawInfo.mappings.isEmpty && rawInfo.dynamicArrays.isEmpty &&
          rawInfo.subStructs.isEmpty && !rawInfo.scalars.isEmpty && rawInfo.wordCount > 0 do
        throwError "unsupported storage encoding {encoding} for {name}"
      unless (← mNat (← mField base "numberOfBytes")) == rawInfo.wordCount * 32 do
        throwError "unsupported storage encoding {encoding} for {name}"
      let field : Field := { name, ty := .uint256, slot := some slot }
      return { slot, field, keyCount := 0, memberNames := #[], opaqueNames := #[],
               dynamicArrayElemType := some (rawBaseLabel, .uint256, .bytes32),
               dynamicArrayStructId := some sid }
    throwError "unsupported storage encoding {encoding} for {name}"
  unless encoding == "mapping" do
    throwError "unsupported storage encoding {encoding} for {name}"
  let key1 ← liftM (mappingKey (normalizeSolcLayoutType (← get) (← mStr (← mField top "key"))))
  let valueId ← mStr (← mField top "value")
  let value ← liftM (layoutType types valueId)
  let encoding ← mStr (← mField value "encoding")
  let (key2, structTy) ←
    if encoding == "mapping" then
      let key2 ← liftM (mappingKey (normalizeSolcLayoutType (← get) (← mStr (← mField value "key"))))
      let innerId ← mStr (← mField value "value")
      pure (some key2, ← liftM (layoutType types innerId))
    else if encoding == "inplace" then
      pure (none, value)
    else
      throwError "unsupported mapping value encoding {encoding} for {name}"
  if let some k2 := key2 then
    if (← mStr (← mField structTy "encoding")) == "mapping" then
      let key3 ← liftM (mappingKey (normalizeSolcLayoutType (← get) (← mStr (← mField structTy "key"))))
      let valKey ← mStr (← mField structTy "value")
      let leafTy ← liftM (layoutType types valKey)
      if (normalizeSolcLayoutType (← get) valKey).startsWith "t_struct(" then
        let some valSid := resolveStructIdFromSolcType? (← get) valKey
          | throwError "unsupported 3-key mapping value type {valKey} for {name}"
        let _ ← resolveRawStructInfo valSid Json.null
        let mapInfo : StructMappingInfo :=
          { member := "__solidity_value"
            solcType := valKey
            wordOffset := 0
            keyType := key3
            valueWidth := 256
            booleanValue := false
            valueStructId := some valSid }
        let field : Field := { name, ty := .mappingStruct2 key1 k2 [], slot := some slot }
        return { slot, field, keyCount := 2, memberNames := #[], opaqueNames := #[],
                 thirdKeyMapping := some mapInfo }
      if (field? leafTy "members").isNone && (optStr leafTy "base").isNone then
        let leafEncoding ← mStr (← mField leafTy "encoding")
        unless leafEncoding == "inplace" do
          throwError "unsupported 3-key mapping value encoding {leafEncoding} for {name}"
        let rawLeafType ← mStr (← mField leafTy "label")
        let leafType := (← get).userValueTypes.find? rawLeafType |>.getD rawLeafType
        let width ←
          if leafType == "bool" then pure 8
          else if leafType == "address" || leafType == "address payable" || leafType.startsWith "contract " then pure 160
          else if leafType == "bytes32" || leafType == "int256" || leafType == "int" then pure 256
          else if leafType.startsWith "uint" then
            let some bits := (leafType.drop 4).toNat? | throwError "invalid 3-key mapping uint layout {rawLeafType}"
            unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
              throwError "invalid 3-key mapping uint width {bits}"
            pure bits
          else throwError "unsupported 3-key mapping value type {rawLeafType} for {name}"
        let bytes ← mNat (← mField leafTy "numberOfBytes")
        unless bytes * 8 == width do
          throwError "3-key mapping value size disagrees with type {rawLeafType}"
        let mapInfo : StructMappingInfo :=
          { member := "__solidity_value"
            solcType := valKey
            wordOffset := 0
            keyType := key3
            valueWidth := width
            booleanValue := leafType == "bool" }
        let field : Field := { name, ty := .mappingStruct2 key1 k2 [], slot := some slot }
        return { slot, field, keyCount := 2, memberNames := #[], opaqueNames := #[],
                 thirdKeyMapping := some mapInfo }
      throwError "unsupported 3-key mapping value type for {name}"
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
    let rawLeafType ← mStr (← mField structTy "label")
    let leafType := (← get).userValueTypes.find? rawLeafType |>.getD rawLeafType
    let width ←
      if leafType == "bool" then pure 8
      else if leafType == "address" || leafType == "address payable" || leafType.startsWith "contract " then pure 160
      else if leafType == "bytes32" || leafType == "int256" || leafType == "int" then pure 256
      else if leafType.startsWith "uint" then
        let some bits := (leafType.drop 4).toNat? | throwError "invalid mapping uint layout {rawLeafType}"
        unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
          throwError "invalid mapping uint width {bits}"
        pure bits
      else throwError "unsupported scalar mapping value type {rawLeafType}"
    let bytes ← mNat (← mField structTy "numberOfBytes")
    unless bytes * 8 == width do
      throwError "scalar mapping value size disagrees with type {rawLeafType}"
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
  let (members', names, skipped, booleanMembers, structFixedArrays, structMappings, structDynamicArrays, subStructs) ←
    decodeStructLayoutMembers name "" 0 types structTy
  let ty : FieldType :=
    match key2 with
    | some k2 => .mappingStruct2 key1 k2 members'.toList
    | none => .mappingStruct key1 members'.toList
  let field : Field := { name, ty, slot := some slot }
  pure { slot, field, keyCount := if key2.isSome then 2 else 1,
         memberNames := names, opaqueNames := skipped, booleanMembers, structFixedArrays, structMappings,
         structDynamicArrays, subStructs, structMembers := members' }

/-- Resolve only reached fields: an unrelated unsupported layout must not
prevent importing a supported function closure. -/
private def resolveField (name : String) (at_ : Json) : M FieldInfo := do
  if name == rawStorageFieldName || name.startsWith "_verity_struct_" then
    failAt at_ s!"reserved storage field name {name}"
  if let some info := (← get).fieldsByName.find? name then return info
  let env ← get
  let some item := env.layoutItems.find? name | failAt at_ s!"no storage layout for {name}"
  let info ← try buildField env.layoutTypes item catch ex =>
    failAt at_ (← ex.toMessageData.toString)
  modify fun e => { e with fieldsByName := e.fieldsByName.insert name info }
  return info

private def rawStructMemberSlot (baseSlot : Expr) (wordOffset : Nat) : Expr :=
  if wordOffset == 0 then baseSlot else .add baseSlot (.literal wordOffset)

private def readRawStructScalar (pre : Array Stmt) (baseSlot : Expr) (mInfo : RawStructMemberInfo) : M Val := do
  modify fun e => { e with usedRawStorage := true }
  let wordSlot := rawStructMemberSlot baseSlot mInfo.wordOffset
  let rawWord := Expr.storageArrayElement rawStorageFieldName wordSlot
  let shifted := if mInfo.byteOffset == 0 then rawWord else Expr.shr (.literal (mInfo.byteOffset * 8)) rawWord
  let masked := if mInfo.bitWidth < 256 then Expr.bitAnd shifted (.literal (2 ^ mInfo.bitWidth - 1)) else shifted
  let cleaned := if mInfo.isBool then Expr.logicalNot (.logicalNot masked) else masked
  let dest ← fresh
  pure { pre := pre.push (.letVar dest cleaned), expr := .localVar dest }

private def writeRawStructScalar (pre : Array Stmt) (baseSlot : Expr) (mInfo : RawStructMemberInfo)
    (valExpr : Expr) (deleting : Bool) : M (Array Stmt) := do
  modify fun e => { e with usedRawStorage := true }
  let wordSlot := rawStructMemberSlot baseSlot mInfo.wordOffset
  let cleanVal :=
    if mInfo.isBool && !deleting then Expr.logicalNot (.logicalNot valExpr)
    else if mInfo.bitWidth < 256 then Expr.bitAnd valExpr (.literal (2 ^ mInfo.bitWidth - 1))
    else valExpr
  if mInfo.bitWidth == 256 && mInfo.byteOffset == 0 then
    return pre.push (.setStorageArrayElement rawStorageFieldName wordSlot cleanVal)
  else
    let shiftBits := mInfo.byteOffset * 8
    let mask := (2 ^ mInfo.bitWidth - 1) * (2 ^ shiftBits)
    let invMask := (2 ^ 256 - 1) - mask
    let shiftedVal := if deleting then Expr.literal 0 else if shiftBits == 0 then cleanVal else Expr.shl (.literal shiftBits) cleanVal
    let oldWord ← fresh
    let newWord := if deleting then Expr.bitAnd (.localVar oldWord) (.literal invMask)
                   else Expr.bitOr (.bitAnd (.localVar oldWord) (.literal invMask)) shiftedVal
    return pre ++ #[
      .letVar oldWord (.storageArrayElement rawStorageFieldName wordSlot),
      .setStorageArrayElement rawStorageFieldName wordSlot newWord
    ]

private def computeSPathBaseSlot (path : SPath) (info : FieldInfo) (wordOffset : Nat) (at_ : Json) :
    M (Array Stmt × Expr) := do
  modify fun e => { e with encodingMemory := true }
  let (count, baseStmts, baseSlot) ← match path with
    | .zero _ => do
        let bSlot ← fresh
        pure (0, #[Stmt.letVar bSlot (.literal info.slot)], bSlot)
    | .one _ k1 => do
        let bSlot ← fresh
        let stmts : Array Stmt := #[
          .mstore (.literal 0) k1,
          .mstore (.literal 32) (.literal info.slot),
          .letVar bSlot (.keccak256 (.literal 0) (.literal 64))
        ]
        pure (1, stmts, bSlot)
    | .two _ k1 k2 => do
        let outerSlot ← fresh
        let bSlot ← fresh
        let stmts : Array Stmt := #[
          .mstore (.literal 0) k1,
          .mstore (.literal 32) (.literal info.slot),
          .letVar outerSlot (.keccak256 (.literal 0) (.literal 64)),
          .mstore (.literal 0) k2,
          .mstore (.literal 32) (.localVar outerSlot),
          .letVar bSlot (.keccak256 (.literal 0) (.literal 64))
        ]
        pure (2, stmts, bSlot)
    | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
        failAt at_ "storage struct member access requires all outer mapping keys"
  unless info.keyCount == count do
    failAt at_ "storage struct mapping key count differs"
  let slotExpr :=
    if wordOffset == 0 then Expr.localVar baseSlot
    else .add (.localVar baseSlot) (.literal wordOffset)
  return (baseStmts, slotExpr)

private def resolveStructDynamicSlot (path : SPath) (dynInfo : StructDynamicArrayInfo) (at_ : Json) :
    M (Array Stmt × Expr) := do
  if let .rawSlot _ baseSlot := path then
    return (#[], rawStructMemberSlot baseSlot dynInfo.wordOffset)
  else
    let rawName ← match path with
      | .zero name | .one name _ | .two name _ _ => pure name
      | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
          failAt at_ "struct dynamic array element requires all outer mapping keys"
    let (name, _) := splitSPathField rawName
    let info ← resolveField name at_
    markField name
    markStructDynamicArray name dynInfo.member
    computeSPathBaseSlot path info dynInfo.wordOffset at_

private def readStorageDynamicArrayLength (pre : Array Stmt) (fieldName : String) (slotExpr : Expr) : M Val := do
  let raw := if fieldName != "" then Expr.storage fieldName else Expr.storageArrayElement rawStorageFieldName slotExpr
  if fieldName != "" then
    markField fieldName
  else
    modify fun e => { e with usedRawStorage := true }
  let dest ← fresh
  pure { pre := pre.push (.letVar dest raw), expr := .localVar dest }

private def storageDynamicStructElementPath (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemSid : Nat) (indexExpr : Expr) (at_ : Json) (oobStmt : Stmt := .panicCode (.literal 0x32)) :
    M (Array Stmt × SPath) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let rawInfo ← resolveRawStructInfo elemSid at_
  let capturedIdx ← fresh
  let lenVal ← readStorageDynamicArrayLength (pre.push (.letVar capturedIdx indexExpr)) fieldName slotExpr
  let baseDataSlot ← fresh
  let elemSlot ← fresh
  let idxExpr := Expr.localVar capturedIdx
  let wordOff := if rawInfo.wordCount == 1 then idxExpr else Expr.mul idxExpr (.literal rawInfo.wordCount)
  let stmts : Array Stmt := #[
    .ite (.lt idxExpr lenVal.expr) [] [oobStmt],
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar elemSlot (.add (.localVar baseDataSlot) wordOff)
  ]
  return (lenVal.pre ++ stmts, .rawSlot elemSid (.localVar elemSlot))

private def readStorageDynamicArrayElement (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (indexExpr : Expr) (oobStmt : Stmt := .panicCode (.literal 0x32)) : M Val := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let (bits, perWord, isBool) := dynamicStorageArrayElemLayout elemTy
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let baseDataSlot ← fresh
  let elemSlot ← fresh
  let dest ← fresh
  let wordOff := if perWord == 1 then indexExpr else Expr.div indexExpr (.literal perWord)
  let rawWord := Expr.storageArrayElement rawStorageFieldName (.localVar elemSlot)
  let shifted :=
    if perWord == 1 then rawWord
    else Expr.shr (.mul (.mod indexExpr (.literal perWord)) (.literal bits)) rawWord
  let masked :=
    if bits < 256 then Expr.bitAnd shifted (.literal (2 ^ bits - 1))
    else shifted
  let cleaned := if isBool then Expr.logicalNot (.logicalNot masked) else masked
  let stmts : Array Stmt := #[
    .ite (.lt indexExpr lenVal.expr) [] [oobStmt],
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar elemSlot (.add (.localVar baseDataSlot) wordOff),
    .letVar dest cleaned
  ]
  pure { pre := lenVal.pre ++ stmts, expr := .localVar dest }

private def writeStorageDynamicArrayElementAtUnchecked (baseDataSlot : String) (elemTy : String)
    (indexExpr valExpr : Expr) (deleting : Bool) : M (Array Stmt) := do
  let (bits, perWord, isBool) := dynamicStorageArrayElemLayout elemTy
  let elemSlot ← fresh
  let wordOff := if perWord == 1 then indexExpr else Expr.div indexExpr (.literal perWord)
  let cleanVal :=
    if deleting then Expr.literal 0
    else if isBool then Expr.logicalNot (.logicalNot valExpr)
    else if bits < 256 then Expr.bitAnd valExpr (.literal (2 ^ bits - 1))
    else valExpr
  if bits == 256 && perWord == 1 then
    return #[
      .letVar elemSlot (.add (.localVar baseDataSlot) wordOff),
      .setStorageArrayElement rawStorageFieldName (.localVar elemSlot) cleanVal
    ]
  else
    let shiftBits :=
      if perWord == 1 then Expr.literal 0
      else Expr.mul (.mod indexExpr (.literal perWord)) (.literal bits)
    let elemMask :=
      if perWord == 1 then Expr.literal (2 ^ bits - 1)
      else Expr.shl shiftBits (.literal (2 ^ bits - 1))
    let invMask := Expr.bitNot elemMask
    let shiftedVal :=
      if deleting then Expr.literal 0
      else if perWord == 1 then cleanVal
      else Expr.shl shiftBits cleanVal
    let oldWord ← fresh
    let newWord :=
      if deleting then Expr.bitAnd (.localVar oldWord) invMask
      else Expr.bitOr (.bitAnd (.localVar oldWord) invMask) shiftedVal
    return #[
      .letVar elemSlot (.add (.localVar baseDataSlot) wordOff),
      .letVar oldWord (.storageArrayElement rawStorageFieldName (.localVar elemSlot)),
      .setStorageArrayElement rawStorageFieldName (.localVar elemSlot) newWord
    ]

private def writeStorageDynamicArrayElement (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (indexExpr valExpr : Expr) (deleting : Bool) : M (Array Stmt) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let baseDataSlot ← fresh
  let writeStmts ← writeStorageDynamicArrayElementAtUnchecked baseDataSlot elemTy indexExpr valExpr deleting
  let stmts : Array Stmt := #[
    .ite (.lt indexExpr lenVal.expr) [] [.panicCode (.literal 0x32)],
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32))
  ] ++ writeStmts
  return lenVal.pre ++ stmts

private def pushStorageDynamicArray (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (valExpr? : Option Expr) : M Val := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let newLen ← fresh
  let baseDataSlot ← fresh
  let writeLenStmt : Stmt :=
    if fieldName != "" then .setStorage fieldName (.localVar newLen)
    else .setStorageArrayElement rawStorageFieldName slotExpr (.localVar newLen)
  let elemVal := valExpr?.getD (.literal 0)
  let writeStmts ← writeStorageDynamicArrayElementAtUnchecked baseDataSlot elemTy lenVal.expr elemVal valExpr?.isNone
  let stmts : Array Stmt := #[
    .letVar newLen (.add lenVal.expr (.literal 1)),
    writeLenStmt,
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32))
  ] ++ writeStmts
  pure { pre := lenVal.pre ++ stmts, expr := elemVal }

private def pushStorageDynamicStructArray (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemSid : Nat) (memberVals? : Option (Array (String × String × Expr))) (at_ : Json) :
    M (Array Stmt × SPath) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let rawInfo ← resolveRawStructInfo elemSid at_
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let newLen ← fresh
  let baseDataSlot ← fresh
  let elemSlot ← fresh
  let writeLenStmt : Stmt :=
    if fieldName != "" then .setStorage fieldName (.localVar newLen)
    else .setStorageArrayElement rawStorageFieldName slotExpr (.localVar newLen)
  let wordOff := if rawInfo.wordCount == 1 then lenVal.expr else Expr.mul lenVal.expr (.literal rawInfo.wordCount)
  let mut stmts : Array Stmt := #[
    .letVar newLen (.add lenVal.expr (.literal 1)),
    writeLenStmt,
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar elemSlot (.add (.localVar baseDataSlot) wordOff)
  ]
  for w in [:rawInfo.wordCount] do
    stmts := stmts.push (.setStorageArrayElement rawStorageFieldName (rawStructMemberSlot (.localVar elemSlot) w) (.literal 0))
  if let some memberVals := memberVals? then
    unless memberVals.size == rawInfo.scalars.size do
      failAt at_ "struct array push member count mismatch"
    for (mName, _, mExpr) in memberVals do
      let some mInfo := rawInfo.scalars.find? (·.member == mName)
        | failAt at_ s!"unknown struct member {mName}"
      let writeStmts ← writeRawStructScalar #[] (.localVar elemSlot) mInfo mExpr false
      stmts := stmts ++ writeStmts
  return (lenVal.pre ++ stmts, .rawSlot elemSid (.localVar elemSlot))

private def popStorageDynamicArray (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (elemStructId? : Option Nat := none) (at_ : Json := Json.null) : M (Array Stmt) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let newLen ← fresh
  let baseDataSlot ← fresh
  let clearStmts ← match elemStructId? with
    | some elemSid => do
        let rawInfo ← resolveRawStructInfo elemSid at_
        let elemSlot ← fresh
        let wordOff := if rawInfo.wordCount == 1 then Expr.localVar newLen else Expr.mul (.localVar newLen) (.literal rawInfo.wordCount)
        let mut clears : Array Stmt := #[
          .letVar elemSlot (.add (.localVar baseDataSlot) wordOff)
        ]
        for w in [:rawInfo.wordCount] do
          clears := clears.push (.setStorageArrayElement rawStorageFieldName (rawStructMemberSlot (.localVar elemSlot) w) (.literal 0))
        pure clears
    | none =>
        writeStorageDynamicArrayElementAtUnchecked baseDataSlot elemTy (.localVar newLen) (.literal 0) true
  let writeLenStmt : Stmt :=
    if fieldName != "" then .setStorage fieldName (.localVar newLen)
    else .setStorageArrayElement rawStorageFieldName slotExpr (.localVar newLen)
  let stmts : Array Stmt := #[
    .ite (.gt lenVal.expr (.literal 0)) [] [.panicCode (.literal 0x31)],
    .letVar newLen (.sub lenVal.expr (.literal 1)),
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32))
  ] ++ clearStmts ++ #[
    writeLenStmt
  ]
  return lenVal.pre ++ stmts

private def deleteStorageDynamicArray (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (elemStructId? : Option Nat := none) (at_ : Json := Json.null) : M (Array Stmt) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let baseDataSlot ← fresh
  let wordCount ← fresh
  let loopIdx ← fresh
  let wordCountExpr ← match elemStructId? with
    | some elemSid => do
        let rawInfo ← resolveRawStructInfo elemSid at_
        pure (if rawInfo.wordCount == 1 then lenVal.expr else Expr.mul lenVal.expr (.literal rawInfo.wordCount))
    | none => do
        let (_, perWord, _) := dynamicStorageArrayElemLayout elemTy
        pure (if perWord == 1 then lenVal.expr
              else Expr.div (.add lenVal.expr (.literal (perWord - 1))) (.literal perWord))
  let writeLenStmt : Stmt :=
    if fieldName != "" then .setStorage fieldName (.literal 0)
    else .setStorageArrayElement rawStorageFieldName slotExpr (.literal 0)
  let stmts : Array Stmt := #[
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar wordCount wordCountExpr,
    .forEach loopIdx (.localVar wordCount) [
      .setStorageArrayElement rawStorageFieldName (.add (.localVar baseDataSlot) (.localVar loopIdx)) (.literal 0)
    ],
    writeLenStmt
  ]
  return lenVal.pre ++ stmts

private def copyStorageDynamicArrayToMemory (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (modelElemTy : ParamType) (abiKind : SolidityAbi.ScalarKind) (hintName : String) :
    M (Array Stmt × ScalarArrayParam) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let (bits, perWord, isBool) := dynamicStorageArrayElemLayout elemTy
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let lengthBinding ← freshFor (if hintName == "" then "arr_len" else s!"{hintName}_len")
  let arrayPtr ← freshFor (if hintName == "" then "arr_ptr" else hintName)
  let nextFree ← fresh
  let baseDataSlot ← fresh
  let copyIdx ← fresh
  let byteCount := Expr.add (.literal 32) (.mul (.localVar lengthBinding) (.literal 32))
  let allocStmts := AbiEncoding.reserve arrayPtr nextFree byteCount
  let wordOff :=
    if perWord == 1 then Expr.localVar copyIdx
    else Expr.div (.localVar copyIdx) (.literal perWord)
  let rawWord := Expr.storageArrayElement rawStorageFieldName (.add (.localVar baseDataSlot) wordOff)
  let shifted :=
    if perWord == 1 then rawWord
    else Expr.shr (.mul (.mod (.localVar copyIdx) (.literal perWord)) (.literal bits)) rawWord
  let masked :=
    if bits < 256 then Expr.bitAnd shifted (.literal (2 ^ bits - 1))
    else shifted
  let elemVal := if isBool then Expr.logicalNot (.logicalNot masked) else masked
  let copyStmts : Array Stmt := #[
    .letVar lengthBinding lenVal.expr
  ] ++ allocStmts.toArray ++ #[
    .mstore (.localVar arrayPtr) (.localVar lengthBinding),
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .forEach copyIdx (.localVar lengthBinding) [
      .mstore
        (.add (.add (.localVar arrayPtr) (.literal 32)) (.mul (.localVar copyIdx) (.literal 32)))
        elemVal
    ]
  ]
  let desc : ScalarArrayParam := {
    param := hintName
    elementType := elemTy
    modelElementType := modelElemTy
    abiKind
    inMemory := true
    lengthBinding
    memoryPointer := arrayPtr
    nextFreeBinding := nextFree
  }
  return (lenVal.pre ++ copyStmts, desc)

private def computeStructMappingLeafSlot (path : SPath) (info : FieldInfo) (mapInfo : StructMappingInfo)
    (innerKey : Expr) (at_ : Json) : M (Array Stmt × Expr) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  let (baseStmts, mapBaseExpr) ← computeSPathBaseSlot path info mapInfo.wordOffset at_
  let leafSlot ← fresh
  let leafStmts : Array Stmt := #[
    .mstore (.literal 0) innerKey,
    .mstore (.literal 32) mapBaseExpr,
    .letVar leafSlot (.keccak256 (.literal 0) (.literal 64))
  ]
  return (baseStmts ++ leafStmts, .localVar leafSlot)

private def readStructMappingElement (pre : Array Stmt) (path : SPath) (mapInfo : StructMappingInfo)
    (innerKey : Expr) (at_ : Json) : M Val := do
  if let .rawSlot _ baseSlot := path then
    modify fun e => { e with encodingMemory := true, usedRawStorage := true }
    let mapBaseExpr := rawStructMemberSlot baseSlot mapInfo.wordOffset
    let leafSlot ← fresh
    let slotStmts : Array Stmt := #[
      .mstore (.literal 0) innerKey,
      .mstore (.literal 32) mapBaseExpr,
      .letVar leafSlot (.keccak256 (.literal 0) (.literal 64))
    ]
    let raw := Expr.storageArrayElement rawStorageFieldName (.localVar leafSlot)
    let masked :=
      if mapInfo.valueWidth < 256 then Expr.bitAnd raw (.literal (2 ^ mapInfo.valueWidth - 1))
      else raw
    let cleaned :=
      if mapInfo.booleanValue then Expr.logicalNot (.logicalNot masked)
      else masked
    let dest ← fresh
    return { pre := pre ++ slotStmts ++ #[.letVar dest cleaned], expr := .localVar dest }
  let rawName ← match path with
    | .zero name | .one name _ | .two name _ _ => pure name
    | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
        failAt at_ "struct mapping element requires both outer mapping keys"
  let (name, _) := splitSPathField rawName
  let info ← resolveField name at_
  markField name
  markStructMapping name mapInfo.member
  let (slotStmts, slotExpr) ← computeStructMappingLeafSlot path info mapInfo innerKey at_
  let raw := Expr.storageArrayElement rawStorageFieldName slotExpr
  let masked :=
    if mapInfo.valueWidth < 256 then Expr.bitAnd raw (.literal (2 ^ mapInfo.valueWidth - 1))
    else raw
  let cleaned :=
    if mapInfo.booleanValue then Expr.logicalNot (.logicalNot masked)
    else masked
  let dest ← fresh
  pure { pre := pre ++ slotStmts ++ #[.letVar dest cleaned], expr := .localVar dest }

private def writeStructMappingElement (pre : Array Stmt) (path : SPath) (mapInfo : StructMappingInfo)
    (innerKey valExpr : Expr) (deleting : Bool) (at_ : Json) : M (Array Stmt) := do
  if let .rawSlot _ baseSlot := path then
    modify fun e => { e with encodingMemory := true, usedRawStorage := true }
    let mapBaseExpr := rawStructMemberSlot baseSlot mapInfo.wordOffset
    let leafSlot ← fresh
    let slotStmts : Array Stmt := #[
      .mstore (.literal 0) innerKey,
      .mstore (.literal 32) mapBaseExpr,
      .letVar leafSlot (.keccak256 (.literal 0) (.literal 64))
    ]
    let slotExpr := Expr.localVar leafSlot
    let cleanVal :=
      if mapInfo.booleanValue && !deleting then Expr.logicalNot (.logicalNot valExpr)
      else if mapInfo.valueWidth < 256 then Expr.bitAnd valExpr (.literal (2 ^ mapInfo.valueWidth - 1))
      else valExpr
    if mapInfo.valueWidth == 256 then
      return pre ++ slotStmts ++ #[.setStorageArrayElement rawStorageFieldName slotExpr cleanVal]
    else
      let mask := 2 ^ mapInfo.valueWidth - 1
      let invMask := (2 ^ 256 - 1) - mask
      let oldWord ← fresh
      let newWord := Expr.bitOr (.bitAnd (.localVar oldWord) (.literal invMask)) cleanVal
      return pre ++ slotStmts ++ #[
        .letVar oldWord (.storageArrayElement rawStorageFieldName slotExpr),
        .setStorageArrayElement rawStorageFieldName slotExpr newWord
      ]
  let rawName ← match path with
    | .zero name | .one name _ | .two name _ _ => pure name
    | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
        failAt at_ "struct mapping element requires both outer mapping keys"
  let (name, _) := splitSPathField rawName
  let info ← resolveField name at_
  markField name
  markStructMapping name mapInfo.member
  let (slotStmts, slotExpr) ← computeStructMappingLeafSlot path info mapInfo innerKey at_
  let cleanVal :=
    if mapInfo.booleanValue && !deleting then Expr.logicalNot (.logicalNot valExpr)
    else if mapInfo.valueWidth < 256 then Expr.bitAnd valExpr (.literal (2 ^ mapInfo.valueWidth - 1))
    else valExpr
  if mapInfo.valueWidth == 256 then
    return pre ++ slotStmts ++ #[.setStorageArrayElement rawStorageFieldName slotExpr cleanVal]
  else
    let mask := 2 ^ mapInfo.valueWidth - 1
    let invMask := (2 ^ 256 - 1) - mask
    let oldWord ← fresh
    let newWord := Expr.bitOr (.bitAnd (.localVar oldWord) (.literal invMask)) cleanVal
    return pre ++ slotStmts ++ #[
      .letVar oldWord (.storageArrayElement rawStorageFieldName slotExpr),
      .setStorageArrayElement rawStorageFieldName slotExpr newWord
    ]

private def memberRead (pre : Array Stmt) (path : SPath) (member : String) (at_ : Json) : M Val := do
  if let .rawSlot structId baseSlot := path then
    let rawInfo ← resolveRawStructInfo structId at_
    let some mInfo := rawInfo.scalars.find? (·.member == member)
      | failAt at_ s!"member {member} is not a scalar member of {rawInfo.structName}"
    return ← readRawStructScalar pre baseSlot mInfo
  let (fieldName, qualMember, read) ← match path with
    | .zero rawField =>
        let (field, subPrefix) := splitSPathField rawField
        let qm := qualifySPathMember subPrefix member
        pure (field, qm, Expr.storage (topStructMemberFieldName field qm))
    | .one rawField key =>
        let (field, subPrefix) := splitSPathField rawField
        let qm := qualifySPathMember subPrefix member
        pure (field, qm, Expr.structMember field key qm)
    | .two rawField k1 k2 =>
        let (field, subPrefix) := splitSPathField rawField
        let qm := qualifySPathMember subPrefix member
        pure (field, qm, Expr.structMember2 field k1 k2 qm)
    | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ => failAt at_ "member access on an incomplete mapping"
  let info ← resolveField fieldName at_
  if info.opaqueNames.contains qualMember then
    failAt at_ s!"member {qualMember} is opaque in this slice"
  unless info.memberNames.contains qualMember do
    failAt at_ s!"member {qualMember} is not a layout member of {fieldName}"
  markField fieldName
  let expr := if info.booleanMembers.contains qualMember then Expr.logicalNot (.logicalNot read) else read
  pure { pre, expr }

private def scalarMappingRead (pre : Array Stmt) (path : SPath) (at_ : Json) : M Val := do
  let (name, count, read) ← match path with
    | .one field key => pure (field, 1, Expr.structMember field key "__solidity_value")
    | .two field key1 key2 => pure (field, 2, Expr.structMember2 field key1 key2 "__solidity_value")
    | .zero _ | .rawSlot _ _ | .bytesSlot _ _ => failAt at_ "storage or memory path used as a value"
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

private def maxSafeExponent (base bits : Nat) : Nat := Id.run do
  let limit := 2 ^ bits
  let mut acc := 1
  let mut exp := 0
  for _ in [:bits] do
    if acc * base < limit then
      acc := acc * base
      exp := exp + 1
  return exp

private def maxSafeBase (exponent bits : Nat) : Nat := Id.run do
  if exponent >= bits then
    return 1
  let limit := 2 ^ bits
  let boundBits := bits / exponent + 1
  let mut lo := 0
  let mut hi := 2 ^ boundBits
  for _ in [:boundBits + 2] do
    if lo < hi then
      let mid := (lo + hi + 1) / 2
      if mid ^ exponent < limit then
        lo := mid
      else
        hi := mid - 1
  return lo

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

private def lowerYulAddmod (a b m : Expr) : M Val := do
  let mBinding ← fresh
  let aModBinding ← fresh
  let bModBinding ← fresh
  let diffBinding ← fresh
  let resBinding ← fresh
  let stmts : Array Stmt := #[
    .letVar mBinding m,
    .letVar aModBinding (.mod a (.localVar mBinding)),
    .letVar bModBinding (.mod b (.localVar mBinding)),
    .letVar diffBinding (.sub (.localVar mBinding) (.localVar bModBinding)),
    .letVar resBinding (.literal 0),
    .ite (.lt (.localVar aModBinding) (.localVar diffBinding))
      [.assignVar resBinding (.add (.localVar aModBinding) (.localVar bModBinding))]
      [.assignVar resBinding (.sub (.localVar aModBinding) (.localVar diffBinding))]
  ]
  pure { pre := stmts, expr := .localVar resBinding }

private def lowerYulMulmod (a b m : Expr) : M Val := do
  let mBinding ← fresh
  let termBinding ← fresh
  let remBinding ← fresh
  let accBinding ← fresh
  let diffBinding ← fresh
  let idxBinding ← fresh
  let loopBody : List Stmt := [
    .assignVar diffBinding (.sub (.localVar mBinding) (.localVar termBinding)),
    .ite (.eq (.bitAnd (.localVar remBinding) (.literal 1)) (.literal 1))
      [.ite (.lt (.localVar accBinding) (.localVar diffBinding))
        [.assignVar accBinding (.add (.localVar accBinding) (.localVar termBinding))]
        [.assignVar accBinding (.sub (.localVar accBinding) (.localVar diffBinding))]]
      [],
    .ite (.lt (.localVar termBinding) (.localVar diffBinding))
      [.assignVar termBinding (.add (.localVar termBinding) (.localVar termBinding))]
      [.assignVar termBinding (.sub (.localVar termBinding) (.localVar diffBinding))],
    .assignVar remBinding (.shr (.literal 1) (.localVar remBinding))
  ]
  let stmts : Array Stmt := #[
    .letVar mBinding m,
    .letVar termBinding (.mod a (.localVar mBinding)),
    .letVar remBinding (.mod b (.localVar mBinding)),
    .letVar accBinding (.literal 0),
    .letVar diffBinding (.literal 0),
    .forEach idxBinding (.literal 256) loopBody
  ]
  pure { pre := stmts, expr := .localVar accBinding }

private def yulZeroTwoZeroLiteral? (j : Json) : M Bool := do
  if (← mKind j) != "YulLiteral" then return false
  if optStr j "kind" != some "number" || optStr j "type" != some "" then return false
  let raw ← mStr (← mField j "value")
  pure ((Compiler.Hex.parseHexNat? raw <|> raw.toNat?) == some 32)

private def yulMemoryArrayPtr? (j : Json) : M (Option (String × String)) := do
  if (← mKind j) != "YulIdentifier" then return none
  let name ← mStr (← mField j "name")
  let env ← get
  if env.yulNames.contains name then return none
  let some ptr := env.yulMemoryArrays.find? name | return none
  return some (name, ptr)

private def yulMemoryArrayPayloadSlice? (ptrNode sizeNode : Json) : M (Option (Expr × Expr)) := do
  if (← mKind ptrNode) != "YulFunctionCall" || (← mKind sizeNode) != "YulFunctionCall" then
    return none
  let ptrFn ← mStr (← mField (← mField ptrNode "functionName") "name")
  let sizeFn ← mStr (← mField (← mField sizeNode "functionName") "name")
  unless ptrFn == "add" && sizeFn == "mul" do return none
  let ptrArgs ← mArr (← mField ptrNode "arguments")
  let sizeArgs ← mArr (← mField sizeNode "arguments")
  unless ptrArgs.size == 2 && sizeArgs.size == 2 do return none
  let arrFromPtr? ←
    if ← yulZeroTwoZeroLiteral? ptrArgs[1]! then
      yulMemoryArrayPtr? ptrArgs[0]!
    else if ← yulZeroTwoZeroLiteral? ptrArgs[0]! then
      yulMemoryArrayPtr? ptrArgs[1]!
    else
      pure none
  let some (arrName, arrayPtr) := arrFromPtr? | return none
  let mloadArg? (node : Json) : M (Option String) := do
    if (← mKind node) != "YulFunctionCall" then return none
    let fn ← mStr (← mField (← mField node "functionName") "name")
    unless fn == "mload" do return none
    let margs ← mArr (← mField node "arguments")
    unless margs.size == 1 do return none
    let some (mname, _) ← yulMemoryArrayPtr? margs[0]! | return none
    return some mname
  let arrFromSize? ←
    if ← yulZeroTwoZeroLiteral? sizeArgs[1]! then
      mloadArg? sizeArgs[0]!
    else if ← yulZeroTwoZeroLiteral? sizeArgs[0]! then
      mloadArg? sizeArgs[1]!
    else
      pure none
  unless arrFromSize? == some arrName do return none
  return some (.add (.localVar arrayPtr) (.literal 32), .mul (.mload (.localVar arrayPtr)) (.literal 32))

private def yulMemoryArrayElementLoad? (addrNode : Json) (lowerYulFn : Json → M Val) : M (Option Val) := do
  if (← mKind addrNode) != "YulFunctionCall" then return none
  let outerFn ← mStr (← mField (← mField addrNode "functionName") "name")
  unless outerFn == "add" do return none
  let outerArgs ← mArr (← mField addrNode "arguments")
  unless outerArgs.size == 2 do return none
  let matchBaseAdd? (node : Json) : M (Option String) := do
    if (← mKind node) != "YulFunctionCall" then return none
    let fn ← mStr (← mField (← mField node "functionName") "name")
    unless fn == "add" do return none
    let nargs ← mArr (← mField node "arguments")
    unless nargs.size == 2 do return none
    if ← yulZeroTwoZeroLiteral? nargs[1]! then
      return (← yulMemoryArrayPtr? nargs[0]!).map Prod.snd
    else if ← yulZeroTwoZeroLiteral? nargs[0]! then
      return (← yulMemoryArrayPtr? nargs[1]!).map Prod.snd
    else
      return none
  let matchIndexMul? (node : Json) : M (Option Json) := do
    if (← mKind node) != "YulFunctionCall" then return none
    let fn ← mStr (← mField (← mField node "functionName") "name")
    unless fn == "mul" do return none
    let nargs ← mArr (← mField node "arguments")
    unless nargs.size == 2 do return none
    if ← yulZeroTwoZeroLiteral? nargs[1]! then
      return some nargs[0]!
    else if ← yulZeroTwoZeroLiteral? nargs[0]! then
      return some nargs[1]!
    else
      return none
  let matched? ← do
    if let some arrayPtr ← matchBaseAdd? outerArgs[0]! then
      if let some posNode ← matchIndexMul? outerArgs[1]! then
        pure (some (arrayPtr, posNode))
      else
        pure none
    else if let some arrayPtr ← matchBaseAdd? outerArgs[1]! then
      if let some posNode ← matchIndexMul? outerArgs[0]! then
        pure (some (arrayPtr, posNode))
      else
        pure none
    else
      pure none
  let some (arrayPtr, posNode) := matched? | return none
  let posVal ← lowerYulFn posNode
  return some {
    pre := posVal.pre,
    expr := .mload (.add (.add (.localVar arrayPtr) (.literal 32)) (.mul posVal.expr (.literal 32)))
  }

private partial def lowerYul (j : Json) : M Val := do
  match ← mKind j with
  | "YulLiteral" =>
      unless optStr j "kind" == some "number" do
        failAt j "only numeric Yul literals are supported"
      unless optStr j "type" == some "" do
        failAt j "typed Yul literals are unsupported"
      let raw ← mStr (← mField j "value")
      let value ← match Compiler.Hex.parseHexNat? raw <|> raw.toNat? with
        | some value => pure value
        | none => failAt j "invalid numeric Yul literal"
      unless value < 2^256 do failAt j "numeric Yul literal exceeds one EVM word"
      pure { pre := #[], expr := .literal value }
  | "YulIdentifier" =>
      let name ← mStr (← mField j "name")
      let env ← get
      if let some (binding, ty) := env.helperResult then
        if ty == "bool" || (bitsOf ty).getD 256 < 256 then
          if let some (.localVar foundBinding) := env.yulNames.find? name then
            if foundBinding == binding then
              failAt j "Yul reads of narrow named results are unsupported"
      match env.yulNames.find? name with
      | some expr => pure { pre := #[], expr }
      | none => failAt j s!"unbound Yul identifier {name}"
  | "YulFunctionCall" =>
      let fname ← mStr (← mField (← mField j "functionName") "name")
      let args ← mArr (← mField j "arguments")
      if fname == "mload" then
        if args.size == 1 then
          if let some v ← yulMemoryArrayElementLoad? args[0]! lowerYul then
            return v
        failAt j "unsupported Yul builtin mload"
      let expectedArity? : Option Nat := match fname with
        | "caller" | "address" | "timestamp" | "number" | "chainid"
        | "selfbalance" | "origin" => some 0
        | "iszero" | "not" | "tload" | "clz" => some 1
        | "add" | "sub" | "mul" | "div" | "sdiv" | "mod" | "smod" | "exp"
        | "and" | "or" | "xor" | "byte" | "shl" | "shr" | "sar" | "signextend"
        | "lt" | "gt" | "slt" | "sgt" | "eq" | "keccak256" => some 2
        | "addmod" | "mulmod" => some 3
        | _ => none
      let some expectedArity := expectedArity?
        | failAt j s!"unsupported Yul builtin {fname}"
      unless args.size == expectedArity do
        failAt j s!"unsupported Yul builtin {fname}"
      if fname == "keccak256" && args.size == 2 then
        if let some (sliceOff, sliceSize) ← yulMemoryArrayPayloadSlice? args[0]! args[1]! then
          return { pre := #[], expr := .keccak256 sliceOff sliceSize }
      let mut pre : Array Stmt := #[]
      let mut xs : Array Expr := #[]
      for arg in args do
        let v ← lowerYul arg
        pre := pre ++ v.pre
        xs := xs.push v.expr
      match fname, xs with
      | "add", #[a, b] => pure { pre, expr := .add a b }
      | "sub", #[a, b] => pure { pre, expr := .sub a b }
      | "mul", #[a, b] => pure { pre, expr := .mul a b }
      | "div", #[a, b] => pure { pre, expr := .div a b }
      | "sdiv", #[a, b] => pure { pre, expr := .sdiv a b }
      | "mod", #[a, b] => pure { pre, expr := .mod a b }
      | "smod", #[a, b] => pure { pre, expr := .smod a b }
      | "exp", #[a, b] => pure { pre, expr := .externalCall builtinExpName [a, b] }
      | "and", #[a, b] => pure { pre, expr := .bitAnd a b }
      | "or", #[a, b] => pure { pre, expr := .bitOr a b }
      | "xor", #[a, b] => pure { pre, expr := .bitXor a b }
      | "byte", #[a, b] => pure { pre, expr := .byte a b }
      | "shl", #[a, b] => pure { pre, expr := .shl a b }
      | "shr", #[a, b] => pure { pre, expr := .shr a b }
      | "sar", #[a, b] => pure { pre, expr := .sar a b }
      | "signextend", #[a, b] => pure { pre, expr := .signextend a b }
      | "lt", #[a, b] => pure { pre, expr := .lt a b }
      | "gt", #[a, b] => pure { pre, expr := .gt a b }
      | "slt", #[a, b] => pure { pre, expr := .slt a b }
      | "sgt", #[a, b] => pure { pre, expr := .sgt a b }
      | "eq", #[a, b] => pure { pre, expr := .eq a b }
      | "iszero", #[a] => pure { pre, expr := .logicalNot a }
      | "not", #[a] => pure { pre, expr := .bitNot a }
      | "tload", #[a] => pure { pre, expr := .tload a }
      | "caller", #[] => pure { pre, expr := .caller }
      | "address", #[] => pure { pre, expr := .contractAddress }
      | "timestamp", #[] => pure { pre, expr := .blockTimestamp }
      | "number", #[] => pure { pre, expr := .blockNumber }
      | "chainid", #[] => pure { pre, expr := .chainid }
      | "selfbalance", #[] => pure { pre, expr := .selfBalance }
      | "origin", #[] => pure { pre, expr := .txOrigin }
      | "keccak256", #[a, b] => do
          let (.literal off, .literal size) := (a, b)
            | failAt j "only scratch-space keccak256 over 0x00..0x3f is supported"
          let env ← get
          let validScratch :=
            (off == 0 && size == 32 && env.yulScratch0) ||
            (off == 32 && size == 32 && env.yulScratch32) ||
            (off == 0 && size == 64 && env.yulScratch0 && env.yulScratch32)
          unless validScratch do
            failAt j "keccak256 requires scratch-space words 0x00..0x3f to be written in the same Yul block"
          pure { pre, expr := .keccak256 (.literal off) (.literal size) }
      | "addmod", #[a, b, m] => do
          let v ← lowerYulAddmod a b m
          pure { pre := pre ++ v.pre, expr := v.expr }
      | "mulmod", #[a, b, m] => do
          let v ← lowerYulMulmod a b m
          pure { pre := pre ++ v.pre, expr := v.expr }
      | "clz", #[a] =>
          let inputBinding ← fresh
          let remBinding ← fresh
          let countBinding ← fresh
          let mut searchStmts : List Stmt := []
          for shift in [128, 64, 32, 16, 8, 4, 2, 1] do
            let shifted := Expr.shr (.literal shift) (.localVar remBinding)
            searchStmts := searchStmts ++ [.ite (.eq shifted (.literal 0))
              [.assignVar countBinding (.add (.localVar countBinding) (.literal shift))]
              [.assignVar remBinding shifted]]
          let stmts : Array Stmt := #[
            .letVar inputBinding a,
            .letVar remBinding (.localVar inputBinding),
            .letVar countBinding (.literal 0),
            .ite (.eq (.localVar inputBinding) (.literal 0))
              [.assignVar countBinding (.literal 256)]
              searchStmts
          ]
          pure { pre := pre ++ stmts, expr := .localVar countBinding }
      | _, _ => failAt j s!"unsupported Yul builtin {fname}"
  | kind => failAt j s!"unsupported Yul node {kind}"

private def checkYulReturnTarget (j asg varNode : Json) (vname retName : String) : M Unit := do
  let targetSrc ← mStr (← mField varNode "src")
  let refs ← mArr (← mField j "externalReferences")
  let mut targetId? : Option Nat := none
  for ref in refs do
    if (← mStr (← mField ref "src")) == targetSrc then
      unless !(← mBool (← mField ref "isOffset")) && !(← mBool (← mField ref "isSlot")) &&
           (field? ref "suffix").isNone && (← mNat (← mField ref "valueSize")) == 1 do
        failAt asg s!"Yul assigns {vname}, not the return declaration {retName}"
      targetId? := some (← mNat (← mField ref "declaration"))
  let some targetId := targetId?
    | failAt asg s!"Yul assigns {vname}, not the return declaration {retName}"
  unless (← get).helperReturnId == some targetId do
    failAt asg s!"Yul assigns {vname}, not the return declaration {retName}"

private def lowerAssembly (j : Json) (retName : String) : M Val := do
  let assignedInAsm := bodyAssignedIds j
  if !assignedInAsm.isEmpty then
    modify fun e => { e with zeroInitLocals := e.zeroInitLocals.filter (!assignedInAsm.contains ·) }
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
  checkYulReturnTarget j asg vars[0]! vname retName
  lowerYul (← mField asg "value")

private def isFullWordYulScalar : ParamType → Bool
  | .uint256 | .int256 | .bytes32 => true
  | _ => false

private def cleanHelperResultExpr (ty : String) (v : Val) : Expr :=
  if ty == "bool" then Expr.logicalNot (.logicalNot v.expr)
  else if ty == "bytes4" then Expr.bitAnd v.expr (.literal ((2 ^ 32 - 1) * 16 ^ 56))
  else
    match bitsOf ty with
    | some width => if width < 256 then Expr.bitAnd v.expr (.literal (2^width-1)) else v.expr
    | none => v.expr

private def yulNatLit? (node : Json) : M (Option Nat) := do
  if (← mKind node) != "YulLiteral" then return none
  unless optStr node "kind" == some "number" && optStr node "type" == some "" do return none
  let raw ← mStr (← mField node "value")
  let some value := Compiler.Hex.parseHexNat? raw <|> raw.toNat? | return none
  unless value < 2^256 do return none
  return some value

private def yulStringPrefixLit? (node : Json) : M (Option (Nat × Nat)) := do
  if (← mKind node) != "YulLiteral" then return none
  unless optStr node "kind" == some "string" && optStr node "type" == some "" do return none
  if let some hex := optStr node "hexValue" then
    unless hex.length % 2 == 0 do return none
    let byteLen := hex.length / 2
    unless 0 < byteLen && byteLen < 32 do return none
    let chars := hex.toList.toArray
    let mut word : Nat := 0
    for i in [:chars.size] do
      let some d := Compiler.Hex.hexCharToNat? chars[i]! | return none
      word := word * 16 + d
    return some (byteLen, word * 16 ^ (64 - hex.length))
  if let some strVal := optStr node "value" then
    let bytes := strVal.toUTF8.data
    let byteLen := bytes.size
    unless 0 < byteLen && byteLen < 32 do return none
    let mut word : Nat := 0
    for b in bytes do
      word := word * 256 + b.toNat
    return some (byteLen, word * 2 ^ ((32 - byteLen) * 8))
  return none

private def lowerYulDirectAssignmentTarget (j stmt varNode : Json) (refs : Array Json) (retName : String) (rhsVal : Val) : M Stmt := do
  let vname ← mStr (← mField varNode "name")
  if retName != "" && vname == retName && (← get).helperResult.isSome then
    checkYulReturnTarget j stmt varNode vname retName
    let some (binding, ty) := (← get).helperResult
      | failAt stmt s!"Yul assigns {vname}, not the return declaration {retName}"
    if ty.startsWith "enum " then
      failAt j "Yul assignment to an enum result is unsupported"
    let cleaned := cleanHelperResultExpr ty rhsVal
    return .assignVar binding cleaned
  else
    let targetSrc ← mStr (← mField varNode "src")
    let mut targetId? : Option Nat := none
    for ref in refs do
      if (← mStr (← mField ref "src")) == targetSrc then
        unless !(← mBool (← mField ref "isOffset")) && !(← mBool (← mField ref "isSlot")) &&
             (field? ref "suffix").isNone && (← mNat (← mField ref "valueSize")) == 1 do
          failAt stmt s!"Yul assignment to non-scalar reference {vname} is unsupported"
        targetId? := some (← mNat (← mField ref "declaration"))
    let some targetId := targetId?
      | if retName != "" then failAt stmt s!"Yul assigns {vname}, not the return name {retName}"
        else failAt stmt s!"unresolved Yul assignment target {vname}"
    let env ← get
    if env.enumBounds.contains targetId then
      failAt j "Yul assignment to an enum variable is unsupported"
    let some binding := env.writableLocals.find? targetId
      | if retName != "" then failAt stmt s!"Yul assigns {vname}, not the return name {retName}"
        else failAt stmt s!"Yul assignment target {vname} is not a writable scalar local"
    let unshadowed := match env.yulNames.find? vname with
      | some (.localVar b) => b == binding
      | _ => false
    unless unshadowed do
      if retName != "" then failAt stmt s!"Yul assigns {vname}, not the return declaration {retName}"
      else failAt stmt s!"Yul assignment target {vname} is shadowed"
    let some scalarType := env.scalarTy.find? targetId
      | failAt stmt s!"unknown scalar type for Yul assignment target {vname}"
    unless isFullWordYulScalar scalarType do
      failAt stmt s!"Yul assignment to narrow local {vname} is unsupported"
    return .assignVar binding rhsVal.expr

private def lowerYulPrefixKeccakBlock? (j : Json) (stmts refs : Array Json) (retName : String) : M (Option (Array Stmt)) := do
  let mstoreArgs? (stmt : Json) : M (Option (Json × Json)) := do
    if (← mKind stmt) != "YulExpressionStatement" then return none
    let expr ← mField stmt "expression"
    if (← mKind expr) != "YulFunctionCall" then return none
    let fn ← mStr (← mField (← mField expr "functionName") "name")
    unless fn == "mstore" do return none
    let args ← mArr (← mField expr "arguments")
    unless args.size == 2 do return none
    return some (args[0]!, args[1]!)
  let keccakAssign? (stmt : Json) : M (Option (Json × Json × Json)) := do
    if (← mKind stmt) != "YulAssignment" then return none
    let vars ← mArr (← mField stmt "variableNames")
    unless vars.size == 1 do return none
    let val ← mField stmt "value"
    if (← mKind val) != "YulFunctionCall" then return none
    let fn ← mStr (← mField (← mField val "functionName") "name")
    unless fn == "keccak256" do return none
    let args ← mArr (← mField val "arguments")
    unless args.size == 2 do return none
    return some (vars[0]!, args[0]!, args[1]!)
  if stmts.size == 3 then
    let some (off0Node, strNode) ← mstoreArgs? stmts[0]! | return none
    let some 0 ← yulNatLit? off0Node | return none
    let some (prefixLen, prefixWord) ← yulStringPrefixLit? strNode | return none
    let some (off1Node, msgNode) ← mstoreArgs? stmts[1]! | return none
    let some off1 ← yulNatLit? off1Node | return none
    unless off1 == prefixLen do return none
    let some (varNode, kOffNode, kSizeNode) ← keccakAssign? stmts[2]! | return none
    let some 0 ← yulNatLit? kOffNode | return none
    let some kSize ← yulNatLit? kSizeNode | return none
    unless kSize == prefixLen + 32 do return none
    let msgVal ← lowerYul msgNode
    let keccakExpr := Expr.keccak256 (.literal 0) (.literal (prefixLen + 32))
    let assignStmt ← lowerYulDirectAssignmentTarget j stmts[2]! varNode refs retName { pre := #[], expr := keccakExpr }
    let shrBits := prefixLen * 8
    let shlBits := (32 - prefixLen) * 8
    return some (msgVal.pre ++ #[
      .mstore (.literal 0) (.bitOr (.literal prefixWord) (.shr (.literal shrBits) msgVal.expr)),
      .mstore (.literal 32) (.shl (.literal shlBits) msgVal.expr),
      assignStmt
    ])
  if stmts.size == 5 then
    let declStmt := stmts[0]!
    if (← mKind declStmt) != "YulVariableDeclaration" then return none
    let vars ← mArr (← mField declStmt "variables")
    unless vars.size == 1 do return none
    let varDecl := vars[0]!
    unless optStr varDecl "type" == some "" do return none
    let ptrName ← mStr (← mField varDecl "name")
    unless ptrName.all (fun c => c.isAlphanum || c == '_') && ptrName != "" do return none
    let some initNode := (field? declStmt "value").filter (!·.isNull) | return none
    if (← mKind initNode) != "YulFunctionCall" then return none
    let initFn ← mStr (← mField (← mField initNode "functionName") "name")
    unless initFn == "mload" do return none
    let initArgs ← mArr (← mField initNode "arguments")
    unless initArgs.size == 1 do return none
    let some 64 ← yulNatLit? initArgs[0]! | return none
    let isPtrIdent (node : Json) : M Bool := do
      if (← mKind node) != "YulIdentifier" then return false
      return (← mStr (← mField node "name")) == ptrName
    let isPtrAddConst (node : Json) (expectedOff : Nat) : M Bool := do
      if (← mKind node) != "YulFunctionCall" then return false
      let fn ← mStr (← mField (← mField node "functionName") "name")
      unless fn == "add" do return false
      let nargs ← mArr (← mField node "arguments")
      unless nargs.size == 2 do return false
      if ← isPtrIdent nargs[0]! then
        return (← yulNatLit? nargs[1]!) == some expectedOff
      else if ← isPtrIdent nargs[1]! then
        return (← yulNatLit? nargs[0]!) == some expectedOff
      else
        return false
    let some (ptrNode1, strNode) ← mstoreArgs? stmts[1]! | return none
    unless ← isPtrIdent ptrNode1 do return none
    let some (prefixLen, prefixWord) ← yulStringPrefixLit? strNode | return none
    let some (ptrNode2, domNode) ← mstoreArgs? stmts[2]! | return none
    unless ← isPtrAddConst ptrNode2 prefixLen do return none
    let some (ptrNode3, structNode) ← mstoreArgs? stmts[3]! | return none
    unless ← isPtrAddConst ptrNode3 (prefixLen + 32) do return none
    let some (varNode, kPtrNode, kSizeNode) ← keccakAssign? stmts[4]! | return none
    unless ← isPtrIdent kPtrNode do return none
    let some kSize ← yulNatLit? kSizeNode | return none
    unless kSize == prefixLen + 64 do return none
    let vname ← mStr (← mField varNode "name")
    if vname == ptrName then return none
    let domVal ← lowerYul domNode
    let structVal ← lowerYul structNode
    let ptrBinding ← freshFor ptrName
    modify fun e => { e with encodingMemory := true }
    let keccakExpr := Expr.keccak256 (.localVar ptrBinding) (.literal (prefixLen + 64))
    let assignStmt ← lowerYulDirectAssignmentTarget j stmts[4]! varNode refs retName { pre := #[], expr := keccakExpr }
    let shrBits := prefixLen * 8
    let shlBits := (32 - prefixLen) * 8
    return some (domVal.pre ++ structVal.pre ++ #[
      .letVar ptrBinding (.mload (.literal 64)),
      .mstore (.localVar ptrBinding) (.bitOr (.literal prefixWord) (.shr (.literal shrBits) domVal.expr)),
      .mstore (.add (.localVar ptrBinding) (.literal 32)) (.bitOr (.shl (.literal shlBits) domVal.expr) (.shr (.literal shrBits) structVal.expr)),
      .mstore (.add (.localVar ptrBinding) (.literal 64)) (.shl (.literal shlBits) structVal.expr),
      assignStmt
    ])
  return none

private partial def lowerYulStmtSlice (j : Json) (stmts refs : Array Json) (retName : String) : M (Array Stmt) := do
  let mut yulLocals : RBMap String String compare := RBMap.empty
  let mut out : Array Stmt := #[]
  for stmt in stmts do
    match ← mKind stmt with
    | "YulVariableDeclaration" =>
        let vars ← mArr (← mField stmt "variables")
        unless vars.size == 1 do failAt stmt "Yul variable declaration must have one variable"
        let varNode := vars[0]!
        unless optStr varNode "type" == some "" do
          failAt varNode "typed Yul variables are unsupported"
        let vname ← mStr (← mField varNode "name")
        unless vname.all (fun c => c.isAlphanum || c == '_') && vname != "" do
          failAt varNode s!"unsupported Yul variable name {vname}"
        if yulLocals.contains vname then
          failAt varNode s!"duplicate Yul variable declaration {vname}"
        let v ← match (field? stmt "value").filter (!·.isNull) with
          | some valNode => lowerYul valNode
          | none => pure { pre := #[], expr := .literal 0 }
        let binding ← freshFor vname
        let expr := Expr.localVar binding
        modify fun e => { e with yulNames := e.yulNames.insert vname expr }
        yulLocals := yulLocals.insert vname binding
        out := out ++ v.pre |>.push (.letVar binding v.expr)
    | "YulAssignment" =>
        let vars ← mArr (← mField stmt "variableNames")
        unless vars.size == 1 do failAt stmt "Yul assignment must have one target"
        let varNode := vars[0]!
        let vname ← mStr (← mField varNode "name")
        if let some yulBinding := yulLocals.find? vname then
          let v ← lowerYul (← mField stmt "value")
          out := out ++ v.pre |>.push (.assignVar yulBinding v.expr)
        else
          let v ← lowerYul (← mField stmt "value")
          let assignStmt ← lowerYulDirectAssignmentTarget j stmt varNode refs retName v
          out := out ++ v.pre |>.push assignStmt
    | "YulExpressionStatement" =>
        let expr ← mField stmt "expression"
        unless (← mKind expr) == "YulFunctionCall" do
          failAt stmt "unsupported Yul expression statement"
        let fname ← mStr (← mField (← mField expr "functionName") "name")
        let args ← mArr (← mField expr "arguments")
        if fname == "tstore" then
          unless args.size == 2 do failAt expr "tstore requires two arguments"
          let slotVal ← lowerYul args[0]!
          let valVal ← lowerYul args[1]!
          out := out ++ slotVal.pre ++ valVal.pre |>.push (.tstore slotVal.expr valVal.expr)
        else if fname == "mstore" then
          unless args.size == 2 do failAt expr "mstore requires two arguments"
          let offVal ← lowerYul args[0]!
          let valVal ← lowerYul args[1]!
          let .literal off := offVal.expr
            | failAt expr "only scratch-space mstore at 0x00 or 0x20 is supported"
          unless offVal.pre.isEmpty && (off == 0 || off == 32) do
            failAt expr "only scratch-space mstore at 0x00 or 0x20 is supported"
          if off == 0 then
            modify fun e => { e with yulScratch0 := true }
          else
            modify fun e => { e with yulScratch32 := true }
          out := out ++ valVal.pre |>.push (.mstore (.literal off) valVal.expr)
        else
          failAt stmt s!"unsupported Yul expression statement {fname} (unsupported statement InlineAssembly)"
    | kind => failAt stmt s!"unsupported Yul statement {kind}"
  pure out

private partial def lowerAssemblyStmts (j : Json) (retName : String) : M (Array Stmt) := do
  let assignedInAsm := bodyAssignedIds j
  if !assignedInAsm.isEmpty then
    modify fun e => { e with zeroInitLocals := e.zeroInitLocals.filter (!assignedInAsm.contains ·) }
  let ast ← mField j "AST"
  unless (← mKind ast) == "YulBlock" do failAt j "assembly is not a Yul block"
  let stmts ← mArr (← mField ast "statements")
  let refs ← mArr (← mField j "externalReferences")
  let savedYulNames := (← get).yulNames
  let savedScratch0 := (← get).yulScratch0
  let savedScratch32 := (← get).yulScratch32
  modify fun e => { e with yulScratch0 := false, yulScratch32 := false }
  if let some prefixStmts ← lowerYulPrefixKeccakBlock? j stmts refs retName then
    modify fun e => { e with yulNames := savedYulNames, yulScratch0 := savedScratch0, yulScratch32 := savedScratch32 }
    return prefixStmts
  let out ← lowerYulStmtSlice j stmts refs retName
  modify fun e => { e with yulNames := savedYulNames, yulScratch0 := savedScratch0, yulScratch32 := savedScratch32 }
  pure out

private def isMsgDataNode (j : Json) : M Bool := do
  if (← mKind j) != "MemberAccess" then return false
  unless optStr j "memberName" == some "data" do return false
  let base ← mField j "expression"
  if (← mKind base) != "Identifier" || optStr base "name" != some "msg" then return false
  unless (← refInt base) == -15 do
    failAt base "msg does not resolve to the transaction builtin"
  return true

private def argumentAt (call : Json) (i : Nat) : M Json := do
  -- `i` counts the receiver plus explicit arguments. The receiver is not in
  -- `arguments` when the call is `using for`.
  let callee ← mField call "expression"
  let args ← mArr (← mField call "arguments")
  let hasReceiver ← match ← mKind callee with
    | "MemberAccess" =>
        let base ← mField callee "expression"
        let baseTy ← mType base
        pure !(baseTy.startsWith "type(library " || baseTy.startsWith "type(contract ")
    | _ => pure false
  if hasReceiver then
    if i == 0 then mField callee "expression" else pure args[i - 1]!
  else
    pure args[i]!

private def convert (paramTy argTy : String) (v : Val) (at_ : Json) : M Val := do
  let argTy := if argTy.endsWith " storage ref" then (argTy.dropEnd 12).toString else argTy
  if argTy == paramTy then return v
  if paramTy == "int256" || paramTy == "int" then
    if argTy == "int256" || argTy == "int" || argTy.startsWith "int_const" then
      return v
    if argTy.startsWith "uint" then
      if let some sb := bitsOf argTy then
        if sb < 256 then return v
    failAt at_ s!"unsupported implicit conversion from {argTy} to {paramTy}"
  if (paramTy == "address" || paramTy == "address payable" || paramTy.startsWith "contract ") &&
      (argTy == "address" || argTy == "address payable" || argTy.startsWith "contract ") then
    return v
  if paramTy.startsWith "uint" && argTy.startsWith "uint" then
    match bitsOf paramTy, bitsOf argTy with
    | some pb, some sb =>
        if sb ≤ pb then return v
        else failAt at_ s!"implicit narrowing from {argTy} to {paramTy}"
    | _, _ => failAt at_ s!"unsupported implicit conversion from {argTy} to {paramTy}"
  if paramTy == "bytes4" && argTy.startsWith "int_const" && !argTy.startsWith "int_const -" then
    let .literal n := v.expr
      | failAt at_ s!"unsupported implicit conversion from {argTy} to {paramTy}"
    let raw := optStr at_ "value" |>.getD ""
    let hexDigits := ((raw.drop 2).toString.splitOn "_").foldl (· ++ ·) ""
    unless v.pre.isEmpty && n < 2 ^ 32 &&
        (n == 0 || (raw.startsWith "0x" && hexDigits.length == 8)) do
      failAt at_ s!"unsupported implicit conversion from {argTy} to {paramTy}"
    return { pre := #[], expr := .literal (n * 16 ^ 56) }
  if argTy.startsWith "int_const" && !argTy.startsWith "int_const -" && !paramTy.startsWith "enum " && (bitsOf paramTy).isSome then
    return v
  failAt at_ s!"unsupported implicit conversion from {argTy} to {paramTy}"

private partial def stmtContainsPlaceholder (s : Json) : M Bool := do
  match ← mKind s with
  | "PlaceholderStatement" => pure true
  | "Block" | "UncheckedBlock" =>
      let stmts ← mArr (← mField s "statements")
      stmts.anyM stmtContainsPlaceholder
  | "IfStatement" =>
      let yes ← stmtContainsPlaceholder (← mField s "trueBody")
      let no ← match field? s "falseBody" with
        | some j => if j.isNull then pure false else stmtContainsPlaceholder j
        | none => pure false
      pure (yes || no)
  | "ForStatement" =>
      stmtContainsPlaceholder (← mField s "body")
  | _ => pure false

/-- Syntactic definite revert: every path through `s` unconditionally reverts,
    including calls to builtin `revert(...)` and resolved internal/private helpers
    whose bodies unconditionally revert. -/
private partial def stmtAlwaysReverts (visited : List Nat) (s : Json) : M Bool := do
  match ← mKind s with
  | "RevertStatement" => pure true
  | "Block" | "UncheckedBlock" =>
      let stmts ← mArr (← mField s "statements")
      stmts.anyM (stmtAlwaysReverts visited)
  | "IfStatement" =>
      let yes ← stmtAlwaysReverts visited (← mField s "trueBody")
      let no ← match field? s "falseBody" with
        | some j => if j.isNull then pure false else stmtAlwaysReverts visited j
        | none => pure false
      pure (yes && no)
  | "ExpressionStatement" =>
      let expr := field? s "expression" |>.getD Json.null
      unless optStr expr "nodeType" == some "FunctionCall" && optStr expr "kind" == some "functionCall" do
        return false
      let callee := field? expr "expression" |>.getD Json.null
      let calleeKind := optStr callee "nodeType"
      if calleeKind == some "Identifier" && optStr callee "name" == some "revert" then
        return (field? callee "referencedDeclaration").bind (fun v => v.getInt?.toOption) == some (-19)
      let some refId := (field? callee "referencedDeclaration").bind (fun v => v.getInt?.toOption)
        | return false
      unless refId ≥ 0 do return false
      let env ← get
      let targetId? : Option Nat ← do
        if calleeKind == some "Identifier" then
          match env.funContractId.find? refId.toNat with
          | some cid =>
              if env.linearizedBases.contains cid then
                pure (resolveInContracts env env.linearizedBases.toList refId.toNat)
              else
                pure (some refId.toNat)
          | none => pure (some refId.toNat)
        else if calleeKind == some "MemberAccess" then
          let base := field? callee "expression" |>.getD Json.null
          let baseTy ← mType base
          if baseTy.startsWith "type(library " then
            pure (some refId.toNat)
          else if baseTy.startsWith "type(contract super " then
            match env.stack.head?.bind env.funContractId.find? with
            | some callerCid =>
                match env.linearizedBases.findIdx? (· == callerCid) with
                | some idx =>
                    let superBases := (env.linearizedBases.extract (idx + 1) env.linearizedBases.size).toList
                    pure (resolveInContracts env superBases refId.toNat)
                | none => pure none
            | none => pure none
          else if baseTy.startsWith "type(contract " then
            pure (some refId.toNat)
          else
            match env.funContractId.find? refId.toNat with
            | some cid =>
                if env.contractKinds.find? cid == some "library" then pure (some refId.toNat)
                else pure none
            | none => pure none
        else
          pure none
      let some targetId := targetId? | return false
      if visited.contains targetId then return false
      let some fn := env.funs.find? targetId | return false
      let vis := optStr fn "visibility" |>.getD ""
      unless vis == "internal" || vis == "private" || vis == "public" do return false
      let some body := (field? fn "body").filter (!·.isNull) | return false
      stmtAlwaysReverts (targetId :: visited) body
  | _ => pure false

/-- Syntactic definite return: every path through `s` ends in a helper result.
    Assembly results count because `lowerHelperFrom` treats them as results. -/
private partial def helperReturns (s : Json) : M Bool := do
  match ← mKind s with
  | "Return" | "RevertStatement" => pure true
  | "InlineAssembly" => pure (← get).helperResult.isNone
  | "Block" | "UncheckedBlock" => ((← mArr (← mField s "statements")).back?.map helperReturns).getD (pure false)
  | "IfStatement" =>
      let yes ← helperReturns (← mField s "trueBody")
      let no ← match field? s "falseBody" with
        | some j => if j.isNull then pure false else helperReturns j
        | none => pure false
      pure (yes && no)
  | _ => stmtAlwaysReverts [] s

private def helperListReturns (stmts : Array Json) : M Bool := do
  match stmts.back? with
  | some s => helperReturns s
  | none => pure false

private inductive AbiDecodeTypeItem where
  | scalar (ty : String) (pty : ParamType) (enumBound? : Option Nat)
  | flatStruct (sid : Nat) (sName : String) (members : Array (String × String))
  | scalarArray (elemStr : String) (elemPty : ParamType) (abiKind : SolidityAbi.ScalarKind)
  | dynamicBytes (isString : Bool)

private instance : Inhabited AbiDecodeTypeItem := ⟨.dynamicBytes false⟩

private inductive AbiDecodedValue where
  | scalar (ty : String) (pty : ParamType) (expr : Expr)
  | flatStruct (sid : Nat) (sName : String) (members : Array (String × String × Expr))
  | scalarArray (elemStr : String) (elemPty : ParamType) (abiKind : SolidityAbi.ScalarKind) (desc : ScalarArrayParam)
  | dynamicBytes (isString : Bool) (buf : EncodedBytes)

private instance : Inhabited AbiDecodedValue := ⟨.scalar "" .uint256 (.literal 0)⟩

private def readAbiDecodeWord (fromCalldata : Bool) (addr : Expr) : Expr :=
  if fromCalldata then
    .calldataload addr
  else
    let rem := Expr.bitAnd addr (.literal 31)
    let aligned := Expr.bitAnd addr (.bitNot (.literal 31))
    let shiftBits := Expr.mul rem (.literal 8)
    .bitOr
      (.shl shiftBits (.mload aligned))
      (.shr (.sub (.literal 256) shiftBits) (.mload (.add aligned (.literal 32))))

private def abiDecodeScalarGuard? (ty : String) (enumBound? : Option Nat) (word : Expr) : Option Stmt :=
  if ty == "uint256" || ty == "uint" || ty == "int256" || ty == "int" || ty == "bytes32" then
    none
  else if ty == "bool" then
    some (AbiLowering.guard (.lt word (.literal 2)))
  else if ty == "address" || ty == "address payable" || ty.startsWith "contract " then
    some (AbiLowering.guard (.lt word (.literal (2 ^ 160))))
  else if ty == "bytes4" then
    some (AbiLowering.guard (.eq (.bitAnd word (.literal (2 ^ 224 - 1))) (.literal 0)))
  else if ty.startsWith "enum " then
    enumBound?.map fun bound => AbiLowering.guard (.lt word (.literal bound))
  else if ty.startsWith "uint" then
    match bitsOf ty with
    | some bits =>
        if bits < 256 then some (AbiLowering.guard (.lt word (.literal (2 ^ bits)))) else none
    | none => none
  else
    none

set_option maxHeartbeats 800000 in
mutual

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
  | "UnaryOperation" =>
      let op := optStr j "operator"
      if op == some "++" || op == some "--" then
        lowerIncDecExpr j
      else do
        unless (field? j "prefix").bind (fun v => v.getBool?.toOption) == some true do
          failAt j "unsupported unary operation"
        let sub ← mField j "subExpression"
        if op == some "!" then
          unless (← mType sub) == "bool" && (← mType j) == "bool" do
            failAt j "logical negation requires a bool operand"
          let v ← lowerExpr sub
          pure { pre := v.pre, expr := .logicalNot v.expr }
        else if op == some "-" then
          let jTy ← mType j
          let subTy ← mType sub
          let v ← lowerExpr sub
          if jTy.startsWith "int_const" then
            unless v.pre.isEmpty do failAt j "negative constant requires a pure literal operand"
            let .literal n := v.expr | failAt j "negative constant requires a pure literal operand"
            if n == 0 then
              pure { pre := #[], expr := .literal 0 }
            else if n ≤ 2 ^ 255 then
              pure { pre := #[], expr := .literal (2 ^ 256 - n) }
            else
              failAt j "negative constant out of int256 range"
          else if (jTy == "int256" || jTy == "int") && (subTy == "int256" || subTy == "int") then
            let a ← atom v
            if (← get).unchecked then
              pure { pre := a.pre, expr := .sub (.literal 0) a.expr }
            else
              let dest ← fresh
              let ok := Stmt.assignVar dest (.sub (.literal 0) a.expr)
              let ite := iteStmt (.eq a.expr (.literal (2 ^ 255))) overflowPanic ok
              pure { pre := a.pre.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }
          else
            failAt j s!"unary negation requires an int256 operand, found {subTy}"
        else if op == some "~" then
          let jTy ← mType j
          let subTy ← mType sub
          unless jTy == subTy do
            failAt j s!"bitwise negation operand type {subTy} does not match {jTy}"
          let v ← lowerExpr sub
          let a ← atom v
          if jTy == "int256" || jTy == "int" || jTy == "bytes32" then
            pure { pre := a.pre, expr := .bitNot a.expr }
          else if jTy == "bytes4" then
            pure { pre := a.pre, expr := .bitAnd (.bitNot a.expr) (.literal ((2 ^ 32 - 1) * 16 ^ 56)) }
          else if jTy.startsWith "uint" then
            let some bits := bitsOf jTy | failAt j s!"unsupported bitwise negation type {jTy}"
            let inverted := if bits < 256 then Expr.bitAnd (.bitNot a.expr) (.literal (2 ^ bits - 1)) else .bitNot a.expr
            pure { pre := a.pre, expr := inverted }
          else
            failAt j s!"unsupported bitwise negation type {jTy}"
        else
          failAt j "unsupported unary operation"
  | "BinaryOperation" => lowerBinary j
  | "Conditional" => lowerConditional j
  | "FunctionCall" => lowerCall j
  | "Assignment" => lowerAssignmentExpr j
  | "Identifier" | "MemberAccess" | "IndexAccess" =>
      match ← lowerRef j with
      | .expr v => pure v
      | .state name pre =>
          let info ← resolveField name j
          unless info.keyCount == 0 do failAt j "mapping used as a scalar value"
          if info.bytesStorage then failAt j "bytes or string storage variable used as a scalar value"
          if info.dynamicArrayElemType.isSome then failAt j "dynamic storage array used as a scalar value"
          markField name
          if info.booleanScalar then
            pure { pre, expr := .logicalNot (.logicalNot (.storage name)) }
          else
            pure { pre, expr := .storage name }
      | .path pre path => scalarMappingRead pre path j
      | .fixedElement pre path index =>
          let (name, count, read) ← match path with
            | .zero name => pure (name, 0, fun member => Expr.storage (topStructMemberFieldName (splitSPathField name).1 member))
            | .one name key => pure (name, 1, fun member => Expr.structMember name key member)
            | .two name key1 key2 => pure (name, 2, fun member => Expr.structMember2 name key1 key2 member)
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
            | .rawSlot _ _ | .bytesSlot _ _ => failAt j "fixed array element on raw storage slot struct is outside this slice"
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
      | .structFixedElement pre path arrInfo index =>
          let (rawName, count, read) ← match path with
            | .zero name => pure (name, 0, fun member => Expr.storage (topStructMemberFieldName (splitSPathField name).1 member))
            | .one name key => pure (name, 1, fun member => Expr.structMember (splitSPathField name).1 key member)
            | .two name key1 key2 => pure (name, 2, fun member => Expr.structMember2 (splitSPathField name).1 key1 key2 member)
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
            | .rawSlot _ _ | .bytesSlot _ _ => failAt j "fixed array element on raw storage slot struct is outside this slice"
          let (name, _) := splitSPathField rawName
          let info ← resolveField name j
          unless info.keyCount == count do failAt j "fixed array mapping key count differs"
          let dest ← fresh
          let mut pre := pre.push (.ite (.lt index (.literal arrInfo.length))
            [] [.panicCode (.literal 0x32)]) |>.push (.letVar dest (.literal 0))
          for i in [:arrInfo.length] do
            pre := pre.push (.ite (.eq index (.literal i))
              [.assignVar dest (read s!"__solidity_struct_array_{arrInfo.member}_{i}")] [])
          markField name
          markStructFixedArray name arrInfo.member
          pure { pre, expr := .localVar dest }
      | .structFixedArray _ _ arrInfo =>
          failAt j s!"struct fixed array member {arrInfo.member} requires an element index"
      | .structMappingElement pre path mapInfo key =>
          readStructMappingElement pre path mapInfo key j
      | .structMapping _ _ mapInfo =>
          failAt j s!"struct mapping member {mapInfo.member} requires a mapping key"
      | .structDynamicElement pre path dynInfo index =>
          if let .rawSlot _ baseSlot := path then
            let slotExpr := rawStructMemberSlot baseSlot dynInfo.wordOffset
            readStorageDynamicArrayElement pre "" slotExpr dynInfo.elemType index
          else
            let rawName ← match path with
              | .zero name | .one name _ | .two name _ _ => pure name
              | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
                  failAt j "struct dynamic array element requires all outer mapping keys"
            let (name, _) := splitSPathField rawName
            let info ← resolveField name j
            markField name
            markStructDynamicArray name dynInfo.member
            let (slotStmts, slotExpr) ← computeSPathBaseSlot path info dynInfo.wordOffset j
            readStorageDynamicArrayElement (pre ++ slotStmts) "" slotExpr dynInfo.elemType index
      | .storageDynamicElement pre fieldName slotExpr elemTy index =>
          readStorageDynamicArrayElement pre fieldName slotExpr elemTy index
      | .structDynamicArray _ _ dynInfo =>
          failAt j s!"struct dynamic array member {dynInfo.member} requires an element index"
      | _ => failAt j "storage or memory path used as a value"
  | kind => failAt j s!"unsupported expression {kind}"

private partial def isThisAddressConv (j : Json) : M Bool := do
  unless (← mKind j) == "FunctionCall" && optStr j "kind" == some "typeConversion" do
    return false
  let ty ← mType j
  unless ty == "address" || ty == "address payable" do
    return false
  let args ← mArr (← mField j "arguments")
  unless args.size == 1 do
    return false
  let arg := args[0]!
  if (← mKind arg) == "Identifier" && optStr arg "name" == some "this" then
    unless (← refInt arg) == -28 do
      failAt arg "this does not resolve to the current contract builtin"
    return true
  isThisAddressConv arg

private partial def isByteBufferIdent (j : Json) : M (Option EncodedBytes) := do
  unless (← mKind j) == "Identifier" do return none
  let id ← refInt j
  unless id ≥ 0 do return none
  return (← get).byteBuffers.find? id.toNat

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
      else if let some elem := env.abiElements.find? n then
        pure (.abiElement elem.rootId elem.memberIndex elem.pointer elem.inMemory #[])
      else if env.flatStructs.contains n then
        pure (.flatStruct n)
      else if env.byteBuffers.contains n then
        failAt j "encoded byte locals are limited to hash and packed encoding operands"
      else if env.stringBuffers.contains n then
        failAt j "string locals and memory parameters are limited to hash, packed encoding, and bytes(s).length operands"
      else if env.calldataBytes.contains n then
        pure (.calldataBytes n #[])
      else if env.scalarArrays.contains n then
        pure (.scalarArray n #[])
      else if let some name := env.storageBytesVars.find? n then
        pure (.state name #[])
      else if let some (fieldName, slotExpr, elemTy, elemSid?) := env.storageDynamicArrayVars.find? n then
        if let some elemSid := elemSid? then
          if fieldName != "" then
            pure (.state fieldName #[])
          else
            pure (.structDynamicArray #[] (.rawSlot 0 slotExpr) {
              member := ""
              solcType := elemTy ++ "[]"
              wordOffset := 0
              elemType := elemTy
              modelElemType := .uint256
              abiKind := .bytes32
              elemStructId := some elemSid
            })
        else
          let some (_, modelElemTy, abiKind) := dynamicStorageArrayElement? elemTy
            | failAt j s!"unsupported storage dynamic array element type {elemTy}"
          if fieldName != "" then
            pure (.state fieldName #[])
          else
            pure (.structDynamicArray #[] (.rawSlot 0 slotExpr) {
              member := ""
              solcType := elemTy ++ "[]"
              wordOffset := 0
              elemType := elemTy
              modelElemType := modelElemTy
              abiKind
            })
      else if let some decl := env.numericConstants.find? n then
        if env.constantStack.contains n then failAt j "cyclic constant initializer"
        let declared ← mType decl
        unless (declared.startsWith "uint" && (bitsOf declared).isSome) ||
            declared == "bool" || declared == "bytes32" || declared == "bytes4" ||
            declared == "int256" || declared == "int" ||
            declared == "address" || declared == "address payable" do
          failAt j s!"unsupported numeric constant type {declared}"
        let initializer ← mField decl "value"
        modify fun e => { e with constantStack := n :: e.constantStack }
        let rawValue ← lowerExpr initializer
        let value ← convert declared (← mType initializer) rawValue initializer
        modify fun e => { e with constantStack := env.constantStack }
        pure (.expr value)
      else if let some decl := env.stateVars.find? n then
        let name ← mStr (← mField decl "name")
        if optStr decl "mutability" == some "immutable" then
          failAt j s!"immutable state variable {name} is outside this slice"
        if env.duplicateLayoutLabels.contains name then
          failAt j s!"shadowed storage declaration {name} is outside this slice"
        if let some item := env.layoutItems.find? name then
          unless (← mNat (← mField item "astId")) == n do
            failAt j s!"shadowed storage declaration {name} is outside this slice"
        if (← mType j).startsWith "struct " && !(← mType j).contains "[" then
          let info ← resolveField name j
          unless info.keyCount == 0 && !info.scalarMapping && info.fixedArrayLength.isNone do
            failAt j s!"unsupported storage struct state variable {name}"
          pure (.path #[] (.zero name))
        else if !(← mType j).startsWith "mapping(" && (← mType j).contains "[" && !(← mType j).contains "[]" then
          let info ← resolveField name j
          unless info.keyCount == 0 && info.fixedArrayLength.isSome do
            failAt j s!"unsupported fixed storage array state variable {name}"
          pure (.path #[] (.zero name))
        else
          pure (.state name #[])
      else if env.funs.contains n || env.fnPtrs.contains n then
        failAt j "function pointers are outside this slice"
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
      let indexExpression ← mField j "indexExpression"
      let key ← atom (← lowerExpr indexExpression)
      match base with
      | .state name pre =>
          let info ← resolveField name j
          if info.bytesStorage then failAt j "index access on bytes or string storage variable is outside this slice"
          if let some elemSid := info.dynamicArrayStructId then
            let ty ← mType indexExpression
            unless ty.startsWith "uint" || ty.startsWith "int_const" do
              failAt j "dynamic storage array index must be unsigned"
            let (elemPre, elemPath) ← storageDynamicStructElementPath (pre ++ key.pre) name (.literal info.slot) elemSid key.expr j
            return .path elemPre elemPath
          if let some (elemTy, _, _) := info.dynamicArrayElemType then
            let ty ← mType indexExpression
            unless ty.startsWith "uint" || ty.startsWith "int_const" do
              failAt j "dynamic storage array index must be unsigned"
            let captured ← fresh
            return .storageDynamicElement ((pre ++ key.pre).push (.letVar captured key.expr))
              name (.literal info.slot) elemTy (.localVar captured)
          markField name
          if info.keyCount == 2 then
            pure (.path (pre ++ key.pre) (.outer name key.expr))
          else
            pure (.path (pre ++ key.pre) (.one name key.expr))
      | .path pre (.outer field k1) =>
          let info ← resolveField field j
          if let some mapInfo := info.thirdKeyMapping then
            pure (.structMapping (pre ++ key.pre) (.two field k1 key.expr) mapInfo)
          else
            pure (.path (pre ++ key.pre) (.two field k1 key.expr))
      | .path pre path =>
          let rawName ← match path with
            | .zero name | .one name _ | .two name _ _ => pure name
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
            | .rawSlot _ _ | .bytesSlot _ _ => failAt j "index of a raw storage slot struct is outside this slice"
          let (name, _) := splitSPathField rawName
          let info ← resolveField name j
          unless info.fixedArrayLength.isSome do
            failAt j "index of a storage value requires a fixed array layout"
          let ty ← mType indexExpression
          unless ty.startsWith "uint" || ty.startsWith "int_const" do
            failAt j "fixed storage array index must be unsigned"
          let captured ← fresh
          pure (.fixedElement ((pre ++ key.pre).push (.letVar captured key.expr))
            path (.localVar captured))
      | .structFixedArray pre path arrInfo =>
          let rawName ← match path with
            | .zero name | .one name _ | .two name _ _ => pure name
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
            | .rawSlot _ _ | .bytesSlot _ _ => failAt j "fixed array element on raw storage slot struct is outside this slice"
          let (name, _) := splitSPathField rawName
          let _ ← resolveField name j
          let ty ← mType indexExpression
          unless ty.startsWith "uint" || ty.startsWith "int_const" do
            failAt j "fixed storage array index must be unsigned"
          let captured ← fresh
          pure (.structFixedElement ((pre ++ key.pre).push (.letVar captured key.expr))
            path arrInfo (.localVar captured))
      | .structMapping pre path mapInfo =>
          match path with
          | .rawSlot _ _ => pure ()
          | .bytesSlot _ _ => failAt j "struct mapping element on StorageSlot.BytesSlot is outside this slice"
          | .zero rawName | .one rawName _ | .two rawName _ _ =>
              let (name, _) := splitSPathField rawName
              let _ ← resolveField name j
          | .outer _ _ => failAt j "struct mapping element requires both outer mapping keys"
          if let some valSid := mapInfo.valueStructId then
            let (slotStmts, slotExpr) ←
              if let .rawSlot _ baseSlot := path then do
                modify fun e => { e with encodingMemory := true, usedRawStorage := true }
                let mapBaseExpr := rawStructMemberSlot baseSlot mapInfo.wordOffset
                let leafSlot ← fresh
                pure (#[
                  Stmt.mstore (.literal 0) key.expr,
                  Stmt.mstore (.literal 32) mapBaseExpr,
                  Stmt.letVar leafSlot (.keccak256 (.literal 0) (.literal 64))
                ], Expr.localVar leafSlot)
              else do
                let rawName ← match path with
                  | .zero name | .one name _ | .two name _ _ => pure name
                  | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
                      failAt j "struct mapping element requires both outer mapping keys"
                let (name, _) := splitSPathField rawName
                let info ← resolveField name j
                markField name
                markStructMapping name mapInfo.member
                computeStructMappingLeafSlot path info mapInfo key.expr j
            return .path (pre ++ key.pre ++ slotStmts) (.rawSlot valSid slotExpr)
          let captured ← fresh
          pure (.structMappingElement ((pre ++ key.pre).push (.letVar captured key.expr))
            path mapInfo (.localVar captured))
      | .structDynamicArray pre path dynInfo =>
          match path with
          | .rawSlot _ _ => pure ()
          | .bytesSlot _ _ => failAt j "struct dynamic array element on StorageSlot.BytesSlot is outside this slice"
          | .zero rawName | .one rawName _ | .two rawName _ _ =>
              let (name, _) := splitSPathField rawName
              let _ ← resolveField name j
          | .outer _ _ => failAt j "struct dynamic array element requires all outer mapping keys"
          let ty ← mType indexExpression
          unless ty.startsWith "uint" || ty.startsWith "int_const" do
            failAt j "dynamic storage array index must be unsigned"
          if let some elemSid := dynInfo.elemStructId then
            let (slotPre, arrSlot) ← if let .rawSlot _ baseSlot := path then
              pure (#[], rawStructMemberSlot baseSlot dynInfo.wordOffset)
            else do
              let rawName ← match path with
                | .zero name | .one name _ | .two name _ _ => pure name
                | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
                    failAt j "struct dynamic array element requires all outer mapping keys"
              let (name, _) := splitSPathField rawName
              let info ← resolveField name j
              markField name
              markStructDynamicArray name dynInfo.member
              computeSPathBaseSlot path info dynInfo.wordOffset j
            let (elemPre, elemPath) ← storageDynamicStructElementPath (pre ++ key.pre ++ slotPre) "" arrSlot elemSid key.expr j
            return .path elemPre elemPath
          let captured ← fresh
          pure (.structDynamicElement ((pre ++ key.pre).push (.letVar captured key.expr))
            path dynInfo (.localVar captured))
      | .snapshot elements =>
          let ty ← mType indexExpression
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
          if !key.pre.isEmpty && (statefulCallIn indexExpression (← get) || assignmentIn indexExpression) then
            failAt j "stateful or assignment struct-array index is unsupported"
          let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
          let some schema := mem.schema | failAt j "missing ABI schema"
          if let some (.scalarArray field) := schema[memberIndex]? then
            if mem.calldataLocation then
              let header ← fresh
              let length ← fresh
              let data ← fresh
              let checks := AbiLowering.staticArrayHead (.localVar (mem.abiStem ++ "_calldata"))
                memberIndex 1 header length data
              let pre := pre ++ checks.toArray ++ key.pre ++ #[.ite (.lt key.expr (.localVar length))
                [] [.panicCode (.literal 0x32)]]
              let value := Expr.calldataload (.add (.localVar data) (.mul key.expr (.literal 32)))
              let bound := SolidityAbi.scalarBound field.kind
              let pre := if bound < 2^256 then
                pre.push (AbiLowering.guard (.lt value (.literal bound))) else pre
              return .expr { pre, expr := value }
            else
              let array := Expr.mload (.add (.localVar (mem.abiStem ++ "_memory"))
                (.literal (32*memberIndex)))
              let pre := (pre ++ key.pre).push (.ite (.lt key.expr (.mload array)) [] [.panicCode (.literal 0x32)])
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
            let pre := pre ++ checks.toArray ++ key.pre ++ #[.ite (.lt key.expr (.localVar length))
              [] [.panicCode (.literal 0x32)]]
            pure (.abiElement id memberIndex
              (.add (.localVar data) (.mul key.expr (.literal (32*fields.length)))) false pre)
          else
            let array := Expr.mload (.add (.localVar (mem.abiStem ++ "_memory"))
              (.literal (32*memberIndex)))
            let pre := (pre ++ key.pre).push (.ite (.lt key.expr (.mload array)) [] [.panicCode (.literal 0x32)])
            pure (.abiElement id memberIndex
              (.mload (.add (.add array (.literal 32)) (.mul key.expr (.literal 32)))) true pre)
      | .scalarArray id pre =>
          if !key.pre.isEmpty && (statefulCallIn indexExpression (← get) || !pre.isEmpty) then
            failAt j "stateful or assignment array index is unsupported"
          let ty ← mType indexExpression
          unless ty.startsWith "uint" || ty.startsWith "int_const" do
            failAt j "scalar array index must be unsigned"
          let some arr := (← get).scalarArrays.find? id | failAt j "unknown scalar array parameter"
          if !arr.inMemory then
            let pre := pre ++ key.pre ++ #[.ite (.lt key.expr (.localVar arr.lengthBinding))
              [] [.panicCode (.literal 0x32)]]
            let value := Expr.calldataload (.add (.localVar arr.dataBinding) (.mul key.expr (.literal 32)))
            let bound := SolidityAbi.scalarBound arr.abiKind
            let pre := if bound < 2^256 then
              pre.push (AbiLowering.guard (.lt value (.literal bound))) else pre
            return .expr { pre, expr := value }
          else
            let pre := (pre ++ key.pre).push (.ite (.lt key.expr (.localVar arr.lengthBinding)) [] [.panicCode (.literal 0x32)])
            let value := Expr.mload (.add (.add (.localVar arr.memoryPointer) (.literal 32)) (.mul key.expr (.literal 32)))
            return .expr { pre, expr := value }
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
      else if (← mKind base) == "Identifier" && optStr base "name" == some "tx" &&
          optStr ((field? base "typeDescriptions").getD Json.null) "typeIdentifier" == some "t_magic_transaction" then
        unless (← refInt base) == -26 do failAt base "tx does not resolve to the Solidity builtin"
        unless member == "origin" do failAt j s!"unsupported transaction context member {member}"
        pure (.expr { pre := #[], expr := .txOrigin })
      else if ((← mKind base) == "Identifier" || (← mKind base) == "MemberAccess") &&
          (← mType base).startsWith "type(enum " then
        let baseId ← refInt base
        unless baseId ≥ 0 do failAt base "unresolved enum type"
        let some members := (← get).enums.find? baseId.toNat
          | failAt base s!"unresolved enum {baseId}"
        let some idx := members.findIdx? (· == member)
          | failAt j s!"unknown enum member {member}"
        pure (.expr { pre := #[], expr := .literal idx })
      else if member == "length" && (← isByteBufferIdent base).isSome then
        let some buf ← isByteBufferIdent base
          | failAt base "internal error: missing byte buffer"
        pure (.expr { pre := buf.pre, expr := buf.size })
      else if member == "length" && (← isMsgDataNode base) then
        pure (.expr { pre := #[], expr := .calldatasize })
      else if member == "length" && (← mKind base) == "FunctionCall" &&
          optStr base "kind" == some "functionCall" &&
          ((← mType base) == "bytes calldata" || (← mType base) == "bytes memory" || (← mType base) == "bytes") then
        let baseArgs ← mArr (← mField base "arguments")
        if baseArgs.isEmpty then
          let pre ← lowerMsgDataExpr base
          pure (.expr { pre, expr := .calldatasize })
        else
          let buf ← lowerEncodedBytes base
          pure (.expr { pre := buf.pre, expr := buf.size })
      else if member == "length" && (← mKind base) == "FunctionCall" &&
          optStr base "kind" == some "typeConversion" &&
          ((← mType base) == "bytes" || (← mType base) == "bytes memory" || (← mType base) == "bytes calldata" ||
           (← mType base) == "bytes storage pointer") then
        let args ← mArr (← mField base "arguments")
        unless args.size == 1 do failAt base "bytes() conversion expects one argument"
        let arg := args[0]!
        if (← mKind arg) == "Identifier" then
          let id ← refInt arg
          if id ≥ 0 then
            if let some cb := (← get).calldataBytes.find? id.toNat then
              return .expr { pre := #[], expr := .localVar cb.lengthBinding }
        if let some val ← lowerStorageBytesLength? arg then
          return .expr val
        if (← mType base) == "bytes storage pointer" then
          failAt base "bytes() storage conversion requires a resolved storage identifier"
        let buf ← lowerEncodedBytes arg
        pure (.expr { pre := buf.pre, expr := buf.size })
      else if member == "max" || member == "min" then
        lowerTypeBound j base member
      else if member == "interfaceId" then
        lowerInterfaceId j base
      else if member == "selector" then
        lowerSelectorMemberAccess j base
      else if member == "balance" &&
          ((← mType base) == "address" || (← mType base) == "address payable") then
        if ← isThisAddressConv base then
          pure (.expr { pre := #[], expr := .selfBalance })
        else
          failAt j "external account balance reads are outside this slice"
      else if member == "code" &&
          ((← mType base) == "address" || (← mType base) == "address payable" ||
           (← mType base).startsWith "contract ") then
        failAt j "external contract code reads are outside this slice"
      else if ((← mKind base) == "FunctionCall" || (← mKind base) == "Conditional" || (← mKind base) == "TupleExpression") &&
          (← mType base).startsWith "struct " && !(← mType base).contains "[" &&
          (← mType base).endsWith " memory" then
        let (_, sName, initPre, memberVals) ← lowerFlatStructValue base none false
        let some (_, _, mExpr) := memberVals.find? (fun (mName, _, _) => mName == member)
          | failAt j s!"{member} is not a member of {sName}"
        pure (.expr { pre := initPre, expr := mExpr })
      else
        match ← lowerRef base with
        | .path pre path =>
            if let .rawSlot structId baseSlot := path then
              let rawInfo ← resolveRawStructInfo structId j
              if let some subInfo := rawInfo.subStructs.find? (·.member == member) then
                pure (.path pre (.rawSlot subInfo.structId (rawStructMemberSlot baseSlot subInfo.wordOffset)))
              else if let some mapInfo := rawInfo.mappings.find? (·.member == member) then
                pure (.structMapping pre path mapInfo)
              else if let some dynInfo := rawInfo.dynamicArrays.find? (·.member == member) then
                pure (.structDynamicArray pre path dynInfo)
              else if let some mInfo := rawInfo.scalars.find? (·.member == member) then
                pure (.expr (← readRawStructScalar pre baseSlot mInfo))
              else
                failAt j s!"{member} is not a supported member of {rawInfo.structName}"
            else if let .bytesSlot fieldName _ := path then
              unless member == "value" do
                failAt j s!"unsupported StorageSlot bytes/string slot member {member}"
              pure (.state fieldName pre)
            else
              let rawFieldName ← match path with
                | .zero field | .one field _ | .two field _ _ => pure field
                | .outer _ _ => failAt j "member access on an incomplete mapping"
                | .rawSlot _ _ | .bytesSlot _ _ => failAt j "internal error: unexpected raw/bytes slot path"
              let (fieldName, subPrefix) := splitSPathField rawFieldName
              let qualMember := qualifySPathMember subPrefix member
              let info ← resolveField fieldName j
              if member == "length" && subPrefix == "" && info.fixedArrayLength.isSome then
                let some len := info.fixedArrayLength | failAt j "missing fixed array length"
                pure (.expr { pre, expr := .literal len })
              else if info.subStructs.any (·.1 == qualMember) then
                pure (.path pre (appendSPathSub path member))
              else if let some arrInfo := info.structFixedArrays.find? (·.member == qualMember) then
                pure (.structFixedArray pre path arrInfo)
              else if let some mapInfo := info.structMappings.find? (·.member == qualMember) then
                pure (.structMapping pre path mapInfo)
              else if let some dynInfo := info.structDynamicArrays.find? (·.member == qualMember) then
                pure (.structDynamicArray pre path dynInfo)
              else
                pure (.expr (← memberRead pre path member j))
        | .structFixedArray pre _ arrInfo =>
            unless member == "length" do failAt j s!"unsupported fixed array member {member}"
            pure (.expr { pre, expr := .literal arrInfo.length })
        | .snapshot elements =>
            unless member == "length" do failAt j s!"unsupported fixed array member {member}"
            pure (.expr { pre := #[], expr := .literal elements.size })
        | .flatStruct id =>
            let some flat := (← get).flatStructs.find? id | failAt j "unknown flat struct local"
            let some (_, _, binding) := flat.members.find? (fun (mName, _, _) => mName == member)
              | failAt j s!"{member} is not a member of {flat.structName}"
            pure (.expr { pre := #[], expr := .localVar binding })
        | .mem id pre =>
            let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
            if let some schema := mem.schema then
              if let some i := mem.members.findIdx? (fun p => p.1 == member) then
                if let some (.structArray _ _) := schema[i]? then
                  return .abiArray id i pre
                if let some (.scalarArray _) := schema[i]? then
                  return .abiArray id i pre
                if let some (.bytesField _) := schema[i]? then
                  return .abiBytesField id i pre
                if let some (.nestedStruct _ subSid subSname subMembers subSchema) := schema[i]? then
                  let subId := 1000000000 + (← get).next
                  modify fun e => { e with next := e.next + 1 }
                  if mem.calldataLocation then
                    let subStem ← freshAbiStem subSchema false
                    let checks := AbiLowering.nestedStructCalldataHead
                      (.localVar (mem.abiStem ++ "_calldata")) i subSchema.length (subStem ++ "_calldata")
                    let subMem : MemParam :=
                      { structId := subSid
                        param := s!"{mem.param}_{member}"
                        structName := subSname
                        members := subMembers.toArray
                        staticTypes := none
                        calldataLocation := true
                        headBinding := ""
                        schema := some subSchema
                        abiStem := subStem }
                    modify fun e => { e with mems := e.mems.insert subId subMem }
                    return .mem subId (pre ++ checks.toArray)
                  else
                    let subStem ← freshAbiStem subSchema true
                    let loadPtr := Stmt.letVar (subStem ++ "_memory")
                      (.mload (.add (.localVar (mem.abiStem ++ "_memory")) (.literal (32*i))))
                    let subMem : MemParam :=
                      { structId := subSid
                        param := s!"{mem.param}_{member}"
                        structName := subSname
                        members := subMembers.toArray
                        staticTypes := none
                        calldataLocation := false
                        headBinding := ""
                        schema := some subSchema
                        abiStem := subStem }
                    modify fun e => { e with mems := e.mems.insert subId subMem }
                    return .mem subId (pre.push loadPtr)
            pure (.expr (← readAbiMember id pre member j))
        | .abiBytesField id memberIndex pre =>
            unless member == "length" do failAt j s!"unsupported bytes member {member}"
            let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
            let some schema := mem.schema | failAt j "missing ABI schema"
            let some (.bytesField _) := schema[memberIndex]?
              | failAt j "length requires a schema-checked ABI bytes field"
            if mem.calldataLocation then
              let header ← fresh
              let length ← fresh
              let data ← fresh
              let checks := AbiLowering.calldataBytesFieldHead
                (.localVar (mem.abiStem ++ "_calldata")) memberIndex header length data
              return .expr { pre := pre ++ checks.toArray, expr := .localVar length }
            else
              let bytesPtr := Expr.mload (.add (.localVar (mem.abiStem ++ "_memory"))
                (.literal (32*memberIndex)))
              return .expr { pre, expr := .mload bytesPtr }
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
        | .abiElement id memberIndex pointer inMemory pre =>
            let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
            let some schema := mem.schema | failAt j "missing ABI schema"
            let some (.structArray _ fields) := schema[memberIndex]?
              | failAt j "expected a struct-array element"
            let some i := fields.findIdx? (fun f => f.name == member)
              | failAt j s!"unknown struct-array member {member}"
            let some field := fields[i]? | failAt j "missing struct-array field"
            let offset := Expr.add pointer (.literal (32*i))
            let value := if !inMemory then Expr.calldataload offset else Expr.mload offset
            let bound := SolidityAbi.scalarBound field.kind
            let pre := if !inMemory && bound < 2^256 then
              pre.push (AbiLowering.guard (.lt value (.literal bound))) else pre
            pure (.expr { pre, expr := value })
        | .calldataBytes id pre =>
            unless member == "length" do failAt j s!"unsupported bytes member {member}"
            let some cb := (← get).calldataBytes.find? id | failAt j "unknown calldata bytes parameter"
            pure (.expr { pre, expr := .localVar cb.lengthBinding })
        | .scalarArray id pre =>
            unless member == "length" do failAt j s!"unsupported array member {member}"
            let some arr := (← get).scalarArrays.find? id | failAt j "unknown scalar array parameter"
            pure (.expr { pre, expr := .localVar arr.lengthBinding })
        | .structDynamicArray pre path dynInfo =>
            unless member == "length" do failAt j s!"unsupported array member {member}"
            if let .rawSlot _ baseSlot := path then
              let slotExpr := rawStructMemberSlot baseSlot dynInfo.wordOffset
              let val ← readStorageDynamicArrayLength pre "" slotExpr
              pure (.expr val)
            else
              let rawName ← match path with
                | .zero name | .one name _ | .two name _ _ => pure name
                | .outer _ _ => failAt j "struct dynamic array length requires all outer mapping keys"
                | .rawSlot _ _ | .bytesSlot _ _ =>
                    failAt j "struct dynamic array length requires all outer mapping keys"
              let (name, _) := splitSPathField rawName
              let info ← resolveField name j
              markField name
              markStructDynamicArray name dynInfo.member
              let (slotStmts, slotExpr) ← computeSPathBaseSlot path info dynInfo.wordOffset j
              let val ← readStorageDynamicArrayLength (pre ++ slotStmts) "" slotExpr
              pure (.expr val)
        | .state name pre =>
            let info ← resolveField name j
            if member == "length" && info.dynamicArrayElemType.isSome then
              let val ← readStorageDynamicArrayLength pre name (.literal info.slot)
              return .expr val
            unless member == "length" && info.bytesStorage && !info.stringStorage do
              failAt j s!"unsupported member {member}"
            let val ← lowerStorageBytesLength name pre
            pure (.expr val)
        | _ => failAt j s!"unsupported member {member}"
  | "FunctionCall" =>
      let kind ← mStr (← mField j "kind")
      let ty ← mType j
      if kind == "functionCall" && ty.startsWith "struct " && !ty.contains "[" &&
          (ty.endsWith " storage pointer" || ty.endsWith " storage ref") then
        let callee ← mField j "expression"
        if (← mKind callee) == "MemberAccess" &&
            (field? callee "referencedDeclaration").isNone &&
            optStr callee "memberName" == some "push" then
          let base ← mField callee "expression"
          let baseRef ← lowerRef base
          let some (pre, fieldName, slotExpr, _, _, _, some elemSid) ← resolveStorageDynamicArrayTarget baseRef base
            | failAt callee "storage struct array push target is outside this slice"
          let args ← mArr (← mField j "arguments")
          if args.isEmpty then
            let (pushStmts, pushPath) ← pushStorageDynamicStructArray pre fieldName slotExpr elemSid none j
            return .path pushStmts pushPath
          else if args.size == 1 then
            let arg := args[0]!
            if !pre.isEmpty && (statefulCallIn arg (← get) || assignmentIn arg) then
              failAt arg "storage array push prelude with stateful argument is unsupported"
            let (argSid, _, argPre, memberVals) ← lowerFlatStructValue arg (some elemSid) true
            unless argSid == elemSid do
              failAt arg "storage struct array push argument type mismatch"
            let (pushStmts, pushPath) ← pushStorageDynamicStructArray (pre ++ argPre) fieldName slotExpr elemSid (some memberVals) j
            return .path pushStmts pushPath
          else
            failAt j "storage array push expects at most one argument"
        let (fnId, vals) ← resolveCallTargetAndArgs j
        let (pre, path) ← inlineStorageRefFn fnId vals j
        pure (.path pre path)
      else
        failAt j s!"unsupported reference FunctionCall ({kind} : {ty})"
  | kind => failAt j s!"unsupported reference {kind}"

private partial def lowerTypeBound (at_ base : Json) (member : String) : M Ref := do
  unless (← mKind base) == "FunctionCall" do
    failAt at_ s!"{member} is only supported on type(T)"
  let callee ← mField base "expression"
  unless (← mKind callee) == "Identifier" && optStr callee "name" == some "type" do
    failAt at_ s!"{member} is only supported on type(T)"
  let args ← mArr (← mField base "arguments")
  unless args.size == 1 do failAt at_ "type() expects one argument"
  let arg := args[0]!
  if (← mKind arg) == "Identifier" || (← mKind arg) == "MemberAccess" then
    let argTy ← mType arg
    if argTy.startsWith "type(enum " then
      let eid ← refInt arg
      unless eid ≥ 0 do failAt arg "unresolved enum type"
      let some members := (← get).enums.find? eid.toNat
        | failAt arg s!"unresolved enum {eid}"
      unless !members.isEmpty && members.size ≤ 256 do
        failAt arg s!"invalid enum member count {members.size}"
      let bound := if member == "max" then members.size - 1 else 0
      return .expr { pre := #[], expr := .literal bound }
  unless (← mKind arg) == "ElementaryTypeNameExpression" do
    failAt at_ "type() expects an elementary type"
  let tname ← mStr (← mField (← mField arg "typeName") "name")
  if tname == "int256" || tname == "int" then
    let bound := if member == "max" then 2 ^ 255 - 1 else 2 ^ 255
    pure (.expr { pre := #[], expr := .literal bound })
  else if tname.startsWith "uint" then
    let some bits := bitsOf tname | failAt at_ s!"unsupported type().{member} {tname}"
    let bound := if member == "max" then 2 ^ bits - 1 else 0
    pure (.expr { pre := #[], expr := .literal bound })
  else
    failAt at_ s!"unsupported type().{member} {tname}"

private partial def lowerInterfaceId (at_ base : Json) : M Ref := do
  unless (← mKind base) == "FunctionCall" do
    failAt at_ "interfaceId is only supported on type(I)"
  let callee ← mField base "expression"
  unless (← mKind callee) == "Identifier" && optStr callee "name" == some "type" do
    failAt at_ "interfaceId is only supported on type(I)"
  let args ← mArr (← mField base "arguments")
  unless args.size == 1 do failAt at_ "type() expects one argument"
  let arg := args[0]!
  unless (← mKind arg) == "Identifier" || (← mKind arg) == "MemberAccess" do
    failAt arg "type(I).interfaceId expects an interface identifier"
  let cid ← refInt arg
  unless cid ≥ 0 do failAt arg "unresolved interface type"
  let env ← get
  unless env.contractKinds.find? cid.toNat == some "interface" do
    failAt arg "type(I).interfaceId requires an interface type"
  let some nodes := env.contractNodes.find? cid.toNat
    | failAt arg s!"unresolved interface definition {cid}"
  let mut acc : Nat := 0
  for node in nodes do
    if let some hex := optStr node "functionSelector" then
      unless hex.length == 8 do
        failAt node s!"invalid functionSelector hex length {hex.length}"
      let chars := hex.toList.toArray
      let mut word := 0
      for index in [:chars.size] do
        let some digit := Compiler.Hex.hexCharToNat? chars[index]!
          | failAt node "invalid functionSelector hex digit"
        word := word * 16 + digit
      acc := Nat.xor acc word
  return .expr { pre := #[], expr := .literal (acc * 16 ^ 56) }

private partial def lowerSelectorMemberAccess (at_ base : Json) : M Ref := do
  unless (← mType at_) == "bytes4" do
    failAt at_ "function .selector member access is outside this slice"
  let parseSelectorHex (node : Json) (hex : String) : M Ref := do
    unless hex.length == 8 do
      failAt node s!"invalid selector hex length {hex.length}"
    let chars := hex.toList.toArray
    let mut word := 0
    for index in [:chars.size] do
      let some digit := Compiler.Hex.hexCharToNat? chars[index]!
        | failAt node "invalid selector hex digit"
      word := word * 16 + digit
    return .expr { pre := #[], expr := .literal (word * 16 ^ 56) }
  if (← mKind base) == "MemberAccess" then
    let receiver ← mField base "expression"
    unless ← isPureSelectorReceiver receiver do
      failAt receiver "selector receiver must be a contract/interface type, this, or a local/parameter"
    let declId ← refInt base
    unless declId ≥ 0 do
      failAt at_ "function .selector member access is outside this slice"
    let env ← get
    if let some decl := (env.funs.find? declId.toNat <|> env.stateVars.find? declId.toNat) then
      let some hex := optStr decl "functionSelector"
        | failAt at_ "function .selector member access is outside this slice"
      return ← parseSelectorHex base hex
    if let some errDecl := env.errorDecls.find? declId.toNat then
      let some hex := optStr errDecl "errorSelector"
        | failAt at_ "function .selector member access is outside this slice"
      return ← parseSelectorHex base hex
    failAt at_ "function .selector member access is outside this slice"
  else if (← mKind base) == "Identifier" then
    let declId ← refInt base
    if declId ≥ 0 then
      if let some errDecl := (← get).errorDecls.find? declId.toNat then
        if let some hex := optStr errDecl "errorSelector" then
          return ← parseSelectorHex base hex
    failAt at_ "function .selector member access is outside this slice"
  else
    failAt at_ "function .selector member access is outside this slice"

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
  unless op == "&&" || op == "||" do
    if (assignmentIn (← mField j "leftExpression") && (!right.pre.isEmpty || !isOrderIndependentSibling right.expr)) ||
        (assignmentIn (← mField j "rightExpression") && (!left.pre.isEmpty || !isOrderIndependentSibling left.expr)) then
      failAt j "assignment operand with non-atomic sibling requires explicit evaluation-order support"
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
  if common.startsWith "int_const" && op == "**" then
    if left.pre.isEmpty && right.pre.isEmpty then
      if let .literal a := left.expr then
        if let .literal b := right.expr then
          if a ≤ 1 || b < 256 then
            let power := a ^ b
            if power < 2 ^ 256 then return { pre := #[], expr := .literal power }
    failAt j s!"unsupported operand type {common}"
  if common.startsWith "int_const" && !common.startsWith "int_const -" && op == "<<" then
    let leftTy ← mType (← mField j "leftExpression")
    let rightTy ← mType (← mField j "rightExpression")
    if !leftTy.startsWith "int_const -" && !rightTy.startsWith "int_const -" &&
        left.pre.isEmpty && right.pre.isEmpty then
      if let .literal a := left.expr then
        if let .literal b := right.expr then
          if a == 0 || b < 256 then
            let shifted := a * 2 ^ b
            if shifted < 2 ^ 256 then return { pre := #[], expr := .literal shifted }
    failAt j s!"unsupported operand type {common}"
  if common.startsWith "int_const" && !common.startsWith "int_const -" && op == ">>" then
    let leftTy ← mType (← mField j "leftExpression")
    let rightTy ← mType (← mField j "rightExpression")
    if !leftTy.startsWith "int_const -" && !rightTy.startsWith "int_const -" &&
        left.pre.isEmpty && right.pre.isEmpty then
      if let .literal a := left.expr then
        if let .literal b := right.expr then
          let shifted := if b >= 256 then 0 else a / 2 ^ b
          if shifted < 2 ^ 256 then return { pre := #[], expr := .literal shifted }
    failAt j s!"unsupported operand type {common}"
  let isSigned := common == "int256" || common == "int"
  if common == "bytes4" then
    let leftTy ← mType (← mField j "leftExpression")
    let rightTy ← mType (← mField j "rightExpression")
    unless leftTy == "bytes4" && rightTy == "bytes4" do
      failAt j "implicit constant conversion to bytes4 is outside this slice"
  unless (bitsOf common).isSome || common == "bool" || common == "bytes4" || isSigned do
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
      if isSigned then
        if (← get).unchecked then
          let a ← atom left
          let b ← atom right
          pure { pre := a.pre ++ b.pre, expr := .add a.expr b.expr }
        else
          checkedSignedAdd left right
      else
        unless common.startsWith "uint" do failAt j s!"unsupported add type {common}"
        let some bits := bitsOf common | failAt j s!"unsupported add type {common}"
        if (← get).unchecked then
          let a ← atom left
          let b ← atom right
          let wrapped := if bits < 256 then Expr.bitAnd (.add a.expr b.expr) (.literal (2 ^ bits - 1)) else .add a.expr b.expr
          pure { pre := a.pre ++ b.pre, expr := wrapped }
        else
          checkedAdd bits left right
  | "-" =>
      if isSigned then
        if (← get).unchecked then
          let a ← atom left
          let b ← atom right
          pure { pre := a.pre ++ b.pre, expr := .sub a.expr b.expr }
        else
          checkedSignedSub left right
      else
        unless common.startsWith "uint" do failAt j s!"unsupported sub type {common}"
        let some bits := bitsOf common | failAt j s!"unsupported sub type {common}"
        if (← get).unchecked then
          let a ← atom left
          let b ← atom right
          let wrapped := if bits < 256 then Expr.bitAnd (.sub a.expr b.expr) (.literal (2 ^ bits - 1)) else .sub a.expr b.expr
          pure { pre := a.pre ++ b.pre, expr := wrapped }
        else
          checkedSub left right
  | "*" =>
      if isSigned then
        if (← get).unchecked then
          let a ← atom left
          let b ← atom right
          pure { pre := a.pre ++ b.pre, expr := .mul a.expr b.expr }
        else
          checkedSignedMul left right
      else
        unless common.startsWith "uint" do failAt j s!"unsupported mul type {common}"
        let some bits := bitsOf common | failAt j s!"unsupported mul type {common}"
        if (← get).unchecked then
          let a ← atom left
          let b ← atom right
          let wrapped := if bits < 256 then Expr.bitAnd (.mul a.expr b.expr) (.literal (2 ^ bits - 1)) else .mul a.expr b.expr
          pure { pre := a.pre ++ b.pre, expr := wrapped }
        else
          checkedMul bits left right
  | "**" =>
      let leftTy ← mType (← mField j "leftExpression")
      let rightTy ← mType (← mField j "rightExpression")
      unless common.startsWith "uint" &&
          (leftTy.startsWith "uint" || (leftTy.startsWith "int_const" && !leftTy.startsWith "int_const -")) &&
          (rightTy.startsWith "uint" || (rightTy.startsWith "int_const" && !rightTy.startsWith "int_const -")) do
        failAt j s!"unsupported exp type {common}"
      let some bits := bitsOf common | failAt j s!"unsupported exp type {common}"
      if (← get).unchecked then
        let a ← atom left
        let b ← atom right
        let raw := Expr.externalCall builtinExpName [a.expr, b.expr]
        let wrapped := if bits < 256 then Expr.bitAnd raw (.literal (2 ^ bits - 1)) else raw
        pure { pre := a.pre ++ b.pre, expr := wrapped }
      else
        checkedExp bits left right j
  | "<<" =>
      let rightTy ← mType (← mField j "rightExpression")
      unless rightTy.startsWith "uint" || (rightTy.startsWith "int_const" && !rightTy.startsWith "int_const -") do
        failAt j s!"shift amount must be unsigned, found {rightTy}"
      let a ← atom left
      let b ← atom right
      if isSigned || common == "bytes32" then
        pure { pre := a.pre ++ b.pre, expr := .shl b.expr a.expr }
      else if common.startsWith "uint" then
        let some bits := bitsOf common | failAt j s!"unsupported shift type {common}"
        let shifted := if bits < 256 then Expr.bitAnd (.shl b.expr a.expr) (.literal (2 ^ bits - 1)) else .shl b.expr a.expr
        pure { pre := a.pre ++ b.pre, expr := shifted }
      else
        failAt j s!"unsupported shift type {common}"
  | ">>" =>
      let rightTy ← mType (← mField j "rightExpression")
      unless rightTy.startsWith "uint" || (rightTy.startsWith "int_const" && !rightTy.startsWith "int_const -") do
        failAt j s!"shift amount must be unsigned, found {rightTy}"
      let a ← atom left
      let b ← atom right
      if isSigned then
        pure { pre := a.pre ++ b.pre, expr := .sar b.expr a.expr }
      else if (common.startsWith "uint" && (bitsOf common).isSome) || common == "bytes32" then
        pure { pre := a.pre ++ b.pre, expr := .shr b.expr a.expr }
      else
        failAt j s!"unsupported shift type {common}"
  | "&" | "|" | "^" =>
      unless (common.startsWith "uint" && (bitsOf common).isSome) || common == "bytes32" || common == "bytes4" || isSigned do
        failAt j s!"unsupported bitwise operand type {common}"
      let a ← atom left
      let b ← atom right
      let bitOp := if op == "&" then Expr.bitAnd else if op == "|" then Expr.bitOr else Expr.bitXor
      pure { pre := a.pre ++ b.pre, expr := bitOp a.expr b.expr }
  | "/" =>
      if isSigned then
        signedDiv (← get).unchecked left right
      else
        unless common.startsWith "uint" do failAt j s!"unsupported div type {common}"
        checkedDiv left right
  | "%" =>
      unless common.startsWith "uint" do failAt j "modulo requires unsigned scalar operands"
      checkedModulo left right
  | "<" =>
      if isSigned then cmp .slt left right else cmp .lt left right
  | ">" =>
      if isSigned then cmp .sgt left right else cmp .gt left right
  | "<=" =>
      if isSigned then
        let v ← cmp .sgt left right
        pure { v with expr := .logicalNot v.expr }
      else
        cmp .le left right
  | ">=" =>
      if isSigned then
        let v ← cmp .slt left right
        pure { v with expr := .logicalNot v.expr }
      else
        cmp .ge left right
  | "==" => cmp .eq left right
  | "!=" =>
      let v ← cmp .eq left right
      pure { v with expr := .logicalNot v.expr }
  | _ => failAt j s!"unsupported operator {op}"

private partial def isConstLiteralVal (v : Val) : Bool :=
  v.pre.isEmpty && match v.expr with | .literal _ => true | _ => false

private partial def checkedExp (bits : Nat) (left right : Val) (at_ : Json) : M Val := do
  unless isConstLiteralVal left || isConstLiteralVal right do
    failAt at_ "checked exponentiation with dynamic base and exponent is outside this slice"
  if left.pre.isEmpty then
    if let .literal baseVal := left.expr then
      let b ← atom right
      if baseVal == 0 then
        return { pre := b.pre, expr := .eq b.expr (.literal 0) }
      else if baseVal == 1 then
        return { pre := b.pre, expr := .literal 1 }
      else
        let dest ← fresh
        let maxExp := maxSafeExponent baseVal bits
        let ok := Stmt.assignVar dest (.externalCall builtinExpName [.literal baseVal, b.expr])
        let ite := iteStmt (.lt (.literal maxExp) b.expr) overflowPanic ok
        return { pre := b.pre.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }
  if right.pre.isEmpty then
    if let .literal expVal := right.expr then
      let a ← atom left
      if expVal == 0 then
        return { pre := a.pre, expr := .literal 1 }
      else if expVal == 1 then
        return a
      else
        let dest ← fresh
        let maxBase := maxSafeBase expVal bits
        let ok := Stmt.assignVar dest (.externalCall builtinExpName [a.expr, .literal expVal])
        let ite := iteStmt (.lt (.literal maxBase) a.expr) overflowPanic ok
        return { pre := a.pre.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }
  let a ← atom left
  let b ← atom right
  pure { pre := a.pre ++ b.pre, expr := .externalCall builtinExpName [a.expr, b.expr] }

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

private partial def checkedSignedAdd (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let sumVar ← fresh
  let dest ← fresh
  let sum := Expr.localVar sumVar
  let ok := Stmt.assignVar dest sum
  let nonNegB := iteStmt (.slt sum a.expr) overflowPanic ok
  let negB := iteStmt (.sgt sum a.expr) overflowPanic ok
  let check := Stmt.ite (.slt b.expr (.literal 0)) [negB] [nonNegB]
  pure { pre := a.pre ++ b.pre |>.push (.letVar sumVar (.add a.expr b.expr)) |>.push (.letVar dest (.literal 0)) |>.push check,
         expr := .localVar dest }

private partial def checkedSignedSub (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let diffVar ← fresh
  let dest ← fresh
  let diff := Expr.localVar diffVar
  let ok := Stmt.assignVar dest diff
  let negB := iteStmt (.slt diff a.expr) overflowPanic ok
  let nonNegB := iteStmt (.sgt diff a.expr) overflowPanic ok
  let check := Stmt.ite (.slt b.expr (.literal 0)) [negB] [nonNegB]
  pure { pre := a.pre ++ b.pre |>.push (.letVar diffVar (.sub a.expr b.expr)) |>.push (.letVar dest (.literal 0)) |>.push check,
         expr := .localVar dest }

private partial def checkedSignedMul (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let prodVar ← fresh
  let dest ← fresh
  let prod := Expr.localVar prodVar
  let ok := Stmt.assignVar dest prod
  let minTimesNegOne := iteStmt (.eq b.expr (.literal (2 ^ 255))) overflowPanic ok
  let divCheck := iteStmt (.eq (.sdiv prod a.expr) b.expr)
    (iteStmt (.eq a.expr (.literal (2 ^ 256 - 1))) minTimesNegOne ok)
    overflowPanic
  let check := iteStmt (.eq a.expr (.literal 0)) ok divCheck
  pure { pre := a.pre ++ b.pre |>.push (.letVar prodVar (.mul a.expr b.expr)) |>.push (.letVar dest (.literal 0)) |>.push check,
         expr := .localVar dest }

private partial def signedDiv (isUnchecked : Bool) (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let ok := Stmt.assignVar dest (.sdiv a.expr b.expr)
  let nonZero :=
    if isUnchecked then
      ok
    else
      iteStmt (.eq a.expr (.literal (2 ^ 255)))
        (iteStmt (.eq b.expr (.literal (2 ^ 256 - 1))) overflowPanic ok)
        ok
  let check := iteStmt (.eq b.expr (.literal 0)) divPanic nonZero
  pure { pre := a.pre ++ b.pre |>.push (.letVar dest (.literal 0)) |>.push check,
         expr := .localVar dest }

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
  let args ← mArr (← mField j "arguments")
  unless args.size == 1 do failAt j "cast expects one argument"
  let callTy ← mType j
  if callTy.startsWith "contract " then
    let v ← lowerExpr args[0]!
    let src ← mType args[0]!
    unless src == "address" || src == "address payable" || src.startsWith "contract " do
      failAt j s!"unsupported contract cast source {src}"
    return v
  if callTy.startsWith "enum " then
    let members ← resolveEnumMembers targetExpr callTy
    let v ← lowerExpr args[0]!
    let src ← mType args[0]!
    if src == callTy then
      return v
    unless (src.startsWith "uint" && (bitsOf src).isSome) ||
        src == "int256" || src == "int" || src.startsWith "int_const" do
      failAt j s!"unsupported enum cast source {src} for {callTy}"
    let a ← atom v
    let dest ← fresh
    let check := Stmt.ite (.lt a.expr (.literal members.size))
      [.assignVar dest a.expr] [.panicCode (.literal 0x21)]
    return { pre := a.pre.push (.letVar dest (.literal 0)) |>.push check,
             expr := .localVar dest }
  unless (← mKind targetExpr) == "ElementaryTypeNameExpression" do
    failAt j "unsupported cast"
  let tname ← mStr (← mField (← mField targetExpr "typeName") "name")
  let src ← mType args[0]!
  if (tname == "bytes32" || tname == "bytes4") &&
      (src == "bytes" || src == "bytes memory" || src == "bytes calldata" ||
       src == "bytes storage ref" || src == "bytes storage pointer") then
    return ← lowerBytesToFixedBytes args[0]! (if tname == "bytes32" then 32 else 4) j
  let v ← lowerExpr args[0]!
  if src.startsWith "int" && src != "int256" && src != "int" && !src.startsWith "int_const" then
    failAt j s!"unsupported cast source {src}"
  if tname == "int256" || tname == "int" then
    unless src == "int256" || src == "int" || src.startsWith "int_const" ||
        (src.startsWith "uint" && (bitsOf src).isSome) do
      failAt j s!"unsupported cast source {src} for {tname}"
    return v
  if tname == "bytes4" then
    if src == "bytes4" then
      return v
    else if src == "bytes32" then
      let a ← atom v
      let dest ← fresh
      let bound := Stmt.letVar dest (.bitAnd a.expr (.literal ((2 ^ 32 - 1) * 16 ^ 56)))
      return { pre := a.pre.push bound, expr := .localVar dest }
    else if src == "uint32" then
      let a ← atom v
      let dest ← fresh
      let shifted := Stmt.letVar dest (.shl (.literal 224) (.bitAnd a.expr (.literal (2 ^ 32 - 1))))
      return { pre := a.pre.push shifted, expr := .localVar dest }
    else
      failAt j s!"unsupported cast source {src} for bytes4"
  if src == "bytes4" then
    if tname == "bytes32" then
      return v
    else if tname == "uint32" then
      let a ← atom v
      let dest ← fresh
      let shifted := Stmt.letVar dest (.shr (.literal 224) a.expr)
      return { pre := a.pre.push shifted, expr := .localVar dest }
    else
      failAt j s!"unsupported cast target {tname} from bytes4"
  let some bits := bitsOf tname | failAt j s!"unsupported cast target {tname}"
  let narrow : Bool :=
    match bitsOf src with
    | some sb => decide (sb > bits)
    | none => decide (bits < 256) && !src.startsWith "int_const" && !src.startsWith "enum "
  if narrow then
    let a ← atom v
    let dest ← fresh
    let bound := Stmt.letVar dest (.bitAnd a.expr (.literal (2 ^ bits - 1)))
    pure { pre := a.pre.push bound, expr := .localVar dest }
  else
    pure v

private partial def checkEncodingStructRef (j : Json) : M Unit := do
  match ← mKind j with
  | "Identifier" => pure ()
  | "MemberAccess" => checkEncodingStructRef (← mField j "expression")
  | "IndexAccess" =>
      checkEncodingStructRef (← mField j "baseExpression")
      let idx ← mField j "indexExpression"
      unless (← mKind idx) == "Identifier" || (← mKind idx) == "Literal" do
        failAt idx "effectful ABI encoding argument is unsupported"
  | _ => failAt j "effectful ABI encoding argument is unsupported"

/-- Restrict the entire argument tree, not merely its outer cast. This keeps
custom reverts or effects hidden beneath a cast out of the admitted fragment. -/
private partial def checkEncodingScalar (j : Json) : M Unit := do
  match ← mKind j with
  | "Identifier" | "Literal" => pure ()
  | "MemberAccess" =>
      if optStr j "memberName" == some "interfaceId" || optStr j "memberName" == some "selector" then pure ()
      else checkEncodingScalar (← mField j "expression")
  | "UnaryOperation" =>
      unless optStr j "operator" == some "-" && (← mType j).startsWith "int_const -" do
        failAt j "effectful ABI encoding argument is unsupported"
      checkEncodingScalar (← mField j "subExpression")
  | "FunctionCall" =>
      let args ← mArr (← mField j "arguments")
      if optStr j "kind" == some "typeConversion" then
        if (← mType j).startsWith "enum " then
          unless args.size == 1 && (← mType args[0]!) == (← mType j) do
            failAt j "fallible enum conversion in ABI encoding argument is unsupported"
        for arg in args do checkEncodingScalar arg
      else if optStr j "kind" == some "functionCall" then
        unless (← mArr (← mField j "names")).isEmpty do
          failAt j "effectful ABI encoding argument is unsupported"
        let callee ← mField j "expression"
        if (← mKind callee) == "Identifier" || (← mKind callee) == "MemberAccess" then
          let refId := (field? callee "referencedDeclaration").bind (fun v => v.getInt?.toOption)
          if refId == some (-8) && (← mKind callee) == "Identifier" && args.size == 1 then
            pure ()
          else if let some id := refId then
            unless id >= 0 do
              failAt j "effectful ABI encoding argument is unsupported"
            let env ← get
            let natId := id.toNat
            let targetId := resolveInContracts env env.linearizedBases.toList natId |>.getD natId
            if fnHasCustomRevert env targetId then
              failAt j "effectful ABI encoding argument is unsupported"
            if (← mKind callee) == "MemberAccess" then
              let base ← mField callee "expression"
              let baseTy ← mType base
              unless baseTy.startsWith "type(library " do
                if baseTy.startsWith "struct " then
                  checkEncodingStructRef base
                else
                  checkEncodingScalar base
            for arg in args do
              if (← mType arg).startsWith "struct " then
                checkEncodingStructRef arg
              else
                checkEncodingScalar arg
          else
            failAt j "effectful ABI encoding argument is unsupported"
        else
          failAt j "effectful ABI encoding argument is unsupported"
      else
        failAt j "effectful ABI encoding argument is unsupported"
  | _ => failAt j "effectful ABI encoding argument is unsupported"

private partial def checkEncodingStructArg (j : Json) : M Unit := do
  if (← mKind j) == "FunctionCall" && optStr j "kind" == some "structConstructorCall" then
    for arg in (← mArr (← mField j "arguments")) do
      checkEncodingScalar arg
  else
    checkEncodingStructRef j

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
    | .bytesField _ | .nestedStruct _ _ _ _ _ =>
        failAt arg "ABI encoding of nested dynamic structs or bytes fields is outside this slice"
    | .scalarArray _ | .structArray _ _ =>
        let kinds : List SolidityAbi.ScalarKind := match member with
          | .scalarArray field => [field.kind]
          | .structArray _ fields => fields.map (fun (field : AbiSchema.ScalarField) => field.kind)
          | .scalar _ | .bytesField _ | .nestedStruct _ _ _ _ _ => []
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
  if (← mKind j) == "MemberAccess" && optStr j "memberName" == some "selector" && ty == "bytes4" then
    return ← lowerSelectorBytes j
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
    let size := if ty == "bool" then 1 else if ty == "bytes4" then 4 else (bitsOf ty).getD 256 / 8
    let pointer ← fresh
    let finish ← fresh
    modify fun env => { env with encodingMemory := true }
    let padded := if ty == "bytes4" then value.expr else Expr.mul value.expr (.literal (2^(8*(32-size))))
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

/-- Check that a `.selector` receiver is a contract/interface type, `this`, or a
pure local/parameter/cast expression that cannot read storage or trigger effects. -/
private partial def isPureSelectorReceiver (j : Json) : M Bool := do
  let ty ← mType j
  if ty.startsWith "type(contract " || ty.startsWith "type(library " then
    return (← mKind j) == "Identifier" || (← mKind j) == "MemberAccess"
  match ← mKind j with
  | "Identifier" =>
      let id ← refInt j
      if id == -28 && optStr j "name" == some "this" then return true
      if id ≥ 0 then return (← get).values.contains id.toNat
      return false
  | "Literal" => return true
  | "FunctionCall" =>
      unless optStr j "kind" == some "typeConversion" && ty.startsWith "contract " do
        return false
      let args ← mArr (← mField j "arguments")
      unless args.size == 1 do return false
      isPureSelectorReceiver args[0]!
  | _ => return false

/-- Resolve `<receiver>.<fn>` to its declaration and a 4-byte memory buffer
containing the left-aligned 32-bit function selector. -/
private partial def lowerMemberFunctionSelector (fnExpr : Json) : M (Json × EncodedBytes) := do
  unless (← mKind fnExpr) == "MemberAccess" do
    failAt fnExpr "selector target must be a contract or interface member"
  let receiver ← mField fnExpr "expression"
  unless ← isPureSelectorReceiver receiver do
    failAt receiver "selector receiver must be a contract/interface type, this, or a local/parameter"
  let declId ← refInt fnExpr
  unless declId ≥ 0 do
    failAt fnExpr "unresolved selector target declaration"
  let env ← get
  let some decl := (env.funs.find? declId.toNat <|> env.stateVars.find? declId.toNat <|> env.errorDecls.find? declId.toNat)
    | failAt fnExpr s!"unresolved selector declaration {declId}"
  let some hex := (optStr decl "functionSelector" <|> optStr decl "errorSelector")
    | failAt fnExpr "selector target has no functionSelector"
  unless hex.length == 8 do
    failAt fnExpr s!"invalid functionSelector hex length {hex.length}"
  let chars := hex.toList.toArray
  let mut word := 0
  for index in [:chars.size] do
    let some digit := Compiler.Hex.hexCharToNat? chars[index]!
      | failAt fnExpr "invalid functionSelector hex digit"
    word := word * 16 + digit
  let padded := word * 16 ^ 56
  let pointer ← fresh
  let finish ← fresh
  modify fun e => { e with encodingMemory := true }
  return (decl,
          { pre := (AbiEncoding.staticWords pointer finish [.literal padded]).toArray,
            pointer := .localVar pointer, size := .literal 4 })

/-- Lower `<receiver>.<fn>.selector` to a 4-byte memory buffer containing the
left-aligned 32-bit function selector from the referenced declaration. -/
private partial def lowerSelectorBytes (j : Json) : M EncodedBytes := do
  unless (← mKind j) == "MemberAccess" && optStr j "memberName" == some "selector" &&
      (← mType j) == "bytes4" do
    failAt j "selector argument must be a function .selector expression"
  let fnExpr ← mField j "expression"
  if (← mKind fnExpr) == "Identifier" then
    let declId ← refInt fnExpr
    if declId ≥ 0 then
      if let some errDecl := (← get).errorDecls.find? declId.toNat then
        if let some hex := optStr errDecl "errorSelector" then
          unless hex.length == 8 do
            failAt fnExpr s!"invalid errorSelector hex length {hex.length}"
          let chars := hex.toList.toArray
          let mut word := 0
          for index in [:chars.size] do
            let some digit := Compiler.Hex.hexCharToNat? chars[index]!
              | failAt fnExpr "invalid errorSelector hex digit"
            word := word * 16 + digit
          let padded := word * 16 ^ 56
          let pointer ← fresh
          let finish ← fresh
          modify fun e => { e with encodingMemory := true }
          return { pre := (AbiEncoding.staticWords pointer finish [.literal padded]).toArray,
                   pointer := .localVar pointer, size := .literal 4 }
  return (← lowerMemberFunctionSelector fnExpr).2

private partial def encodeSelectorAndWords (selBuffer : EncodedBytes) (pre : Array Stmt) (words : List Expr) : M EncodedBytes := do
  if words.isEmpty then
    return { selBuffer with pre }
  let wordsPointer ← fresh
  let wordsFinish ← fresh
  modify fun env => { env with encodingMemory := true }
  let mut pre := pre ++ (AbiEncoding.staticWords wordsPointer wordsFinish words).toArray
  let wordsBuffer : EncodedBytes :=
    { pre := #[], pointer := .localVar wordsPointer, size := .literal (32 * words.length) }
  let buffers := [{ selBuffer with pre := #[] }, wordsBuffer]
  let sizeName ← fresh
  let size := Expr.localVar sizeName
  pre := pre.push (.letVar sizeName (.literal (4 + 32 * words.length)))
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
  return { pre, pointer := .localVar pointer, size }

private partial def lowerStorageBytesLength (name : String) (pre : Array Stmt) : M Val := do
  markField name
  let raw ← fresh
  let outOfPlace ← fresh
  let len ← fresh
  let shortCheck := Expr.lt (.localVar len) (.literal 32)
  let stmts : Array Stmt := #[
    .letVar raw (.storage name),
    .letVar outOfPlace (.bitAnd (.localVar raw) (.literal 1)),
    .letVar len (.div (.localVar raw) (.literal 2)),
    .ite (.eq (.localVar outOfPlace) (.literal 0))
      [.assignVar len (.bitAnd (.localVar len) (.literal 0x7f))]
      [],
    .ite (.eq (.localVar outOfPlace) shortCheck)
      [.panicCode (.literal 0x22)]
      []
  ]
  return { pre := pre ++ stmts, expr := .localVar len }

private partial def storageBytesSourceVar? (j : Json) : M (Option String) := do
  if (← mKind j) == "MemberAccess" && optStr j "memberName" == some "value" then
    let base ← mField j "expression"
    let baseTy ← mType base
    if baseTy.startsWith "struct " &&
        (baseTy.endsWith " storage pointer" || baseTy.endsWith " storage ref") then
      match ← lowerRef base with
      | .path pre (.bytesSlot fieldName _) =>
          if pre.isEmpty then return some fieldName
      | _ => pure ()
  if (← mKind j) == "Identifier" then
    let id ← refInt j
    unless id ≥ 0 do return none
    let env ← get
    if env.values.contains id.toNat || env.paths.contains id.toNat || env.snapshots.contains id.toNat ||
       env.mems.contains id.toNat || env.abiElements.contains id.toNat ||
       env.byteBuffers.contains id.toNat || env.stringBuffers.contains id.toNat ||
       env.calldataBytes.contains id.toNat || env.scalarArrays.contains id.toNat ||
       env.numericConstants.contains id.toNat then
      return none
    if let some name := env.storageBytesVars.find? id.toNat then
      return some name
    let some decl := env.stateVars.find? id.toNat | return none
    if (field? decl "constant").bind (fun value => value.getBool?.toOption) == some true then
      return none
    if optStr decl "mutability" == some "immutable" then
      return none
    let name ← mStr (← mField decl "name")
    if env.duplicateLayoutLabels.contains name then
      failAt j s!"shadowed storage declaration {name} is outside this slice"
    if let some item := env.layoutItems.find? name then
      unless (← mNat (← mField item "astId")) == id.toNat do
        failAt j s!"shadowed storage declaration {name} is outside this slice"
    let info ← resolveField name j
    unless info.bytesStorage do return none
    return some name
  if (← mKind j) == "FunctionCall" && optStr j "kind" == some "typeConversion" then
    let ty ← mType j
    if ty == "bytes storage pointer" || ty == "string storage pointer" then
      let args ← mArr (← mField j "arguments")
      if args.size == 1 then
        return ← storageBytesSourceVar? args[0]!
  return none

private partial def lowerStorageBytesLength? (j : Json) : M (Option Val) := do
  let some name ← storageBytesSourceVar? j | return none
  some <$> lowerStorageBytesLength name #[]

private partial def unwrapBytesConversion (j : Json) : M Json := do
  if (← mKind j) == "FunctionCall" && optStr j "kind" == some "typeConversion" then
    let ty ← mType j
    if ty == "bytes" || ty == "bytes memory" || ty == "bytes calldata" || ty == "bytes storage pointer" then
      let args ← mArr (← mField j "arguments")
      if args.size == 1 then
        return ← unwrapBytesConversion args[0]!
  return j

private partial def lowerBytesToFixedBytes (arg : Json) (byteWidth : Nat) (at_ : Json) : M Val := do
  let fullMask : Nat := if byteWidth == 32 then 2 ^ 256 - 1 else (2 ^ 32 - 1) * 16 ^ 56
  let inner ← unwrapBytesConversion arg
  if (← mKind inner) == "Identifier" then
    let id ← refInt inner
    if id ≥ 0 then
      if let some cb := (← get).calldataBytes.find? id.toNat then
        if !cb.inMemory then
          let word ← fresh
          let lenExpr := Expr.localVar cb.lengthBinding
          let rawWord := Expr.bitAnd (.calldataload (.localVar cb.dataBinding)) (.literal fullMask)
          let maskShift := Expr.shl (.mul (.literal 8) (.sub (.literal byteWidth) lenExpr)) (.literal fullMask)
          let stmts : Array Stmt := #[
            .letVar word rawWord,
            .ite (.lt lenExpr (.literal byteWidth))
              [.assignVar word (.bitAnd (.localVar word) maskShift)]
              []
          ]
          return { pre := stmts, expr := .localVar word }
  if let some storageName ← storageBytesSourceVar? inner then
    let info ← resolveField storageName at_
    unless info.bytesStorage do
      failAt at_ "storage byte conversion requires a string or bytes storage variable"
    markField storageName
    modify fun e => { e with encodingMemory := true }
    let raw ← fresh
    let outOfPlace ← fresh
    let len ← fresh
    let dataSlot ← fresh
    let word ← fresh
    let shortCheck := Expr.lt (.localVar len) (.literal 32)
    let maskShift := Expr.shl (.mul (.literal 8) (.sub (.literal byteWidth) (.localVar len))) (.literal fullMask)
    let stmts : Array Stmt := #[
      .letVar raw (.storage storageName),
      .letVar outOfPlace (.bitAnd (.localVar raw) (.literal 1)),
      .letVar len (.div (.localVar raw) (.literal 2)),
      .ite (.eq (.localVar outOfPlace) (.literal 0))
        [.assignVar len (.bitAnd (.localVar len) (.literal 0x7f))]
        [],
      .ite (.eq (.localVar outOfPlace) shortCheck)
        [.panicCode (.literal 0x22)]
        [],
      .letVar word (.bitAnd (.localVar raw) (.literal fullMask)),
      .ite (.gt (.localVar len) (.literal 31))
        [ .mstore (.literal 0) (.literal info.slot),
          .letVar dataSlot (.keccak256 (.literal 0) (.literal 32)),
          .assignVar word (.bitAnd (.storageArrayElement storageName (.localVar dataSlot)) (.literal fullMask)) ]
        [],
      .ite (.lt (.localVar len) (.literal byteWidth))
        [.assignVar word (.bitAnd (.localVar word) maskShift)]
        []
    ]
    return { pre := stmts, expr := .localVar word }
  let buf ← lowerEncodedBytes arg
  let ptr ← fresh
  let len ← fresh
  let word ← fresh
  let maskShift := Expr.shl (.mul (.literal 8) (.sub (.literal byteWidth) (.localVar len))) (.literal fullMask)
  let stmts : Array Stmt := buf.pre ++ #[
    .letVar ptr buf.pointer,
    .letVar len buf.size,
    .letVar word (.bitAnd (.mload (.localVar ptr)) (.literal fullMask)),
    .ite (.lt (.localVar len) (.literal byteWidth))
      [.assignVar word (.bitAnd (.localVar word) maskShift)]
      []
  ]
  return { pre := stmts, expr := .localVar word }

private partial def lowerStorageBytesRead (name : String) (at_ : Json) : M EncodedBytes := do
  let info ← resolveField name at_
  unless info.bytesStorage do
    failAt at_ "storage byte buffer read requires a string or bytes storage variable"
  markField name
  modify fun e => { e with encodingMemory := true }
  let raw ← fresh
  let outOfPlace ← fresh
  let len ← fresh
  let pointer ← fresh
  let finish ← fresh
  let dataSlot ← fresh
  let wordCount ← fresh
  let copyIdx ← fresh
  let shortCheck := Expr.lt (.localVar len) (.literal 32)
  let reserveStmts := AbiEncoding.reserve pointer finish
    (.bitAnd (.add (.localVar len) (.literal 31)) (.bitNot (.literal 31)))
  let shortWord := Expr.bitAnd (.localVar raw) (.bitNot (.literal 0xff))
  let longBranch : List Stmt := [
    .mstore (.literal 0) (.literal info.slot),
    .letVar dataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar wordCount (.div (.add (.localVar len) (.literal 31)) (.literal 32)),
    .forEach copyIdx (.localVar wordCount) [
      .mstore (.add (.localVar pointer) (.mul (.localVar copyIdx) (.literal 32)))
        (.storageArrayElement name (.add (.localVar dataSlot) (.localVar copyIdx)))
    ]
  ]
  let stmts : Array Stmt := #[
    .letVar raw (.storage name),
    .letVar outOfPlace (.bitAnd (.localVar raw) (.literal 1)),
    .letVar len (.div (.localVar raw) (.literal 2)),
    .ite (.eq (.localVar outOfPlace) (.literal 0))
      [.assignVar len (.bitAnd (.localVar len) (.literal 0x7f))]
      [],
    .ite (.eq (.localVar outOfPlace) shortCheck)
      [.panicCode (.literal 0x22)]
      []
  ] ++ reserveStmts.toArray ++ #[
    .ite (.eq (.localVar outOfPlace) (.literal 0))
      [ .ite (.gt (.localVar len) (.literal 0))
          [.mstore (.localVar pointer) shortWord]
          [] ]
      longBranch
  ]
  return { pre := stmts, pointer := .localVar pointer, size := .localVar len }

private partial def lowerStorageBytesDelete (name : String) (pre : Array Stmt) : M (Array Stmt) := do
  let info ← resolveField name Json.null
  markField name
  modify fun e => { e with encodingMemory := true }
  let oldRaw ← fresh
  let oldOutOfPlace ← fresh
  let oldLen ← fresh
  let dataSlot ← fresh
  let oldSlotCount ← fresh
  let clearIdx ← fresh
  let shortCheck := Expr.lt (.localVar oldLen) (.literal 32)
  let clearLong : List Stmt := [
    .mstore (.literal 0) (.literal info.slot),
    .letVar dataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar oldSlotCount (.div (.add (.localVar oldLen) (.literal 31)) (.literal 32)),
    .forEach clearIdx (.localVar oldSlotCount) [
      .setStorageArrayElement name (.add (.localVar dataSlot) (.localVar clearIdx)) (.literal 0)
    ],
    .setStorage name (.literal 0)
  ]
  let stmts : Array Stmt := #[
    .letVar oldRaw (.storage name),
    .letVar oldOutOfPlace (.bitAnd (.localVar oldRaw) (.literal 1)),
    .letVar oldLen (.div (.localVar oldRaw) (.literal 2)),
    .ite (.eq (.localVar oldOutOfPlace) (.literal 0))
      [.assignVar oldLen (.bitAnd (.localVar oldLen) (.literal 0x7f))]
      [],
    .ite (.eq (.localVar oldOutOfPlace) shortCheck)
      [.panicCode (.literal 0x22)]
      [],
    .ite (.gt (.localVar oldLen) (.literal 0))
      [ .ite (.gt (.localVar oldLen) (.literal 31))
          clearLong
          [.setStorage name (.literal 0)] ]
      []
  ]
  return pre ++ stmts

private partial def lowerStorageBytesWrite (name : String) (pre : Array Stmt) (target right : Json) : M (Array Stmt) := do
  let info ← resolveField name target
  let targetTy ← mType target
  let rightTy ← mType right
  if info.stringStorage then
    unless rightTy == "string" || rightTy == "string memory" || rightTy == "string calldata" ||
           rightTy == "string storage ref" || rightTy == "string storage pointer" ||
           rightTy.startsWith "literal_string " do
      failAt right s!"cannot assign {rightTy} to {targetTy}"
  else
    unless rightTy == "bytes" || rightTy == "bytes memory" || rightTy == "bytes calldata" ||
           rightTy == "bytes storage ref" || rightTy == "bytes storage pointer" ||
           rightTy.startsWith "literal_string " do
      failAt right s!"cannot assign {rightTy} to {targetTy}"
  markField name
  if let some srcName ← storageBytesSourceVar? right then
    if srcName == name then
      return pre
  let buf ← lowerEncodedBytes right
  modify fun e => { e with encodingMemory := true }
  let ptr ← fresh
  let newLen ← fresh
  let oldRaw ← fresh
  let oldOutOfPlace ← fresh
  let oldLen ← fresh
  let cleanupDataSlot ← fresh
  let oldSlotCount ← fresh
  let newSlotCount ← fresh
  let clearCount ← fresh
  let clearIdx ← fresh
  let writeDataSlot ← fresh
  let fullWords ← fresh
  let copyIdx ← fresh
  let remBytes ← fresh
  let lastWord ← fresh
  let shortWord ← fresh
  let shortCheck := Expr.lt (.localVar oldLen) (.literal 32)
  let maskDynamic (data bytes : Expr) : Expr :=
    .bitAnd data (.bitNot (.shr (.mul (.literal 8) bytes) (.bitNot (.literal 0))))
  let cleanupStmts : List Stmt := [
    .ite (.gt (.localVar oldLen) (.literal 31))
      [ .ite (.gt (.localVar oldLen) (.localVar newLen))
          [ .mstore (.literal 0) (.literal info.slot),
            .letVar cleanupDataSlot (.keccak256 (.literal 0) (.literal 32)),
            .letVar oldSlotCount (.div (.add (.localVar oldLen) (.literal 31)) (.literal 32)),
            .letVar newSlotCount (.div (.add (.localVar newLen) (.literal 31)) (.literal 32)),
            .ite (.lt (.localVar newLen) (.literal 32))
              [.assignVar newSlotCount (.literal 0)]
              [],
            .letVar clearCount (.sub (.localVar oldSlotCount) (.localVar newSlotCount)),
            .forEach clearIdx (.localVar clearCount) [
              .setStorageArrayElement name
                (.add (.add (.localVar cleanupDataSlot) (.localVar newSlotCount)) (.localVar clearIdx))
                (.literal 0)
            ] ]
          [] ]
      []
  ]
  let writeLongStmts : List Stmt := [
    .mstore (.literal 0) (.literal info.slot),
    .letVar writeDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar fullWords (.div (.localVar newLen) (.literal 32)),
    .forEach copyIdx (.localVar fullWords) [
      .setStorageArrayElement name
        (.add (.localVar writeDataSlot) (.localVar copyIdx))
        (.mload (.add (.localVar ptr) (.mul (.localVar copyIdx) (.literal 32))))
    ],
    .letVar remBytes (.bitAnd (.localVar newLen) (.literal 0x1f)),
    .ite (.gt (.localVar remBytes) (.literal 0))
      [ .letVar lastWord (.mload (.add (.localVar ptr) (.mul (.localVar fullWords) (.literal 32)))),
        .setStorageArrayElement name
          (.add (.localVar writeDataSlot) (.localVar fullWords))
          (maskDynamic (.localVar lastWord) (.localVar remBytes)) ]
      [],
    .setStorage name (.add (.mul (.localVar newLen) (.literal 2)) (.literal 1))
  ]
  let writeShortStmts : List Stmt := [
    .letVar shortWord (.literal 0),
    .ite (.gt (.localVar newLen) (.literal 0))
      [ .assignVar shortWord
          (maskDynamic (.mload (.localVar ptr)) (.localVar newLen)) ]
      [],
    .setStorage name (.bitOr (.localVar shortWord) (.mul (.localVar newLen) (.literal 2)))
  ]
  let stmts : Array Stmt := #[
    .letVar ptr buf.pointer,
    .letVar newLen buf.size,
    .ite (.gt (.localVar newLen) (.literal 0xffffffffffffffff))
      [.panicCode (.literal 0x41)]
      [],
    .letVar oldRaw (.storage name),
    .letVar oldOutOfPlace (.bitAnd (.localVar oldRaw) (.literal 1)),
    .letVar oldLen (.div (.localVar oldRaw) (.literal 2)),
    .ite (.eq (.localVar oldOutOfPlace) (.literal 0))
      [.assignVar oldLen (.bitAnd (.localVar oldLen) (.literal 0x7f))]
      [],
    .ite (.eq (.localVar oldOutOfPlace) shortCheck)
      [.panicCode (.literal 0x22)]
      []
  ] ++ cleanupStmts.toArray ++ #[
    .ite (.gt (.localVar newLen) (.literal 31))
      writeLongStmts
      writeShortStmts
  ]
  return pre ++ buf.pre ++ stmts

private partial def isAbiDecodeCall (j : Json) : M Bool := do
  let j ← stripParens j
  unless (← mKind j) == "FunctionCall" && optStr j "kind" == some "functionCall" do
    return false
  let callee ← mField j "expression"
  unless (← mKind callee) == "MemberAccess" && optStr callee "memberName" == some "decode" do
    return false
  let base ← mField callee "expression"
  if (← mKind base) == "Identifier" && optStr base "name" == some "abi" then
    return (← refInt base) == -1
  return false

private partial def parseAbiDecodeItem (comp : Json) : M AbiDecodeTypeItem := do
  let comp ← stripParens comp
  if comp.isNull then
    failAt comp "empty abi.decode type component"
  let rawTy ← mType comp
  unless rawTy.startsWith "type(" && rawTy.endsWith ")" do
    failAt comp s!"abi.decode requires a type argument, found {rawTy}"
  let innerRaw := ((rawTy.drop 5).dropEnd 1).toString
  let cleanTy :=
    if innerRaw.endsWith " storage pointer" then (innerRaw.dropEnd 16).toString
    else if innerRaw.endsWith " storage ref" then (innerRaw.dropEnd 12).toString
    else if innerRaw.endsWith " memory" then (innerRaw.dropEnd 7).toString
    else if innerRaw.endsWith " calldata" then (innerRaw.dropEnd 9).toString
    else innerRaw
  if cleanTy == "bytes" then
    return .dynamicBytes false
  if cleanTy == "string" then
    return .dynamicBytes true
  if cleanTy.endsWith "[]" then
    let some (elemStr, elemPty, abiKind) := scalarArrayElement? cleanTy
      | failAt comp s!"unsupported abi.decode array type {cleanTy}"
    return .scalarArray elemStr elemPty abiKind
  if cleanTy.startsWith "struct " && !cleanTy.contains "[" then
    let refId := (field? comp "referencedDeclaration").bind (fun v => v.getInt?.toOption) |>.getD (-1)
    let (sid, sDecl) ← do
      if refId ≥ 0 then
        if let some decl := (← get).structs.find? refId.toNat then
          pure (refId.toNat, decl)
        else
          let targetName := ((cleanTy.drop 7).toString.splitOn ".").getLastD ""
          match (← get).structs.toList.filter (fun (_, d) => optStr d "name" == some targetName) with
          | [x] => pure x
          | _ => failAt comp s!"unable to resolve struct declaration for {cleanTy}"
      else
        let targetName := ((cleanTy.drop 7).toString.splitOn ".").getLastD ""
        match (← get).structs.toList.filter (fun (_, d) => optStr d "name" == some targetName) with
        | [x] => pure x
        | _ => failAt comp s!"unable to resolve struct declaration for {cleanTy}"
    let sName ← mStr (← mField sDecl "name")
    let sMembers ← mArr (← mField sDecl "members")
    if sMembers.isEmpty then
      failAt comp "empty struct in abi.decode is unsupported"
    let mut members : Array (String × String) := #[]
    for mNode in sMembers do
      let mName ← mStr (← mField mNode "name")
      let mTy ← mType mNode
      unless !mTy.startsWith "enum " && (paramType mTy).isSome do
        failAt mNode s!"unsupported abi.decode struct member type {mTy}"
      members := members.push (mName, mTy)
    return .flatStruct sid sName members
  let refId := (field? comp "referencedDeclaration").bind (fun v => v.getInt?.toOption) |>.getD (-1)
  let scalarTy ← if refId ≥ 0 then
    if let some uTy := (← get).userValueTypeById.find? refId.toNat then
      pure uTy
    else
      pure cleanTy
  else
    pure cleanTy
  let enumBound? ← validateEnumTypeIfNeeded comp scalarTy
  let some pty := paramType scalarTy
    | failAt comp s!"unsupported abi.decode type {cleanTy}"
  return .scalar scalarTy pty enumBound?

private partial def lowerAbiDecodeDataSource (rawNode callee : Json) : M (Array Stmt × Bool × Expr × Expr) := do
  let inner ← unwrapBytesConversion (← stripParens rawNode)
  if (← mKind inner) == "Identifier" then
    let id ← refInt inner
    if id ≥ 0 then
      if let some cb := (← get).calldataBytes.find? id.toNat then
        let ptrVar ← fresh
        let lenVar ← fresh
        if cb.inMemory then
          return (#[
            .letVar ptrVar (.add (.localVar cb.memoryPointer) (.literal 32)),
            .letVar lenVar (.localVar cb.lengthBinding)
          ], false, .localVar ptrVar, .localVar lenVar)
        else
          return (#[
            .letVar ptrVar (.localVar cb.dataBinding),
            .letVar lenVar (.localVar cb.lengthBinding)
          ], true, .localVar ptrVar, .localVar lenVar)
      if let some buf := (← get).byteBuffers.find? id.toNat then
        let ptrVar ← fresh
        let lenVar ← fresh
        return (buf.pre ++ #[
          .letVar ptrVar buf.pointer,
          .letVar lenVar buf.size
        ], false, .localVar ptrVar, .localVar lenVar)
      if let some storageName ← storageBytesSourceVar? inner then
        let buf ← lowerStorageBytesRead storageName inner
        let ptrVar ← fresh
        let lenVar ← fresh
        return (buf.pre ++ #[
          .letVar ptrVar buf.pointer,
          .letVar lenVar buf.size
        ], false, .localVar ptrVar, .localVar lenVar)
  if (← mKind inner) == "MemberAccess" then
    if let some storageName ← storageBytesSourceVar? inner then
      let buf ← lowerStorageBytesRead storageName inner
      let ptrVar ← fresh
      let lenVar ← fresh
      return (buf.pre ++ #[
        .letVar ptrVar buf.pointer,
        .letVar lenVar buf.size
      ], false, .localVar ptrVar, .localVar lenVar)
    let innerTy ← mType inner
    if innerTy == "bytes" || innerTy == "bytes memory" || innerTy == "bytes calldata" then
      if (← mType (← mField inner "expression")).startsWith "struct " then
        if let .abiBytesField rootId memberIndex refPre ← lowerRef inner then
          let some mem := (← get).mems.find? rootId | failAt inner "unknown ABI root"
          let some schema := mem.schema | failAt inner "missing ABI schema"
          let some (.bytesField _) := schema[memberIndex]?
            | failAt inner "expected a schema-checked ABI bytes field"
          if mem.calldataLocation then
            let header ← fresh
            let length ← fresh
            let data ← fresh
            let checks := AbiLowering.calldataBytesFieldHead
              (.localVar (mem.abiStem ++ "_calldata")) memberIndex header length data
            return (refPre ++ checks.toArray, true, .localVar data, .localVar length)
          else
            let bytesPtr ← fresh
            let length ← fresh
            let dataPtr ← fresh
            let loadStmts : Array Stmt := #[
              .letVar bytesPtr (.mload (.add (.localVar (mem.abiStem ++ "_memory")) (.literal (32 * memberIndex)))),
              .letVar length (.mload (.localVar bytesPtr)),
              .letVar dataPtr (.add (.localVar bytesPtr) (.literal 32))
            ]
            return (refPre ++ loadStmts, false, .localVar dataPtr, .localVar length)
  failAt callee "abi.decode is outside this slice"

private partial def lowerAbiDecodeItems (j : Json) : M (Array Stmt × Array AbiDecodedValue) := do
  let j ← stripParens j
  unless ← isAbiDecodeCall j do
    failAt j "expected abi.decode call"
  let callee ← mField j "expression"
  let args ← mArr (← mField j "arguments")
  unless args.size == 2 do
    failAt j "abi.decode requires a byte buffer and a type tuple"
  let typeArg ← stripParens args[1]!
  let typeComps ← if (← mKind typeArg) == "TupleExpression" then do
    if ← mBool (← mField typeArg "isInlineArray") then
      failAt typeArg "inline arrays are outside this slice"
    mArr (← mField typeArg "components")
  else
    pure #[typeArg]
  if typeComps.isEmpty then
    failAt typeArg "abi.decode requires at least one target type"
  let mut items : Array AbiDecodeTypeItem := #[]
  for comp in typeComps do
    items := items.push (← parseAbiDecodeItem comp)
  let (srcPre, fromCalldata, basePtr, lenExpr) ← lowerAbiDecodeDataSource args[0]! callee
  let mut totalHeadSize : Nat := 0
  for item in items do
    match item with
    | .scalar _ _ _ | .scalarArray _ _ _ | .dynamicBytes _ =>
        totalHeadSize := totalHeadSize + 32
    | .flatStruct _ _ members =>
        totalHeadSize := totalHeadSize + 32 * members.size
  let mut pre := srcPre.push (AbiLowering.guard (.logicalNot (.lt lenExpr (.literal totalHeadSize))))
  let mut headCursor : Nat := 0
  let mut decoded : Array AbiDecodedValue := #[]
  let allocGuard (cond : Expr) : Stmt := .ite cond [] [.panicCode (.literal 0x41)]
  for item in items do
    match item with
    | .scalar ty pty enumBound? =>
        let wordVar ← fresh
        let wordAddr := if headCursor == 0 then basePtr else Expr.add basePtr (.literal headCursor)
        pre := pre.push (.letVar wordVar (readAbiDecodeWord fromCalldata wordAddr))
        if let some g := abiDecodeScalarGuard? ty enumBound? (.localVar wordVar) then
          pre := pre.push g
        decoded := decoded.push (.scalar ty pty (.localVar wordVar))
        headCursor := headCursor + 32
    | .flatStruct sid sName members =>
        let structPtr ← fresh
        let structFinish ← fresh
        modify fun e => { e with encodingMemory := true }
        pre := pre ++ (AbiEncoding.reserve structPtr structFinish (.literal (32 * members.size))).toArray
        let mut memberVals : Array (String × String × Expr) := #[]
        for mIdx in [:members.size] do
          let (mName, mTy) := members[mIdx]!
          let wordVar ← fresh
          let off := headCursor + 32 * mIdx
          let wordAddr := if off == 0 then basePtr else Expr.add basePtr (.literal off)
          pre := pre.push (.letVar wordVar (readAbiDecodeWord fromCalldata wordAddr))
          if let some g := abiDecodeScalarGuard? mTy none (.localVar wordVar) then
            pre := pre.push g
          pre := pre.push (.mstore (.add (.localVar structPtr) (.literal (32 * mIdx))) (.localVar wordVar))
          memberVals := memberVals.push (mName, mTy, .localVar wordVar)
        decoded := decoded.push (.flatStruct sid sName memberVals)
        headCursor := headCursor + 32 * members.size
    | .scalarArray elemStr elemPty abiKind =>
        let relOff ← fresh
        let arrHeader ← fresh
        let arrLen ← fresh
        let arrPtr ← fresh
        let nextFree ← fresh
        let arrData ← fresh
        let copyIdx ← fresh
        let elemVal ← fresh
        let headAddr := if headCursor == 0 then basePtr else Expr.add basePtr (.literal headCursor)
        modify fun e => { e with encodingMemory := true }
        pre := pre ++ #[
          .letVar relOff (readAbiDecodeWord fromCalldata headAddr),
          AbiLowering.guard (.le (.localVar relOff) (.literal (2 ^ 64 - 1))),
          AbiLowering.guard (.le (.add (.localVar relOff) (.literal 32)) lenExpr),
          .letVar arrHeader (.add basePtr (.localVar relOff)),
          .letVar arrLen (readAbiDecodeWord fromCalldata (.localVar arrHeader)),
          allocGuard (.le (.localVar arrLen) (.literal (2 ^ 64 - 1))),
          .letVar arrPtr (.mload (.literal 64)),
          .letVar nextFree (.add (.localVar arrPtr) (.mul (.literal 32) (.add (.localVar arrLen) (.literal 1)))),
          allocGuard (.le (.localVar nextFree) (.literal (2 ^ 64 - 1))),
          allocGuard (.ge (.localVar nextFree) (.localVar arrPtr)),
          .letVar arrData (.add (.localVar arrHeader) (.literal 32)),
          AbiLowering.guard (.le (.add (.add (.localVar relOff) (.literal 32)) (.mul (.literal 32) (.localVar arrLen))) lenExpr),
          .mstore (.localVar arrPtr) (.localVar arrLen),
          .mstore (.literal 64) (.localVar nextFree)
        ]
        let elemAddr := Expr.add (.localVar arrData) (.mul (.localVar copyIdx) (.literal 32))
        let bound := SolidityAbi.scalarBound abiKind
        let elemChecks : List Stmt :=
          if bound == 2 ^ 256 then []
          else [AbiLowering.guard (.lt (.localVar elemVal) (.literal bound))]
        let loopBody : List Stmt :=
          [ .letVar elemVal (readAbiDecodeWord fromCalldata elemAddr) ] ++
          elemChecks ++
          [ .mstore (.add (.add (.localVar arrPtr) (.literal 32)) (.mul (.localVar copyIdx) (.literal 32))) (.localVar elemVal) ]
        pre := pre.push (.forEach copyIdx (.localVar arrLen) loopBody)
        let desc : ScalarArrayParam := {
          param := arrPtr
          elementType := elemStr
          modelElementType := elemPty
          abiKind := abiKind
          inMemory := true
          lengthBinding := arrLen
          memoryPointer := arrPtr
        }
        decoded := decoded.push (.scalarArray elemStr elemPty abiKind desc)
        headCursor := headCursor + 32
    | .dynamicBytes isString =>
        let relOff ← fresh
        let byteHeader ← fresh
        let byteLen ← fresh
        let bytesPointer ← fresh
        let nextFree ← fresh
        let byteData ← fresh
        let copyIdx ← fresh
        let headAddr := if headCursor == 0 then basePtr else Expr.add basePtr (.literal headCursor)
        let alignedSize := Expr.bitAnd
          (.add (.add (.localVar byteLen) (.literal 32)) (.literal 31))
          (.bitNot (.literal 31))
        let wordCount := Expr.div (.add (.localVar byteLen) (.literal 31)) (.literal 32)
        modify fun e => { e with encodingMemory := true }
        pre := pre ++ #[
          .letVar relOff (readAbiDecodeWord fromCalldata headAddr),
          AbiLowering.guard (.le (.localVar relOff) (.literal (2 ^ 64 - 1))),
          AbiLowering.guard (.le (.add (.localVar relOff) (.literal 32)) lenExpr),
          .letVar byteHeader (.add basePtr (.localVar relOff)),
          .letVar byteLen (readAbiDecodeWord fromCalldata (.localVar byteHeader)),
          allocGuard (.le (.localVar byteLen) (.literal (2 ^ 64 - 1))),
          .letVar bytesPointer (.mload (.literal 64)),
          .letVar nextFree (.add (.localVar bytesPointer) alignedSize),
          allocGuard (.le (.localVar nextFree) (.literal (2 ^ 64 - 1))),
          allocGuard (.ge (.localVar nextFree) (.localVar bytesPointer)),
          .letVar byteData (.add (.localVar byteHeader) (.literal 32)),
          AbiLowering.guard (.le (.add (.add (.localVar relOff) (.literal 32)) (.localVar byteLen)) lenExpr),
          .mstore (.localVar bytesPointer) (.localVar byteLen),
          .mstore (.literal 64) (.localVar nextFree),
          .forEach copyIdx wordCount
            [.mstore (.add (.add (.localVar bytesPointer) (.literal 32)) (.mul (.localVar copyIdx) (.literal 32)))
              (readAbiDecodeWord fromCalldata (.add (.localVar byteData) (.mul (.localVar copyIdx) (.literal 32))))],
          .mstore (.add (.add (.localVar bytesPointer) (.literal 32)) (.localVar byteLen)) (.literal 0)
        ]
        let buf : EncodedBytes := {
          pre := #[]
          pointer := .add (.localVar bytesPointer) (.literal 32)
          size := .localVar byteLen
        }
        decoded := decoded.push (.dynamicBytes isString buf)
        headCursor := headCursor + 32
  return (pre, decoded)

private partial def lowerEncodedStaticStructWords (arg : Json) : M (Array Stmt × List Expr) := do
  let ty ← mType arg
  let (sid, sDecl) ← resolveStructDeclFromType arg
  let sMembers ← mArr (← mField sDecl "members")
  if sMembers.isEmpty then
    failAt arg s!"unsupported ABI encoding argument type {ty}"
  for mNode in sMembers do
    let mTy ← mType mNode
    unless !mTy.startsWith "enum " && (paramType mTy).isSome do
      failAt arg s!"unsupported ABI encoding argument type {ty}"
  checkEncodingStructArg arg
  let (_, _, sPre, memberVals) ← lowerFlatStructValue arg (some sid) true
  let mut pre : Array Stmt := sPre
  let mut words : List Expr := []
  for (_, _, expr) in memberVals do
    let v ← atom { pre := #[], expr }
    pre := pre ++ v.pre
    words := words ++ [v.expr]
  return (pre, words)

/-- Encode complete admitted byte schemas, without name-based library rules. -/
private partial def lowerEncodedBytes (j : Json) : M EncodedBytes := do
  if (← mKind j) == "Conditional" then
    let condNode ← mField j "condition"
    unless (← mType condNode) == "bool" do failAt condNode "conditional condition must be bool"
    let condVal ← atom (← lowerExpr condNode)
    let yesBuf ← lowerEncodedBytes (← mField j "trueExpression")
    let noBuf ← lowerEncodedBytes (← mField j "falseExpression")
    let ptr ← fresh
    let size ← fresh
    let yesStmts := yesBuf.pre ++ #[.assignVar ptr yesBuf.pointer, .assignVar size yesBuf.size]
    let noStmts := noBuf.pre ++ #[.assignVar ptr noBuf.pointer, .assignVar size noBuf.size]
    let stmts := condVal.pre ++ #[
      .letVar ptr (.literal 0),
      .letVar size (.literal 0),
      .ite condVal.expr yesStmts.toList noStmts.toList
    ]
    return { pre := stmts, pointer := .localVar ptr, size := .localVar size }
  if (← mKind j) == "Literal" then
    unless optStr j "kind" == some "hexString" || optStr j "kind" == some "string" ||
        optStr j "kind" == some "unicodeString" do
      failAt j "unsupported literal byte buffer"
    return ← lowerLiteralBytes j
  if (← mKind j) == "MemberAccess" && optStr j "memberName" == some "selector" then
    return ← lowerSelectorBytes j
  if (← mKind j) == "MemberAccess" && optStr j "memberName" == some "value" then
    if let some name ← storageBytesSourceVar? j then
      return ← lowerStorageBytesRead name j
  if (← mKind j) == "MemberAccess" &&
      ((← mType j) == "bytes" || (← mType j) == "bytes memory" || (← mType j) == "bytes calldata") then
    if (← mType (← mField j "expression")).startsWith "struct " then
      if let .abiBytesField id memberIndex pre ← lowerRef j then
        let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
        let some schema := mem.schema | failAt j "missing ABI schema"
        let some (.bytesField _) := schema[memberIndex]?
          | failAt j "expected a schema-checked ABI bytes field"
        if mem.calldataLocation then
          let header ← fresh
          let length ← fresh
          let data ← fresh
          let checks := AbiLowering.calldataBytesFieldHead
            (.localVar (mem.abiStem ++ "_calldata")) memberIndex header length data
          let pointer ← fresh
          let finish ← fresh
          let copyIdx ← fresh
          let wordCount := Expr.div (.add (.localVar length) (.literal 31)) (.literal 32)
          modify fun e => { e with encodingMemory := true }
          let alloc := AbiEncoding.reserve pointer finish (.mul (.literal 32) wordCount)
          let copyStmt := Stmt.forEach copyIdx wordCount
            [.mstore (.add (.localVar pointer) (.mul (.localVar copyIdx) (.literal 32)))
              (.calldataload (.add (.localVar data) (.mul (.localVar copyIdx) (.literal 32))))]
          return { pre := pre ++ checks.toArray ++ (alloc ++ [copyStmt]).toArray,
                   pointer := .localVar pointer, size := .localVar length }
        else
          let bytesPtr ← fresh
          let length ← fresh
          let loadStmts : Array Stmt := #[
            .letVar bytesPtr (.mload (.add (.localVar (mem.abiStem ++ "_memory")) (.literal (32 * memberIndex)))),
            .letVar length (.mload (.localVar bytesPtr))
          ]
          return { pre := pre ++ loadStmts,
                   pointer := .add (.localVar bytesPtr) (.literal 32),
                   size := .localVar length }
  if (← mKind j) == "Identifier" then
    let id ← refInt j
    if id ≥ 0 then
      if let some buffer := (← get).byteBuffers.find? id.toNat then
        return buffer
      if let some buffer := (← get).stringBuffers.find? id.toNat then
        return buffer
      if let some cb := (← get).calldataBytes.find? id.toNat then
        if cb.inMemory then
          return { pre := #[], pointer := .add (.localVar cb.memoryPointer) (.literal 32), size := .localVar cb.lengthBinding }
        else
          let pointer ← fresh
          let finish ← fresh
          let copyIdx ← fresh
          let wordCount := Expr.div (.add (.localVar cb.lengthBinding) (.literal 31)) (.literal 32)
          modify fun e => { e with encodingMemory := true }
          let alloc := AbiEncoding.reserve pointer finish (.mul (.literal 32) wordCount)
          let copyStmt := Stmt.forEach copyIdx wordCount
            [.mstore (.add (.localVar pointer) (.mul (.localVar copyIdx) (.literal 32)))
              (.calldataload (.add (.localVar cb.dataBinding) (.mul (.localVar copyIdx) (.literal 32))))]
          return { pre := (alloc ++ [copyStmt]).toArray, pointer := .localVar pointer, size := .localVar cb.lengthBinding }
      if let some name := (← get).storageBytesVars.find? id.toNat then
        return ← lowerStorageBytesRead name j
    let some decl := (← get).stateVars.find? id.toNat
      | failAt j "only literal constants are supported as named byte buffers"
    if (field? decl "constant").bind (fun value => value.getBool?.toOption) == some true then
      let value ← mField decl "value"
      unless (← mKind value) == "Literal" do
        failAt value "byte constant must have a literal initializer"
      return ← lowerEncodedBytes value
    if optStr decl "mutability" == some "immutable" then
      let name ← mStr (← mField decl "name")
      failAt j s!"immutable state variable {name} is outside this slice"
    let name ← mStr (← mField decl "name")
    let env ← get
    if env.duplicateLayoutLabels.contains name then
      failAt j s!"shadowed storage declaration {name} is outside this slice"
    if let some item := env.layoutItems.find? name then
      unless (← mNat (← mField item "astId")) == id.toNat do
        failAt j s!"shadowed storage declaration {name} is outside this slice"
    let info ← resolveField name j
    if info.bytesStorage then
      return ← lowerStorageBytesRead name j
    failAt j "mutable byte buffers are unsupported"
  unless (← mKind j) == "FunctionCall" do
    failAt j "hash input must be a supported ABI encoding"
  if optStr j "kind" == some "typeConversion" then
    let ty ← mType j
    if ty == "bytes" || ty == "bytes memory" || ty == "bytes calldata" || ty == "bytes storage pointer" ||
       ty == "string" || ty == "string memory" || ty == "string calldata" || ty == "string storage pointer" then
      let args ← mArr (← mField j "arguments")
      unless args.size == 1 do failAt j s!"{ty} conversion expects one argument"
      return ← lowerEncodedBytes args[0]!
  let callee ← mField j "expression"
  if optStr j "kind" == some "functionCall" && (← mKind callee) == "MemberAccess" then
    let base ← mField callee "expression"
    if (← mKind base) == "ElementaryTypeNameExpression" &&
        optStr callee "memberName" == some "concat" &&
        (field? callee "referencedDeclaration").isNone then
      let tname := optStr (field? base "typeName" |>.getD Json.null) "name" |>.getD ""
      let args ← mArr (← mField j "arguments")
      if tname == "bytes" then
        for arg in args do
          let argTy ← mType arg
          unless argTy == "bytes" || argTy == "bytes memory" || argTy == "bytes calldata" ||
              argTy == "bytes storage ref" || argTy == "bytes storage pointer" ||
              argTy == "bytes32" || argTy == "bytes4" || argTy.startsWith "literal_string " do
            failAt arg s!"unsupported bytes.concat argument type {argTy}"
        return ← lowerPacked args
      if tname == "string" then
        for arg in args do
          let argTy ← mType arg
          unless argTy == "string" || argTy == "string memory" || argTy == "string calldata" ||
              argTy == "string storage ref" || argTy == "string storage pointer" ||
              argTy.startsWith "literal_string " do
            failAt arg s!"unsupported string.concat argument type {argTy}"
        return ← lowerPacked args
  if optStr j "kind" == some "functionCall" then
    let isHelperCall :=
      ((← mKind callee) == "Identifier" || (← mKind callee) == "MemberAccess") &&
      ((field? callee "referencedDeclaration").bind (fun v => v.getInt?.toOption)).any (· ≥ 0)
    if isHelperCall then
      let ty ← mType j
      if ty == "string memory" || ty == "string" || ty == "bytes memory" || ty == "bytes" then
        let (fnId, vals) ← resolveCallTargetAndArgs j
        return ← inlineStringFn fnId vals j
  unless (← mKind callee) == "MemberAccess" do
    failAt callee "hash input must be a supported ABI encoding"
  let base ← mField callee "expression"
  let isAbiBuiltin ← if (← mKind base) == "Identifier" && optStr base "name" == some "abi" then
    pure ((← refInt base) == -1)
  else
    pure false
  unless isAbiBuiltin do
    failAt callee "encoding does not resolve to the abi builtin"
  let args ← mArr (← mField j "arguments")
  if optStr callee "memberName" == some "decode" then
    let (decodePre, decoded) ← lowerAbiDecodeItems j
    unless decoded.size == 1 do
      failAt j "abi.decode byte buffer expression requires a single bytes or string target type"
    let .dynamicBytes _ buf := decoded[0]!
      | failAt j "abi.decode byte buffer expression requires a bytes or string target type"
    return { pre := decodePre ++ buf.pre, pointer := buf.pointer, size := buf.size }
  if optStr callee "memberName" == some "encodePacked" then
    return ← lowerPacked args
  if optStr callee "memberName" == some "encodeWithSelector" then
    unless args.size ≥ 1 do
      failAt j "abi.encodeWithSelector requires a selector argument"
    let selBuffer ← lowerSelectorBytes args[0]!
    let mut pre := selBuffer.pre
    let mut words := []
    for arg in args.extract 1 args.size do
      let ty ← mType arg
      if ty.startsWith "struct " && !ty.contains "[" then
        let (sPre, sWords) ← lowerEncodedStaticStructWords arg
        pre := pre ++ sPre
        words := words ++ sWords
      else
        unless (paramType ty).isSome do
          failAt arg s!"unsupported ABI encoding argument type {ty}"
        checkEncodingScalar arg
        let value ← atom (← lowerExpr arg)
        pre := pre ++ value.pre
        words := words ++ [value.expr]
    return ← encodeSelectorAndWords selBuffer pre words
  if optStr callee "memberName" == some "encodeWithSignature" then
    unless args.size ≥ 1 do
      failAt j "abi.encodeWithSignature requires a signature argument"
    let sigNode := args[0]!
    let sigTy ← mType sigNode
    unless sigTy == "string" || sigTy == "string memory" || sigTy == "string calldata" ||
        sigTy == "string storage ref" || sigTy == "string storage pointer" ||
        sigTy.startsWith "literal_string " do
      failAt sigNode s!"unsupported abi.encodeWithSignature signature type {sigTy}"
    let sigBuf ← lowerEncodedBytes sigNode
    let selPtr ← fresh
    let selFinish ← fresh
    modify fun e => { e with encodingMemory := true }
    let selWord := Expr.bitAnd (.keccak256 sigBuf.pointer sigBuf.size) (.literal (0xffffffff * 16 ^ 56))
    let selBuffer : EncodedBytes :=
      { pre := sigBuf.pre ++ (AbiEncoding.staticWords selPtr selFinish [selWord]).toArray,
        pointer := .localVar selPtr,
        size := .literal 4 }
    let mut pre := selBuffer.pre
    let mut words := []
    for arg in args.extract 1 args.size do
      let ty ← mType arg
      if ty.startsWith "struct " && !ty.contains "[" then
        let (sPre, sWords) ← lowerEncodedStaticStructWords arg
        pre := pre ++ sPre
        words := words ++ sWords
      else
        unless (paramType ty).isSome do
          failAt arg s!"unsupported ABI encoding argument type {ty}"
        checkEncodingScalar arg
        let value ← atom (← lowerExpr arg)
        pre := pre ++ value.pre
        words := words ++ [value.expr]
    return ← encodeSelectorAndWords selBuffer pre words
  if optStr callee "memberName" == some "encodeCall" then
    unless args.size == 2 do
      failAt j "abi.encodeCall requires a function pointer and an argument tuple"
    let (decl, selBuffer) ← lowerMemberFunctionSelector args[0]!
    unless (← mKind decl) == "FunctionDefinition" do
      failAt args[0]! "abi.encodeCall target must be a function declaration"
    let params ← mArr (← mField (← mField decl "parameters") "parameters")
    let callArgs ← if (← mKind args[1]!) == "TupleExpression" then do
      if ← mBool (← mField args[1]! "isInlineArray") then
        failAt args[1]! "inline arrays are outside this slice"
      mArr (← mField args[1]! "components")
    else
      pure #[args[1]!]
    unless callArgs.size == params.size do
      failAt args[1]! s!"abi.encodeCall argument count {callArgs.size} does not match declaration {params.size}"
    let mut pre := selBuffer.pre
    let mut words := []
    for idx in [:params.size] do
      let p := params[idx]!
      let arg := callArgs[idx]!
      if arg.isNull then failAt args[1]! "empty abi.encodeCall tuple component"
      let pty ← mType p
      let argTy ← mType arg
      if pty.startsWith "struct " && !pty.contains "[" then
        let (pSid, pDecl) ← resolveStructDeclFromType p
        let pMembers ← mArr (← mField pDecl "members")
        if pMembers.isEmpty then
          failAt p s!"unsupported ABI encoding argument type {pty}"
        for mNode in pMembers do
          let mTy ← mType mNode
          unless !mTy.startsWith "enum " && (paramType mTy).isSome do
            failAt p s!"unsupported ABI encoding argument type {pty}"
        unless argTy.startsWith "struct " && !argTy.contains "[" do
          failAt arg s!"abi.encodeCall argument type {argTy} does not match parameter {pty}"
        let (argSid, _) ← resolveStructDeclFromType arg
        unless pSid == argSid do
          failAt arg s!"abi.encodeCall argument type {argTy} does not match parameter {pty}"
        let (sPre, sWords) ← lowerEncodedStaticStructWords arg
        pre := pre ++ sPre
        words := words ++ sWords
      else
        unless (paramType pty).isSome do
          failAt p s!"unsupported ABI encoding argument type {pty}"
        checkEncodingScalar arg
        let rawVal ← lowerExpr arg
        let converted ← convert pty argTy rawVal arg
        if let some b := bitsOf pty then
          if b < 256 && (argTy.startsWith "int_const" && !argTy.startsWith "int_const -") then
            if let .literal n := converted.expr then
              unless n < 2 ^ b do
                failAt arg s!"literal {n} exceeds width of {pty}"
        let value ← atom converted
        pre := pre ++ value.pre
        words := words ++ [value.expr]
    return ← encodeSelectorAndWords selBuffer pre words
  unless optStr callee "memberName" == some "encode" do
    failAt callee "unsupported ABI encoding builtin"
  if args.size == 1 then
    if (← mType args[0]!).startsWith "struct " && !(← mType args[0]!).contains "[" then
      let isMemRoot ← if (← mKind args[0]!) != "FunctionCall" && (← mKind args[0]!) != "Conditional" && (← mKind args[0]!) != "TupleExpression" then
        match ← lowerRef args[0]! with
        | .mem _ _ => pure true
        | _ => pure false
      else
        pure false
      if isMemRoot then
        return ← lowerEncodedRoot args[0]!
  let mut pre := #[]
  let mut words := []
  for arg in args do
    let ty ← mType arg
    if ty.startsWith "struct " && !ty.contains "[" then
      let (sPre, sWords) ← lowerEncodedStaticStructWords arg
      pre := pre ++ sPre
      words := words ++ sWords
    else
      unless (paramType ty).isSome do
        failAt arg s!"unsupported ABI encoding argument type {ty}"
      -- Avoid assigning an evaluation order to multiple effectful arguments.
      -- Scalar paths and casts have no source-level writes or custom reverts.
      checkEncodingScalar arg
      let raw ← lowerExpr arg
      let value ← if raw.pre.isEmpty then pure raw else atom raw
      pre := pre ++ value.pre
      words := words ++ [value.expr]
  let pointer ← fresh
  let finish ← fresh
  modify fun env => { env with encodingMemory := true }
  pre := pre ++ (AbiEncoding.staticWords pointer finish words).toArray
  return { pre, pointer := .localVar pointer, size := .literal (32 * words.length) }

private partial def resolveStorageDynamicArrayTarget (ref : Ref) (at_ : Json) :
    M (Option (Array Stmt × String × Expr × String × ParamType × SolidityAbi.ScalarKind × Option Nat)) := do
  match ref with
  | .state name pre =>
      let info ← resolveField name at_
      if let some (elemTy, modelElemTy, abiKind) := info.dynamicArrayElemType then
        return some (pre, name, .literal info.slot, elemTy, modelElemTy, abiKind, info.dynamicArrayStructId)
      return none
  | .structDynamicArray pre path dynInfo =>
      if let .rawSlot _ baseSlot := path then
        let slotExpr := rawStructMemberSlot baseSlot dynInfo.wordOffset
        return some (pre, "", slotExpr, dynInfo.elemType, dynInfo.modelElemType, dynInfo.abiKind, dynInfo.elemStructId)
      else
        let rawName ← match path with
          | .zero name | .one name _ | .two name _ _ => pure name
          | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
              failAt at_ "struct dynamic array requires all outer mapping keys"
        let (name, _) := splitSPathField rawName
        let info ← resolveField name at_
        markField name
        markStructDynamicArray name dynInfo.member
        let (slotStmts, slotExpr) ← computeSPathBaseSlot path info dynInfo.wordOffset at_
        return some (pre ++ slotStmts, "", slotExpr, dynInfo.elemType, dynInfo.modelElemType, dynInfo.abiKind, dynInfo.elemStructId)
  | _ => return none

private partial def lowerCallArgs (j : Json) (receiver? : Option Json) : M (Array CallArg) := do
  let args ← mArr (← mField j "arguments")
  let nodes := match receiver? with
    | some recv => #[recv] ++ args
    | none => args
  let mut vals : Array CallArg := #[]
  for arg in nodes do
    if statefulCallIn arg (← get) then
      failAt arg "stateful helper call arguments require explicit evaluation-order support"
    if nodes.size > 1 && assignmentIn arg then
      failAt arg "assignment expression in multi-argument call requires explicit evaluation-order support"
    let argTy ← mType arg
    if argTy.startsWith "struct " && !argTy.contains "[" then
      if (← mKind arg) == "FunctionCall" &&
          (optStr arg "kind" == some "structConstructorCall" ||
           (optStr arg "kind" == some "functionCall" && argTy.endsWith " memory")) then
        let (sid, sName, initPre, memberVals) ← lowerFlatStructValue arg none false
        vals := vals.push (.flatStruct sid sName memberVals initPre)
      else
        match ← lowerRef arg with
        | .mem id pre =>
            let some descriptor := (← get).mems.find? id
              | failAt arg "unknown reference argument"
            vals := vals.push (.memory descriptor pre)
        | .abiElement rootId memberIndex pointer inMemory pre =>
            vals := vals.push (.abiElement { rootId, memberIndex, pointer, inMemory } pre)
        | .flatStruct _ =>
            let (sid, sName, initPre, memberVals) ← lowerFlatStructValue arg none true
            vals := vals.push (.flatStruct sid sName memberVals initPre)
        | .path pre path =>
            let (sid, _) ← resolveStructDeclFromType arg
            let capture (key : Expr) : M (Array Stmt × Expr) := do
              let env ← get
              let writable := match key with
                | .localVar name => env.writableLocals.toList.any (fun (_, b) => b == name)
                | _ => false
              if !writable then
                return (#[], key)
              let binding ← fresh
              pure (#[.letVar binding key], .localVar binding)
            match path with
            | .rawSlot rawSid slot =>
                unless rawSid == sid do
                  failAt arg "raw storage slot struct argument declaration differs"
                let (spre, frozenSlot) ← capture slot
                vals := vals.push (.storagePath sid (.rawSlot rawSid frozenSlot) (pre ++ spre))
            | .bytesSlot fieldName isString =>
                vals := vals.push (.storagePath sid (.bytesSlot fieldName isString) pre)
            | .zero rawField =>
                let (field, _) := splitSPathField rawField
                let info ← resolveField field arg
                unless !info.scalarMapping && info.fixedArrayLength.isNone && info.keyCount == 0 do
                  failAt arg "storage struct argument requires a struct storage path"
                vals := vals.push (.storagePath sid (.zero rawField) pre)
            | .one rawField key =>
                let (field, _) := splitSPathField rawField
                let info ← resolveField field arg
                unless !info.scalarMapping && info.fixedArrayLength.isNone && info.keyCount == 1 do
                  failAt arg "storage struct argument requires a struct storage path"
                let (kpre, k) ← capture key
                vals := vals.push (.storagePath sid (.one rawField k) (pre ++ kpre))
            | .two rawField key1 key2 =>
                let (field, _) := splitSPathField rawField
                let info ← resolveField field arg
                unless !info.scalarMapping && info.fixedArrayLength.isNone && info.keyCount == 2 do
                  failAt arg "storage struct argument requires a struct storage path"
                let (kpre1, k1) ← capture key1
                let (kpre2, k2) ← capture key2
                vals := vals.push (.storagePath sid (.two rawField k1 k2) (pre ++ kpre1 ++ kpre2))
            | .outer _ _ =>
                failAt arg "storage struct argument requires all mapping keys"
        | _ => failAt arg "only root memory/calldata struct arguments are supported"
    else if argTy.startsWith "struct " && argTy.contains "[]" then
      let ref ← lowerRef arg
      if let some (pre, fieldName, slotExpr, elemTy, _, _, some elemSid) ← resolveStorageDynamicArrayTarget ref arg then
        let (spre, frozenSlot) ← do
          let env ← get
          let writable := match slotExpr with
            | .localVar name => env.writableLocals.toList.any (fun (_, b) => b == name)
            | _ => false
          if !writable then pure (#[], slotExpr)
          else do
            let binding ← fresh
            pure (#[.letVar binding slotExpr], .localVar binding)
        vals := vals.push (.storageDynamicArray fieldName frozenSlot elemTy (some elemSid) (pre ++ spre))
      else
        failAt arg "only storage struct dynamic array arguments are supported"
    else if let some (elemStr, _, _) := scalarArrayElement? argTy then
      if ← isAbiDecodeCall arg then
        let (decodePre, decoded) ← lowerAbiDecodeItems arg
        unless decoded.size == 1 do
          failAt arg "array abi.decode argument requires a single array target type"
        let .scalarArray decElemStr _ _ desc := decoded[0]!
          | failAt arg "array abi.decode argument requires a dynamic scalar array target type"
        unless decElemStr == elemStr do
          failAt arg "dynamic memory array argument type differs from declaration"
        vals := vals.push (.scalarArray desc decodePre)
      else
        let isArrayHelperCall ← if (← mKind arg) == "FunctionCall" && optStr arg "kind" == some "functionCall" then
          pure ((← mKind (← mField arg "expression")) != "NewExpression")
        else
          pure false
        if isArrayHelperCall then
          let (fnId, innerVals) ← resolveCallTargetAndArgs arg
          let (arrPre, desc) ← inlineArrayFn fnId innerVals elemStr arg
          vals := vals.push (.scalarArray desc arrPre)
        else
          let ref ← lowerRef arg
          if let .scalarArray id pre := ref then
            let some descriptor := (← get).scalarArrays.find? id
              | failAt arg "unknown scalar array argument"
            vals := vals.push (.scalarArray descriptor pre)
          else if let some (pre, fieldName, slotExpr, elemTy, _, _, none) ← resolveStorageDynamicArrayTarget ref arg then
            let (spre, frozenSlot) ← do
              let env ← get
              let writable := match slotExpr with
                | .localVar name => env.writableLocals.toList.any (fun (_, b) => b == name)
                | _ => false
              if !writable then pure (#[], slotExpr)
              else do
                let binding ← fresh
                pure (#[.letVar binding slotExpr], .localVar binding)
            vals := vals.push (.storageDynamicArray fieldName frozenSlot elemTy none (pre ++ spre))
          else
            failAt arg "only scalar array parameter arguments are supported"
    else if argTy == "string" || argTy == "string memory" || argTy == "string calldata" ||
            argTy == "string storage ref" || argTy == "string storage pointer" ||
            argTy.startsWith "literal_string " then
      if (← mKind arg) == "Identifier" then
        let id ← refInt arg
        if id ≥ 0 then
          if let some cb := (← get).calldataBytes.find? id.toNat then
            if !cb.inMemory then
              vals := vals.push (.calldataBytes cb #[])
              continue
      if let some storageName ← storageBytesSourceVar? arg then
        vals := vals.push (.storageBytes storageName true)
        continue
      let buf ← lowerEncodedBytes arg
      vals := vals.push (.stringBuffer buf)
    else if argTy == "bytes" || argTy == "bytes memory" || argTy == "bytes calldata" ||
            argTy == "bytes storage ref" || argTy == "bytes storage pointer" then
      if (← mKind arg) == "Identifier" then
        let id ← refInt arg
        if id ≥ 0 then
          if let some cb := (← get).calldataBytes.find? id.toNat then
            if !cb.inMemory then
              vals := vals.push (.calldataBytes cb #[])
              continue
      if let some storageName ← storageBytesSourceVar? arg then
        vals := vals.push (.storageBytes storageName false)
        continue
      let buf ← lowerEncodedBytes arg
      vals := vals.push (.byteBuffer buf)
    else if argTy.startsWith "function (" then
      let (fpre, ptr) ← lowerFnPtrInit arg
      vals := vals.push (.fnPtr ptr fpre)
    else
      vals := vals.push (.scalar (← lowerExpr arg))
  pure vals

private partial def atomizeCallArgs (vals : Array CallArg) : M (Array Stmt × Array CallArg) := do
  let mut pre : Array Stmt := #[]
  let mut out : Array CallArg := #[]
  for val in vals do
    match val with
    | .scalar v =>
        let a ← atom v
        pre := pre ++ a.pre
        out := out.push (.scalar { pre := #[], expr := a.expr })
    | .memory desc mpre =>
        pre := pre ++ mpre
        out := out.push (.memory desc #[])
    | .abiElement bound epre =>
        let ptrAtom ← atom { pre := epre, expr := bound.pointer }
        pre := pre ++ ptrAtom.pre
        out := out.push (.abiElement { bound with pointer := ptrAtom.expr } #[])
    | .scalarArray desc apre =>
        pre := pre ++ apre
        out := out.push (.scalarArray desc #[])
    | .byteBuffer buf =>
        let ptrBinding ← fresh
        let sizeBinding ← fresh
        pre := pre ++ buf.pre ++ #[.letVar ptrBinding buf.pointer, .letVar sizeBinding buf.size]
        out := out.push (.byteBuffer { pre := #[], pointer := .localVar ptrBinding, size := .localVar sizeBinding })
    | .stringBuffer buf =>
        let ptrBinding ← fresh
        let sizeBinding ← fresh
        pre := pre ++ buf.pre ++ #[.letVar ptrBinding buf.pointer, .letVar sizeBinding buf.size]
        out := out.push (.stringBuffer { pre := #[], pointer := .localVar ptrBinding, size := .localVar sizeBinding })
    | .calldataBytes desc cpre =>
        pre := pre ++ cpre
        out := out.push (.calldataBytes desc #[])
    | .storagePath sid path spre =>
        pre := pre ++ spre
        out := out.push (.storagePath sid path #[])
    | .flatStruct sid sName members fpre =>
        pre := pre ++ fpre
        out := out.push (.flatStruct sid sName members #[])
    | .storageBytes fieldName isString =>
        out := out.push (.storageBytes fieldName isString)
    | .storageDynamicArray fieldName slotExpr elemTy elemSid? spre =>
        let slotAtom ← atom { pre := spre, expr := slotExpr }
        pre := pre ++ slotAtom.pre
        out := out.push (.storageDynamicArray fieldName slotAtom.expr elemTy elemSid? #[])
    | .fnPtr ptr fpre =>
        pre := pre ++ fpre
        out := out.push (.fnPtr ptr #[])
  pure (pre, out)

private partial def resolveFnPtrTarget (j : Json) : M Nat := do
  match ← mKind j with
  | "Identifier" =>
      let id ← refInt j
      if id < 0 then failAt j "builtin function pointers are outside this slice"
      let env ← get
      if let some (.direct fnId) := env.fnPtrs.find? id.toNat then
        return fnId
      if env.fnPtrs.contains id.toNat then
        failAt j "nested conditional function pointers are outside this slice"
      unless env.funs.contains id.toNat do
        failAt j "function pointer initializer does not resolve to an internal function"
      let resolvedId ← match env.funContractId.find? id.toNat with
        | some cid =>
            if env.linearizedBases.contains cid then
              match resolveInContracts env env.linearizedBases.toList id.toNat with
              | some rid => pure rid
              | none => failAt j s!"unresolved inherited function {id.toNat}"
            else
              pure id.toNat
        | none => pure id.toNat
      let some fn := env.funs.find? resolvedId | failAt j s!"unresolved function {resolvedId}"
      let vis := optStr fn "visibility" |>.getD ""
      unless vis == "internal" || vis == "private" || vis == "public" do
        failAt j "function pointer target must be an internal, private, or public function"
      pure resolvedId
  | "MemberAccess" =>
      let base ← mField j "expression"
      let id ← refInt j
      if id < 0 then failAt j "builtin function pointers are outside this slice"
      let baseTy ← mType base
      if baseTy.startsWith "type(library " then
        let some fn := (← get).funs.find? id.toNat | failAt j s!"unresolved function {id.toNat}"
        let vis := optStr fn "visibility" |>.getD ""
        unless vis == "internal" || vis == "private" do
          failAt j "external library function pointers are outside this slice"
        pure id.toNat
      else if baseTy.startsWith "type(contract super " then
        let isSuper ← if (← mKind base) == "Identifier" && optStr base "name" == some "super" then
          pure ((← refInt base) == -25)
        else
          pure false
        unless isSuper do failAt base "invalid super callee"
        let env ← get
        let some callerFnId := env.stack.head? | failAt j "super reference outside function context"
        let some callerCid := env.funContractId.find? callerFnId | failAt j "super reference outside contract function"
        let some idx := env.linearizedBases.findIdx? (· == callerCid) | failAt j "enclosing contract is outside target inheritance chain"
        let superBases := (env.linearizedBases.extract (idx + 1) env.linearizedBases.size).toList
        let some resolvedId := resolveInContracts env superBases id.toNat | failAt j s!"unresolved super function {id.toNat}"
        pure resolvedId
      else if baseTy.startsWith "type(contract " then
        unless (← mKind base) == "Identifier" do failAt base "qualified base function reference requires a contract identifier"
        let baseCid ← refInt base
        let env ← get
        unless baseCid ≥ 0 && env.linearizedBases.contains baseCid.toNat do
          failAt base "qualified function reference contract is not a base of the target contract"
        unless env.funContractId.find? id.toNat == some baseCid.toNat do
          failAt j "qualified function reference is not declared in the named base contract"
        pure id.toNat
      else
        failAt j "external or bound function pointers are outside this slice"
  | _ => failAt j "unsupported function pointer initializer"

private partial def lowerFnPtrInit (j : Json) : M (Array Stmt × FnPtr) := do
  if (← mKind j) == "Conditional" then
    let condNode ← mField j "condition"
    unless (← mType condNode) == "bool" do failAt condNode "conditional condition must be bool"
    let condVal ← lowerExpr condNode
    let condBinding ← fresh
    let trueFnId ← resolveFnPtrTarget (← mField j "trueExpression")
    let falseFnId ← resolveFnPtrTarget (← mField j "falseExpression")
    let pre := condVal.pre.push (.letVar condBinding condVal.expr)
    pure (pre, .branch (.localVar condBinding) trueFnId falseFnId)
  else if (← mKind j) == "Identifier" then
    let id ← refInt j
    if id ≥ 0 then
      if let some ptr := (← get).fnPtrs.find? id.toNat then
        return (#[], ptr)
    let fnId ← resolveFnPtrTarget j
    pure (#[], .direct fnId)
  else
    let fnId ← resolveFnPtrTarget j
    pure (#[], .direct fnId)

private partial def resolveCallTargetAndArgs (j : Json) : M (Nat × Array CallArg) := do
  let names ← mArr (← mField j "names")
  unless names.isEmpty do failAt j "named call arguments are outside this slice"
  let callee ← mField j "expression"
  let (fnId, receiver?) ← match ← mKind callee with
    | "FunctionCallOptions" =>
        failAt callee "external contract calls are outside this slice"
    | "MemberAccess" =>
        let base ← mField callee "expression"
        let baseTy ← mType base
        if (← mKind base) == "Identifier" && optStr base "name" == some "abi" then
          if (← refInt base) == -1 then
            let member := optStr callee "memberName" |>.getD ""
            if member == "decode" then
              failAt callee "abi.decode is outside this slice"
            else
              failAt callee s!"abi.{member} is only supported as a byte buffer"
        if (← mKind base) == "ElementaryTypeNameExpression" &&
            optStr callee "memberName" == some "concat" &&
            (field? callee "referencedDeclaration").isNone then
          let tname := optStr (field? base "typeName" |>.getD Json.null) "name" |>.getD ""
          if tname == "bytes" || tname == "string" then
            failAt callee s!"{tname}.concat is only supported as a byte buffer"
        if (field? callee "referencedDeclaration").isNone then
          let member := optStr callee "memberName" |>.getD ""
          if (baseTy == "address" || baseTy == "address payable" || baseTy.startsWith "contract ") &&
              ["call", "staticcall", "delegatecall", "transfer", "send"].contains member then
            failAt callee "external contract calls are outside this slice"
          if ["push", "pop"].contains member then
            failAt callee s!"storage array {member} is outside this slice"
        let id ← refInt callee
        if id < 0 then failAt callee "builtin call is outside this slice"
        if baseTy.startsWith "type(library " then
          pure (id.toNat, none)
        else if baseTy.startsWith "type(contract super " then
          let isSuper ← if (← mKind base) == "Identifier" && optStr base "name" == some "super" then
            pure ((← refInt base) == -25)
          else
            pure false
          unless isSuper do
            failAt base "invalid super callee"
          let env ← get
          let some callerFnId := env.stack.head?
            | failAt callee "super call outside function context"
          let some callerCid := env.funContractId.find? callerFnId
            | failAt callee "super call outside contract function"
          let some idx := env.linearizedBases.findIdx? (· == callerCid)
            | failAt callee "enclosing contract is outside target inheritance chain"
          let superBases := (env.linearizedBases.extract (idx + 1) env.linearizedBases.size).toList
          let some resolvedId := resolveInContracts env superBases id.toNat
            | failAt callee s!"unresolved super function {id.toNat}"
          pure (resolvedId, none)
        else if baseTy.startsWith "type(contract " then
          unless (← mKind base) == "Identifier" do
            failAt base "qualified base call requires a contract identifier"
          let baseCid ← refInt base
          let env ← get
          unless baseCid ≥ 0 && env.linearizedBases.contains baseCid.toNat do
            failAt base "qualified call contract is not a base of the target contract"
          unless env.funContractId.find? id.toNat == some baseCid.toNat do
            failAt callee "qualified call function is not declared in the named base contract"
          pure (id.toNat, none)
        else
          pure (id.toNat, some base)
    | "Identifier" =>
        let id ← refInt callee
        if id < 0 then failAt callee "builtin call is outside this slice"
        let env ← get
        let resolvedId ← match env.funContractId.find? id.toNat with
          | some cid =>
              if env.linearizedBases.contains cid then
                match resolveInContracts env env.linearizedBases.toList id.toNat with
                | some rid => pure rid
                | none => failAt callee s!"unresolved inherited function {id.toNat}"
              else
                pure id.toNat
          | none => pure id.toNat
        pure (resolvedId, none)
    | _ => failAt callee "unsupported callee"
  if receiver?.isSome then
    let env ← get
    let isLibrary := match env.funContractId.find? fnId with
      | some cid => env.contractKinds.find? cid == some "library"
      | none => false
    unless isLibrary do
      failAt callee "external contract calls are outside this slice"
  let vals ← lowerCallArgs j receiver?
  pure (fnId, vals)

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
    if (← mKind callee) == "Identifier" then
      let calleeId ← refInt callee
      if calleeId == -8 then
        let args ← mArr (← mField j "arguments")
        unless args.size == 1 do failAt j "keccak256 requires one byte buffer"
        let bytes ← lowerEncodedBytes args[0]!
        return { pre := bytes.pre, expr := .keccak256 bytes.pointer bytes.size }
      if calleeId == -2 || calleeId == -16 then
        let isMul := calleeId == -16
        let bname := if isMul then "mulmod" else "addmod"
        unless optStr callee "name" == some bname &&
            (← mType callee) == "function (uint256,uint256,uint256) pure returns (uint256)" do
          failAt callee s!"{bname} must resolve to the global uint256 builtin"
        let args ← mArr (← mField j "arguments")
        unless args.size == 3 do failAt j s!"{bname} requires three uint256 arguments"
        let mut pre : Array Stmt := #[]
        let mut argExprs : Array Expr := #[]
        for modArg in args do
          if statefulCallIn modArg (← get) then
            failAt modArg s!"stateful {bname} arguments require explicit evaluation-order support"
          if assignmentIn modArg then
            failAt modArg s!"assignment expression in {bname} requires explicit evaluation-order support"
          let converted ← convert "uint256" (← mType modArg) (← lowerExpr modArg) modArg
          let bound ← atom converted
          pre := pre ++ bound.pre
          argExprs := argExprs.push bound.expr
        let #[a, b, m] := argExprs
          | failAt j s!"{bname} requires three uint256 arguments"
        let modCheck : Stmt := .ite (.eq m (.literal 0)) [.panic .divisionByZero] []
        let modVal ← if isMul then lowerYulMulmod a b m else lowerYulAddmod a b m
        return { pre := pre.push modCheck ++ modVal.pre, expr := modVal.expr }
      if calleeId ≥ 0 then
        if let some ptr := (← get).fnPtrs.find? calleeId.toNat then
          let vals ← lowerCallArgs j none
          match ptr with
          | .direct fnId => return ← inlineFn fnId vals j
          | .branch cond trueFnId falseFnId =>
              let (argPre, atomicVals) ← atomizeCallArgs vals
              let yesVal ← inlineFn trueFnId atomicVals j
              let noVal ← inlineFn falseFnId atomicVals j
              let dest ← fresh
              let thenB := yesVal.pre.push (.assignVar dest yesVal.expr)
              let elseB := noVal.pre.push (.assignVar dest noVal.expr)
              return { pre := argPre.push (.letVar dest (.literal 0)) |>.push (.ite cond thenB.toList elseB.toList),
                       expr := .localVar dest }
    if (← mKind callee) == "MemberAccess" && (field? callee "referencedDeclaration").isNone then
      let mname := optStr callee "memberName" |>.getD ""
      if mname == "push" || mname == "pop" then
        let base ← mField callee "expression"
        let baseRef ← lowerRef base
        if let some (pre, fieldName, slotExpr, elemTy, _, _, elemSid?) ← resolveStorageDynamicArrayTarget baseRef base then
          if elemSid?.isSome then
            failAt j s!"storage struct array {mname} cannot be used as a scalar value"
          let args ← mArr (← mField j "arguments")
          if mname == "push" then
            if args.isEmpty then
              return ← pushStorageDynamicArray pre fieldName slotExpr elemTy none
            else if args.size == 1 then
              let arg := args[0]!
              if !pre.isEmpty && (statefulCallIn arg (← get) || assignmentIn arg) then
                failAt arg "storage array push prelude with stateful argument is unsupported"
              let val ← atom (← convert elemTy (← mType arg) (← lowerExpr arg) arg)
              return ← pushStorageDynamicArray (pre ++ val.pre) fieldName slotExpr elemTy (some val.expr)
            else
              failAt j "storage array push expects at most one argument"
          else
            failAt j "storage array pop does not return a value"
        failAt callee s!"storage array {mname} is outside this slice"
      if mname == "wrap" || mname == "unwrap" then
        let base ← mField callee "expression"
        let baseRef := (field? base "referencedDeclaration").bind (fun v => v.getInt?.toOption) |>.getD (-1)
        if baseRef ≥ 0 then
          if let some uTy := (← get).userValueTypeById.find? baseRef.toNat then
            unless (paramType uTy).isSome && !uTy.startsWith "enum " do
              failAt callee s!"unsupported user-defined value type underlying type {uTy}"
            let args ← mArr (← mField j "arguments")
            unless args.size == 1 do
              failAt j s!"{mname} requires one argument"
            let arg := args[0]!
            return ← convert uTy (← mType arg) (← lowerExpr arg) arg
    if ← isAbiDecodeCall j then
      let (decodePre, decoded) ← lowerAbiDecodeItems j
      unless decoded.size == 1 do
        failAt j "scalar abi.decode expression requires a single scalar target type"
      let .scalar _ _ expr := decoded[0]!
        | failAt j "scalar abi.decode expression requires a scalar target type"
      return { pre := decodePre, expr }
    let (fnId, vals) ← resolveCallTargetAndArgs j
    inlineFn fnId vals j
  else
    failAt j s!"unsupported call kind {kind}"

private partial def bindHelperParams (params : Array Json) (args : Array CallArg) (body : Json) (at_ : Json)
    (savedYul : RBMap String Expr compare) : M (Array Stmt × RBMap String Expr compare) := do
  let mut pre : Array Stmt := #[]
  let mut yul := savedYul
  for i in [:params.size] do
    let p := params[i]!
    let pname ← mStr (← mField p "name")
    let pid ← mNat (← mField p "id")
    let pty ← mType p
    discard (validateEnumTypeIfNeeded p pty)
    let argNode ← argumentAt at_ i
    let argTy ← mType argNode
    let some arg := args[i]? | failAt at_ s!"missing argument {i}"
    if pname != "" then
      modify fun e => { e with yulMemoryArrays := e.yulMemoryArrays.erase pname }
    match arg with
    | .scalar value =>
        let converted ← convert pty argTy value at_
        if (bodyCompoundAssignedIds body).contains pid || (bodyDirectAssignedIds body).contains pid then
          let some scalar := paramType pty
            | failAt p s!"unsupported writable helper parameter type {pty}"
          let binding ← freshFor (if pname == "" then "param" else pname)
          let expr := Expr.localVar binding
          pre := pre ++ converted.pre |>.push (.letVar binding converted.expr)
          modify fun e =>
            { e with values := e.values.insert pid expr,
                     writableLocals := e.writableLocals.insert pid binding,
                     scalarTy := e.scalarTy.insert pid scalar }
          if pname != "" then
            yul := yul.insert pname expr
        else
          let bound ← atom converted
          pre := pre ++ bound.pre
          modify fun e => { e with values := e.values.insert pid bound.expr }
          if pname != "" then
            yul := yul.insert pname bound.expr
    | .memory descriptor effects =>
        unless pty.startsWith "struct " && !pty.contains "[" do
          failAt p "reference argument requires a struct parameter"
        let sid ← refInt (← mField p "typeName")
        unless sid >= 0 && sid.toNat == descriptor.structId do
          failAt p "reference argument struct declaration differs"
        let location := optStr p "storageLocation" |>.getD "default"
        let expected := if descriptor.calldataLocation then "calldata" else "memory"
        if descriptor.calldataLocation && location == "memory" && descriptor.schema.isSome then
          let (convStmts, memDesc) ← convertStructCalldataToMemory descriptor p
          pre := pre ++ effects ++ convStmts
          modify fun e => { e with mems := e.mems.insert pid memDesc }
        else if location == expected then
          pre := pre ++ effects
          modify fun e => { e with mems := e.mems.insert pid descriptor }
        else
          failAt p "reference argument location conversion is unsupported"
        if pname != "" then
          yul := yul.erase pname
    | .abiElement bound effects =>
        unless pty.startsWith "struct " && !pty.contains "[" do
          failAt p "reference argument requires a struct parameter"
        let sid ← refInt (← mField p "typeName")
        let some mem := (← get).mems.find? bound.rootId | failAt p "unknown ABI root"
        let some schema := mem.schema | failAt p "missing ABI schema"
        let some (.structArray _ fields) := schema[bound.memberIndex]?
          | failAt p "expected a struct-array element"
        let some parentDecl := (← get).structs.find? mem.structId
          | failAt p "unknown parent struct"
        let parentMembers ← mArr (← mField parentDecl "members")
        let some memberNode := parentMembers[bound.memberIndex]?
          | failAt p "missing parent struct member"
        let elemSid ← refInt (← mField (← mField memberNode "typeName") "baseType")
        unless sid >= 0 && elemSid >= 0 && elemSid.toNat == sid.toNat do
          failAt p "reference argument struct declaration differs"
        let location := optStr p "storageLocation" |>.getD "default"
        if location == "calldata" then
          unless !bound.inMemory do
            failAt p "reference argument location conversion is unsupported"
          let ptrAtom ← atom { pre := #[], expr := bound.pointer }
          let elemBound : AbiElementLocal := { bound with pointer := ptrAtom.expr, inMemory := false }
          pre := pre ++ effects ++ ptrAtom.pre
          modify fun e => { e with abiElements := e.abiElements.insert pid elemBound }
        else if location == "memory" then
          if !bound.inMemory then
            let ptrAtom ← atom { pre := #[], expr := bound.pointer }
            let elemStem ← freshAbiElementStem fields
            let (matPtr, _, matStmts) := AbiRootLowering.materializeElementFromCalldata ptrAtom.expr elemStem fields
            let elemBound : AbiElementLocal := { bound with pointer := .localVar matPtr, inMemory := true }
            pre := pre ++ effects ++ ptrAtom.pre ++ matStmts.toArray
            modify fun e =>
              { e with abiElements := e.abiElements.insert pid elemBound,
                       encodingMemory := true }
          else
            let ptrAtom ← atom { pre := #[], expr := bound.pointer }
            let elemBound : AbiElementLocal := { bound with pointer := ptrAtom.expr, inMemory := true }
            pre := pre ++ effects ++ ptrAtom.pre
            modify fun e => { e with abiElements := e.abiElements.insert pid elemBound }
        else
          failAt p "reference argument location conversion is unsupported"
        if pname != "" then
          yul := yul.erase pname
    | .scalarArray descriptor effects =>
        let some (elemStr, _, _) := scalarArrayElement? pty
          | failAt p "scalar array argument requires a scalar array parameter"
        unless elemStr == descriptor.elementType do
          failAt p "scalar array element type differs"
        let location := optStr p "storageLocation" |>.getD "default"
        if !descriptor.inMemory && location == "memory" then
          let arrayPtr ← fresh
          let nextFree ← fresh
          let namePrefix ← fresh
          for reserved in [s!"{namePrefix}_index"] do
            if (← get).sourceNames.contains reserved then
              failAt p s!"generated ABI helper name {reserved} collides with a source identifier"
            modify fun e => { e with bound := reserved :: e.bound }
          let convStmts := AbiLowering.materializeCalldataScalarArray
            (.localVar descriptor.dataBinding) (.localVar descriptor.lengthBinding)
            arrayPtr nextFree namePrefix descriptor.abiKind
          let memDesc : ScalarArrayParam :=
            { descriptor with
              param := pname
              inMemory := true
              memoryPointer := arrayPtr
              nextFreeBinding := nextFree
              namePrefix := namePrefix }
          pre := pre ++ effects ++ convStmts.toArray
          modify fun e =>
            { e with scalarArrays := e.scalarArrays.insert pid memDesc,
                     yulMemoryArrays := if pname == "" then e.yulMemoryArrays else e.yulMemoryArrays.insert pname arrayPtr,
                     encodingMemory := true }
        else if (location == "calldata" && !descriptor.inMemory) || (location == "memory" && descriptor.inMemory) then
          pre := pre ++ effects
          let boundDesc := { descriptor with param := pname }
          modify fun e =>
            { e with scalarArrays := e.scalarArrays.insert pid boundDesc,
                     yulMemoryArrays := if location == "memory" && descriptor.inMemory && pname != "" then e.yulMemoryArrays.insert pname descriptor.memoryPointer else e.yulMemoryArrays }
        else
          failAt p "scalar array argument location conversion is unsupported"
        if pname != "" then
          yul := yul.erase pname
    | .byteBuffer buffer =>
        let location := optStr p "storageLocation" |>.getD "default"
        unless pty == "bytes" && location == "memory" do
          failAt p "byte buffer argument requires a bytes memory parameter"
        let ptrBinding ← freshFor (if pname == "" then "bytes_ptr" else pname)
        let sizeBinding ← fresh
        pre := pre ++ buffer.pre ++ #[.letVar ptrBinding buffer.pointer, .letVar sizeBinding buffer.size]
        let retained : EncodedBytes :=
          { pre := #[], pointer := .localVar ptrBinding, size := .localVar sizeBinding }
        modify fun e =>
          { e with byteBuffers := e.byteBuffers.insert pid retained }
        if pname != "" then
          yul := yul.erase pname
    | .stringBuffer buffer =>
        let location := optStr p "storageLocation" |>.getD "default"
        if pty == "bytes" && location == "memory" && argTy.startsWith "literal_string " then
          let ptrBinding ← freshFor (if pname == "" then "bytes_ptr" else pname)
          let sizeBinding ← fresh
          pre := pre ++ buffer.pre ++ #[.letVar ptrBinding buffer.pointer, .letVar sizeBinding buffer.size]
          let retained : EncodedBytes :=
            { pre := #[], pointer := .localVar ptrBinding, size := .localVar sizeBinding }
          modify fun e =>
            { e with byteBuffers := e.byteBuffers.insert pid retained }
        else
          unless pty == "string" && location == "memory" do
            failAt p "string buffer argument requires a string memory parameter"
          let ptrBinding ← freshFor (if pname == "" then "str_ptr" else pname)
          let sizeBinding ← fresh
          pre := pre ++ buffer.pre ++ #[.letVar ptrBinding buffer.pointer, .letVar sizeBinding buffer.size]
          let retained : EncodedBytes :=
            { pre := #[], pointer := .localVar ptrBinding, size := .localVar sizeBinding }
          modify fun e =>
            { e with stringBuffers := e.stringBuffers.insert pid retained }
        if pname != "" then
          yul := yul.erase pname
    | .calldataBytes descriptor effects =>
        let location := optStr p "storageLocation" |>.getD "default"
        let expectedTy := if descriptor.isString then "string" else "bytes"
        unless pty == expectedTy do
          failAt p s!"calldata {expectedTy} argument requires a {expectedTy} parameter"
        if location == "calldata" && !descriptor.inMemory then
          pre := pre ++ effects
          modify fun e => { e with calldataBytes := e.calldataBytes.insert pid descriptor }
        else if location == "memory" then
          let retained ← if descriptor.inMemory then do
            pre := pre ++ effects
            pure ({ pre := #[], pointer := .add (.localVar descriptor.memoryPointer) (.literal 32), size := .localVar descriptor.lengthBinding } : EncodedBytes)
          else do
            let pointer ← fresh
            let finish ← fresh
            let copyIdx ← fresh
            let wordCount := Expr.div (.add (.localVar descriptor.lengthBinding) (.literal 31)) (.literal 32)
            modify fun e => { e with encodingMemory := true }
            let alloc := AbiEncoding.reserve pointer finish (.mul (.literal 32) wordCount)
            let copyStmt := Stmt.forEach copyIdx wordCount
              [.mstore (.add (.localVar pointer) (.mul (.localVar copyIdx) (.literal 32)))
                (.calldataload (.add (.localVar descriptor.dataBinding) (.mul (.localVar copyIdx) (.literal 32))))]
            pre := pre ++ effects ++ (alloc ++ [copyStmt]).toArray
            pure ({ pre := #[], pointer := .localVar pointer, size := .localVar descriptor.lengthBinding } : EncodedBytes)
          if descriptor.isString then
            modify fun e => { e with stringBuffers := e.stringBuffers.insert pid retained }
          else
            modify fun e => { e with byteBuffers := e.byteBuffers.insert pid retained }
        else
          failAt p s!"unsupported {pty} helper parameter location {location}"
        if pname != "" then
          yul := yul.erase pname
    | .storagePath argSid path effects =>
        unless pty.startsWith "struct " && !pty.contains "[" do
          failAt p "storage struct argument requires a struct parameter"
        let sid ← refInt (← mField p "typeName")
        unless sid >= 0 && sid.toNat == argSid do
          failAt p "storage struct argument declaration differs"
        let location := optStr p "storageLocation" |>.getD "default"
        if location == "storage" then
          if (bodyAssignedIds body).contains pid then
            failAt p "reassigned storage struct parameters are outside this slice"
          pre := pre ++ effects
          modify fun e => { e with paths := e.paths.insert pid path }
        else if location == "memory" then
          if (bodyAssignedIds body).contains pid then
            failAt p "reassigned flat struct parameters are outside this slice"
          let some sDecl := (← get).structs.find? argSid
            | failAt p "unknown struct declaration"
          let sName ← mStr (← mField sDecl "name")
          let sMembers ← mArr (← mField sDecl "members")
          if let .rawSlot rawSid baseSlot := path then
            unless rawSid == argSid do
              failAt p "raw storage slot struct argument declaration differs"
            let rawInfo ← resolveRawStructInfo rawSid p
            unless rawInfo.subStructs.isEmpty && rawInfo.mappings.isEmpty &&
                rawInfo.dynamicArrays.isEmpty && rawInfo.scalars.size == sMembers.size do
              failAt p "struct storage-to-memory parameter copy requires a scalar-member struct layout"
            pre := pre ++ effects
            let mut members : Array (String × String × String) := #[]
            for mNode in sMembers do
              let mName ← mStr (← mField mNode "name")
              let mTy ← mType mNode
              let some mInfo := rawInfo.scalars.find? (·.member == mName)
                | failAt mNode s!"unsupported flat struct storage member {mName}"
              let readVal ← atom (← readRawStructScalar #[] baseSlot mInfo)
              let binding ← freshFor s!"{if pname == "" then "struct_param" else pname}_{mName}"
              pre := pre ++ readVal.pre |>.push (.letVar binding readVal.expr)
              members := members.push (mName, mTy, binding)
            modify fun e =>
              { e with flatStructs := e.flatStructs.insert pid { structId := argSid, structName := sName, members } }
          else
            let (rawFieldName, count) ← match path with
              | .zero field => pure (field, 0)
              | .one field _ => pure (field, 1)
              | .two field _ _ => pure (field, 2)
              | .outer _ _ => failAt p "struct storage read requires all mapping keys"
              | .rawSlot _ _ | .bytesSlot _ _ =>
                  failAt p "raw or bytes slot struct storage-to-memory parameter copy is outside this slice"
            let (fieldName, subPrefix) := splitSPathField rawFieldName
            unless subPrefix == "" do
              failAt p "nested storage struct storage-to-memory parameter copy is outside this slice"
            let info ← resolveField fieldName p
            unless !info.scalarMapping && info.fixedArrayLength.isNone && info.keyCount == count &&
                info.structMappings.isEmpty && info.opaqueNames.isEmpty &&
                info.structFixedArrays.isEmpty && info.structDynamicArrays.isEmpty &&
                !info.memberNames.isEmpty do
              failAt p "struct storage-to-memory parameter copy requires a scalar-member struct layout"
            unless sMembers.size == info.memberNames.size do
              failAt p "struct declaration member count does not match storage layout"
            pre := pre ++ effects
            let mut members : Array (String × String × String) := #[]
            for mNode in sMembers do
              let mName ← mStr (← mField mNode "name")
              let mTy ← mType mNode
              unless !mTy.startsWith "enum " && (paramType mTy).isSome && info.memberNames.contains mName do
                failAt mNode s!"unsupported flat struct storage member {mName}"
              let readVal ← atom (← memberRead #[] path mName p)
              let binding ← freshFor s!"{if pname == "" then "struct_param" else pname}_{mName}"
              pre := pre ++ readVal.pre |>.push (.letVar binding readVal.expr)
              members := members.push (mName, mTy, binding)
            modify fun e =>
              { e with flatStructs := e.flatStructs.insert pid { structId := argSid, structName := sName, members } }
        else
          failAt p s!"unsupported storage struct helper parameter location {location}"
        if pname != "" then
          yul := yul.erase pname
    | .flatStruct argSid sName memberVals effects =>
        unless pty.startsWith "struct " && !pty.contains "[" do
          failAt p "flat struct argument requires a struct parameter"
        let sid ← refInt (← mField p "typeName")
        unless sid >= 0 && sid.toNat == argSid do
          failAt p "flat struct argument declaration differs"
        let location := optStr p "storageLocation" |>.getD "default"
        unless location == "memory" do
          failAt p s!"unsupported flat struct helper parameter location {location}"
        if (bodyAssignedIds body).contains pid then
          failAt p "reassigned flat struct parameters are outside this slice"
        pre := pre ++ effects
        let mut members : Array (String × String × String) := #[]
        for (mName, mTy, mExpr) in memberVals do
          let binding ← freshFor s!"{if pname == "" then "struct_param" else pname}_{mName}"
          pre := pre.push (.letVar binding mExpr)
          members := members.push (mName, mTy, binding)
        modify fun e =>
          { e with flatStructs := e.flatStructs.insert pid { structId := argSid, structName := sName, members } }
        if pname != "" then
          yul := yul.erase pname
    | .storageBytes storageName isString =>
        let location := optStr p "storageLocation" |>.getD "default"
        let expectedTy := if isString then "string" else "bytes"
        unless pty == expectedTy do
          failAt p s!"storage {expectedTy} argument requires a {expectedTy} parameter"
        if location == "storage" then
          if (bodyAssignedIds body).contains pid then
            failAt p s!"reassigned storage {pty} parameters are outside this slice"
          modify fun e => { e with storageBytesVars := e.storageBytesVars.insert pid storageName }
        else if location == "memory" then
          let buffer ← lowerStorageBytesRead storageName p
          let ptrBinding ← freshFor (if pname == "" then "bytes_ptr" else pname)
          let sizeBinding ← fresh
          pre := pre ++ buffer.pre ++ #[.letVar ptrBinding buffer.pointer, .letVar sizeBinding buffer.size]
          let retained : EncodedBytes :=
            { pre := #[], pointer := .localVar ptrBinding, size := .localVar sizeBinding }
          if isString then
            modify fun e => { e with stringBuffers := e.stringBuffers.insert pid retained }
          else
            modify fun e => { e with byteBuffers := e.byteBuffers.insert pid retained }
        else
          failAt p s!"unsupported storage {pty} helper parameter location {location}"
        if pname != "" then
          yul := yul.erase pname
    | .storageDynamicArray fieldName slotExpr elemTy elemSid? effects =>
        if let some elemSid := elemSid? then
          let location := optStr p "storageLocation" |>.getD "default"
          unless location == "storage" && pty.startsWith "struct " && pty.contains "[]" do
            failAt p "storage struct dynamic array argument requires a storage struct array parameter"
          let pTypeName ← mField p "typeName"
          unless (← mKind pTypeName) == "ArrayTypeName" do
            failAt p "storage struct dynamic array parameter must be an array type"
          let baseSid ← refInt (← mField pTypeName "baseType")
          unless baseSid >= 0 && baseSid.toNat == elemSid do
            failAt p "storage struct dynamic array element declaration differs"
          if (bodyAssignedIds body).contains pid then
            failAt p "reassigned storage dynamic array parameters are outside this slice"
          pre := pre ++ effects
          modify fun e =>
            { e with storageDynamicArrayVars := e.storageDynamicArrayVars.insert pid (fieldName, slotExpr, elemTy, some elemSid) }
          if pname != "" then
            let env ← get
            let slotVal : Expr := if fieldName != "" then
              match env.fieldsByName.find? fieldName with
              | some fInfo => .literal fInfo.slot
              | none => slotExpr
            else slotExpr
            yul := yul.insert s!"{pname}.slot" slotVal
        else
          let some (elemStr, modelElemTy, abiKind) := scalarArrayElement? pty
            | failAt p "storage dynamic array argument requires a scalar array parameter"
          unless elemStr == elemTy do
            failAt p "storage dynamic array element type differs"
          let location := optStr p "storageLocation" |>.getD "default"
          if location == "storage" then
            if (bodyAssignedIds body).contains pid then
              failAt p "reassigned storage dynamic array parameters are outside this slice"
            pre := pre ++ effects
            modify fun e =>
              { e with storageDynamicArrayVars := e.storageDynamicArrayVars.insert pid (fieldName, slotExpr, elemTy, none) }
            if pname != "" then
              let env ← get
              let slotVal : Expr := if fieldName != "" then
                match env.fieldsByName.find? fieldName with
                | some fInfo => .literal fInfo.slot
                | none => slotExpr
              else slotExpr
              yul := yul.insert s!"{pname}.slot" slotVal
          else if location == "memory" then
            let (copyStmts, memDesc) ← copyStorageDynamicArrayToMemory effects fieldName slotExpr elemTy modelElemTy abiKind pname
            pre := pre ++ copyStmts
            modify fun e =>
              { e with scalarArrays := e.scalarArrays.insert pid memDesc,
                       yulMemoryArrays := if pname == "" then e.yulMemoryArrays else e.yulMemoryArrays.insert pname memDesc.memoryPointer,
                       encodingMemory := true }
            if pname != "" then
              yul := yul.erase pname
          else
            failAt p s!"unsupported storage dynamic array helper parameter location {location}"
    | .fnPtr ptr effects =>
        let some typeNameNode := field? p "typeName"
          | failAt p "function pointer argument requires a function parameter"
        unless optStr typeNameNode "nodeType" == some "FunctionTypeName" do
          failAt p "function pointer argument requires a function parameter"
        let fvis := optStr typeNameNode "visibility" |>.getD ""
        unless fvis == "internal" do
          failAt p s!"only internal function pointer parameters are supported, found {fvis}"
        if (bodyAssignedIds body).contains pid then
          failAt p "reassigned function pointer parameters are outside this slice"
        pre := pre ++ effects
        modify fun e =>
          { e with fnPtrs := e.fnPtrs.insert pid ptr }
        if pname != "" then
          yul := yul.erase pname
  pure (pre, yul)

private partial def bindYulExternalConstants (j : Json) (allowAllStateVarSlots : Bool := true) : M (Array Stmt) := do
  let mut pre : Array Stmt := #[]
  let some extRefs := field? j "externalReferences" | return pre
  let refs ← mArr extRefs
  for r in refs do
    let declId := ((field? r "declaration").bind (fun v => v.getInt?.toOption)).getD (-1)
    if declId >= 0 then
      let n := declId.toNat
      let env ← get
      if let some decl := env.numericConstants.find? n then
        if !(← mBool (← mField r "isOffset")) && !(← mBool (← mField r "isSlot")) &&
           (field? r "suffix").isNone && (← mNat (← mField r "valueSize")) == 1 then
          let ident ← mStr (← mField decl "name")
          if !env.yulNames.contains ident then
            if env.constantStack.contains n then failAt j "cyclic constant initializer"
            let declared ← mType decl
            unless (declared.startsWith "uint" && (bitsOf declared).isSome) ||
                declared == "bool" || declared == "bytes32" || declared == "bytes4" ||
                declared == "int256" || declared == "int" ||
                declared == "address" || declared == "address payable" do
              failAt j s!"unsupported numeric constant type {declared}"
            let initializer ← mField decl "value"
            modify fun e => { e with constantStack := n :: e.constantStack }
            let rawValue ← lowerExpr initializer
            let value ← convert declared (← mType initializer) rawValue initializer
            let savedStack := env.constantStack
            let a ← atom value
            pre := pre ++ a.pre
            modify fun e => { e with constantStack := savedStack, yulNames := e.yulNames.insert ident a.expr }
      else if let some decl := env.stateVars.find? n then
        if !(← mBool (← mField r "isOffset")) && (← mBool (← mField r "isSlot")) &&
           optStr r "suffix" == some "slot" && (← mNat (← mField r "valueSize")) == 1 then
          let isConst := (field? decl "constant").bind (fun value => value.getBool?.toOption) == some true
          let isImm := optStr decl "mutability" == some "immutable"
          unless isConst || isImm do
            let ident ← mStr (← mField decl "name")
            let slotName := s!"{ident}.slot"
            if !env.yulNames.contains ident && !env.yulNames.contains slotName then
              if env.duplicateLayoutLabels.contains ident then
                failAt j s!"shadowed storage declaration {ident} is outside this slice"
              if let some item := env.layoutItems.find? ident then
                unless (← mNat (← mField item "astId")) == n do
                  failAt j s!"shadowed storage declaration {ident} is outside this slice"
              let info ← resolveField ident j
              if allowAllStateVarSlots || info.dynamicArrayElemType.isSome then
                markField ident
                modify fun e =>
                  { e with yulNames := e.yulNames.insert slotName (.literal info.slot),
                           usedRawStorage := e.usedRawStorage || info.dynamicArrayElemType.isSome }
  return pre

private partial def lowerShortStringAllocAssembly? (declStmt asmStmt : Json) : M (Option (Array Stmt)) := do
  unless (← mKind declStmt) == "VariableDeclarationStatement" &&
         (← mKind asmStmt) == "InlineAssembly" do
    return none
  let decls ← mArr (← mField declStmt "declarations")
  unless decls.size == 1 && !decls[0]!.isNull do return none
  let d := decls[0]!
  let strName ← mStr (← mField d "name")
  let strId ← mNat (← mField d "id")
  if (← get).bodyAssigned.contains strId then return none
  let loc := optStr d "storageLocation" |>.getD "default"
  let dTy ← mType d
  unless loc == "memory" && (dTy == "string" || dTy == "bytes") do return none
  let init := field? declStmt "initialValue" |>.getD Json.null
  if init.isNull then return none
  unless (← mKind init) == "FunctionCall" && optStr init "kind" == some "functionCall" do return none
  let callee ← mField init "expression"
  unless (← mKind callee) == "NewExpression" do return none
  let initArgs ← mArr (← mField init "arguments")
  unless initArgs.size == 1 do return none
  let capArg := initArgs[0]!
  let ast ← mField asmStmt "AST"
  unless (← mKind ast) == "YulBlock" do return none
  let ystmts ← mArr (← mField ast "statements")
  unless ystmts.size == 2 do return none
  let ys0 := ystmts[0]!
  let ys1 := ystmts[1]!
  unless (← mKind ys0) == "YulExpressionStatement" && (← mKind ys1) == "YulExpressionStatement" do
    return none
  let e0 ← mField ys0 "expression"
  let e1 ← mField ys1 "expression"
  unless (← mKind e0) == "YulFunctionCall" && (← mKind e1) == "YulFunctionCall" do
    return none
  let fn0 ← mStr (← mField (← mField e0 "functionName") "name")
  let fn1 ← mStr (← mField (← mField e1 "functionName") "name")
  unless fn0 == "mstore" && fn1 == "mstore" do return none
  let args0 ← mArr (← mField e0 "arguments")
  let args1 ← mArr (← mField e1 "arguments")
  unless args0.size == 2 && args1.size == 2 do return none
  let a00 := args0[0]!
  let a01 := args0[1]!
  let a10 := args1[0]!
  let a11 := args1[1]!
  unless (← mKind a00) == "YulIdentifier" && optStr a00 "name" == some strName do
    return none
  unless (← mKind a10) == "YulFunctionCall" &&
         (← mStr (← mField (← mField a10 "functionName") "name")) == "add" do
    return none
  let addArgs ← mArr (← mField a10 "arguments")
  unless addArgs.size == 2 do return none
  unless (← mKind addArgs[0]!) == "YulIdentifier" && optStr addArgs[0]! "name" == some strName do
    return none
  let savedYul := (← get).yulNames
  let extPre ← bindYulExternalConstants asmStmt
  let addOffVal ← lowerYul addArgs[1]!
  let isOff32 := match addOffVal.expr with
    | .literal 32 => addOffVal.pre.isEmpty
    | _ => false
  unless isOff32 do
    modify fun e => { e with yulNames := savedYul }
    return none
  let capVal ← atom (← lowerExpr capArg)
  let isCap32 := match capVal.expr with
    | .literal 32 => true
    | _ => false
  unless isCap32 do
    modify fun e => { e with yulNames := savedYul }
    return none
  let lenVal ← lowerYul a01
  let wordVal ← lowerYul a11
  modify fun e => { e with yulNames := savedYul, encodingMemory := true }
  let lenBinding ← freshFor s!"{strName}_len"
  let wordBinding ← freshFor s!"{strName}_word"
  let ptr ← freshFor strName
  let finish ← fresh
  let allocStmts := AbiEncoding.reserve ptr finish (.literal 32)
  let pre := capVal.pre ++ extPre ++ lenVal.pre ++ wordVal.pre ++ #[
    .letVar lenBinding lenVal.expr,
    .letVar wordBinding wordVal.expr
  ] ++ allocStmts.toArray ++ #[
    .mstore (.localVar ptr) (.localVar wordBinding)
  ]
  let retained : EncodedBytes :=
    { pre := #[], pointer := .localVar ptr, size := .localVar lenBinding }
  if dTy == "string" then
    modify fun e => { e with stringBuffers := e.stringBuffers.insert strId retained, yulNames := e.yulNames.erase strName }
  else
    modify fun e => { e with byteBuffers := e.byteBuffers.insert strId retained, yulNames := e.yulNames.erase strName }
  return some pre

private partial def lowerStringHelperStmts (stmts : List Json) : M EncodedBytes := do
  match stmts with
  | [] => failAt Json.null "string helper did not end with a return statement"
  | declStmt :: asmStmt :: rest =>
      if let some allocPre ← lowerShortStringAllocAssembly? declStmt asmStmt then
        let tailBuf ← lowerStringHelperStmts rest
        return { tailBuf with pre := allocPre ++ tailBuf.pre }
      match ← mKind declStmt with
      | "VariableDeclarationStatement" =>
          let sPre ← lowerLocal declStmt
          let tailBuf ← lowerStringHelperStmts (asmStmt :: rest)
          return { tailBuf with pre := sPre ++ tailBuf.pre }
      | "ExpressionStatement" =>
          if ← stmtAlwaysReverts [] declStmt then
            failAt asmStmt "statement after string helper revert"
          let sPre ← lowerEffect declStmt
          let tailBuf ← lowerStringHelperStmts (asmStmt :: rest)
          return { tailBuf with pre := sPre ++ tailBuf.pre }
      | "Block" =>
          let inner ← mArr (← mField declStmt "statements")
          lowerStringHelperStmts (inner.toList ++ asmStmt :: rest)
      | "IfStatement" =>
          let condNode ← mField declStmt "condition"
          unless (← mType condNode) == "bool" do failAt condNode "if condition must be bool"
          let condVal ← atom (← lowerExpr condNode)
          let tNode ← mField declStmt "trueBody"
          let tStmts ← if (← mKind tNode) == "Block" then
            Array.toList <$> mArr (← mField tNode "statements")
          else
            pure [tNode]
          let fNode := field? declStmt "falseBody" |>.getD Json.null
          unless fNode.isNull do
            failAt declStmt "statements after returning if/else in string helper are unsupported"
          let saved ← get
          let restoreLexical : M Unit := modify fun e =>
            { e with values := saved.values, writableLocals := saved.writableLocals,
                     paths := saved.paths, byteBuffers := saved.byteBuffers,
                     stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars,
                     storageDynamicArrayVars := saved.storageDynamicArrayVars,
                     yulNames := saved.yulNames }
          let yesBuf ← lowerStringHelperStmts tStmts
          restoreLexical
          let noBuf ← lowerStringHelperStmts (asmStmt :: rest)
          restoreLexical
          let ptr ← fresh
          let size ← fresh
          let yesStmts := yesBuf.pre ++ #[.assignVar ptr yesBuf.pointer, .assignVar size yesBuf.size]
          let noStmts := noBuf.pre ++ #[.assignVar ptr noBuf.pointer, .assignVar size noBuf.size]
          let pre := condVal.pre ++ #[
            .letVar ptr (.literal 0),
            .letVar size (.literal 0),
            .ite condVal.expr yesStmts.toList noStmts.toList
          ]
          return { pre, pointer := .localVar ptr, size := .localVar size }
      | _ => failAt declStmt "unsupported statement before return in string helper"
  | [s] =>
      match ← mKind s with
      | "Return" =>
          let retExpr := field? s "expression" |>.getD Json.null
          if retExpr.isNull then failAt s "string helper return requires an expression"
          lowerEncodedBytes retExpr
      | "RevertStatement" =>
          let revStmts ← lowerRevert s
          return { pre := revStmts, pointer := .literal 0, size := .literal 0 }
      | "ExpressionStatement" =>
          if ← stmtAlwaysReverts [] s then
            let effStmts ← lowerEffect s
            return { pre := effStmts, pointer := .literal 0, size := .literal 0 }
          else
            failAt s "string helper must end with a return statement"
      | "Block" =>
          let inner ← mArr (← mField s "statements")
          lowerStringHelperStmts inner.toList
      | "UncheckedBlock" =>
          let savedUnchecked := (← get).unchecked
          modify fun e => { e with unchecked := true }
          let inner ← mArr (← mField s "statements")
          let res ← lowerStringHelperStmts inner.toList
          modify fun e => { e with unchecked := savedUnchecked }
          return res
      | "IfStatement" =>
          let condNode ← mField s "condition"
          unless (← mType condNode) == "bool" do failAt condNode "if condition must be bool"
          let condVal ← atom (← lowerExpr condNode)
          let tNode ← mField s "trueBody"
          let fNode := field? s "falseBody" |>.getD Json.null
          if fNode.isNull then
            failAt s "string helper if statement without else must be followed by a return"
          let tStmts ← if (← mKind tNode) == "Block" then
            Array.toList <$> mArr (← mField tNode "statements")
          else
            pure [tNode]
          let fStmts ← if (← mKind fNode) == "Block" then
            Array.toList <$> mArr (← mField fNode "statements")
          else
            pure [fNode]
          let saved ← get
          let restoreLexical : M Unit := modify fun e =>
            { e with values := saved.values, writableLocals := saved.writableLocals,
                     paths := saved.paths, byteBuffers := saved.byteBuffers,
                     stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars,
                     storageDynamicArrayVars := saved.storageDynamicArrayVars,
                     yulNames := saved.yulNames }
          let yesBuf ← lowerStringHelperStmts tStmts
          restoreLexical
          let noBuf ← lowerStringHelperStmts fStmts
          restoreLexical
          let ptr ← fresh
          let size ← fresh
          let yesStmts := yesBuf.pre ++ #[.assignVar ptr yesBuf.pointer, .assignVar size yesBuf.size]
          let noStmts := noBuf.pre ++ #[.assignVar ptr noBuf.pointer, .assignVar size noBuf.size]
          let pre := condVal.pre ++ #[
            .letVar ptr (.literal 0),
            .letVar size (.literal 0),
            .ite condVal.expr yesStmts.toList noStmts.toList
          ]
          return { pre, pointer := .localVar ptr, size := .localVar size }
      | _ => failAt s "string helper must end with a return statement"

private partial def inlineStringFn (fnId : Nat) (args : Array CallArg) (at_ : Json) : M EncodedBytes := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let visibility := optStr fn "visibility" |>.getD ""
  unless visibility == "internal" || visibility == "private" || visibility == "public" do
    failAt at_ "string helper calls require an internal, private, or public declaration"
  let saved ← get
  let savedYul := saved.yulNames
  let savedFile := saved.currentFile
  let frameFile := saved.nodeFile.find? fnId |>.getD saved.currentFile
  let frame := fnId :: saved.stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mods ← mArr (← mField fn "modifiers")
  unless mods.isEmpty do failAt fn "modifiers on string-returning helpers are outside this slice"
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "string helper must have one return parameter"
  let r := rets[0]!
  let rname ← mStr (← mField r "name")
  unless rname == "" do failAt r "named string helper return is unsupported"
  let rloc := optStr r "storageLocation" |>.getD "default"
  let rty ← mType r
  unless rloc == "memory" && (rty == "string" || rty == "bytes") do
    failAt r "string helper return must be string memory or bytes memory"
  let (boundPre, yul) ← bindHelperParams params args body at_ savedYul
  modify fun e => { e with yulNames := yul }
  noteFn fn
  let stmts ← mArr (← mField body "statements")
  if stmts.isEmpty then
    failAt fn "empty string helper is outside this slice"
  let resBuf ← lowerStringHelperStmts stmts.toList
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  return { pre := boundPre ++ resBuf.pre, pointer := resBuf.pointer, size := resBuf.size }

private partial def lowerArrayReinterpretAssembly? (declStmt asmStmt : Json) (rest : List Json) : M (Option Unit) := do
  unless (← mKind declStmt) == "VariableDeclarationStatement" &&
         (← mKind asmStmt) == "InlineAssembly" do
    return none
  let decls ← mArr (← mField declStmt "declarations")
  unless decls.size == 1 && !decls[0]!.isNull do return none
  let d := decls[0]!
  let resName ← mStr (← mField d "name")
  let resId ← mNat (← mField d "id")
  if (rest.flatMap bodyAssignedIds).contains resId then return none
  let loc := optStr d "storageLocation" |>.getD "default"
  let dTy ← mType d
  unless loc == "memory" do return none
  let some (elemStr, elemPty, abiKind) := scalarArrayElement? dTy
    | return none
  let init := field? declStmt "initialValue" |>.getD Json.null
  unless init.isNull do return none
  let ast ← mField asmStmt "AST"
  unless (← mKind ast) == "YulBlock" do return none
  let ystmts ← mArr (← mField ast "statements")
  unless ystmts.size == 1 do return none
  let ys := ystmts[0]!
  unless (← mKind ys) == "YulAssignment" do return none
  let varNames ← mArr (← mField ys "variableNames")
  unless varNames.size == 1 && (← mKind varNames[0]!) == "YulIdentifier" &&
         optStr varNames[0]! "name" == some resName do
    return none
  let valNode ← mField ys "value"
  unless (← mKind valNode) == "YulIdentifier" do return none
  let srcName ← mStr (← mField valNode "name")
  let some (_, srcDesc) := (← get).scalarArrays.toList.find? (fun (_, a) => a.param == srcName && a.inMemory)
    | return none
  let resDesc : ScalarArrayParam :=
    { srcDesc with
      param := resName
      elementType := elemStr
      modelElementType := elemPty
      abiKind := abiKind }
  modify fun e =>
    { e with scalarArrays := e.scalarArrays.insert resId resDesc,
             yulMemoryArrays := e.yulMemoryArrays.insert resName resDesc.memoryPointer,
             yulNames := e.yulNames.erase resName }
  return some ()

private partial def lowerArrayHelperStmts (expectedElemTy : String) (stmts : List Json) :
    M (Array Stmt × ScalarArrayParam) := do
  match stmts with
  | [] => failAt Json.null "array helper did not end with a return statement"
  | declStmt :: asmStmt :: rest =>
      if (← lowerArrayReinterpretAssembly? declStmt asmStmt rest).isSome then
        lowerArrayHelperStmts expectedElemTy rest
      else
        match ← mKind declStmt with
        | "VariableDeclarationStatement" =>
            let sPre ← lowerLocal declStmt
            let (tailPre, desc) ← lowerArrayHelperStmts expectedElemTy (asmStmt :: rest)
            return (sPre ++ tailPre, desc)
        | "ExpressionStatement" =>
            let sPre ← lowerEffect declStmt
            let (tailPre, desc) ← lowerArrayHelperStmts expectedElemTy (asmStmt :: rest)
            return (sPre ++ tailPre, desc)
        | "Block" =>
            let inner ← mArr (← mField declStmt "statements")
            lowerArrayHelperStmts expectedElemTy (inner.toList ++ asmStmt :: rest)
        | _ => failAt declStmt "unsupported statement before return in array helper"
  | [s] =>
      match ← mKind s with
      | "Return" =>
          let retExpr := field? s "expression" |>.getD Json.null
          if retExpr.isNull then failAt s "array helper return requires an expression"
          if ← isAbiDecodeCall retExpr then
            let (decodePre, decoded) ← lowerAbiDecodeItems retExpr
            unless decoded.size == 1 do
              failAt retExpr "array abi.decode return requires a single array target type"
            let .scalarArray decElemStr _ _ desc := decoded[0]!
              | failAt retExpr "array abi.decode return requires a dynamic scalar array target type"
            unless decElemStr == expectedElemTy do
              failAt retExpr "returned scalar array type or location mismatch"
            return (decodePre, desc)
          if (← mKind retExpr) == "FunctionCall" && optStr retExpr "kind" == some "functionCall" then
            let (fnId, vals) ← resolveCallTargetAndArgs retExpr
            return ← inlineArrayFn fnId vals expectedElemTy retExpr
          let ref ← lowerRef retExpr
          if let .scalarArray id pre := ref then
            let some desc := (← get).scalarArrays.find? id
              | failAt retExpr "unknown scalar array local in return"
            unless desc.inMemory && desc.elementType == expectedElemTy do
              failAt retExpr "returned scalar array type or location mismatch"
            return (pre, desc)
          if let some (pre, fieldName, slotExpr, elemTy, modelElemTy, abiKind, none) ← resolveStorageDynamicArrayTarget ref retExpr then
            unless elemTy == expectedElemTy do
              failAt retExpr "returned storage dynamic array element type mismatch"
            return ← copyStorageDynamicArrayToMemory pre fieldName slotExpr elemTy modelElemTy abiKind ""
          failAt retExpr "unsupported array helper return expression"
      | "Block" =>
          let inner ← mArr (← mField s "statements")
          lowerArrayHelperStmts expectedElemTy inner.toList
      | "UncheckedBlock" =>
          let savedUnchecked := (← get).unchecked
          modify fun e => { e with unchecked := true }
          let inner ← mArr (← mField s "statements")
          let res ← lowerArrayHelperStmts expectedElemTy inner.toList
          modify fun e => { e with unchecked := savedUnchecked }
          return res
      | _ => failAt s "array helper must end with a return statement"

private partial def inlineArrayFn (fnId : Nat) (args : Array CallArg) (expectedElemTy : String) (at_ : Json) :
    M (Array Stmt × ScalarArrayParam) := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let visibility := optStr fn "visibility" |>.getD ""
  unless visibility == "internal" || visibility == "private" || visibility == "public" do
    failAt at_ "array helper calls require an internal, private, or public declaration"
  let saved ← get
  let savedYul := saved.yulNames
  let savedFile := saved.currentFile
  let frameFile := saved.nodeFile.find? fnId |>.getD saved.currentFile
  let frame := fnId :: saved.stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mods ← mArr (← mField fn "modifiers")
  unless mods.isEmpty do failAt fn "modifiers on array-returning helpers are outside this slice"
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "array helper must have one return parameter"
  let r := rets[0]!
  let rname ← mStr (← mField r "name")
  unless rname == "" do failAt r "named array helper return is unsupported"
  let rloc := optStr r "storageLocation" |>.getD "default"
  let rty ← mType r
  let some (retElemTy, _, _) := scalarArrayElement? rty
    | failAt r "array helper return must be a supported scalar array"
  unless rloc == "memory" && retElemTy == expectedElemTy do
    failAt r "array helper return type or location mismatch"
  let (boundPre, yul) ← bindHelperParams params args body at_ savedYul
  modify fun e => { e with yulNames := yul }
  noteFn fn
  let stmts ← mArr (← mField body "statements")
  if stmts.isEmpty then
    failAt fn "empty array helper is outside this slice"
  let (resPre, resDesc) ← lowerArrayHelperStmts retElemTy stmts.toList
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  return (boundPre ++ resPre, resDesc)

private partial def inlineStorageRefFn (fnId : Nat) (args : Array CallArg) (at_ : Json) : M (Array Stmt × SPath) := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let visibility := optStr fn "visibility" |>.getD ""
  unless visibility == "internal" || visibility == "private" do
    failAt at_ "storage pointer helper calls require an internal or private declaration"
  let saved ← get
  let savedYul := saved.yulNames
  let savedFile := saved.currentFile
  let frameFile := saved.nodeFile.find? fnId |>.getD saved.currentFile
  let frame := fnId :: saved.stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mods ← mArr (← mField fn "modifiers")
  unless mods.isEmpty do failAt fn "modifiers on storage pointer helpers are outside this slice"
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "storage pointer helper must have one return parameter"
  let r := rets[0]!
  let retName ← mStr (← mField r "name")
  let retId ← mNat (← mField r "id")
  let rloc := optStr r "storageLocation" |>.getD "default"
  let rty ← mType r
  unless rloc == "storage" && rty.startsWith "struct " && !rty.contains "[" do
    failAt r "storage pointer helper return must be a struct storage reference"
  let (retStructId, retStructDecl) ← resolveStructDeclFromType r
  let (boundPre, yul) ← bindHelperParams params args body at_ savedYul
  modify fun e => { e with yulNames := yul }
  noteFn fn
  let stmts ← mArr (← mField body "statements")
  if stmts.isEmpty then
    failAt fn "empty storage pointer helper is outside this slice"
  let mut pre := boundPre
  let mut retPath? : Option SPath := none
  for idx in [:stmts.size] do
    if retPath?.isSome then
      failAt stmts[idx]! "unreachable statement after storage pointer helper result"
    let s := stmts[idx]!
    match ← mKind s with
    | "VariableDeclarationStatement" =>
        pre := pre ++ (← lowerLocal s)
    | "ExpressionStatement" =>
        let expr ← mField s "expression"
        if (← mKind expr) == "Assignment" && optStr expr "operator" == some "=" then
          let lhs ← mField expr "leftHandSide"
          let rhs ← mField expr "rightHandSide"
          let isRetLhs ←
            if (← mKind lhs) == "Identifier" then pure ((← refInt lhs) == retId) else pure false
          if isRetLhs then
            match ← lowerRef rhs with
            | .path rpre rpath =>
                pre := pre ++ rpre
                retPath? := some rpath
            | _ => failAt rhs "storage pointer return assignment requires a storage path"
          else
            pre := pre ++ (← lowerEffect s)
        else
          pre := pre ++ (← lowerEffect s)
    | "Return" =>
        let retExpr := field? s "expression" |>.getD Json.null
        if retExpr.isNull then
          if let some p := (← get).paths.find? retId then
            retPath? := some p
          else
            failAt s "storage pointer helper return is unassigned"
        else
          let isRetIdent ←
            if (← mKind retExpr) == "Identifier" then
              pure ((← refInt retExpr) == retId)
            else
              pure false
          if isRetIdent then
            if let some p := (← get).paths.find? retId then
              retPath? := some p
            else
              failAt s "storage pointer helper return is unassigned"
          else
            match ← lowerRef retExpr with
            | .path rpre rpath =>
                pre := pre ++ rpre
                retPath? := some rpath
            | _ => failAt retExpr "storage pointer helper return requires a storage path"
    | "InlineAssembly" =>
        let ast ← mField s "AST"
        unless (← mKind ast) == "YulBlock" do failAt s "assembly is not a Yul block"
        let ystmts ← mArr (← mField ast "statements")
        let assignsRetSlot ← ystmts.anyM fun ys => do
          if (← mKind ys) == "YulAssignment" then
            let vars ← mArr (← mField ys "variableNames")
            if vars.size == 1 then
              pure (retName != "" && (← mStr (← mField vars[0]! "name")) == s!"{retName}.slot")
            else pure false
          else pure false
        if !assignsRetSlot && idx + 1 < stmts.size then
          let savedAsmYul := (← get).yulNames
          let extPre ← bindYulExternalConstants s
          let asmStmts ← lowerAssemblyStmts s ""
          modify fun e => { e with yulNames := savedAsmYul }
          pre := pre ++ extPre ++ asmStmts
          continue
        unless retName != "" do
          failAt s "assembly storage pointer helper requires a named return parameter"
        unless !ystmts.isEmpty do
          failAt s "storage pointer helper assembly must be a single slot assignment"
        let prefixYstmts := ystmts.extract 0 (ystmts.size - 1)
        let prefixAssignsRetSlot ← prefixYstmts.anyM fun pys => do
          if (← mKind pys) == "YulAssignment" then
            let vars ← mArr (← mField pys "variableNames")
            if vars.size == 1 then
              pure ((← mStr (← mField vars[0]! "name")) == s!"{retName}.slot")
            else pure false
          else pure false
        if prefixAssignsRetSlot then
          failAt s "storage pointer helper assembly must be a single slot assignment"
        let ys := ystmts.back!
        if ystmts.size > 1 && (← mKind ys) != "YulAssignment" then
          failAt s "storage pointer helper assembly must be a single slot assignment"
        unless (← mKind ys) == "YulAssignment" do
          failAt ys "storage pointer helper assembly must be a slot assignment"
        let vars ← mArr (← mField ys "variableNames")
        unless vars.size == 1 do failAt ys "Yul slot assignment must have one target"
        let lhsName ← mStr (← mField vars[0]! "name")
        unless lhsName == s!"{retName}.slot" do
          if ystmts.size > 1 then
            failAt s "storage pointer helper assembly must be a single slot assignment"
          failAt ys s!"expected assignment to {retName}.slot, found {lhsName}"
        let rhs ← mField ys "value"
        let mut matchedBytesSlot : Option SPath := none
        if prefixYstmts.isEmpty && (← mKind rhs) == "YulIdentifier" then
          let rhsName ← mStr (← mField rhs "name")
          if rhsName.endsWith ".slot" then
            let varPrefix := (rhsName.dropEnd 5).toString
            for p in params do
              if (← mStr (← mField p "name")) == varPrefix then
                let pid ← mNat (← mField p "id")
                if let some storageName := (← get).storageBytesVars.find? pid then
                  let sMembers ← mArr (← mField retStructDecl "members")
                  unless sMembers.size == 1 do
                    failAt r "StorageSlot bytes/string wrapper struct must have a single value member"
                  let m0 := sMembers[0]!
                  let m0Name ← mStr (← mField m0 "name")
                  let m0Ty ← mType m0
                  unless m0Name == "value" && (m0Ty == "string" || m0Ty == "bytes") do
                    failAt r "StorageSlot bytes/string wrapper struct must have a single string or bytes member named value"
                  matchedBytesSlot := some (.bytesSlot storageName (m0Ty == "string"))
        if let some bpath := matchedBytesSlot then
          if idx + 1 == stmts.size then
            retPath? := some bpath
          else
            modify fun e => { e with paths := e.paths.insert retId bpath }
        else
          let savedAsmYul := (← get).yulNames
          let savedScratch0 := (← get).yulScratch0
          let savedScratch32 := (← get).yulScratch32
          modify fun e => { e with yulScratch0 := false, yulScratch32 := false }
          let extPre ← bindYulExternalConstants s false
          let refs ← mArr (← mField s "externalReferences")
          let prefixPre ← lowerYulStmtSlice s prefixYstmts refs ""
          let slotVal ← lowerYul rhs
          modify fun e => { e with yulNames := savedAsmYul, yulScratch0 := savedScratch0, yulScratch32 := savedScratch32 }
          let rawInfo ← resolveRawStructInfo retStructId fn
          if !prefixYstmts.isEmpty then
            unless prefixYstmts.size == 1 do
              failAt s "storage pointer helper assembly must be a single slot assignment"
            unless rawInfo.wordCount == 1 do
              failAt s "Checkpoints._unsafeAccess requires a 1-slot struct element array"
          let slotBinding ← freshFor "raw_slot"
          pre := pre ++ extPre ++ prefixPre ++ slotVal.pre |>.push (.letVar slotBinding slotVal.expr)
          let rpath := SPath.rawSlot retStructId (.localVar slotBinding)
          if idx + 1 == stmts.size then
            retPath? := some rpath
          else
            modify fun e => { e with paths := e.paths.insert retId rpath }
    | _ => failAt s "unsupported statement in storage pointer helper"
  let some finalPath := retPath?
    | failAt fn "storage pointer helper did not assign or return a storage slot"
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  return (pre, finalPath)

private partial def inlineFlatStructFn (fnId : Nat) (args : Array CallArg) (at_ : Json) :
    M (Nat × String × Array Stmt × Array (String × String × Expr)) := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let visibility := optStr fn "visibility" |>.getD ""
  unless visibility == "internal" || visibility == "private" || visibility == "public" do
    failAt at_ "struct helper calls require an internal, private, or public declaration"
  let saved ← get
  let savedYul := saved.yulNames
  let savedFile := saved.currentFile
  let frameFile := saved.nodeFile.find? fnId |>.getD saved.currentFile
  let frame := fnId :: saved.stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mods ← mArr (← mField fn "modifiers")
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "struct helper must have one return parameter"
  let r := rets[0]!
  let rname ← mStr (← mField r "name")
  let rid ← mNat (← mField r "id")
  let rloc := optStr r "storageLocation" |>.getD "default"
  let rty ← mType r
  unless rloc == "memory" && rty.startsWith "struct " && !rty.contains "[" do
    failAt r "struct helper return must be a memory struct"
  let (retSid, retDecl) ← resolveStructDeclFromType r
  let retStructName ← mStr (← mField retDecl "name")
  let retMembers ← mArr (← mField retDecl "members")
  unless !retMembers.isEmpty do
    failAt r s!"empty struct {retStructName} is unsupported"
  let (boundPre, yul) ← bindHelperParams params args body at_ savedYul
  let mut pre := boundPre
  modify fun e => { e with yulNames := yul }
  let mut memberBindings : Array (String × String × String) := #[]
  let mut memberExprs : Array (String × String × Expr) := #[]
  for mNode in retMembers do
    let mName ← mStr (← mField mNode "name")
    let mTy ← mType mNode
    unless !mTy.startsWith "enum " && (paramType mTy).isSome do
      failAt mNode s!"unsupported flat struct return member {mName} of type {mTy}"
    let binding ← freshFor s!"{if rname == "" then "ret_struct" else rname}_{mName}"
    pre := pre.push (.letVar binding (.literal 0))
    memberBindings := memberBindings.push (mName, mTy, binding)
    memberExprs := memberExprs.push (mName, mTy, .localVar binding)
  if rname != "" then
    modify fun e =>
      { e with flatStructs := e.flatStructs.insert rid { structId := retSid, structName := retStructName, members := memberBindings },
               yulNames := e.yulNames.erase rname }
  modify fun e =>
    { e with helperResult := none, helperReturnId := none, multiHelperResults := none,
             flatStructHelperResult := some (retSid, retStructName, memberBindings, rname != "") }
  noteFn fn
  let (modStmts, modPost) ← lowerModifiers mods
  modify fun e => { e with helperPost := modPost }
  let stmts ← mArr (← mField body "statements")
  unless rname != "" || !stmts.isEmpty do
    failAt fn "inlined struct helper with unnamed return has an empty body"
  unless rname != "" do
    let definitelyReturns ← match stmts.back? with
      | some b => voidHelperReturns b
      | none => pure false
    unless definitelyReturns do
      failAt fn "inlined struct helper does not return on every path"
  let bodyStmts ← lowerVoidHelperFrom stmts.toList (pure modPost)
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  return (retSid, retStructName, pre ++ modStmts ++ bodyStmts, memberExprs)

private partial def unwrapSignFlipStmts (j : Json) (unchecked : Bool) : M (Array Json × Bool) := do
  let kind ← mKind j
  if kind == "Block" || kind == "UncheckedBlock" then
    let u' := unchecked || kind == "UncheckedBlock"
    let ss ← mArr (← mField j "statements")
    if ss.size == 1 then
      let k0 ← mKind ss[0]!
      if k0 == "Block" || k0 == "UncheckedBlock" then
        unwrapSignFlipStmts ss[0]! u'
      else
        pure (ss, u')
    else
      pure (ss, u')
  else
    pure (#[j], unchecked)

private partial def jsonReferencesDecl (j : Json) (declId : Nat) : Bool :=
  match j with
  | .obj kvs =>
      let selfMatch := match kvs.toList.find? (fun (k, _) => k == "referencedDeclaration") with
        | some (_, v) => v.getInt?.toOption == some (Int.ofNat declId)
        | none => false
      selfMatch || kvs.toList.any (fun (_, v) => jsonReferencesDecl v declId)
  | .arr xs => xs.any (fun x => jsonReferencesDecl x declId)
  | _ => false

/-- Recognizes bounded sign-flip self-calls such as `TickLib.wExp(int256 x)`:
    when a helper `f(int256 x)` whose top-level body is `if (x < 0) ... else { falseBody }`
    (or `if (x < 0) { return ...; } <rest>`) calls `f(-x)` from its `x < 0` branch, `-x` is
    guaranteed non-negative for all `x != type(int256).min` (and for `x == type(int256).min`,
    `wExp(-x)` re-enters the `x < 0` branch and reverts by infinite recursion). Thus `f(-x)`
    can be lowered by guarding against `(-x) < 0` and inlining the non-negative path with
    `x` bound to `-x`. -/
private partial def trySignFlipSelfCall? (fnId : Nat) (args : Array CallArg) (at_ : Json) : M (Option Val) := do
  let stack := (← get).stack
  unless stack.head? == some fnId && !(stack.drop 1).contains fnId do
    return none
  let some fn := (← get).funs.find? fnId | return none
  if optStr fn "visibility" == some "external" then return none
  let mods ← mArr (← mField fn "modifiers")
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless mods.isEmpty && params.size == 1 && args.size == 1 && rets.size == 1 do
    return none
  let p0 := params[0]!
  let pid ← mNat (← mField p0 "id")
  let pty ← mType p0
  unless pty == "int256" || pty == "int" do return none
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull) | return none
  unless implemented && !(bodyAssignedIds body).contains pid do return none
  let arg0 ← stripParens (← argumentAt at_ 0)
  unless (← mKind arg0) == "UnaryOperation" && optStr arg0 "operator" == some "-" do
    return none
  let sub ← stripParens (← mField arg0 "subExpression")
  unless (← mKind sub) == "Identifier" do return none
  unless (← refInt sub) == pid do return none
  let (bodyStmts, topUnchecked) ← unwrapSignFlipStmts body false
  if bodyStmts.isEmpty then return none
  let topStmt := bodyStmts[0]!
  unless (← mKind topStmt) == "IfStatement" do return none
  let cond ← stripParens (← mField topStmt "condition")
  unless (← mKind cond) == "BinaryOperation" do return none
  let op ← mStr (← mField cond "operator")
  let lhs ← stripParens (← mField cond "leftExpression")
  let rhs ← stripParens (← mField cond "rightExpression")
  let isNegCheck ←
    if op == "<" then
      if (← mKind lhs) == "Identifier" then
        if (← refInt lhs) == pid then isZeroLiteral rhs else pure false
      else
        pure false
    else if op == ">" then
      if (← mKind rhs) == "Identifier" then
        if (← refInt rhs) == pid then isZeroLiteral lhs else pure false
      else
        pure false
    else
      pure false
  unless isNegCheck do return none
  let (falseStmts, falseUnchecked) ←
    if bodyStmts.size == 1 then do
      let some fBody := (field? topStmt "falseBody").filter (!·.isNull) | return none
      unwrapSignFlipStmts fBody topUnchecked
    else do
      unless ((field? topStmt "falseBody").filter (!·.isNull)).isNone do return none
      let tBody ← mField topStmt "trueBody"
      unless (← voidHelperReturns tBody) do return none
      pure (bodyStmts.extract 1 bodyStmts.size, topUnchecked)
  if falseStmts.isEmpty then return none
  let fBodyJson := Json.arr falseStmts
  if jsonReferencesDecl fBodyJson fnId then return none
  let saved ← get
  let savedYul := saved.yulNames
  let savedFile := saved.currentFile
  let frameFile := saved.nodeFile.find? fnId |>.getD saved.currentFile
  let frame := fnId :: saved.stack
  modify fun e =>
    { e with stack := frame, currentFile := frameFile, unchecked := falseUnchecked,
             bodyAssigned := bodyAssignedIds fBodyJson, zeroInitLocals := #[] }
  let retName ← mStr (← mField rets[0]! "name")
  let retId ← mNat (← mField rets[0]! "id")
  let (boundPre, yul) ← bindHelperParams params args fBodyJson at_ savedYul
  let mut pre := boundPre
  modify fun e =>
    { e with yulNames := yul, helperResult := none, helperReturnId := some retId,
             multiHelperResults := none, flatStructHelperResult := none }
  let some boundParamExpr := (← get).values.find? pid
    | failAt at_ "unbound sign-flip parameter"
  pre := pre.push (.ite (.slt boundParamExpr (.literal 0)) [.revertReturndata] [])
  noteFn fn
  let resultType ← mType rets[0]!
  discard (validateEnumTypeIfNeeded rets[0]! resultType)
  if retName != "" then
    let declaration := rets[0]!
    let id ← mNat (← mField declaration "id")
    let ty ← mType declaration
    let some scalar := paramType ty
      | failAt declaration s!"unsupported named helper result type {ty}"
    let binding ← freshFor retName
    let expr := Expr.localVar binding
    pre := pre.push (.letVar binding (.literal 0))
    modify fun e =>
      { e with helperResult := some (binding, ty),
               values := e.values.insert id expr, writableLocals := e.writableLocals.insert id binding,
               scalarTy := e.scalarTy.insert id scalar, yulNames := e.yulNames.insert retName expr }
  let result ← lowerHelper falseStmts retName
  let finalResult : Val := { pre := pre ++ result.pre, expr := result.expr }
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, zeroInitLocals := saved.zeroInitLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  return some finalResult

private partial def inlineFn (fnId : Nat) (args : Array CallArg) (at_ : Json) : M Val := do
  if (← get).stack.contains fnId then
    if let some v ← trySignFlipSelfCall? fnId args at_ then
      return v
    failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  -- External library calls cross an ABI/delegatecall boundary. A root
  -- descriptor may only be shared with helpers in the same call frame.
  if optStr fn "visibility" == some "external" then
    for arg in args do
      match arg with
      | .memory _ _ | .abiElement _ _ | .scalarArray _ _ | .byteBuffer _ | .stringBuffer _ | .calldataBytes _ _
      | .storagePath _ _ _ | .flatStruct _ _ _ _ | .storageBytes _ _ | .storageDynamicArray _ _ _ _ _ | .fnPtr _ _ =>
          failAt at_ "external reference helper calls are unsupported"
      | .scalar _ => pure ()
  let saved := ← get
  let savedYul := saved.yulNames
  let savedFile := (← get).currentFile
  let frameFile := (← get).nodeFile.find? fnId |>.getD (← get).currentFile
  let frame := fnId :: (← get).stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body, zeroInitLocals := #[] }
  let mods ← mArr (← mField fn "modifiers")
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "only single-value helpers are inlined"
  let retName ← mStr (← mField rets[0]! "name")
  let retId ← mNat (← mField rets[0]! "id")
  let (boundPre, yul) ← bindHelperParams params args body at_ savedYul
  let mut pre := boundPre
  modify fun e => { e with yulNames := yul }
  noteFn fn
  let stmts ← mArr (← mField body "statements")
  -- Retain the existing direct-result lowering for a single terminal
  -- assembly assignment. A named variable needed by a continuation gets a
  -- declaration-bound slot, initialized before any source-body effect.
  let resultType ← mType rets[0]!
  discard (validateEnumTypeIfNeeded rets[0]! resultType)
  let isSingleYulAssign ← if stmts.size == 1 then do
    if (← mKind stmts[0]!) == "InlineAssembly" then
      let ast ← mField stmts[0]! "AST"
      if (← mKind ast) == "YulBlock" then
        let ystmts ← mArr (← mField ast "statements")
        if ystmts.size == 1 then
          pure ((← mKind ystmts[0]!) == "YulAssignment")
        else pure false
      else pure false
    else pure false
  else pure false
  let terminalAssembly := isSingleYulAssign && mods.isEmpty &&
      (resultType == "uint256" || resultType == "uint" || resultType == "bytes32")
  modify fun e => { e with helperResult := none, helperReturnId := some retId, multiHelperResults := none, flatStructHelperResult := none }
  if retName != "" && !terminalAssembly then
    let declaration := rets[0]!
    let id ← mNat (← mField declaration "id")
    let ty ← mType declaration
    let some scalar := paramType ty
      | failAt declaration s!"unsupported named helper result type {ty}"
    let binding ← freshFor retName
    let expr := Expr.localVar binding
    pre := pre.push (.letVar binding (.literal 0))
    modify fun e =>
      { e with helperResult := some (binding, ty),
               values := e.values.insert id expr, writableLocals := e.writableLocals.insert id binding,
               scalarTy := e.scalarTy.insert id scalar, yulNames := e.yulNames.insert retName expr }
  else if stmts.isEmpty then
    let declaration := rets[0]!
    let ty ← mType declaration
    unless (paramType ty).isSome do
      failAt declaration s!"unsupported helper result type {ty}"
    let binding ← fresh
    pre := pre ++ #[.letVar binding (.literal 0)]
    modify fun e => { e with helperResult := some (binding, ty) }
  let (modStmts, modPost) ← lowerModifiers mods
  pre := pre ++ modStmts
  let result ← lowerHelper stmts retName
  let finalResult ← if modPost.isEmpty then
    pure { pre := pre ++ result.pre, expr := result.expr }
  else do
    let retCapture ← fresh
    pure { pre := (pre ++ result.pre).push (.letVar retCapture result.expr) ++ modPost,
           expr := .localVar retCapture }
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, zeroInitLocals := saved.zeroInitLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  pure finalResult

private partial def inlineVoidFn (fnId : Nat) (args : Array CallArg) (at_ : Json) : M (Array Stmt) := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let visibility := optStr fn "visibility" |>.getD ""
  unless visibility == "internal" || visibility == "private" || visibility == "public" do
    failAt at_ "void helper calls require an internal or private declaration"
  let saved := ← get
  let savedYul := saved.yulNames
  let savedFile := (← get).currentFile
  let savedHelperResult := saved.helperResult
  let savedHelperReturnId := saved.helperReturnId
  let frameFile := (← get).nodeFile.find? fnId |>.getD (← get).currentFile
  let frame := fnId :: (← get).stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body, zeroInitLocals := #[] }
  let mods ← mArr (← mField fn "modifiers")
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.isEmpty do failAt fn "expected void helper"
  let (pre, yul) ← bindHelperParams params args body at_ savedYul
  modify fun e => { e with yulNames := yul, helperResult := none, helperReturnId := none, multiHelperResults := none, flatStructHelperResult := none }
  noteFn fn
  let (modStmts, modPost) ← lowerModifiers mods
  modify fun e => { e with helperPost := modPost }
  let stmts ← mArr (← mField body "statements")
  let bodyStmts ← lowerVoidHelperFrom stmts.toList (pure modPost)
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, zeroInitLocals := saved.zeroInitLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := savedHelperResult, helperReturnId := savedHelperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  pure (pre ++ modStmts ++ bodyStmts)

private partial def lowerMsgDataExpr (j : Json) : M (Array Stmt) := do
  if ← isMsgDataNode j then
    return #[]
  if (← mKind j) == "FunctionCall" && optStr j "kind" == some "functionCall" then
    let names ← mArr (← mField j "names")
    unless names.isEmpty do failAt j "named call arguments are outside this slice"
    let args ← mArr (← mField j "arguments")
    unless args.isEmpty do failAt j "msg.data helper call must take zero arguments"
    let (fnId, vals) ← resolveCallTargetAndArgs j
    return ← inlineMsgDataFn fnId vals j
  failAt j "bytes return requires msg.data or an inlined _msgData() helper"

private partial def inlineMsgDataFn (fnId : Nat) (args : Array CallArg) (at_ : Json) : M (Array Stmt) := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let visibility := optStr fn "visibility" |>.getD ""
  unless visibility == "internal" || visibility == "private" || visibility == "public" do
    failAt at_ "msg.data helper calls require an internal, private, or public declaration"
  let saved ← get
  let savedYul := saved.yulNames
  let savedFile := saved.currentFile
  let frameFile := saved.nodeFile.find? fnId |>.getD saved.currentFile
  let frame := fnId :: saved.stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mods ← mArr (← mField fn "modifiers")
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.isEmpty && args.isEmpty do
    failAt at_ "msg.data helper must take zero parameters"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "msg.data helper must have one return parameter"
  let r := rets[0]!
  let rname ← mStr (← mField r "name")
  unless rname == "" do failAt r "named msg.data helper return is unsupported"
  let rloc := optStr r "storageLocation" |>.getD "default"
  unless (rloc == "calldata" || rloc == "memory") && (← mType r) == "bytes" do
    failAt r "msg.data helper return must be bytes calldata or bytes memory"
  noteFn fn
  let (modStmts, modPost) ← lowerModifiers mods
  let stmts ← mArr (← mField body "statements")
  unless stmts.size == 1 && (← mKind stmts[0]!) == "Return" do
    failAt fn "msg.data helper must be a single return statement"
  let retExpr := field? stmts[0]! "expression" |>.getD Json.null
  if retExpr.isNull then failAt stmts[0]! "msg.data helper return requires an expression"
  let bodyPre ← lowerMsgDataExpr retExpr
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  pure (modStmts ++ bodyPre ++ modPost)

private partial def inlineMultiFn (fnId : Nat) (args : Array CallArg) (at_ : Json) : M (Array Stmt × Array (Expr × String)) := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let visibility := optStr fn "visibility" |>.getD ""
  unless visibility == "internal" || visibility == "private" || visibility == "public" do
    failAt at_ "multi-return helper calls require an internal or private declaration"
  let saved := ← get
  let savedYul := saved.yulNames
  let savedFile := (← get).currentFile
  let frameFile := (← get).nodeFile.find? fnId |>.getD (← get).currentFile
  let frame := fnId :: (← get).stack
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mods ← mArr (← mField fn "modifiers")
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size > 1 do failAt fn "expected multi-return helper"
  let (boundPre, yul) ← bindHelperParams params args body at_ savedYul
  let mut pre := boundPre
  modify fun e => { e with yulNames := yul }
  let mut results : Array (String × String × Bool) := #[]
  let mut retExprs : Array (Expr × String) := #[]
  for r in rets do
    let rname ← mStr (← mField r "name")
    let rid ← mNat (← mField r "id")
    let rty ← mType r
    discard (validateEnumTypeIfNeeded r rty)
    let some scalar := paramType rty
      | failAt r s!"unsupported multi-return helper result type {rty}"
    let binding ← if rname != "" then freshFor rname else fresh
    let expr := Expr.localVar binding
    pre := pre ++ #[.letVar binding (.literal 0)]
    results := results.push (binding, rty, rname != "")
    retExprs := retExprs.push (expr, rty)
    if rname != "" then
      modify fun e =>
        { e with values := e.values.insert rid expr,
                 writableLocals := e.writableLocals.insert rid binding,
                 scalarTy := e.scalarTy.insert rid scalar,
                 yulNames := e.yulNames.insert rname expr }
  modify fun e => { e with helperResult := none, helperReturnId := none, multiHelperResults := some results, flatStructHelperResult := none }
  noteFn fn
  let (modStmts, modPost) ← lowerModifiers mods
  modify fun e => { e with helperPost := modPost }
  let stmts ← mArr (← mField body "statements")
  let allNamed := results.all (fun (_, _, isNamed) => isNamed)
  unless allNamed || stmts.isEmpty do
    let definitelyReturns ← match stmts.back? with
      | some b => voidHelperReturns b
      | none => pure false
    unless definitelyReturns do
      failAt fn "inlined multi-return helper does not return on every path"
  let bodyStmts ← lowerVoidHelperFrom stmts.toList (pure modPost)
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  pure (pre ++ modStmts ++ bodyStmts, retExprs)

private partial def lowerMultiBranch (j : Json) (expectedTypes : Option (Array (Option String))) :
    M (Array Stmt × Array (Expr × String)) := do
  match ← mKind j with
  | "TupleExpression" =>
      if ← mBool (← mField j "isInlineArray") then
        failAt j "inline arrays are outside this slice"
      let cs ← mArr (← mField j "components")
      unless cs.size > 1 do
        failAt j "tuple expression requires multiple components"
      if let some exp := expectedTypes then
        unless cs.size == exp.size do
          failAt j s!"tuple expression arity {cs.size} does not match target arity {exp.size}"
      let mut pre : Array Stmt := #[]
      let mut rets : Array (Expr × String) := #[]
      for i in [:cs.size] do
        let c := cs[i]!
        if c.isNull then failAt j "empty tuple component"
        if cs.size > 1 && (statefulCallIn c (← get) || assignmentIn c) then
          failAt c "stateful or assignment expression in multi-return tuple requires explicit evaluation-order support"
        let rawTy ← mType c
        let rawVal ← lowerExpr c
        let (val, outTy) ← match expectedTypes.bind (fun xs => xs.getD i none) with
          | some targetTy => do
              let v ← atom (← convert targetTy rawTy rawVal c)
              pure (v, targetTy)
          | none => do
              let v ← atom rawVal
              let outTy := if rawTy.startsWith "int_const" && !rawTy.startsWith "int_const -" then "uint256" else rawTy
              pure (v, outTy)
        pre := pre ++ val.pre
        let finalExpr ← match val.expr with
          | .localVar name => do
              if (← get).writableLocals.toList.any (fun (_, b) => b == name) then
                let snap ← fresh
                pre := pre.push (.letVar snap (.localVar name))
                pure (.localVar snap)
              else
                pure val.expr
          | _ => pure val.expr
        rets := rets.push (finalExpr, outTy)
      return (pre, rets)
  | "Conditional" =>
      let condNode ← mField j "condition"
      unless (← mType condNode) == "bool" do failAt condNode "conditional condition must be bool"
      let cond ← atom (← lowerExpr condNode)
      let (yesPre, yesRets) ← lowerMultiBranch (← mField j "trueExpression") expectedTypes
      let (noPre, noRets) ← lowerMultiBranch (← mField j "falseExpression") expectedTypes
      unless yesRets.size == noRets.size do
        failAt j "conditional tuple branches have mismatched arities"
      let mut pre := cond.pre
      let mut thenB := yesPre
      let mut elseB := noPre
      let mut outRets : Array (Expr × String) := #[]
      for i in [:yesRets.size] do
        let (yExpr, yTy) := yesRets.getD i (.literal 0, "")
        let (nExpr, nTy) := noRets.getD i (.literal 0, "")
        unless yTy == nTy do
          failAt j "conditional tuple branches have mismatched component types"
        let dest ← fresh
        pre := pre.push (.letVar dest (.literal 0))
        thenB := thenB.push (.assignVar dest yExpr)
        elseB := elseB.push (.assignVar dest nExpr)
        outRets := outRets.push (.localVar dest, yTy)
      return (pre.push (.ite cond.expr thenB.toList elseB.toList), outRets)
  | _ =>
      let (callPre, retExprs) ← lowerMultiCall j expectedTypes
      if let some exp := expectedTypes then
        unless retExprs.size == exp.size do
          failAt j s!"tuple expression arity {retExprs.size} does not match target arity {exp.size}"
        let mut pre := callPre
        let mut out : Array (Expr × String) := #[]
        for i in [:retExprs.size] do
          let (rExpr, rTy) := retExprs.getD i (.literal 0, "")
          match exp.getD i none with
          | some targetTy =>
              let v ← atom (← convert targetTy rTy { pre := #[], expr := rExpr } j)
              pre := pre ++ v.pre
              out := out.push (v.expr, targetTy)
          | none =>
              out := out.push (rExpr, rTy)
        return (pre, out)
      return (callPre, retExprs)

private partial def lowerMultiCall (j : Json) (expectedTypes : Option (Array (Option String)) := none) :
    M (Array Stmt × Array (Expr × String)) := do
  if (← mKind j) == "Conditional" then
    return ← lowerMultiBranch j expectedTypes
  unless (← mKind j) == "FunctionCall" && optStr j "kind" == some "functionCall" do
    failAt j "tuple destructuring requires a multi-return helper call"
  if ← isAbiDecodeCall j then
    let (decodePre, decoded) ← lowerAbiDecodeItems j
    unless decoded.size > 1 do
      failAt j "tuple abi.decode requires multiple target types"
    let mut retExprs : Array (Expr × String) := #[]
    for i in [:decoded.size] do
      let wantValue := match expectedTypes with
        | some want => (want.getD i none).isSome
        | none => true
      if wantValue then
        let .scalar ty _ expr := decoded[i]!
          | failAt j "tuple assignment or return from abi.decode only supports scalar components"
        retExprs := retExprs.push (expr, ty)
      else
        retExprs := retExprs.push (.literal 0, "uint256")
    return (decodePre, retExprs)
  let callee ← mField j "expression"
  if (← mKind callee) == "Identifier" then
    let calleeId ← refInt callee
    if calleeId ≥ 0 then
      if let some ptr := (← get).fnPtrs.find? calleeId.toNat then
        let names ← mArr (← mField j "names")
        unless names.isEmpty do failAt j "named call arguments are outside this slice"
        let vals ← lowerCallArgs j none
        match ptr with
        | .direct fnId => return ← inlineMultiFn fnId vals j
        | .branch cond trueFnId falseFnId =>
            let (argPre, atomicVals) ← atomizeCallArgs vals
            let (yesPre, yesRets) ← inlineMultiFn trueFnId atomicVals j
            let (noPre, noRets) ← inlineMultiFn falseFnId atomicVals j
            unless yesRets.size == noRets.size do
              failAt j "conditional function pointer branches have mismatched return arities"
            let mut pre := argPre
            let mut thenB := yesPre
            let mut elseB := noPre
            let mut outRets : Array (Expr × String) := #[]
            for i in [:yesRets.size] do
              let (yExpr, yTy) := yesRets.getD i (.literal 0, "")
              let (nExpr, nTy) := noRets.getD i (.literal 0, "")
              unless yTy == nTy do
                failAt j "conditional function pointer branches have mismatched return types"
              let dest ← fresh
              pre := pre.push (.letVar dest (.literal 0))
              thenB := thenB.push (.assignVar dest yExpr)
              elseB := elseB.push (.assignVar dest nExpr)
              outRets := outRets.push (.localVar dest, yTy)
            return (pre.push (.ite cond thenB.toList elseB.toList), outRets)
  let (fnId, vals) ← resolveCallTargetAndArgs j
  inlineMultiFn fnId vals j

private partial def lowerModifier (modInv : Json) : M (Array Stmt × Array Stmt) := do
  let kind? := optStr modInv "kind"
  if kind?.isSome && kind? != some "modifierInvocation" then
    failAt modInv "base constructor calls are outside this slice"
  let modNode ← mField modInv "modifierName"
  let refId ← refInt modNode
  if refId < 0 then failAt modInv "unresolved modifier"
  let modId := refId.toNat
  if (← get).stack.contains modId then failAt modInv s!"recursive modifier {modId}"
  let some modDecl := (← get).modifiers.find? modId | failAt modInv s!"unresolved modifier {modId}"
  if optStr modDecl "virtual" == some "true" || (field? modDecl "virtual").bind (fun v => v.getBool?.toOption) == some true then
    failAt modDecl "virtual modifiers are outside this slice"
  let implemented := (field? modDecl "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? modDecl "body").filter (!·.isNull)
    | failAt modDecl "modifier has no body"
  unless implemented do failAt modDecl "modifier has no body"
  let stmts ← mArr (← mField body "statements")
  let mut placeholderIdx? : Option Nat := none
  for i in [:stmts.size] do
    if (← mKind stmts[i]!) == "PlaceholderStatement" then
      if placeholderIdx?.isSome then
        failAt modDecl "only a single top-level _; placeholder is supported in modifiers"
      placeholderIdx? := some i
  let some placeholderIdx := placeholderIdx?
    | failAt modDecl "only a single top-level _; placeholder is supported in modifiers"
  let preStmts := stmts.extract 0 placeholderIdx
  let postStmts := stmts.extract (placeholderIdx + 1) stmts.size
  if (← preStmts.anyM stmtContainsPlaceholder) || (← postStmts.anyM stmtContainsPlaceholder) then
    failAt modDecl "only a single top-level _; placeholder is supported in modifiers"
  if (← preStmts.anyM stmtContainsReturn) || (← postStmts.anyM stmtContainsReturn) then
    failAt modDecl "return inside a modifier is outside this slice"
  let params ← mArr (← mField (← mField modDecl "parameters") "parameters")
  let args ← match field? modInv "arguments" with
    | some j => if j.isNull then pure #[] else mArr j
    | none => pure #[]
  unless params.size == args.size do
    failAt modInv s!"modifier arity {args.size} does not match declaration {params.size}"
  let mut argVals : Array Val := #[]
  for i in [:args.size] do
    let argNode := args[i]!
    if statefulCallIn argNode (← get) then
      failAt argNode "stateful modifier arguments require explicit evaluation-order support"
    if args.size > 1 && assignmentIn argNode then
      failAt argNode "assignment expression in multi-argument modifier requires explicit evaluation-order support"
    argVals := argVals.push (← lowerExpr argNode)
  let saved ← get
  let savedYul := saved.yulNames
  let savedFile := saved.currentFile
  let savedHelperResult := saved.helperResult
  let savedHelperReturnId := saved.helperReturnId
  let frameFile := saved.nodeFile.find? modId |>.getD saved.currentFile
  let frame := modId :: saved.stack
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mut pre : Array Stmt := #[]
  let mut yul := savedYul
  for i in [:params.size] do
    let p := params[i]!
    let pname ← mStr (← mField p "name")
    let pid ← mNat (← mField p "id")
    let pty ← mType p
    discard (validateEnumTypeIfNeeded p pty)
    let some scalar := paramType pty
      | failAt p s!"unsupported modifier parameter type {pty}"
    let argNode := args[i]!
    let argTy ← mType argNode
    let some argVal := argVals[i]? | failAt argNode s!"missing modifier argument {i}"
    let converted ← convert pty argTy argVal argNode
    if (bodyCompoundAssignedIds body).contains pid || (bodyDirectAssignedIds body).contains pid then
      let binding ← freshFor (if pname == "" then "param" else pname)
      let expr := Expr.localVar binding
      pre := pre ++ converted.pre |>.push (.letVar binding converted.expr)
      modify fun e =>
        { e with values := e.values.insert pid expr,
                 writableLocals := e.writableLocals.insert pid binding,
                 scalarTy := e.scalarTy.insert pid scalar }
      if pname != "" then
        yul := yul.insert pname expr
    else
      let bound ← atom converted
      pre := pre ++ bound.pre
      modify fun e => { e with values := e.values.insert pid bound.expr }
      if pname != "" then
        yul := yul.insert pname bound.expr
  modify fun e => { e with yulNames := yul, helperResult := none, helperReturnId := none, multiHelperResults := none, flatStructHelperResult := none, helperPost := #[] }
  noteFn modDecl
  let preBodyStmts ← lowerVoidHelperFrom preStmts.toList (pure #[])
  let postBodyStmts ← lowerVoidHelperFrom postStmts.toList (pure #[])
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, yulMemoryArrays := saved.yulMemoryArrays, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths,
             snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, flatStructs := saved.flatStructs, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned,
             helperResult := savedHelperResult, helperReturnId := savedHelperReturnId, multiHelperResults := saved.multiHelperResults, flatStructHelperResult := saved.flatStructHelperResult, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  pure (pre ++ preBodyStmts, postBodyStmts)

private partial def lowerModifiers (mods : Array Json) : M (Array Stmt × Array Stmt) := do
  let mut outPre : Array Stmt := #[]
  let mut outPost : Array Stmt := #[]
  for modInv in mods do
    let (preStmts, postStmts) ← lowerModifier modInv
    outPre := outPre ++ preStmts
    outPost := postStmts ++ outPost
  pure (outPre, outPost)

private partial def lowerHelper (stmts : Array Json) (retName : String) : M Val := do
  let (pre, result) ← lowerHelperFrom stmts.toList retName
  match result with
  | some expr => pure { pre, expr }
  | none => throwError "inlined helper did not return"

/-- Splits an `if` into its lowered boolean condition and branch statements.
    A branch that is not a block is a single statement. -/
private partial def ifParts (s : Json) : M (Val × Array Json × Array Json) := do
  let assignedInIf := bodyAssignedIds s
  if !assignedInIf.isEmpty then
    modify fun e => { e with zeroInitLocals := e.zeroInitLocals.filter (!assignedInIf.contains ·) }
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

private partial def stripParens (j : Json) : M Json := do
  if (← mKind j) == "TupleExpression" then
    unless ← mBool (← mField j "isInlineArray") do
      let cs ← mArr (← mField j "components")
      if cs.size == 1 && !cs[0]!.isNull then
        return ← stripParens cs[0]!
  pure j

private partial def stripUintCast (j : Json) (minBits : Nat) : M Json := do
  let j ← stripParens j
  if (← mKind j) == "FunctionCall" && optStr j "kind" == some "typeConversion" then
    let ty ← mType j
    if let some b := bitsOf ty then
      if ty.startsWith "uint" && b ≥ minBits then
        let args ← mArr (← mField j "arguments")
        if args.size == 1 then
          return ← stripUintCast args[0]! minBits
  pure j

private partial def isIdentId (j : Json) (targetId : Nat) : M Bool := do
  let j ← stripParens j
  if (← mKind j) != "Identifier" then return false
  pure ((← refInt j) == targetId)

private partial def isZeroLiteral (j : Json) : M Bool := do
  let j ← stripParens j
  pure ((← mType j) == "int_const 0")

private partial def isOneLiteral (j : Json) : M Bool := do
  let j ← stripParens j
  pure ((← mType j) == "int_const 1")

private partial def isPositiveShiftConst (j : Json) : M Bool := do
  let j ← stripParens j
  if (← mKind j) != "Literal" || optStr j "kind" != some "number" then return false
  let raw ← mStr (← mField j "value")
  match Compiler.Hex.parseHexNat? raw <|> raw.toNat? with
  | some n => pure (n ≥ 1 && n < 256)
  | none => pure false

private partial def callTargetAndArity? (call : Json) : M (Option (Nat × Nat)) := do
  let call ← stripParens call
  unless (← mKind call) == "FunctionCall" && optStr call "kind" == some "functionCall" do
    return none
  unless (← mArr (← mField call "names")).isEmpty do return none
  let callee ← mField call "expression"
  let args ← mArr (← mField call "arguments")
  match ← mKind callee with
  | "Identifier" =>
      let id ← refInt callee
      if id < 0 then return none
      let env ← get
      let resolvedId := match env.funContractId.find? id.toNat with
        | some cid =>
            if env.linearizedBases.contains cid then
              resolveInContracts env env.linearizedBases.toList id.toNat |>.getD id.toNat
        else id.toNat
        | none => id.toNat
      return some (resolvedId, args.size)
  | "MemberAccess" =>
      let id ← refInt callee
      if id < 0 then return none
      let base ← mField callee "expression"
      let baseTy ← mType base
      if baseTy.startsWith "type(library " || baseTy.startsWith "type(contract " then
        return some (id.toNat, args.size)
      else
        let env ← get
        let isLibrary := match env.funContractId.find? id.toNat with
          | some cid => env.contractKinds.find? cid == some "library"
          | none => false
        if isLibrary then return some (id.toNat, args.size + 1)
        else return none
  | _ => return none

private partial def isYulClzOf (y : Json) (paramName : String) : M Bool := do
  unless (← mKind y) == "YulFunctionCall" do return false
  let fname ← mStr (← mField (← mField y "functionName") "name")
  unless fname == "clz" do return false
  let yargs ← mArr (← mField y "arguments")
  unless yargs.size == 1 do return false
  let arg0 := yargs[0]!
  unless (← mKind arg0) == "YulIdentifier" do return false
  pure ((← mStr (← mField arg0 "name")) == paramName)

private partial def isYulSub255ClzOf (y : Json) (paramName : String) : M Bool := do
  unless (← mKind y) == "YulFunctionCall" do return false
  let fname ← mStr (← mField (← mField y "functionName") "name")
  unless fname == "sub" do return false
  let yargs ← mArr (← mField y "arguments")
  unless yargs.size == 2 do return false
  let arg0 := yargs[0]!
  unless (← mKind arg0) == "YulLiteral" && optStr arg0 "kind" == some "number" do return false
  let raw ← mStr (← mField arg0 "value")
  let some litVal := Compiler.Hex.parseHexNat? raw <|> raw.toNat? | return false
  unless litVal == 255 do return false
  isYulClzOf yargs[1]! paramName

private partial def isMsbCallOn (j : Json) (varId : Nat) : M Bool := do
  let j ← stripUintCast j 8
  let some (fnId, arity) ← callTargetAndArity? j | return false
  unless arity == 1 do return false
  let call ← stripParens j
  let arg0 ← argumentAt call 0
  unless ← isIdentId (← stripUintCast arg0 8) varId do return false
  let some fn := (← get).funs.find? fnId | return false
  unless (← mArr (← mField fn "modifiers")).isEmpty do return false
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless params.size == 1 && rets.size == 1 do return false
  let paramName ← mStr (← mField params[0]! "name")
  let retName ← mStr (← mField rets[0]! "name")
  let some body := (field? fn "body").filter (!·.isNull) | return false
  let stmts ← mArr (← mField body "statements")
  unless stmts.size == 1 do return false
  unless (← mKind stmts[0]!) == "InlineAssembly" do return false
  let ast ← mField stmts[0]! "AST"
  unless (← mKind ast) == "YulBlock" do return false
  let ystmts ← mArr (← mField ast "statements")
  unless ystmts.size == 1 do return false
  unless (← mKind ystmts[0]!) == "YulAssignment" do return false
  let vars ← mArr (← mField ystmts[0]! "variableNames")
  unless vars.size == 1 do return false
  unless (← mStr (← mField vars[0]! "name")) == retName do return false
  isYulSub255ClzOf (← mField ystmts[0]! "value") paramName

private partial def isClearLowestBitExpr (j : Json) (varId bits : Nat) : M Bool := do
  let j ← stripUintCast j bits
  unless (← mKind j) == "BinaryOperation" && optStr j "operator" == some "&" do return false
  let lhs ← stripParens (← mField j "leftExpression")
  let rhs ← stripParens (← mField j "rightExpression")
  let isSubOne (e : Json) : M Bool := do
    let e ← stripUintCast e bits
    unless (← mKind e) == "BinaryOperation" && optStr e "operator" == some "-" do return false
    pure ((← isIdentId (← mField e "leftExpression") varId) &&
          (← isOneLiteral (← mField e "rightExpression")))
  pure (((← isIdentId lhs varId) && (← isSubOne rhs)) ||
        ((← isSubOne lhs) && (← isIdentId rhs varId)))

private partial def isNotShiftBitExpr (j : Json) (bitId : Nat) : M Bool := do
  let j ← stripParens j
  unless (← mKind j) == "UnaryOperation" && optStr j "operator" == some "~" do return false
  let sub ← stripParens (← mField j "subExpression")
  unless (← mKind sub) == "BinaryOperation" && optStr sub "operator" == some "<<" do return false
  let shiftLhs ← stripUintCast (← mField sub "leftExpression") 1
  let shiftRhs ← stripParens (← mField sub "rightExpression")
  pure ((← isOneLiteral shiftLhs) && (← isIdentId shiftRhs bitId))

private partial def isDirectClearBitMaskExpr (j : Json) (varId bitId bits : Nat) : M Bool := do
  let j ← stripUintCast j bits
  unless (← mKind j) == "BinaryOperation" && optStr j "operator" == some "&" do return false
  let lhs ← stripParens (← mField j "leftExpression")
  let rhs ← stripParens (← mField j "rightExpression")
  pure (((← isIdentId lhs varId) && (← isNotShiftBitExpr rhs bitId)) ||
        ((← isNotShiftBitExpr lhs bitId) && (← isIdentId rhs varId)))

private partial def isClearBitExpr (j : Json) (varId bitId bits : Nat) : M Bool := do
  if ← isDirectClearBitMaskExpr j varId bitId bits then return true
  let j ← stripUintCast j bits
  let some (fnId, arity) ← callTargetAndArity? j | return false
  unless arity == 2 do return false
  let call ← stripParens j
  let arg0 ← argumentAt call 0
  let arg1 ← argumentAt call 1
  unless (← isIdentId arg0 varId) && (← isIdentId arg1 bitId) do return false
  let some fn := (← get).funs.find? fnId | return false
  unless (← mArr (← mField fn "modifiers")).isEmpty do return false
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless params.size == 2 && rets.size == 1 do return false
  let p0Id ← mNat (← mField params[0]! "id")
  let p1Id ← mNat (← mField params[1]! "id")
  let some body := (field? fn "body").filter (!·.isNull) | return false
  let stmts ← mArr (← mField body "statements")
  unless stmts.size == 1 do return false
  unless (← mKind stmts[0]!) == "Return" do return false
  let some retExpr := (field? stmts[0]! "expression").filter (!·.isNull) | return false
  isDirectClearBitMaskExpr retExpr p0Id p1Id bits

private partial def isTwoLiteral (j : Json) : M Bool := do
  let j ← stripParens j
  pure ((← mType j) == "int_const 2")

private partial def isSymmetricBinOpOn (j : Json) (op : String) (aId bId bits : Nat) : M Bool := do
  let j ← stripUintCast j bits
  unless (← mKind j) == "BinaryOperation" && optStr j "operator" == some op do return false
  let lhs ← stripUintCast (← mField j "leftExpression") bits
  let rhs ← stripUintCast (← mField j "rightExpression") bits
  pure (((← isIdentId lhs aId) && (← isIdentId rhs bId)) ||
        ((← isIdentId lhs bId) && (← isIdentId rhs aId)))

private partial def isHalfOfExpr (j : Json) (bits : Nat) (checkSub : Json → M Bool) : M Bool := do
  let j ← stripUintCast j bits
  unless (← mKind j) == "BinaryOperation" do return false
  let op := optStr j "operator"
  let lhs ← mField j "leftExpression"
  let rhs ← mField j "rightExpression"
  if op == some "/" then
    pure ((← checkSub lhs) && (← isTwoLiteral rhs))
  else if op == some ">>" then
    pure ((← checkSub lhs) && (← isOneLiteral rhs))
  else
    pure false

private partial def isDirectMidpointExpr (j : Json) (lowId highId bits : Nat) : M Bool := do
  let j ← stripUintCast j bits
  if ← isHalfOfExpr j bits (fun sub => isSymmetricBinOpOn sub "+" lowId highId bits) then
    return true
  unless (← mKind j) == "BinaryOperation" && optStr j "operator" == some "+" do return false
  let lhs ← stripUintCast (← mField j "leftExpression") bits
  let rhs ← stripUintCast (← mField j "rightExpression") bits
  let isXorHalf (e : Json) := isHalfOfExpr e bits (fun sub => isSymmetricBinOpOn sub "^" lowId highId bits)
  if ((← isSymmetricBinOpOn lhs "&" lowId highId bits) && (← isXorHalf rhs)) ||
     ((← isXorHalf lhs) && (← isSymmetricBinOpOn rhs "&" lowId highId bits)) then
    return true
  let isDiffHalf (e : Json) : M Bool :=
    isHalfOfExpr e bits fun sub => do
      let sub ← stripUintCast sub bits
      unless (← mKind sub) == "BinaryOperation" && optStr sub "operator" == some "-" do return false
      pure ((← isIdentId (← stripUintCast (← mField sub "leftExpression") bits) highId) &&
            (← isIdentId (← stripUintCast (← mField sub "rightExpression") bits) lowId))
  pure (((← isIdentId lhs lowId) && (← isDiffHalf rhs)) ||
        ((← isDiffHalf lhs) && (← isIdentId rhs lowId)))

private partial def isBinarySearchMidpointExpr (j : Json) (lowId highId bits : Nat) : M Bool := do
  if ← isDirectMidpointExpr j lowId highId bits then return true
  let j ← stripUintCast j bits
  let some (fnId, arity) ← callTargetAndArity? j | return false
  unless arity == 2 do return false
  let call ← stripParens j
  let arg0 ← stripUintCast (← argumentAt call 0) bits
  let arg1 ← stripUintCast (← argumentAt call 1) bits
  let argsMatch ← pure (((← isIdentId arg0 lowId) && (← isIdentId arg1 highId)) ||
                        ((← isIdentId arg0 highId) && (← isIdentId arg1 lowId)))
  unless argsMatch do return false
  let some fn := (← get).funs.find? fnId | return false
  unless (← mArr (← mField fn "modifiers")).isEmpty do return false
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless params.size == 2 && rets.size == 1 do return false
  let p0Id ← mNat (← mField params[0]! "id")
  let p1Id ← mNat (← mField params[1]! "id")
  let some body := (field? fn "body").filter (!·.isNull) | return false
  let stmts ← mArr (← mField body "statements")
  unless stmts.size == 1 do return false
  let s0 := stmts[0]!
  let retStmt ← if (← mKind s0) == "UncheckedBlock" then do
    let inner ← mArr (← mField s0 "statements")
    if inner.size == 1 then pure inner[0]! else pure Json.null
  else pure s0
  if retStmt.isNull || (← mKind retStmt) != "Return" then return false
  let some retExpr := (field? retStmt "expression").filter (!·.isNull) | return false
  if ← isIdentId arg0 lowId then
    isDirectMidpointExpr retExpr p0Id p1Id bits
  else
    isDirectMidpointExpr retExpr p1Id p0Id bits

/-- Recognizes a binary-search branch statement:
    - `some true` for `high = mid;`
    - `some false` for `low = mid + 1;` (including inside `unchecked { ... }`) -/
private partial def classifyBinarySearchBranch (branchNode : Json) (lowId highId midId bits : Nat) :
    M (Option Bool) := do
  let kind ← mKind branchNode
  if kind == "Block" || kind == "UncheckedBlock" then
    let stmts ← mArr (← mField branchNode "statements")
    unless stmts.size == 1 do return none
    return ← classifyBinarySearchBranch stmts[0]! lowId highId midId bits
  unless kind == "ExpressionStatement" do return none
  let expr ← mField branchNode "expression"
  unless (← mKind expr) == "Assignment" && optStr expr "operator" == some "=" do return none
  let lhs ← mField expr "leftHandSide"
  let rhs ← stripUintCast (← mField expr "rightHandSide") bits
  if ← isIdentId lhs highId then
    if ← isIdentId rhs midId then return some true else return none
  if ← isIdentId lhs lowId then
    if (← mKind rhs) == "BinaryOperation" && optStr rhs "operator" == some "+" then
      let rl ← stripUintCast (← mField rhs "leftExpression") bits
      let rr ← stripUintCast (← mField rhs "rightExpression") bits
      if ((← isIdentId rl midId) && (← isOneLiteral rr)) ||
         ((← isOneLiteral rl) && (← isIdentId rr midId)) then
        return some false
  return none

private partial def stmtContainsInlineAssembly (s : Json) : M Bool := do
  match ← mKind s with
  | "InlineAssembly" => pure true
  | "Block" | "UncheckedBlock" =>
      (← mArr (← mField s "statements")).anyM stmtContainsInlineAssembly
  | "ForStatement" | "WhileStatement" =>
      stmtContainsInlineAssembly (← mField s "body")
  | "IfStatement" =>
      let yes ← stmtContainsInlineAssembly (← mField s "trueBody")
      let no ← match field? s "falseBody" with
        | some j => if j.isNull then pure false else stmtContainsInlineAssembly j
        | none => pure false
      pure (yes || no)
  | _ => pure false

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
        else if (← mKind boundNode) == "MemberAccess" &&
            optStr boundNode "memberName" == some "length" then
          pure bound.pre.isEmpty
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
    if ← stmtContainsInlineAssembly body then
      failAt body "ABI-length loop body may write memory or call external code (unsupported statement InlineAssembly)"
    unless executableStmtListCovered bodyOut.toList do
      failAt body "ABI-length loop body may write memory or call external code"
  modify fun e =>
    { e with values := saved.values, paths := saved.paths,
             snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy,
             writableLocals := saved.writableLocals, zeroInitLocals := saved.zeroInitLocals.filter (!writes.contains ·), fnPtrs := saved.fnPtrs, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
  let mut out : Array Stmt := #[]
  if abiLength then
    let captured ← fresh
    out := out ++ bound.pre |>.push (.letVar captured bound.expr)
    out := out.push (.forEach binding (.localVar captured) bodyOut.toList)
  else
    out := out.push (.forEach binding bound.expr bodyOut.toList)
  pure out

private partial def unwrapLoopBodyStmts (j : Json) : M (Array Json) := do
  let kind ← mKind j
  if kind == "Block" || kind == "UncheckedBlock" then
    let stmts ← mArr (← mField j "statements")
    if stmts.size == 1 && ((← mKind stmts[0]!) == "Block" || (← mKind stmts[0]!) == "UncheckedBlock") then
      unwrapLoopBodyStmts stmts[0]!
    else
      pure stmts
  else
    pure #[j]

/-- Exact bounded while-loop lowering for:
    1. unsigned bit-clearing (`msb` + `clearBit` or `v &= v - 1`) and positive constant right-shift (`v >>= k`)
    2. binary-search `while (low < high)` / `while (high > low)` / `while (low != high)` (with `low == 0` at entry)
       loops where `mid = average(low, high)` and one branch sets `high = mid` while the other sets `low = mid + 1`. -/
private partial def lowerWhile (s : Json) (lowerBody : Json → M (Array Stmt)) : M (Array Stmt) := do
  let cond ← mField s "condition"
  unless (← mKind cond) == "BinaryOperation" do
    failAt cond "a while loop condition must compare a loop variable against zero"
  let condOp ← mStr (← mField cond "operator")
  let condLhs ← stripParens (← mField cond "leftExpression")
  let condRhs ← stripParens (← mField cond "rightExpression")
  if (condOp == "<" || condOp == ">" || condOp == "!=") &&
      (← mKind condLhs) == "Identifier" && (← mKind condRhs) == "Identifier" then
    let lhsRef ← refInt condLhs
    let rhsRef ← refInt condRhs
    if lhsRef ≥ 0 && rhsRef ≥ 0 && lhsRef != rhsRef then
      let lhsId := lhsRef.toNat
      let rhsId := rhsRef.toNat
      let env ← get
      if (env.writableLocals.find? lhsId).isSome && (env.writableLocals.find? rhsId).isSome then
        let lhsTy ← mType condLhs
        let rhsTy ← mType condRhs
        if let some bits := bitsOf lhsTy then
          if lhsTy == rhsTy && lhsTy.startsWith "uint" && bits > 0 && bits ≤ 256 then
            let body ← mField s "body"
            let bodyStmts ← unwrapLoopBodyStmts body
            if ← listContainsReturn bodyStmts then
              failAt s "return inside a while loop is unsupported"
            unless bodyStmts.size == 2 do
              failAt body "a binary-search while loop body must declare mid and branch on mid"
            let midStmt := bodyStmts[0]!
            let ifStmt := bodyStmts[1]!
            unless (← mKind midStmt) == "VariableDeclarationStatement" && (← mKind ifStmt) == "IfStatement" do
              failAt body "a binary-search while loop body must declare mid followed by an if/else update"
            let decls ← mArr (← mField midStmt "declarations")
            let initVal := field? midStmt "initialValue" |>.getD Json.null
            unless decls.size == 1 && !decls[0]!.isNull && !initVal.isNull do
              failAt midStmt "binary-search midpoint declaration requires an initializer"
            let midDecl := decls[0]!
            let midId ← mNat (← mField midDecl "id")
            let midTy ← mType midDecl
            unless midTy == lhsTy && !(bodyAssignedIds body).contains midId do
              failAt midDecl "binary-search midpoint must be an unassigned local of the bound type"
            let ifCond ← mField ifStmt "condition"
            if statefulCallIn ifCond env || assignmentIn ifCond then
              failAt ifCond "stateful or assignment binary-search condition is unsupported"
            let tBody ← mField ifStmt "trueBody"
            let fBody := field? ifStmt "falseBody" |>.getD Json.null
            if fBody.isNull then
              failAt ifStmt "binary-search while loop requires both true and false branches"
            let (lowId, highId) ←
              if condOp == "<" then
                pure (lhsId, rhsId)
              else if condOp == ">" then
                pure (rhsId, lhsId)
              else do
                let fwdMid ← isBinarySearchMidpointExpr initVal lhsId rhsId bits
                let fwdT ← classifyBinarySearchBranch tBody lhsId rhsId midId bits
                let fwdF ← classifyBinarySearchBranch fBody lhsId rhsId midId bits
                let fwdBranches := (fwdT == some true && fwdF == some false) || (fwdT == some false && fwdF == some true)
                if fwdMid && fwdBranches then
                  pure (lhsId, rhsId)
                else
                  let revMid ← isBinarySearchMidpointExpr initVal rhsId lhsId bits
                  let revT ← classifyBinarySearchBranch tBody rhsId lhsId midId bits
                  let revF ← classifyBinarySearchBranch fBody rhsId lhsId midId bits
                  let revBranches := (revT == some true && revF == some false) || (revT == some false && revF == some true)
                  if revMid && revBranches then
                    pure (rhsId, lhsId)
                  else
                    pure (lhsId, rhsId)
            unless ← isBinarySearchMidpointExpr initVal lowId highId bits do
              failAt initVal "binary-search midpoint must be the floor average of low and high"
            let tKind ← classifyBinarySearchBranch tBody lowId highId midId bits
            let fKind ← classifyBinarySearchBranch fBody lowId highId midId bits
            unless (tKind == some true && fKind == some false) ||
                   (tKind == some false && fKind == some true) do
              failAt ifStmt "binary-search branches must assign high = mid and low = mid + 1"
            if condOp == "!=" && !env.zeroInitLocals.contains lowId then
              failAt cond "binary-search while (low != high) requires low to be zero at loop entry"
            let condVal ← lowerExpr cond
            unless condVal.pre.isEmpty do
              failAt cond "while loop condition must be a pure scalar comparison"
            let loopVar ← fresh
            let saved ← get
            let bodyOut ← lowerBody body
            let loopWrites := bodyAssignedIds body
            modify fun e =>
              { e with values := saved.values, paths := saved.paths,
                       snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements,
                       calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy,
                       writableLocals := saved.writableLocals, zeroInitLocals := saved.zeroInitLocals.filter (!loopWrites.contains ·), fnPtrs := saved.fnPtrs, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
            return #[.forEach loopVar (.literal bits) [.ite condVal.expr bodyOut.toList []]]
  let varNode? ←
    if (condOp == "!=" || condOp == ">") && (← isZeroLiteral condRhs) then
      pure (some condLhs)
    else if (condOp == "!=" || condOp == "<") && (← isZeroLiteral condLhs) then
      pure (some condRhs)
    else
      pure none
  let some varNode := varNode?
    | failAt cond "a while loop condition must test v != 0 or v > 0"
  unless (← mKind varNode) == "Identifier" do
    failAt varNode "a while loop variable must be a scalar local identifier"
  let varRef ← refInt varNode
  unless varRef ≥ 0 do
    failAt varNode "a while loop variable must be a resolved local declaration"
  let varId := varRef.toNat
  let env ← get
  unless (env.writableLocals.find? varId).isSome do
    failAt varNode "a while loop variable must be a writable scalar local"
  let varTy ← mType varNode
  let some bits := bitsOf varTy
    | failAt varNode s!"unsupported while loop variable type {varTy}"
  unless varTy.startsWith "uint" && bits > 0 && bits ≤ 256 do
    failAt varNode s!"a while loop variable must be an unsigned integer, found {varTy}"
  let body ← mField s "body"
  let bodyStmts ← unwrapLoopBodyStmts body
  if ← listContainsReturn bodyStmts then
    failAt s "return inside a while loop is unsupported"
  unless bodyStmts.size ≥ 1 do
    failAt body "a while loop body must not be empty"
  let prefixStmts := bodyStmts.extract 0 (bodyStmts.size - 1)
  for preStmt in prefixStmts do
    if (bodyAssignedIds preStmt).contains varId then
      failAt preStmt "a while loop variable may only be updated in the final loop statement"
  let lastStmt := bodyStmts.back!
  unless (← mKind lastStmt) == "ExpressionStatement" do
    failAt lastStmt "a while loop must end with a progress update to the loop variable"
  let stepExpr ← mField lastStmt "expression"
  unless (← mKind stepExpr) == "Assignment" do
    failAt stepExpr "a while loop must end with an assignment to the loop variable"
  let stepOp ← mStr (← mField stepExpr "operator")
  let stepLhs ← mField stepExpr "leftHandSide"
  let stepRhs ← mField stepExpr "rightHandSide"
  unless ← isIdentId stepLhs varId do
    failAt stepLhs "a while loop final statement must assign to the loop variable"
  let rightShiftOk ←
    if stepOp == ">>=" then
      isPositiveShiftConst stepRhs
    else if stepOp == "=" then do
      let rhs ← stripUintCast stepRhs bits
      if (← mKind rhs) == "BinaryOperation" && optStr rhs "operator" == some ">>" then
        pure ((← isIdentId (← mField rhs "leftExpression") varId) &&
              (← isPositiveShiftConst (← mField rhs "rightExpression")))
      else
        pure false
    else
      pure false
  let clearLowestOk ←
    if stepOp == "&=" then do
      let rhs ← stripUintCast stepRhs bits
      if (← mKind rhs) == "BinaryOperation" && optStr rhs "operator" == some "-" then
        pure ((← isIdentId (← mField rhs "leftExpression") varId) &&
              (← isOneLiteral (← mField rhs "rightExpression")))
      else
        pure false
    else if stepOp == "=" then
      isClearLowestBitExpr stepRhs varId bits
    else
      pure false
  let clearMsbOk ←
    if bodyStmts.size ≥ 2 then do
      let firstStmt := bodyStmts[0]!
      if (← mKind firstStmt) == "VariableDeclarationStatement" then
        let decls ← mArr (← mField firstStmt "declarations")
        let initVal := field? firstStmt "initialValue" |>.getD Json.null
        if decls.size == 1 && !decls[0]!.isNull && !initVal.isNull then
          let bitDecl := decls[0]!
          let bitId ← mNat (← mField bitDecl "id")
          let bitTy ← mType bitDecl
          if bitTy.startsWith "uint" && !(bodyAssignedIds body).contains bitId &&
              (← isMsbCallOn initVal varId) then
            if stepOp == "&=" then
              isNotShiftBitExpr stepRhs bitId
            else if stepOp == "=" then
              isClearBitExpr stepRhs varId bitId bits
            else
              pure false
          else
            pure false
        else
          pure false
      else
        pure false
    else
      pure false
  unless rightShiftOk || clearLowestOk || clearMsbOk do
    failAt stepExpr "while loop update is not a recognized bounded bit-clearing or right-shift step"
  let condVal ← lowerExpr cond
  unless condVal.pre.isEmpty do
    failAt cond "while loop condition must be a pure scalar comparison"
  let loopVar ← fresh
  let saved ← get
  let bodyOut ← lowerBody body
  let loopWrites := bodyAssignedIds body
  modify fun e =>
    { e with values := saved.values, paths := saved.paths,
             snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements,
             calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy,
             writableLocals := saved.writableLocals, zeroInitLocals := saved.zeroInitLocals.filter (!loopWrites.contains ·), fnPtrs := saved.fnPtrs, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
  pure #[.forEach loopVar (.literal bits) [.ite condVal.expr bodyOut.toList []]]

private partial def lowerHelperLoopBody (body : Json) : M (Array Stmt) := do
  let statements ← if (← mKind body) == "Block" then mArr (← mField body "statements") else pure #[body]
  let mut out : Array Stmt := #[]
  for statement in statements do
    match ← mKind statement with
    | "Block" =>
        let saved ← get
        out := out ++ (← lowerHelperLoopBody statement)
        modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
    | "UncheckedBlock" =>
        let saved ← get
        modify fun e => { e with unchecked := true }
        let subStmts ← mArr (← mField statement "statements")
        for sub in subStmts do
          let subOut ← lowerHelperLoopBody sub
          out := out ++ subOut
        modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays, unchecked := saved.unchecked }
    | "VariableDeclarationStatement" => out := out ++ (← lowerLocal statement)
    | "ExpressionStatement" => out := out ++ (← lowerEffect statement)
    | "EmitStatement" => out := out ++ (← lowerEmit statement)
    | "RevertStatement" => out := out ++ (← lowerRevert statement)
    | "InlineAssembly" =>
        let savedAsmYul := (← get).yulNames
        let extPre ← bindYulExternalConstants statement
        let asmStmts ← lowerAssemblyStmts statement ""
        modify fun e => { e with yulNames := savedAsmYul }
        out := out ++ extPre ++ asmStmts
    | "ForStatement" => out := out ++ (← lowerFor statement lowerHelperLoopBody)
    | "WhileStatement" => out := out ++ (← lowerWhile statement lowerHelperLoopBody)
    | "IfStatement" =>
        let (condition, _yes, no) ← ifParts statement
        let saved ← get
        let restore : M Unit := modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
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
  | [] =>
      pure (#[], (← get).helperResult.map fun (binding, _) => Expr.localVar binding)
  | s :: rest =>
    match ← mKind s with
    | "Block" | "UncheckedBlock" =>
        let isUnchecked := (← mKind s) == "UncheckedBlock"
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays, unchecked := saved.unchecked }
        if isUnchecked then
          modify fun e => { e with unchecked := true }
        let blockStmts ← mArr (← mField s "statements")
        let blockReturns ← helperListReturns blockStmts
        if blockReturns then
          if let some next := rest.head? then failAt next "statement after helper result"
          let (inner, res) ← lowerHelperFrom blockStmts.toList retName
          restore
          pure (inner, res)
        else if ← listContainsReturn blockStmts then
          failAt s "partial return inside a helper block is outside this slice"
        else
          let (inner, _) ← lowerHelperFrom blockStmts.toList retName
          restore
          let (tail, res) ← lowerHelperFrom rest retName
          pure (inner ++ tail, res)
    | "VariableDeclarationStatement" =>
        let pre ← lowerLocal s
        let (tail, result) ← lowerHelperFrom rest retName
        pure (pre ++ tail, result)
    | "ExpressionStatement" =>
        -- Use the same exact assignment/delete and require rules as root bodies.
        -- The helper continuation still resumes only after these effects.
        let pre ← lowerEffect s
        if ← stmtAlwaysReverts [] s then
          if let some next := rest.head? then failAt next "statement after helper revert"
          pure (pre, some ((← get).helperResult.map (fun (b, _) => Expr.localVar b) |>.getD (.literal 0)))
        else
          let (tail, result) ← lowerHelperFrom rest retName
          pure (pre ++ tail, result)
    | "EmitStatement" =>
        -- Preserve helper events before its scalar-result continuation.
        let emitted ← lowerEmit s
        let (tail, result) ← lowerHelperFrom rest retName
        pure (emitted ++ tail, result)
    | "RevertStatement" =>
        if let some next := rest.head? then failAt next "statement after helper revert"
        let revStmts ← lowerRevert s
        pure (revStmts, some ((← get).helperResult.map (fun (b, _) => Expr.localVar b) |>.getD (.literal 0)))
    | "ForStatement" =>
        let pre ← lowerFor s lowerHelperLoopBody
        let (tail, result) ← lowerHelperFrom rest retName
        pure (pre ++ tail, result)
    | "WhileStatement" =>
        let pre ← lowerWhile s lowerHelperLoopBody
        let (tail, result) ← lowerHelperFrom rest retName
        pure (pre ++ tail, result)
    | "Return" =>
        if let some next := rest.head? then failAt next "statement after helper result"
        let expression := field? s "expression" |>.getD Json.null
        if expression.isNull then
          if let some (retBinding, _) := (← get).helperResult then
            pure (#[], some (.localVar retBinding))
          else
            failAt s "bare helper returns are unsupported"
        else
          let v ← lowerExpr expression
          pure (v.pre, some v.expr)
    | "InlineAssembly" =>
        let isSingleRetAssign ← do
          let ast ← mField s "AST"
          if (← mKind ast) == "YulBlock" then
            let ystmts ← mArr (← mField ast "statements")
            if ystmts.size == 1 then
              if (← mKind ystmts[0]!) == "YulAssignment" then
                let vars ← mArr (← mField ystmts[0]! "variableNames")
                if vars.size == 1 then
                  let vname ← mStr (← mField vars[0]! "name")
                  pure (retName != "" && vname == retName)
                else pure false
              else pure false
            else pure false
          else pure false
        if isSingleRetAssign then
          if let some (binding, ty) := (← get).helperResult then
            if ty.startsWith "enum " then
              failAt s "Yul assignment to an enum result is unsupported"
            let savedAsmYul := (← get).yulNames
            let extPre ← bindYulExternalConstants s
            let v ← lowerAssembly s retName
            modify fun e => { e with yulNames := savedAsmYul }
            let cleaned := cleanHelperResultExpr ty v
            let (tail, result) ← lowerHelperFrom rest retName
            pure ((extPre ++ v.pre).push (.assignVar binding cleaned) ++ tail, result)
          else
            if let some next := rest.head? then failAt next "statement after helper result"
            let savedAsmYul := (← get).yulNames
            let extPre ← bindYulExternalConstants s
            let v ← lowerAssembly s retName
            modify fun e => { e with yulNames := savedAsmYul }
            pure (extPre ++ v.pre, some v.expr)
        else if (← get).helperResult.isSome || !rest.isEmpty then
          if let some (_, ty) := (← get).helperResult then
            if ty.startsWith "enum " then
              failAt s "Yul assignment to an enum result is unsupported"
          let savedAsmYul := (← get).yulNames
          let extPre ← bindYulExternalConstants s
          let asmStmts ← lowerAssemblyStmts s retName
          modify fun e => { e with yulNames := savedAsmYul }
          let (tail, result) ← lowerHelperFrom rest retName
          pure (extPre ++ asmStmts ++ tail, result)
        else
          if let some next := rest.head? then failAt next "statement after helper result"
          let savedAsmYul := (← get).yulNames
          let extPre ← bindYulExternalConstants s
          let v ← lowerAssembly s retName
          modify fun e => { e with yulNames := savedAsmYul }
          pure (extPre ++ v.pre, some v.expr)
    | "IfStatement" =>
        let (condition, yes, no) ← ifParts s
        let yesReturns ← helperListReturns yes
        let noReturns ← helperListReturns no
        if yesReturns && noReturns then
          if let some next := rest.head? then failAt next "statement after helper result"
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
        let restReturns ← helperListReturns rest.toArray
        let yesHasReturn ← listContainsReturn yes
        let noHasReturn ← listContainsReturn no
        if (!yesReturns && !noReturns) || (!rest.isEmpty && !restReturns && !yesHasReturn && !noHasReturn) then
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

private partial def voidHelperReturns (s : Json) : M Bool := do
  match ← mKind s with
  | "Return" | "RevertStatement" => pure true
  | "Block" | "UncheckedBlock" => ((← mArr (← mField s "statements")).back?.map voidHelperReturns).getD (pure false)
  | "IfStatement" =>
      let yes ← voidHelperReturns (← mField s "trueBody")
      let no ← match field? s "falseBody" with
        | some j => if j.isNull then pure false else voidHelperReturns j
        | none => pure false
      pure (yes && no)
  | _ => stmtAlwaysReverts [] s

private partial def stmtContainsReturn (s : Json) : M Bool := do
  match ← mKind s with
  | "Return" => pure true
  | "Block" | "UncheckedBlock" =>
      let stmts ← mArr (← mField s "statements")
      stmts.anyM stmtContainsReturn
  | "ForStatement" | "WhileStatement" =>
      stmtContainsReturn (← mField s "body")
  | "IfStatement" =>
      let yes ← stmtContainsReturn (← mField s "trueBody")
      let no ← match field? s "falseBody" with
        | some j => if j.isNull then pure false else stmtContainsReturn j
        | none => pure false
      pure (yes || no)
  | _ => pure false

private partial def listContainsReturn (stmts : Array Json) : M Bool :=
  stmts.anyM stmtContainsReturn

private partial def lowerVoidHelperFrom (stmts : List Json) (k : M (Array Stmt)) : M (Array Stmt) := do
  match stmts with
  | [] => k
  | s :: rest =>
    let kRest : M (Array Stmt) := lowerVoidHelperFrom rest k
    match ← mKind s with
    | "Block" | "UncheckedBlock" =>
        let isUnchecked := (← mKind s) == "UncheckedBlock"
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays, unchecked := saved.unchecked }
        if isUnchecked then
          modify fun e => { e with unchecked := true }
        let blockStmts ← mArr (← mField s "statements")
        if ← voidHelperReturns s then
          if let some next := rest.head? then failAt next "statement after void helper return"
        if ← listContainsReturn blockStmts then
          lowerVoidHelperFrom blockStmts.toList (do restore; kRest)
        else
          let inner ← lowerVoidHelperFrom blockStmts.toList (pure #[])
          restore
          let tailStmts ← kRest
          pure (inner ++ tailStmts)
    | "VariableDeclarationStatement" =>
        let localStmts ← lowerLocal s
        let tailStmts ← kRest
        pure (localStmts ++ tailStmts)
    | "ExpressionStatement" =>
        if ← stmtAlwaysReverts [] s then
          if let some next := rest.head? then failAt next "statement after void helper revert"
          return ← lowerEffect s
        let effStmts ← lowerEffect s
        let tailStmts ← kRest
        pure (effStmts ++ tailStmts)
    | "EmitStatement" =>
        let emitStmts ← lowerEmit s
        let tailStmts ← kRest
        pure (emitStmts ++ tailStmts)
    | "RevertStatement" =>
        if let some next := rest.head? then failAt next "statement after void helper revert"
        lowerRevert s
    | "InlineAssembly" =>
        let savedAsmYul := (← get).yulNames
        let extPre ← bindYulExternalConstants s
        let asmStmts ← lowerAssemblyStmts s ""
        modify fun e => { e with yulNames := savedAsmYul }
        let tailStmts ← kRest
        pure (extPre ++ asmStmts ++ tailStmts)
    | "ForStatement" =>
        let loopStmts ← lowerFor s lowerHelperLoopBody
        let tailStmts ← kRest
        pure (loopStmts ++ tailStmts)
    | "WhileStatement" =>
        let loopStmts ← lowerWhile s lowerHelperLoopBody
        let tailStmts ← kRest
        pure (loopStmts ++ tailStmts)
    | "Return" =>
        if let some next := rest.head? then failAt next "statement after void helper return"
        let expression := field? s "expression" |>.getD Json.null
        if let some results := (← get).multiHelperResults then
          if expression.isNull then
            unless results.all (fun (_, _, isNamed) => isNamed) do
              failAt s "bare multi-return helper return requires named return parameters"
            pure (← get).helperPost
          else if (← mKind expression) == "TupleExpression" then
            unless !(← mBool (← mField expression "isInlineArray")) do
              failAt expression "multi-return helper return requires a tuple expression"
            let cs ← mArr (← mField expression "components")
            unless cs.size == results.size do
              failAt expression s!"multi-return helper return arity {cs.size} does not match {results.size}"
            let mut pre : Array Stmt := #[]
            let mut vals : Array Expr := #[]
            for i in [:cs.size] do
              let c := cs[i]!
              if c.isNull then failAt expression "empty return component"
              if cs.size > 1 && (statefulCallIn c (← get) || assignmentIn c) then
                failAt c "stateful or assignment expression in multi-return tuple requires explicit evaluation-order support"
              let (_, rty, _) := results[i]!
              let v ← atom (← convert rty (← mType c) (← lowerExpr c) c)
              pre := pre ++ v.pre
              let finalExpr ← match v.expr with
                | .localVar name => do
                    if (← get).writableLocals.toList.any (fun (_, b) => b == name) then
                      let snap ← fresh
                      pre := pre.push (.letVar snap (.localVar name))
                      pure (.localVar snap)
                    else
                      pure v.expr
                | _ => pure v.expr
              vals := vals.push finalExpr
            for i in [:results.size] do
              let (binding, _, _) := results[i]!
              pre := pre.push (.assignVar binding (vals.getD i (.literal 0)))
            pure (pre ++ (← get).helperPost)
          else
            let expectedTypes := results.map fun (_, rty, _) => some rty
            let (branchPre, retExprs) ← lowerMultiBranch expression (some expectedTypes)
            unless retExprs.size == results.size do
              failAt expression s!"multi-return helper return arity {retExprs.size} does not match {results.size}"
            let mut pre := branchPre
            for i in [:results.size] do
              let (binding, _, _) := results[i]!
              let (valExpr, _) := retExprs.getD i (.literal 0, "")
              pre := pre.push (.assignVar binding valExpr)
            pure (pre ++ (← get).helperPost)
        else if let some (retSid, _, memberBindings, isNamed) := (← get).flatStructHelperResult then
          if expression.isNull then
            unless isNamed do
              failAt s "bare struct helper return requires a named return parameter"
            pure (← get).helperPost
          else
            let isSameNamedRet ← if isNamed && (← mKind expression) == "Identifier" then do
              let refId ← refInt expression
              if refId ≥ 0 then
                if let some flat := (← get).flatStructs.find? refId.toNat then
                  pure (flat.members == memberBindings)
                else pure false
              else pure false
            else pure false
            if isSameNamedRet then
              pure (← get).helperPost
            else
              let (exprSid, _, valPre, memberVals) ← lowerFlatStructValue expression (some retSid) true
              unless exprSid == retSid && memberVals.size == memberBindings.size do
                failAt expression "returned struct value does not match helper return type"
              let mut pre := valPre
              for ((bName, _, binding), (vName, _, vExpr)) in memberBindings.zip memberVals do
                unless bName == vName do
                  failAt expression "returned struct member layout mismatch"
                pre := pre.push (.assignVar binding vExpr)
              pure (pre ++ (← get).helperPost)
        else
          unless expression.isNull do failAt s "void helper cannot return a value"
          pure (← get).helperPost
    | "IfStatement" =>
        let (condition, yes, no) ← ifParts s
        let yesAll ← match yes.back? with | some b => voidHelperReturns b | none => pure false
        let noAll ← match no.back? with | some b => voidHelperReturns b | none => pure false
        if yesAll && noAll then
          if let some next := rest.head? then failAt next "statement after void helper return"
        let yesAny ← listContainsReturn yes
        let noAny ← listContainsReturn no
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
        if !yesAny && !noAny then
          let yesStmts ← lowerVoidHelperFrom yes.toList (pure #[])
          restore
          let noStmts ← lowerVoidHelperFrom no.toList (pure #[])
          restore
          let tailStmts ← kRest
          pure (condition.pre.push (.ite condition.expr yesStmts.toList noStmts.toList) ++ tailStmts)
        else
          let kBranch : M (Array Stmt) := do restore; kRest
          let yesStmts ← lowerVoidHelperFrom yes.toList (if yesAll then pure #[] else kBranch)
          restore
          let noStmts ← lowerVoidHelperFrom no.toList (if noAll then pure #[] else kBranch)
          restore
          pure (condition.pre.push (.ite condition.expr yesStmts.toList noStmts.toList))
    | kind => failAt s s!"unsupported void helper statement {kind}"

private partial def resolveStructDeclFromType (j : Json) : M (Nat × Json) := do
  if let some tn := field? j "typeName" then
    let sid ← refInt tn
    if sid ≥ 0 then
      if let some decl := (← get).structs.find? sid.toNat then
        return (sid.toNat, decl)
  let td := field? j "typeDescriptions" |>.getD Json.null
  let tid := optStr td "typeIdentifier" |>.getD ""
  if tid.startsWith "t_struct$_" then
    let segs := tid.splitOn "_$"
    if let some lastSeg := segs.getLast? then
      let digits := String.ofList (lastSeg.toList.takeWhile Char.isDigit)
      if let some sid := digits.toNat? then
        if let some decl := (← get).structs.find? sid then
          return (sid, decl)
  let rawTy ← mType j
  let base :=
    if rawTy.endsWith " storage ref" then (rawTy.dropEnd 12).toString
    else if rawTy.endsWith " storage pointer" then (rawTy.dropEnd 16).toString
    else if rawTy.endsWith " memory" then (rawTy.dropEnd 7).toString
    else if rawTy.endsWith " calldata" then (rawTy.dropEnd 9).toString
    else rawTy
  let targetName := ((base.drop 7).toString.splitOn ".").getLastD ""
  let mut matchedDecls : Array (Nat × Json) := #[]
  for (sid, decl) in (← get).structs.toList do
    if optStr decl "name" == some targetName then
      matchedDecls := matchedDecls.push (sid, decl)
  if matchedDecls.size == 1 then
    return matchedDecls[0]!
  failAt j s!"unable to resolve struct declaration for {rawTy}"

private partial def lowerFlatStructValue (j : Json) (expectedSid? : Option Nat) (allowFlatLocalSource : Bool) :
    M (Nat × String × Array Stmt × Array (String × String × Expr)) := do
  let j ← stripParens j
  if (← mKind j) == "FunctionCall" && optStr j "kind" == some "structConstructorCall" then
    let names ← match field? j "names" with
      | some n => mArr n
      | none => pure #[]
    let callee ← mField j "expression"
    let sid ← refInt callee
    unless sid ≥ 0 do
      failAt j "unresolved struct constructor declaration"
    if let some expectedSid := expectedSid? then
      unless sid.toNat == expectedSid do
        failAt j "struct constructor type mismatch"
    let some sDecl := (← get).structs.find? sid.toNat
      | failAt j "unknown struct declaration"
    let sName ← mStr (← mField sDecl "name")
    let sMembers ← mArr (← mField sDecl "members")
    let args ← mArr (← mField j "arguments")
    unless args.size == sMembers.size && !sMembers.isEmpty do
      failAt j "struct constructor argument count mismatch"
    if names.isEmpty then
      let mut pre : Array Stmt := #[]
      let mut memberVals : Array (String × String × Expr) := #[]
      for (mNode, arg) in sMembers.zip args do
        let mName ← mStr (← mField mNode "name")
        let mTy ← mType mNode
        unless !mTy.startsWith "enum " && (paramType mTy).isSome do
          failAt mNode s!"unsupported flat struct member type {mTy}"
        let rawVal ← lowerExpr arg
        let convVal ← atom (← convert mTy (← mType arg) rawVal arg)
        let normExpr := if mTy == "bool" then Expr.logicalNot (.logicalNot convVal.expr) else convVal.expr
        let normVal ← atom { pre := convVal.pre, expr := normExpr }
        pre := pre ++ normVal.pre
        memberVals := memberVals.push (mName, mTy, normVal.expr)
      return (sid.toNat, sName, pre, memberVals)
    else
      unless names.size == args.size do
        failAt j "named struct constructor name/argument count mismatch"
      let mut pre : Array Stmt := #[]
      let mut evaluatedByName : Array (String × String × Expr) := #[]
      for i in [:args.size] do
        let argName ← mStr names[i]!
        let arg := args[i]!
        if statefulCallIn arg (← get) || assignmentIn arg then
          failAt j "named struct constructor with stateful or assignment argument is outside this slice"
        if evaluatedByName.any (fun (n, _, _) => n == argName) then
          failAt j s!"duplicate named struct constructor argument {argName}"
        let mut matchedMember? : Option Json := none
        for mNode in sMembers do
          if (← mStr (← mField mNode "name")) == argName then
            matchedMember? := some mNode
        let some mNode := matchedMember?
          | failAt j s!"unknown struct constructor member {argName}"
        let mTy ← mType mNode
        unless !mTy.startsWith "enum " && (paramType mTy).isSome do
          failAt mNode s!"unsupported flat struct member type {mTy}"
        let rawVal ← lowerExpr arg
        let convVal ← atom (← convert mTy (← mType arg) rawVal arg)
        let normExpr := if mTy == "bool" then Expr.logicalNot (.logicalNot convVal.expr) else convVal.expr
        let normVal ← atom { pre := convVal.pre, expr := normExpr }
        pre := pre ++ normVal.pre
        evaluatedByName := evaluatedByName.push (argName, mTy, normVal.expr)
      let mut memberVals : Array (String × String × Expr) := #[]
      for mNode in sMembers do
        let mName ← mStr (← mField mNode "name")
        let some (_, mTy, expr) := evaluatedByName.find? (fun (n, _, _) => n == mName)
          | failAt j s!"missing struct constructor member {mName}"
        memberVals := memberVals.push (mName, mTy, expr)
      return (sid.toNat, sName, pre, memberVals)
  if (← mKind j) == "FunctionCall" && optStr j "kind" == some "functionCall" &&
      (← mType j).startsWith "struct " && !(← mType j).contains "[" &&
      (← mType j).endsWith " memory" then
    if ← isAbiDecodeCall j then
      let (decodePre, decoded) ← lowerAbiDecodeItems j
      unless decoded.size == 1 do
        failAt j "struct abi.decode requires a single struct target type"
      let .flatStruct callSid callSName callMembers := decoded[0]!
        | failAt j "struct abi.decode requires a flat struct target type"
      if let some expectedSid := expectedSid? then
        unless callSid == expectedSid do
          failAt j "struct abi.decode return type mismatch"
      return (callSid, callSName, decodePre, callMembers)
    let (fnId, vals) ← resolveCallTargetAndArgs j
    let (callSid, callSName, callPre, callMembers) ← inlineFlatStructFn fnId vals j
    if let some expectedSid := expectedSid? then
      unless callSid == expectedSid do
        failAt j "struct helper return type mismatch"
    let mut pre := callPre
    let mut memberVals : Array (String × String × Expr) := #[]
    for (mName, mTy, mExpr) in callMembers do
      let snap ← atom { pre := #[], expr := mExpr }
      pre := pre ++ snap.pre
      memberVals := memberVals.push (mName, mTy, snap.expr)
    return (callSid, callSName, pre, memberVals)
  if (← mKind j) == "Conditional" then
    let condVal ← atom (← lowerExpr (← mField j "condition"))
    let trueNode ← mField j "trueExpression"
    let falseNode ← mField j "falseExpression"
    let (tSid, sName, tPre, tMembers) ← lowerFlatStructValue trueNode expectedSid? allowFlatLocalSource
    let (fSid, _, fPre, fMembers) ← lowerFlatStructValue falseNode (some tSid) allowFlatLocalSource
    unless tSid == fSid && tMembers.size == fMembers.size do
      failAt j "conditional struct branch type mismatch"
    let mut pre := condVal.pre
    let mut tBranch := tPre
    let mut fBranch := fPre
    let mut memberVals : Array (String × String × Expr) := #[]
    for ((tName, tTy, tExpr), (fName, fTy, fExpr)) in tMembers.zip fMembers do
      unless tName == fName && tTy == fTy do
        failAt j "conditional struct member mismatch"
      let tmp ← fresh
      pre := pre.push (.letVar tmp (.literal 0))
      tBranch := tBranch.push (.assignVar tmp tExpr)
      fBranch := fBranch.push (.assignVar tmp fExpr)
      memberVals := memberVals.push (tName, tTy, .localVar tmp)
    pre := pre.push (.ite condVal.expr tBranch.toList fBranch.toList)
    return (tSid, sName, pre, memberVals)
  match ← lowerRef j with
  | .path pathPre path =>
      let (sid, sDecl) ← resolveStructDeclFromType j
      if let some expectedSid := expectedSid? then
        unless sid == expectedSid do
          failAt j "struct storage source type mismatch"
      let sName ← mStr (← mField sDecl "name")
      let sMembers ← mArr (← mField sDecl "members")
      if let .rawSlot rawSid baseSlot := path then
        unless rawSid == sid do
          failAt j "raw-slot struct declaration mismatch"
        let rawInfo ← resolveRawStructInfo rawSid j
        unless rawInfo.subStructs.isEmpty && rawInfo.mappings.isEmpty &&
            rawInfo.dynamicArrays.isEmpty && rawInfo.scalars.size == sMembers.size && !sMembers.isEmpty do
          failAt j "struct storage read requires a scalar-member struct layout"
        let mut pre : Array Stmt := pathPre
        let mut memberVals : Array (String × String × Expr) := #[]
        for mNode in sMembers do
          let mName ← mStr (← mField mNode "name")
          let mTy ← mType mNode
          let some mInfo := rawInfo.scalars.find? (·.member == mName)
            | failAt mNode s!"unsupported flat struct storage member {mName}"
          let readVal ← atom (← readRawStructScalar #[] baseSlot mInfo)
          pre := pre ++ readVal.pre
          memberVals := memberVals.push (mName, mTy, readVal.expr)
        return (sid, sName, pre, memberVals)
      let (fieldName, count) ← match path with
        | .zero field => pure (field, 0)
        | .one field _ => pure (field, 1)
        | .two field _ _ => pure (field, 2)
        | .outer _ _ => failAt j "struct storage read requires all mapping keys"
        | .rawSlot _ _ | .bytesSlot _ _ => failAt j "whole raw-slot struct storage read is outside this slice"
      let info ← resolveField fieldName j
      unless !info.scalarMapping && info.fixedArrayLength.isNone && info.keyCount == count &&
          info.structMappings.isEmpty && info.opaqueNames.isEmpty &&
          info.structFixedArrays.isEmpty && info.structDynamicArrays.isEmpty &&
          !info.memberNames.isEmpty do
        failAt j "struct storage read requires a scalar-member struct layout"
      unless sMembers.size == info.memberNames.size do
        failAt j "struct declaration member count does not match storage layout"
      let mut pre : Array Stmt := pathPre
      let mut memberVals : Array (String × String × Expr) := #[]
      for mNode in sMembers do
        let mName ← mStr (← mField mNode "name")
        let mTy ← mType mNode
        unless !mTy.startsWith "enum " && (paramType mTy).isSome && info.memberNames.contains mName do
          failAt mNode s!"unsupported flat struct storage member {mName}"
        let readVal ← atom (← memberRead #[] path mName j)
        pre := pre ++ readVal.pre
        memberVals := memberVals.push (mName, mTy, readVal.expr)
      return (sid, sName, pre, memberVals)
  | .flatStruct srcId =>
      unless allowFlatLocalSource do
        failAt j "memory struct local aliasing is outside this slice"
      let some flat := (← get).flatStructs.find? srcId
        | failAt j "unknown flat struct local"
      if let some expectedSid := expectedSid? then
        unless flat.structId == expectedSid do
          failAt j "flat struct local type mismatch"
      let mut pre : Array Stmt := #[]
      let mut memberVals : Array (String × String × Expr) := #[]
      for (mName, mTy, binding) in flat.members do
        let snap ← atom { pre := #[], expr := .localVar binding }
        pre := pre ++ snap.pre
        memberVals := memberVals.push (mName, mTy, snap.expr)
      return (flat.structId, flat.structName, pre, memberVals)
  | .mem srcId memPre =>
      unless allowFlatLocalSource do
        failAt j "memory struct local aliasing is outside this slice"
      let some mem := (← get).mems.find? srcId
        | failAt j "unknown memory struct local"
      let (sid, sDecl) ← resolveStructDeclFromType j
      if let some expectedSid := expectedSid? then
        unless sid == expectedSid do
          failAt j "struct source type mismatch"
      let sName ← mStr (← mField sDecl "name")
      let sMembers ← mArr (← mField sDecl "members")
      let isStaticStruct := mem.staticTypes.isSome ||
        match mem.schema with
        | some s => s.all (fun item => match item with | .scalar _ => true | _ => false)
        | none => false
      unless isStaticStruct && mem.members.size == sMembers.size && !sMembers.isEmpty do
        failAt j "struct value copy requires a static scalar-member struct"
      let mut pre : Array Stmt := memPre
      let mut memberVals : Array (String × String × Expr) := #[]
      for mNode in sMembers do
        let mName ← mStr (← mField mNode "name")
        let mTy ← mType mNode
        unless !mTy.startsWith "enum " && (paramType mTy).isSome do
          failAt mNode s!"unsupported flat struct member type {mTy}"
        let readVal ← atom (← readAbiMember srcId #[] mName j)
        pre := pre ++ readVal.pre
        memberVals := memberVals.push (mName, mTy, readVal.expr)
      return (sid, sName, pre, memberVals)
  | .abiElement id memberIndex pointer inMemory elemPre =>
      unless allowFlatLocalSource do
        failAt j "memory struct local aliasing is outside this slice"
      let some mem := (← get).mems.find? id | failAt j "unknown ABI root"
      let some schema := mem.schema | failAt j "missing ABI schema"
      let some (.structArray _ fields) := schema[memberIndex]?
        | failAt j "expected a struct-array element"
      let (sid, sDecl) ← resolveStructDeclFromType j
      if let some expectedSid := expectedSid? then
        unless sid == expectedSid do
          failAt j "struct source type mismatch"
      let sName ← mStr (← mField sDecl "name")
      let sMembers ← mArr (← mField sDecl "members")
      unless fields.length == sMembers.size && !sMembers.isEmpty do
        failAt j "struct value copy requires a static scalar-member struct"
      let ptrAtom ← atom { pre := elemPre, expr := pointer }
      let mut pre : Array Stmt := ptrAtom.pre
      let mut memberVals : Array (String × String × Expr) := #[]
      for idx in [:sMembers.size] do
        let mNode := sMembers[idx]!
        let mName ← mStr (← mField mNode "name")
        let mTy ← mType mNode
        unless !mTy.startsWith "enum " && (paramType mTy).isSome do
          failAt mNode s!"unsupported flat struct member type {mTy}"
        let some field := fields[idx]?
          | failAt mNode "missing struct-array field"
        unless field.name == mName do
          failAt mNode s!"struct-array field mismatch {mName}"
        let offset := Expr.add ptrAtom.expr (.literal (32 * idx))
        let rawExpr := if !inMemory then Expr.calldataload offset else Expr.mload offset
        let bound := SolidityAbi.scalarBound field.kind
        let readPre := if !inMemory && bound < 2 ^ 256 then
          #[AbiLowering.guard (.lt rawExpr (.literal bound))] else #[]
        let readVal ← atom { pre := readPre, expr := rawExpr }
        pre := pre ++ readVal.pre
        memberVals := memberVals.push (mName, mTy, readVal.expr)
      return (sid, sName, pre, memberVals)
  | _ => failAt j "unsupported struct value expression"

private partial def writeWholeStorageStruct (pre : Array Stmt) (path : SPath) (deleting : Bool)
    (target expression : Json) : M (Array Stmt) := do
  if let .rawSlot rawSid baseSlot := path then
    let rawInfo ← resolveRawStructInfo rawSid target
    if deleting then
      unless rawInfo.mappings.isEmpty do
        failAt target "cannot delete struct with mapping members"
      unless rawInfo.dynamicArrays.isEmpty do
        failAt target "cannot delete struct with dynamic-array members"
      unless rawInfo.subStructs.isEmpty do
        failAt target "cannot delete struct with nested struct members"
      unless rawInfo.wordCount > 0 && !rawInfo.scalars.isEmpty do
        failAt target "cannot delete empty struct layout"
      modify fun e => { e with usedRawStorage := true }
      let mut out := pre
      for w in [:rawInfo.wordCount] do
        out := out.push (.setStorageArrayElement rawStorageFieldName (rawStructMemberSlot baseSlot w) (.literal 0))
      return out
    unless rawInfo.mappings.isEmpty && rawInfo.dynamicArrays.isEmpty &&
        rawInfo.subStructs.isEmpty && !rawInfo.scalars.isEmpty do
      failAt target "whole struct storage assignment requires a scalar-member struct layout"
    let (targetSid, sDecl) ← resolveStructDeclFromType target
    unless targetSid == rawSid do
      failAt target "raw-slot struct target declaration mismatch"
    let sMembers ← mArr (← mField sDecl "members")
    unless sMembers.size == rawInfo.scalars.size do
      failAt target "struct assignment member count mismatch"
    let right ← mField expression "rightHandSide"
    if !pre.isEmpty && (statefulCallIn right (← get) || assignmentIn right) then
      failAt target "struct storage write key prelude with stateful RHS is unsupported"
    let (_, _, rhsPre, memberVals) ← lowerFlatStructValue right (some rawSid) true
    unless memberVals.size == rawInfo.scalars.size do
      failAt target "struct assignment member count mismatch"
    let mut out := rhsPre ++ pre
    for (mName, _, mExpr) in memberVals do
      let some mInfo := rawInfo.scalars.find? (·.member == mName)
        | failAt target s!"unknown struct layout member {mName}"
      let writeStmts ← writeRawStructScalar #[] baseSlot mInfo mExpr false
      out := out ++ writeStmts
    return out
  let (name, count, writeMember) ← match path with
    | .zero field => pure (field, 0, fun member value => Stmt.setStorage (topStructMemberFieldName field member) value)
    | .one field key => pure (field, 1, fun member value => Stmt.setStructMember field key member value)
    | .two field key1 key2 => pure (field, 2, fun member value => Stmt.setStructMember2 field key1 key2 member value)
    | .outer _ _ => failAt target "mapping assignment requires both keys"
    | .rawSlot _ _ | .bytesSlot _ _ => failAt target "whole raw-slot struct storage assignment is outside this slice"
  let info ← resolveField name target
  if deleting then
    if let some length := info.fixedArrayLength then
      unless info.keyCount == count do
        failAt target "fixed array mapping key count differs"
      markField name
      let mut out := pre
      for i in [:length] do
        out := out.push (writeMember s!"__solidity_element_{i}" (.literal 0))
      return out
  unless !info.scalarMapping && info.fixedArrayLength.isNone && info.keyCount == count do
    failAt target "whole struct storage assignment requires a struct storage path"
  if deleting then
    unless info.structMappings.isEmpty do
      failAt target "cannot delete mapping struct with mapping members"
    unless info.opaqueNames.isEmpty do
      failAt target "cannot delete mapping struct with opaque members"
    unless info.structDynamicArrays.isEmpty do
      failAt target "cannot delete mapping struct with dynamic-array members"
    unless info.structFixedArrays.isEmpty do
      failAt target "cannot delete mapping struct with fixed-array members"
    unless !info.memberNames.isEmpty do
      failAt target "cannot delete empty mapping struct layout"
    markField name
    let mut out := pre
    for member in info.memberNames do
      out := out.push (writeMember member (.literal 0))
    return out
  unless info.structMappings.isEmpty && info.opaqueNames.isEmpty &&
      info.structFixedArrays.isEmpty && info.structDynamicArrays.isEmpty && !info.memberNames.isEmpty do
    failAt target "whole struct storage assignment requires a scalar-member struct layout"
  let (targetSid, _) ← resolveStructDeclFromType target
  let right ← mField expression "rightHandSide"
  if !pre.isEmpty && (statefulCallIn right (← get) || assignmentIn right) then
    failAt target "struct storage write key prelude with stateful RHS is unsupported"
  let (_, _, rhsPre, memberVals) ← lowerFlatStructValue right (some targetSid) true
  unless memberVals.size == info.memberNames.size do
    failAt target "struct assignment member count mismatch"
  markField name
  let mut out := pre ++ rhsPre
  for (mName, _, mExpr) in memberVals do
    unless info.memberNames.contains mName do
      failAt target s!"unknown struct layout member {mName}"
    let stored := if info.booleanMembers.contains mName then Expr.logicalNot (.logicalNot mExpr) else mExpr
    out := out.push (writeMember mName stored)
  return out

private partial def lowerEffect (statement : Json) : M (Array Stmt) := do
  let assignedHere := bodyAssignedIds statement
  if !assignedHere.isEmpty then
    modify fun e => { e with zeroInitLocals := e.zeroInitLocals.filter (!assignedHere.contains ·) }
  let expression ← mField statement "expression"
  let kind ← mKind expression
  if kind == "FunctionCall" && optStr expression "kind" == some "functionCall" then
    let callee ← mField expression "expression"
    -- Builtin require keeps its overload set in solc's AST; its existing
    -- dedicated validator must run before strict user-declaration resolution.
    if (← mKind callee) == "Identifier" && optStr callee "name" == some "require" then
      return ← lowerRequire statement
    if (← mKind callee) == "Identifier" && optStr callee "name" == some "revert" then
      return ← lowerBuiltinRevert statement
    if (← mKind callee) == "FunctionCallOptions" then
      failAt callee "external contract calls are outside this slice"
    if (← mKind callee) == "MemberAccess" && (field? callee "referencedDeclaration").isNone then
      let base ← mField callee "expression"
      let baseTy ← mType base
      let member := optStr callee "memberName" |>.getD ""
      if (baseTy == "address" || baseTy == "address payable" || baseTy.startsWith "contract ") &&
          ["call", "staticcall", "delegatecall", "transfer", "send"].contains member then
        failAt callee "external contract calls are outside this slice"
      if ["push", "pop"].contains member then
        if let some (pre, fieldName, slotExpr, elemTy, _, _, elemSid?) ← resolveStorageDynamicArrayTarget (← lowerRef base) base then
          let args ← mArr (← mField expression "arguments")
          if let some elemSid := elemSid? then
            if member == "push" then
              if args.isEmpty then
                return (← pushStorageDynamicStructArray pre fieldName slotExpr elemSid none expression).1
              else if args.size == 1 then
                let arg := args[0]!
                if !pre.isEmpty && (statefulCallIn arg (← get) || assignmentIn arg) then
                  failAt arg "storage array push prelude with stateful argument is unsupported"
                let (argSid, _, argPre, memberVals) ← lowerFlatStructValue arg (some elemSid) true
                unless argSid == elemSid do
                  failAt arg "storage struct array push argument type mismatch"
                return (← pushStorageDynamicStructArray (pre ++ argPre) fieldName slotExpr elemSid (some memberVals) expression).1
              else
                failAt expression "storage array push takes at most one argument"
            else
              unless args.isEmpty do
                failAt expression "storage array pop takes no arguments"
              return ← popStorageDynamicArray pre fieldName slotExpr elemTy (some elemSid)
          if member == "push" then
            if args.isEmpty then
              return (← pushStorageDynamicArray pre fieldName slotExpr elemTy none).pre
            else if args.size == 1 then
              let val ← atom (← convert elemTy (← mType args[0]!) (← lowerExpr args[0]!) args[0]!)
              return (← pushStorageDynamicArray (pre ++ val.pre) fieldName slotExpr elemTy (some val.expr)).pre
            else
              failAt expression "storage array push takes at most one argument"
          else
            unless args.isEmpty do
              failAt expression "storage array pop takes no arguments"
            return ← popStorageDynamicArray pre fieldName slotExpr elemTy
        failAt callee s!"storage array {member} is outside this slice"
    let reference ← refInt callee
    if (← mKind callee) == "Identifier" && (reference == -2 || reference == -16) then
      let modCall ← atom (← lowerCall expression)
      return modCall.pre
    if reference ≥ 0 then
      if let some ptr := (← get).fnPtrs.find? reference.toNat then
        unless (← mKind callee) == "Identifier" do
          failAt callee "function pointer call requires a local identifier"
        let checkFnArity (fnId : Nat) : M Nat := do
          let some declaration := (← get).funs.find? fnId
            | failAt callee "unresolved function pointer target"
          let visibility := optStr declaration "visibility" |>.getD ""
          unless visibility == "internal" || visibility == "private" || visibility == "public" do
            failAt callee "function pointer target requires an internal, private, or public declaration"
          let rets ← mArr (← mField (← mField declaration "returnParameters") "parameters")
          pure rets.size
        let arity ← match ptr with
          | .direct fnId => checkFnArity fnId
          | .branch _ tId fId => do
              let v1 ← checkFnArity tId
              let v2 ← checkFnArity fId
              unless v1 == v2 do failAt callee "function pointer branches have mismatched return arities"
              pure v1
        if arity == 0 then
          let rawVals ← lowerCallArgs expression none
          match ptr with
          | .direct fnId =>
              return ← inlineVoidFn fnId rawVals expression
          | .branch condExpr trueFnId falseFnId =>
              let (argPre, atomicVals) ← atomizeCallArgs rawVals
              let trueStmts ← inlineVoidFn trueFnId atomicVals expression
              let falseStmts ← inlineVoidFn falseFnId atomicVals expression
              return argPre.push (.ite condExpr trueStmts.toList falseStmts.toList)
        else if arity > 1 then
          let (multiPre, _) ← lowerMultiCall expression
          return multiPre
        else
          let result ← atom (← lowerCall expression)
          return result.pre
      if let some declaration := (← get).funs.find? reference.toNat then
        let visibility := optStr declaration "visibility" |>.getD ""
        let internalCallee ← match ← mKind callee with
          | "Identifier" => pure true
          | "MemberAccess" =>
              let base ← mField callee "expression"
              let baseTy ← mType base
              let isSuper : Bool ← if (← mKind base) == "Identifier" && optStr base "name" == some "super" then
                pure (decide ((← refInt base) < 0))
              else
                pure false
              pure (isSuper || baseTy.startsWith "type(contract ")
          | _ => pure false
        if (← mKind callee) == "MemberAccess" && !internalCallee then
          let base ← mField callee "expression"
          let isThis := (← mKind base) == "Identifier" && optStr base "name" == some "this"
          let env ← get
          let isLibrary := match env.funContractId.find? reference.toNat with
            | some cid => env.contractKinds.find? cid == some "library"
            | none => false
          unless isThis || isLibrary do
            failAt callee "external contract calls are outside this slice"
        unless visibility == "internal" || visibility == "private" || (visibility == "public" && internalCallee) do
          failAt callee "discarded helper calls require an internal or private declaration"
        let rets ← mArr (← mField (← mField declaration "returnParameters") "parameters")
        if rets.isEmpty then
          let (fnId, vals) ← resolveCallTargetAndArgs expression
          return ← inlineVoidFn fnId vals expression
        if rets.size == 1 then
          let r := rets[0]!
          let rloc := optStr r "storageLocation" |>.getD "default"
          let rty ← mType r
          if (← mStr (← mField r "name")) == "" && rloc == "memory" && (rty == "string" || rty == "bytes") then
            let (fnId, vals) ← resolveCallTargetAndArgs expression
            let buf ← inlineStringFn fnId vals expression
            let ptrAtom ← atom { pre := #[], expr := buf.pointer }
            let sizeAtom ← atom { pre := #[], expr := buf.size }
            return buf.pre ++ ptrAtom.pre ++ sizeAtom.pre
          if rloc == "memory" then
            if let some (elemStr, _, _) := scalarArrayElement? rty then
              let (fnId, vals) ← resolveCallTargetAndArgs expression
              let (arrPre, _) ← inlineArrayFn fnId vals elemStr expression
              return arrPre
          if rloc == "memory" && rty.startsWith "struct " && !rty.contains "[" then
            let (fnId, vals) ← resolveCallTargetAndArgs expression
            let (_, _, structPre, _) ← inlineFlatStructFn fnId vals expression
            return structPre
        if rets.size > 1 then
          let (fnId, vals) ← resolveCallTargetAndArgs expression
          let (multiPre, _) ← inlineMultiFn fnId vals expression
          return multiPre
        -- Materialize even a discarded result: the final expression can itself
        -- read storage or fail. The helper's effect prelude remains ordered.
        let result ← atom (← lowerCall expression)
        return result.pre
  if kind != "Assignment" && kind != "UnaryOperation" then
    return ← lowerRequire statement
  let deleting := kind == "UnaryOperation"
  let operator ← mStr (← mField expression "operator")
  if deleting && (operator == "++" || operator == "--") then
    return (← lowerIncDecExpr expression).pre
  if !deleting && isCompoundAssignOp operator then
    return ← lowerCompoundAssignment expression operator
  unless (deleting && operator == "delete") || (!deleting && operator == "=") do
    failAt expression "only scalar storage assignment and delete are supported"
  let target ← mField expression (if deleting then "subExpression" else "leftHandSide")
  if !deleting && operator == "=" && (← mKind target) == "TupleExpression" then
    if ← mBool (← mField target "isInlineArray") then
      failAt target "inline arrays are outside this slice"
    let cs ← mArr (← mField target "components")
    unless cs.size > 1 && cs.any (!·.isNull) do
      failAt target "tuple assignment requires multiple components"
    let mut expectedTypes : Array (Option String) := #[]
    for c in cs do
      if c.isNull then
        expectedTypes := expectedTypes.push none
      else
        expectedTypes := expectedTypes.push (some (← mType c))
    let right ← mField expression "rightHandSide"
    let (callPre, retExprs) ← lowerMultiCall right (some expectedTypes)
    unless cs.size == retExprs.size do
      failAt expression s!"tuple assignment arity {cs.size} does not match helper return arity {retExprs.size}"
    let mut seenIds : Array Nat := #[]
    let mut assigns : Array Stmt := #[]
    for i in [:cs.size] do
      let c := cs[i]!
      if c.isNull then continue
      unless (← mKind c) == "Identifier" do
        failAt c "tuple assignment target must be a scalar local or storage identifier"
      let cid ← refInt c
      unless cid ≥ 0 && !seenIds.contains cid.toNat do
        failAt c "duplicate or invalid target in tuple assignment"
      seenIds := seenIds.push cid.toNat
      let cty ← mType c
      let (retExpr, retTy) := retExprs.getD i (.literal 0, "")
      let converted ← atom (← convert cty retTy { pre := #[], expr := retExpr } c)
      if let some bound := (← get).values.find? cid.toNat then
        let .localVar binding := bound
          | failAt c "only materialized scalar locals are writable"
        unless (← get).writableLocals.find? cid.toNat == some binding do
          failAt c "only declaration-bound scalar locals are writable"
        unless (paramType cty).isSome do
          failAt c s!"unsupported scalar local assignment type {cty}"
        assigns := assigns ++ converted.pre |>.push (.assignVar binding converted.expr)
      else
        let .state name pre ← lowerRef c
          | failAt c "assignment target is not scalar storage"
        let info ← resolveField name c
        unless info.keyCount == 0 do failAt c "whole mapping assignment is unsupported"
        if info.bytesStorage then failAt c "bytes or string storage tuple assignment is outside this slice"
        markField name
        let storedExpr := if info.booleanScalar then Expr.logicalNot (.logicalNot converted.expr) else converted.expr
        assigns := assigns ++ pre ++ converted.pre |>.push (.setStorage name storedExpr)
    return callPre ++ assigns
  if (← mKind target) == "Identifier" then
    let id ← refInt target
    if id ≥ 0 then
      if (← get).fnPtrs.contains id.toNat then
        failAt target "reassignment of function pointer locals is outside this slice"
      if let some flat := (← get).flatStructs.find? id.toNat then
        if deleting then
          let mut out : Array Stmt := #[]
          for (_, _, binding) in flat.members do
            out := out.push (.assignVar binding (.literal 0))
          return out
        let right ← mField expression "rightHandSide"
        let (_, _, rhsPre, memberVals) ← lowerFlatStructValue right (some flat.structId) false
        unless memberVals.size == flat.members.size do
          failAt expression "flat struct assignment member count mismatch"
        let mut out := rhsPre
        for ((mName, _, binding), (rhsName, _, mExpr)) in flat.members.zip memberVals do
          unless mName == rhsName do
            failAt expression s!"flat struct member mismatch {mName} != {rhsName}"
          out := out.push (.assignVar binding mExpr)
        return out
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
      if let some buf := (← get).byteBuffers.find? id.toNat then
        if !deleting then
          let right ← mField expression "rightHandSide"
          let isBytesConcat ← if (← mKind right) == "FunctionCall" && optStr right "kind" == some "functionCall" then do
            let callee ← mField right "expression"
            if (← mKind callee) == "MemberAccess" && optStr callee "memberName" == some "concat" &&
                (field? callee "referencedDeclaration").isNone then
              let base ← mField callee "expression"
              pure ((← mKind base) == "ElementaryTypeNameExpression" &&
                    (optStr (field? base "typeName" |>.getD Json.null) "name" |>.getD "") == "bytes")
            else
              pure false
          else
            pure false
          if isBytesConcat then
            if let (.localVar ptrBinding, .localVar sizeBinding) := (buf.pointer, buf.size) then
              let rhsBuf ← lowerEncodedBytes right
              return rhsBuf.pre ++ #[.assignVar ptrBinding rhsBuf.pointer, .assignVar sizeBinding rhsBuf.size]
  if (← mKind target) == "MemberAccess" then
    let member ← mStr (← mField target "memberName")
    match ← lowerRef (← mField target "expression") with
    | .flatStruct structLocalId =>
        let some flat := (← get).flatStructs.find? structLocalId
          | failAt target "unknown flat struct local"
        let some (_, mTy, binding) := flat.members.find? (fun (mName, _, _) => mName == member)
          | failAt target s!"unknown flat struct member {member}"
        if deleting then
          return #[.assignVar binding (.literal 0)]
        let right ← mField expression "rightHandSide"
        let value ← atom (← convert mTy (← mType right) (← lowerExpr right) right)
        let stored := if mTy == "bool" then Expr.logicalNot (.logicalNot value.expr) else value.expr
        return value.pre.push (.assignVar binding stored)
    | .path pre path =>
        if let .rawSlot structId baseSlot := path then
          let rawInfo ← resolveRawStructInfo structId target
          if rawInfo.mappings.any (·.member == member) then
            failAt target s!"struct mapping member {member} requires a mapping key"
          if let some dynInfo := rawInfo.dynamicArrays.find? (·.member == member) then
            if deleting then
              return ← deleteStorageDynamicArray pre "" (rawStructMemberSlot baseSlot dynInfo.wordOffset) dynInfo.elemType dynInfo.elemStructId
            failAt target s!"struct dynamic array member {member} requires an element index"
          let some mInfo := rawInfo.scalars.find? (·.member == member)
            | failAt target s!"member {member} is unsupported in raw-slot struct"
          if deleting then
            return ← writeRawStructScalar pre baseSlot mInfo (.literal 0) true
          let right ← mField expression "rightHandSide"
          if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
            failAt target "raw-slot struct member write prelude with stateful RHS is unsupported"
          let value ← atom (← convert mInfo.ty (← mType right) (← lowerExpr right) right)
          let writeStmts ← writeRawStructScalar #[] baseSlot mInfo value.expr false
          return value.pre ++ pre ++ writeStmts
        if let .bytesSlot fieldName _ := path then
          unless member == "value" do
            failAt target s!"unsupported StorageSlot bytes/string member {member}"
          if deleting then
            return ← lowerStorageBytesDelete fieldName pre
          let right ← mField expression "rightHandSide"
          if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
            failAt target "StorageSlot bytes/string write prelude with stateful RHS is unsupported"
          return ← lowerStorageBytesWrite fieldName pre target right
        let (rawField, count, write) ← match path with
          | .zero rawField =>
              let (field, subPrefix) := splitSPathField rawField
              let qualMember := qualifySPathMember subPrefix member
              pure (rawField, 0, fun (value : Expr) => Stmt.setStorage (topStructMemberFieldName field qualMember) value)
          | .one rawField key =>
              let (field, subPrefix) := splitSPathField rawField
              let qualMember := qualifySPathMember subPrefix member
              pure (rawField, 1, fun (value : Expr) => Stmt.setStructMember field key qualMember value)
          | .two rawField key1 key2 =>
              let (field, subPrefix) := splitSPathField rawField
              let qualMember := qualifySPathMember subPrefix member
              pure (rawField, 2, fun (value : Expr) => Stmt.setStructMember2 field key1 key2 qualMember value)
          | .outer _ _ => failAt target "member assignment requires both mapping keys"
          | .rawSlot _ _ | .bytesSlot _ _ => failAt target "member assignment requires a mapping struct storage path"
        let (name, subPrefix) := splitSPathField rawField
        let qualMember := qualifySPathMember subPrefix member
        let info ← resolveField name target
        if info.structMappings.any (·.member == qualMember) then
          failAt target s!"struct mapping member {member} requires a mapping key"
        if info.opaqueNames.contains qualMember then failAt target s!"member {member} is opaque in this slice"
        if info.structFixedArrays.any (·.member == qualMember) then
          failAt target s!"struct fixed array member {member} requires an element index"
        if let some dynInfo := info.structDynamicArrays.find? (·.member == qualMember) then
          if deleting then
            let (slotPre, arrSlot) ← resolveStructDynamicSlot path dynInfo target
            return ← deleteStorageDynamicArray (pre ++ slotPre) "" arrSlot dynInfo.elemType dynInfo.elemStructId
          failAt target s!"struct dynamic array member {member} requires an element index"
        -- Ordering between effectful key and RHS evaluation needs a separate rule.
        unless pre.isEmpty do failAt target "member write key prelude is unsupported"
        unless !info.scalarMapping && info.keyCount == count && info.memberNames.contains qualMember do
          failAt target "member assignment requires a supported layout member"
        let ty ← mType target
        unless (paramType ty).isSome && !ty.startsWith "enum " do
          failAt target "member assignment requires a supported scalar member"
        let write := if info.booleanMembers.contains qualMember && !deleting then
          fun (value : Expr) => write (.logicalNot (.logicalNot value))
        else write
        markField name
        let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do
          let right ← mField expression "rightHandSide"
          atom (← convert ty (← mType right) (← lowerExpr right) right)
        return value.pre.push (write value.expr)
    | _ => failAt target "member assignment requires a mapping struct storage path"
  if (← mKind target) == "IndexAccess" then
    let baseNode ← mField target "baseExpression"
    if (← mKind baseNode) == "Identifier" then
      let baseId ← refInt baseNode
      if baseId ≥ 0 then
        if let some arr := (← get).scalarArrays.find? baseId.toNat then
          unless arr.inMemory do
            failAt target "calldata scalar arrays are read-only"
          let indexExpression ← mField target "indexExpression"
          if statefulCallIn indexExpression (← get) || assignmentIn indexExpression then
            failAt target "stateful or assignment array index is unsupported"
          let indexTy ← mType indexExpression
          unless indexTy.startsWith "uint" || indexTy.startsWith "int_const" do
            failAt target "scalar array index must be unsigned"
          let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
            let right ← mField expression "rightHandSide"
            atom (← convert arr.elementType (← mType right) (← lowerExpr right) right)
          let key ← atom (← lowerExpr indexExpression)
          let stored := if arr.elementType == "bool" && !deleting then
            Expr.logicalNot (.logicalNot value.expr)
          else value.expr
          return (value.pre ++ key.pre).push (.ite (.lt key.expr (.localVar arr.lengthBinding))
            [] [.panicCode (.literal 0x32)]) |>.push
            (.mstore (.add (.add (.localVar arr.memoryPointer) (.literal 32)) (.mul key.expr (.literal 32))) stored)
    let reference ← lowerRef target
    if let .fixedElement pre path index := reference then
      -- Under the pinned via-IR profile, assignment evaluates and captures
      -- the RHS before the LHS mapping keys and index, then checks bounds.
      -- lowerRef captures the keys/index in their recursive source order.
      let (name, count, write) ← match path with
        | .zero name => pure (name, 0, fun member value => Stmt.setStorage (topStructMemberFieldName (splitSPathField name).1 member) value)
        | .one name key => pure (name, 1, fun member value => Stmt.setStructMember name key member value)
        | .two name key1 key2 => pure (name, 2, fun member value => Stmt.setStructMember2 name key1 key2 member value)
        | .outer _ _ => failAt target "fixed array write requires both mapping keys"
        | .rawSlot _ _ | .bytesSlot _ _ => failAt target "fixed array write on raw-slot struct is outside this slice"
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
    if let .structFixedElement pre path arrInfo index := reference then
      let (rawName, count, write) ← match path with
        | .zero rawName => pure (rawName, 0, fun member value => Stmt.setStorage (topStructMemberFieldName (splitSPathField rawName).1 member) value)
        | .one rawName key => pure (rawName, 1, fun member value => Stmt.setStructMember (splitSPathField rawName).1 key member value)
        | .two rawName key1 key2 => pure (rawName, 2, fun member value => Stmt.setStructMember2 (splitSPathField rawName).1 key1 key2 member value)
        | .outer _ _ => failAt target "fixed array write requires both mapping keys"
        | .rawSlot _ _ | .bytesSlot _ _ => failAt target "fixed array write on raw-slot struct is outside this slice"
      let (name, _) := splitSPathField rawName
      let info ← resolveField name target
      unless info.keyCount == count do failAt target "fixed array mapping key count differs"
      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
        let right ← mField expression "rightHandSide"
        atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
      let capturedValue ← fresh
      let valuePre := value.pre.push (.letVar capturedValue value.expr)
      let mut result := (valuePre ++ pre).push (.ite (.lt index (.literal arrInfo.length))
        [] [.panicCode (.literal 0x32)])
      for i in [:arrInfo.length] do
        result := result.push (.ite (.eq index (.literal i))
          [write s!"__solidity_struct_array_{arrInfo.member}_{i}" (.localVar capturedValue)] [])
      markField name
      markStructFixedArray name arrInfo.member
      return result
    if let .structDynamicElement pre path dynInfo index := reference then
      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
        let right ← mField expression "rightHandSide"
        atom (← convert dynInfo.elemType (← mType right) (← lowerExpr right) right)
      if !pre.isEmpty && !deleting then
        let right ← mField expression "rightHandSide"
        if assignmentIn right || statefulCallIn right (← get) then
          failAt target "struct dynamic array write index prelude with stateful RHS is unsupported"
      let (slotPre, arrSlot) ← resolveStructDynamicSlot path dynInfo target
      return ← writeStorageDynamicArrayElement (pre ++ value.pre ++ slotPre) "" arrSlot dynInfo.elemType index value.expr deleting
    if let .storageDynamicElement pre fieldName slotExpr elemTy index := reference then
      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
        let right ← mField expression "rightHandSide"
        atom (← convert elemTy (← mType right) (← lowerExpr right) right)
      if !pre.isEmpty && !deleting then
        let right ← mField expression "rightHandSide"
        if assignmentIn right || statefulCallIn right (← get) then
          failAt target "storage dynamic array write index prelude with stateful RHS is unsupported"
      return ← writeStorageDynamicArrayElement (pre ++ value.pre) fieldName slotExpr elemTy index value.expr deleting
    if let .structMappingElement pre path mapInfo key := reference then
      let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
        let right ← mField expression "rightHandSide"
        atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
      if !pre.isEmpty && !deleting then
        let right ← mField expression "rightHandSide"
        if assignmentIn right || statefulCallIn right (← get) then
          failAt target "struct mapping write key prelude with stateful RHS is unsupported"
      return ← writeStructMappingElement (pre ++ value.pre) path mapInfo key value.expr deleting target
    let .path pre path := reference
      | failAt target "mapping assignment target is not a storage path"
    if let .rawSlot _ _ := path then
      return ← writeWholeStorageStruct pre path deleting target expression
    let (name, count, write) ← match path with
      | .zero field => pure ((splitSPathField field).1, 0, fun (value : Expr) => Stmt.setStorage (topStructMemberFieldName (splitSPathField field).1 "__solidity_value") value)
      | .one field key => pure ((splitSPathField field).1, 1, fun (value : Expr) => Stmt.setStructMember (splitSPathField field).1 key "__solidity_value" value)
      | .two field key1 key2 => pure ((splitSPathField field).1, 2, fun (value : Expr) => Stmt.setStructMember2 (splitSPathField field).1 key1 key2 "__solidity_value" value)
      | .outer _ _ => failAt target "mapping assignment requires both keys"
      | .rawSlot _ _ | .bytesSlot _ _ => failAt target "mapping assignment target is not a storage path"
    let info ← resolveField name target
    if !info.scalarMapping && (info.fixedArrayLength.isNone || deleting) && info.keyCount == count then
      return ← writeWholeStorageStruct pre path deleting target expression
    unless info.scalarMapping && info.keyCount == count do
      failAt target "only scalar mapping values are writable"
    markField name
    let value ← if deleting then pure ({ pre := #[], expr := (.literal 0 : Expr) } : Val) else do
      let right ← mField expression "rightHandSide"
      atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
    let expr := if info.booleanMapping then Expr.logicalNot (.logicalNot value.expr) else value.expr
    return (pre ++ value.pre).push (write expr)
  unless (← mKind target) == "Identifier" || (← mKind target) == "FunctionCall" do
    failAt target "only a resolved scalar storage identifier is writable"
  match ← lowerRef target with
  | .path pre path =>
      return ← writeWholeStorageStruct pre path deleting target expression
  | .structDynamicArray pre (.rawSlot 0 slotExpr) dynInfo =>
      if deleting then
        return ← deleteStorageDynamicArray pre "" slotExpr dynInfo.elemType dynInfo.elemStructId
      else
        failAt target "whole dynamic storage array assignment is unsupported"
  | .state name pre =>
      let info ← resolveField name target
      unless info.keyCount == 0 do failAt target "whole mapping assignment is unsupported"
      if let some (elemTy, _, _) := info.dynamicArrayElemType then
        if deleting then
          return ← deleteStorageDynamicArray pre name (.literal info.slot) elemTy info.dynamicArrayStructId
        else
          failAt target "whole dynamic storage array assignment is unsupported"
      if info.bytesStorage then
        if deleting then
          return ← lowerStorageBytesDelete name pre
        else
          let right ← mField expression "rightHandSide"
          return ← lowerStorageBytesWrite name pre target right
      markField name
      let value ← if deleting then pure ({ pre := #[], expr := .literal 0 } : Val) else do
        let right ← mField expression "rightHandSide"
        atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
      if info.booleanScalar && !deleting then
        return (pre ++ value.pre).push (.setStorage name (.logicalNot (.logicalNot value.expr)))
      return (pre ++ value.pre).push (.setStorage name value.expr)
  | _ => failAt target "assignment target is not scalar storage"

private partial def combineCompound (operator : String) (ty : String) (lhs rhs : Expr) (at_ : Json) : M Val := do
  let isUnchecked := (← get).unchecked
  if ty == "int256" || ty == "int" then
    if operator == "+=" then
      if isUnchecked then
        pure { pre := #[], expr := .add lhs rhs }
      else
        checkedSignedAdd { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "-=" then
      if isUnchecked then
        pure { pre := #[], expr := .sub lhs rhs }
      else
        checkedSignedSub { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "*=" then
      if isUnchecked then
        pure { pre := #[], expr := .mul lhs rhs }
      else
        checkedSignedMul { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "/=" then
      signedDiv isUnchecked { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "<<=" then
      pure { pre := #[], expr := .shl rhs lhs }
    else if operator == ">>=" then
      pure { pre := #[], expr := .sar rhs lhs }
    else if operator == "&=" then
      pure { pre := #[], expr := .bitAnd lhs rhs }
    else if operator == "|=" then
      pure { pre := #[], expr := .bitOr lhs rhs }
    else if operator == "^=" then
      pure { pre := #[], expr := .bitXor lhs rhs }
    else
      failAt at_ s!"unsupported compound assignment operator {operator}"
  else if ty == "bytes32" then
    if operator == "&=" then
      pure { pre := #[], expr := .bitAnd lhs rhs }
    else if operator == "|=" then
      pure { pre := #[], expr := .bitOr lhs rhs }
    else if operator == "^=" then
      pure { pre := #[], expr := .bitXor lhs rhs }
    else if operator == "<<=" then
      pure { pre := #[], expr := .shl rhs lhs }
    else if operator == ">>=" then
      pure { pre := #[], expr := .shr rhs lhs }
    else
      failAt at_ s!"unsupported compound assignment operator {operator} for {ty}"
  else if ty == "bytes4" then
    if operator == "&=" then
      pure { pre := #[], expr := .bitAnd lhs rhs }
    else if operator == "|=" then
      pure { pre := #[], expr := .bitOr lhs rhs }
    else if operator == "^=" then
      pure { pre := #[], expr := .bitXor lhs rhs }
    else
      failAt at_ s!"unsupported compound assignment operator {operator} for {ty}"
  else
    let some bits := bitsOf ty
      | failAt at_ s!"compound assignment requires an integer type, found {ty}"
    unless ty.startsWith "uint" do
      failAt at_ s!"compound assignment requires an integer type, found {ty}"
    if operator == "+=" then
      if isUnchecked then
        let wrapped := if bits < 256 then Expr.bitAnd (.add lhs rhs) (.literal (2 ^ bits - 1)) else .add lhs rhs
        pure { pre := #[], expr := wrapped }
      else
        checkedAdd bits { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "-=" then
      if isUnchecked then
        let wrapped := if bits < 256 then Expr.bitAnd (.sub lhs rhs) (.literal (2 ^ bits - 1)) else .sub lhs rhs
        pure { pre := #[], expr := wrapped }
      else
        checkedSub { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "*=" then
      if isUnchecked then
        let wrapped := if bits < 256 then Expr.bitAnd (.mul lhs rhs) (.literal (2 ^ bits - 1)) else .mul lhs rhs
        pure { pre := #[], expr := wrapped }
      else
        checkedMul bits { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "/=" then
      checkedDiv { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "%=" then
      checkedModulo { pre := #[], expr := lhs } { pre := #[], expr := rhs }
    else if operator == "<<=" then
      let shifted := if bits < 256 then Expr.bitAnd (.shl rhs lhs) (.literal (2 ^ bits - 1)) else .shl rhs lhs
      pure { pre := #[], expr := shifted }
    else if operator == ">>=" then
      pure { pre := #[], expr := .shr rhs lhs }
    else if operator == "&=" then
      pure { pre := #[], expr := .bitAnd lhs rhs }
    else if operator == "|=" then
      pure { pre := #[], expr := .bitOr lhs rhs }
    else if operator == "^=" then
      pure { pre := #[], expr := .bitXor lhs rhs }
    else
      failAt at_ s!"unsupported compound assignment operator {operator}"

private partial def lowerCompoundAssignment (expression : Json) (operator : String) : M (Array Stmt) := do
  let target ← mField expression "leftHandSide"
  let right ← mField expression "rightHandSide"
  let isSupportedCompoundTy (ty : String) : Bool :=
    (ty.startsWith "uint" && (bitsOf ty).isSome) || ty == "int256" || ty == "int" ||
      (ty == "bytes32" && ["&=", "|=", "^=", "<<=", ">>="].contains operator) ||
      (ty == "bytes4" && ["&=", "|=", "^="].contains operator)
  let lowerRhs (ty : String) : M Val := do
    let rightTy ← mType right
    let raw ← lowerExpr right
    if operator == "<<=" || operator == ">>=" then
      unless rightTy.startsWith "uint" || (rightTy.startsWith "int_const" && !rightTy.startsWith "int_const -") do
        failAt right s!"shift amount must be unsigned, found {rightTy}"
      atom raw
    else
      atom (← convert ty rightTy raw right)
  if (← mKind target) == "Identifier" then
    let id ← refInt target
    if id ≥ 0 then
      if let some bound := (← get).values.find? id.toNat then
        let .localVar binding := bound
          | failAt target "only materialized scalar locals are writable"
        unless (← get).writableLocals.find? id.toNat == some binding do
          failAt target "only declaration-bound scalar locals are writable"
        let ty ← mType target
        unless isSupportedCompoundTy ty do
          failAt target s!"unsupported scalar local compound assignment type {ty}"
        let rhsVal ← lowerRhs ty
        let combined ← combineCompound operator ty (.localVar binding) rhsVal.expr expression
        return rhsVal.pre ++ combined.pre |>.push (.assignVar binding combined.expr)
  if (← mKind target) == "MemberAccess" then
    let cMember ← mStr (← mField target "memberName")
    let .path pre path ← lowerRef (← mField target "expression")
      | failAt target "member assignment requires a mapping struct storage path"
    if let .rawSlot structId baseSlot := path then
      let rawInfo ← resolveRawStructInfo structId target
      if rawInfo.mappings.any (·.member == cMember) then
        failAt target s!"struct mapping member {cMember} requires a mapping key"
      if rawInfo.dynamicArrays.any (·.member == cMember) then
        failAt target s!"struct dynamic array member {cMember} requires an element index"
      let some mInfo := rawInfo.scalars.find? (·.member == cMember)
        | failAt target s!"member {cMember} is unsupported in raw-slot struct"
      let ty ← mType target
      unless isSupportedCompoundTy ty do
        failAt target s!"unsupported raw-slot struct member compound assignment type {ty}"
      if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
        failAt target "raw-slot struct member compound write prelude with stateful RHS is unsupported"
      let rhsVal ← lowerRhs ty
      let lhsVal ← readRawStructScalar pre baseSlot mInfo
      let combined ← combineCompound operator ty lhsVal.expr rhsVal.expr expression
      let writeStmts ← writeRawStructScalar #[] baseSlot mInfo combined.expr false
      return rhsVal.pre ++ lhsVal.pre ++ combined.pre ++ writeStmts
    unless pre.isEmpty do failAt target "member write key prelude is unsupported"
    let (rawField, count, read, write) ← match path with
      | .zero rawField =>
          let (cField, subPrefix) := splitSPathField rawField
          let qualMember := qualifySPathMember subPrefix cMember
          pure (rawField, 0, Expr.storage (topStructMemberFieldName cField qualMember), fun (cVal : Expr) => Stmt.setStorage (topStructMemberFieldName cField qualMember) cVal)
      | .one rawField cKey =>
          let (cField, subPrefix) := splitSPathField rawField
          let qualMember := qualifySPathMember subPrefix cMember
          pure (rawField, 1, Expr.structMember cField cKey qualMember, fun (cVal : Expr) => Stmt.setStructMember cField cKey qualMember cVal)
      | .two rawField cKey1 cKey2 =>
          let (cField, subPrefix) := splitSPathField rawField
          let qualMember := qualifySPathMember subPrefix cMember
          pure (rawField, 2, Expr.structMember2 cField cKey1 cKey2 qualMember, fun (cVal : Expr) => Stmt.setStructMember2 cField cKey1 cKey2 qualMember cVal)
      | .outer _ _ => failAt target "member assignment requires both mapping keys"
      | .rawSlot _ _ | .bytesSlot _ _ => failAt target "member assignment requires a mapping struct storage path"
    let (name, subPrefix) := splitSPathField rawField
    let qualMember := qualifySPathMember subPrefix cMember
    let info ← resolveField name target
    if info.structMappings.any (·.member == qualMember) then
      failAt target s!"struct mapping member {cMember} requires a mapping key"
    if info.opaqueNames.contains qualMember then failAt target s!"member {cMember} is opaque in this slice"
    if info.structFixedArrays.any (·.member == qualMember) then
      failAt target s!"struct fixed array member {cMember} requires an element index"
    if info.structDynamicArrays.any (·.member == qualMember) then
      failAt target s!"struct dynamic array member {cMember} requires an element index"
    unless !info.scalarMapping && info.keyCount == count && info.memberNames.contains qualMember do
      failAt target "member assignment requires a supported layout member"
    let ty ← mType target
    unless ty.startsWith "uint" && (bitsOf ty).isSome do
      failAt target "member assignment requires an unsigned scalar member"
    markField name
    let rhsVal ← lowerRhs ty
    let lhsVar ← fresh
    let combined ← combineCompound operator ty (.localVar lhsVar) rhsVal.expr expression
    return rhsVal.pre.push (.letVar lhsVar read) ++ combined.pre |>.push (write combined.expr)
  if (← mKind target) == "IndexAccess" then
    let reference ← lowerRef target
    if let .fixedElement _ _ _ := reference then
      failAt expression "only scalar storage assignment and delete are supported"
    if let .structFixedElement _ _ _ _ := reference then
      failAt expression "only scalar storage assignment and delete are supported"
    if let .structDynamicElement pre path dynInfo index := reference then
      let ty ← mType target
      unless isSupportedCompoundTy ty do
        failAt target s!"unsupported dynamic array compound assignment type {ty}"
      if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
        failAt target "compound dynamic array write index prelude with stateful RHS is unsupported"
      let rhsVal ← lowerRhs ty
      let (slotPre, arrSlot) ← resolveStructDynamicSlot path dynInfo target
      let lhsVal ← readStorageDynamicArrayElement (pre ++ slotPre) "" arrSlot dynInfo.elemType index
      let combined ← combineCompound operator ty lhsVal.expr rhsVal.expr expression
      let writeStmts ← writeStorageDynamicArrayElement #[] "" arrSlot dynInfo.elemType index combined.expr false
      return rhsVal.pre ++ lhsVal.pre ++ combined.pre ++ writeStmts
    if let .storageDynamicElement pre fieldName slotExpr elemTy index := reference then
      let ty ← mType target
      unless isSupportedCompoundTy ty do
        failAt target s!"unsupported dynamic array compound assignment type {ty}"
      if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
        failAt target "compound dynamic array write index prelude with stateful RHS is unsupported"
      let rhsVal ← lowerRhs ty
      let lhsVal ← readStorageDynamicArrayElement pre fieldName slotExpr elemTy index
      let combined ← combineCompound operator ty lhsVal.expr rhsVal.expr expression
      let writeStmts ← writeStorageDynamicArrayElement #[] fieldName slotExpr elemTy index combined.expr false
      return rhsVal.pre ++ lhsVal.pre ++ combined.pre ++ writeStmts
    if let .structMappingElement pre path mapInfo key := reference then
      let ty ← mType target
      unless isSupportedCompoundTy ty do
        failAt target s!"unsupported mapping compound assignment type {ty}"
      if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
        failAt target "compound mapping write key prelude with stateful RHS is unsupported"
      let rhsVal ← lowerRhs ty
      let lhsVal ← readStructMappingElement pre path mapInfo key target
      let combined ← combineCompound operator ty lhsVal.expr rhsVal.expr expression
      let writeStmts ← writeStructMappingElement #[] path mapInfo key combined.expr false target
      return rhsVal.pre ++ lhsVal.pre ++ combined.pre ++ writeStmts
    let .path pre path := reference
      | failAt target "mapping assignment target is not a storage path"
    let (name, count, read, write) ← match path with
      | .zero _ => failAt target "only scalar mapping values are writable"
      | .one cField cKey => pure ((splitSPathField cField).1, 1, Expr.structMember (splitSPathField cField).1 cKey "__solidity_value", fun (cVal : Expr) => Stmt.setStructMember (splitSPathField cField).1 cKey "__solidity_value" cVal)
      | .two cField cKey1 cKey2 => pure ((splitSPathField cField).1, 2, Expr.structMember2 (splitSPathField cField).1 cKey1 cKey2 "__solidity_value", fun (cVal : Expr) => Stmt.setStructMember2 (splitSPathField cField).1 cKey1 cKey2 "__solidity_value" cVal)
      | .outer _ _ => failAt target "mapping assignment requires both keys"
      | .rawSlot _ _ | .bytesSlot _ _ => failAt target "only scalar mapping values are writable"
    let info ← resolveField name target
    unless info.scalarMapping && info.keyCount == count do
      failAt target "only scalar mapping values are writable"
    let ty ← mType target
    unless isSupportedCompoundTy ty do
      failAt target s!"unsupported mapping compound assignment type {ty}"
    if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
      failAt target "compound mapping write key prelude with stateful RHS is unsupported"
    markField name
    let rhsVal ← lowerRhs ty
    let lhsVar ← fresh
    let combined ← combineCompound operator ty (.localVar lhsVar) rhsVal.expr expression
    return (pre ++ rhsVal.pre).push (.letVar lhsVar read) ++ combined.pre |>.push (write combined.expr)
  unless (← mKind target) == "Identifier" do
    failAt target "only a resolved scalar storage identifier is writable"
  let .state name pre ← lowerRef target
    | failAt target "assignment target is not scalar storage"
  let info ← resolveField name target
  unless info.keyCount == 0 do failAt target "whole mapping assignment is unsupported"
  let ty ← mType target
  unless isSupportedCompoundTy ty do
    failAt target s!"unsupported scalar storage compound assignment type {ty}"
  markField name
  let rhsVal ← lowerRhs ty
  let lhsVar ← fresh
  let combined ← combineCompound operator ty (.localVar lhsVar) rhsVal.expr expression
  return (pre ++ rhsVal.pre).push (.letVar lhsVar (.storage name)) ++ combined.pre |>.push (.setStorage name combined.expr)

private partial def lowerAssignmentExpr (j : Json) : M Val := do
  let operator ← mStr (← mField j "operator")
  unless operator == "=" do
    failAt j "compound assignment expressions are outside this slice"
  let target ← mField j "leftHandSide"
  let right ← mField j "rightHandSide"
  unless (← mKind target) == "Identifier" do
    failAt target "assignment expressions currently require a scalar local or storage identifier"
  let id ← refInt target
  if id ≥ 0 then
    if (← get).fnPtrs.contains id.toNat then
      failAt target "reassignment of function pointer locals is outside this slice"
    if let some bound := (← get).values.find? id.toNat then
      let .localVar binding := bound
        | failAt target "only materialized scalar locals are writable"
      unless (← get).writableLocals.find? id.toNat == some binding do
        failAt target "only declaration-bound scalar locals are writable"
      let ty ← mType target
      unless (paramType ty).isSome do
        failAt target s!"unsupported scalar local assignment type {ty}"
      let value ← atom (← convert ty (← mType right) (← lowerExpr right) right)
      return { pre := value.pre.push (.assignVar binding value.expr), expr := .localVar binding }
  let .state name pre ← lowerRef target
    | failAt target "assignment target is not scalar storage"
  let info ← resolveField name target
  unless info.keyCount == 0 do failAt target "whole mapping assignment is unsupported"
  if info.bytesStorage then failAt target "bytes or string storage assignment expression is outside this slice"
  markField name
  let value ← atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
  let storedExpr := if info.booleanScalar then Expr.logicalNot (.logicalNot value.expr) else value.expr
  let resultVar ← fresh
  return { pre := (pre ++ value.pre).push (.letVar resultVar storedExpr) |>.push (.setStorage name (.localVar resultVar)), expr := .localVar resultVar }

private partial def lowerIncDecExpr (j : Json) : M Val := do
  let operator ← mStr (← mField j "operator")
  let isPrefix := (field? j "prefix").bind (fun v => v.getBool?.toOption) == some true
  let compoundOp := if operator == "++" then "+=" else "-="
  let target ← mField j "subExpression"
  let isSupportedIncDecTy (ty : String) : Bool :=
    (ty.startsWith "uint" && (bitsOf ty).isSome) || ty == "int256" || ty == "int"
  if (← mKind target) == "Identifier" then
    let id ← refInt target
    if id ≥ 0 then
      if let some bound := (← get).values.find? id.toNat then
        let .localVar binding := bound
          | failAt target "only materialized scalar locals are writable"
        unless (← get).writableLocals.find? id.toNat == some binding do
          failAt target "only declaration-bound scalar locals are writable"
        let ty ← mType target
        unless isSupportedIncDecTy ty do
          failAt target s!"unsupported scalar local increment/decrement type {ty}"
        let oldVar ← fresh
        let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
        let stmts := #[Stmt.letVar oldVar (.localVar binding)] ++ combined.pre |>.push (.assignVar binding combined.expr)
        return { pre := stmts, expr := if isPrefix then .localVar binding else .localVar oldVar }
  if (← mKind target) == "MemberAccess" then
    let cMember ← mStr (← mField target "memberName")
    let .path pre path ← lowerRef (← mField target "expression")
      | failAt target "member assignment requires a mapping struct storage path"
    if let .rawSlot structId baseSlot := path then
      let rawInfo ← resolveRawStructInfo structId target
      if rawInfo.mappings.any (·.member == cMember) then
        failAt target s!"struct mapping member {cMember} requires a mapping key"
      if rawInfo.dynamicArrays.any (·.member == cMember) then
        failAt target s!"struct dynamic array member {cMember} requires an element index"
      let some mInfo := rawInfo.scalars.find? (·.member == cMember)
        | failAt target s!"member {cMember} is unsupported in raw-slot struct"
      let ty ← mType target
      unless isSupportedIncDecTy ty do
        failAt target s!"unsupported raw-slot struct member increment/decrement type {ty}"
      let lhsVal ← readRawStructScalar pre baseSlot mInfo
      let oldVar ← fresh
      let newVar ← fresh
      let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
      let writeStmts ← writeRawStructScalar #[] baseSlot mInfo (.localVar newVar) false
      let stmts := (lhsVal.pre.push (.letVar oldVar lhsVal.expr) ++
        combined.pre).push (.letVar newVar combined.expr) ++ writeStmts
      return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }
    unless pre.isEmpty do failAt target "member write key prelude is unsupported"
    let (rawField, count, read, write) ← match path with
      | .zero rawField =>
          let (cField, subPrefix) := splitSPathField rawField
          let qualMember := qualifySPathMember subPrefix cMember
          pure (rawField, 0, Expr.storage (topStructMemberFieldName cField qualMember), fun (cVal : Expr) => Stmt.setStorage (topStructMemberFieldName cField qualMember) cVal)
      | .one rawField cKey =>
          let (cField, subPrefix) := splitSPathField rawField
          let qualMember := qualifySPathMember subPrefix cMember
          pure (rawField, 1, Expr.structMember cField cKey qualMember, fun (cVal : Expr) => Stmt.setStructMember cField cKey qualMember cVal)
      | .two rawField cKey1 cKey2 =>
          let (cField, subPrefix) := splitSPathField rawField
          let qualMember := qualifySPathMember subPrefix cMember
          pure (rawField, 2, Expr.structMember2 cField cKey1 cKey2 qualMember, fun (cVal : Expr) => Stmt.setStructMember2 cField cKey1 cKey2 qualMember cVal)
      | .outer _ _ => failAt target "member assignment requires both mapping keys"
      | .rawSlot _ _ | .bytesSlot _ _ => failAt target "member assignment requires a mapping struct storage path"
    let (name, subPrefix) := splitSPathField rawField
    let qualMember := qualifySPathMember subPrefix cMember
    let info ← resolveField name target
    if info.structMappings.any (·.member == qualMember) then
      failAt target s!"struct mapping member {cMember} requires a mapping key"
    if info.opaqueNames.contains qualMember then failAt target s!"member {cMember} is opaque in this slice"
    if info.structFixedArrays.any (·.member == qualMember) then
      failAt target s!"struct fixed array member {cMember} requires an element index"
    if info.structDynamicArrays.any (·.member == qualMember) then
      failAt target s!"struct dynamic array member {cMember} requires an element index"
    unless !info.scalarMapping && info.keyCount == count && info.memberNames.contains qualMember do
      failAt target "member assignment requires a supported layout member"
    let ty ← mType target
    unless ty.startsWith "uint" && (bitsOf ty).isSome do
      failAt target "member assignment requires an unsigned scalar member"
    markField name
    let oldVar ← fresh
    let newVar ← fresh
    let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
    let stmts := #[Stmt.letVar oldVar read] ++ combined.pre |>.push (.letVar newVar combined.expr) |>.push (write (.localVar newVar))
    return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }
  if (← mKind target) == "IndexAccess" then
    let reference ← lowerRef target
    if let .fixedElement _ _ _ := reference then
      failAt j "only scalar storage assignment and delete are supported"
    if let .structFixedElement _ _ _ _ := reference then
      failAt j "only scalar storage assignment and delete are supported"
    if let .structDynamicElement pre path dynInfo index := reference then
      let ty ← mType target
      unless isSupportedIncDecTy ty do
        failAt target s!"unsupported dynamic array increment/decrement type {ty}"
      let (slotPre, arrSlot) ← resolveStructDynamicSlot path dynInfo target
      let lhsVal ← readStorageDynamicArrayElement (pre ++ slotPre) "" arrSlot dynInfo.elemType index
      let oldVar ← fresh
      let newVar ← fresh
      let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
      let writeStmts ← writeStorageDynamicArrayElement #[] "" arrSlot dynInfo.elemType index (.localVar newVar) false
      let stmts := (lhsVal.pre.push (.letVar oldVar lhsVal.expr) ++
        combined.pre).push (.letVar newVar combined.expr) ++ writeStmts
      return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }
    if let .storageDynamicElement pre fieldName slotExpr elemTy index := reference then
      let ty ← mType target
      unless isSupportedIncDecTy ty do
        failAt target s!"unsupported dynamic array increment/decrement type {ty}"
      let lhsVal ← readStorageDynamicArrayElement pre fieldName slotExpr elemTy index
      let oldVar ← fresh
      let newVar ← fresh
      let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
      let writeStmts ← writeStorageDynamicArrayElement #[] fieldName slotExpr elemTy index (.localVar newVar) false
      let stmts := (lhsVal.pre.push (.letVar oldVar lhsVal.expr) ++
        combined.pre).push (.letVar newVar combined.expr) ++ writeStmts
      return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }
    if let .structMappingElement pre path mapInfo key := reference then
      let ty ← mType target
      unless isSupportedIncDecTy ty do
        failAt target s!"unsupported mapping increment/decrement type {ty}"
      let lhsVal ← readStructMappingElement pre path mapInfo key target
      let oldVar ← fresh
      let newVar ← fresh
      let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
      let writeStmts ← writeStructMappingElement #[] path mapInfo key (.localVar newVar) false target
      let stmts := (lhsVal.pre.push (.letVar oldVar lhsVal.expr) ++
        combined.pre).push (.letVar newVar combined.expr) ++ writeStmts
      return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }
    let .path pre path := reference
      | failAt target "mapping assignment target is not a storage path"
    let (name, count, read, write) ← match path with
      | .zero _ => failAt target "only scalar mapping values are writable"
      | .one cField cKey => pure ((splitSPathField cField).1, 1, Expr.structMember (splitSPathField cField).1 cKey "__solidity_value", fun (cVal : Expr) => Stmt.setStructMember (splitSPathField cField).1 cKey "__solidity_value" cVal)
      | .two cField cKey1 cKey2 => do
          unless pre.isEmpty do failAt target "nested mapping increment/decrement key prelude is unsupported"
          pure ((splitSPathField cField).1, 2, Expr.structMember2 (splitSPathField cField).1 cKey1 cKey2 "__solidity_value", fun (cVal : Expr) => Stmt.setStructMember2 (splitSPathField cField).1 cKey1 cKey2 "__solidity_value" cVal)
      | .outer _ _ => failAt target "mapping assignment requires both keys"
      | .rawSlot _ _ | .bytesSlot _ _ => failAt target "only scalar mapping values are writable"
    let info ← resolveField name target
    unless info.scalarMapping && info.keyCount == count do
      failAt target "only scalar mapping values are writable"
    let ty ← mType target
    unless isSupportedIncDecTy ty do
      failAt target s!"unsupported mapping increment/decrement type {ty}"
    markField name
    let oldVar ← fresh
    let newVar ← fresh
    let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
    let stmts := pre.push (.letVar oldVar read) ++ combined.pre |>.push (.letVar newVar combined.expr) |>.push (write (.localVar newVar))
    return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }
  unless (← mKind target) == "Identifier" do
    failAt target "only a resolved scalar storage identifier is writable"
  let .state name pre ← lowerRef target
    | failAt target "assignment target is not scalar storage"
  let info ← resolveField name target
  unless info.keyCount == 0 do failAt target "whole mapping assignment is unsupported"
  let ty ← mType target
  unless isSupportedIncDecTy ty do
    failAt target s!"unsupported scalar storage increment/decrement type {ty}"
  markField name
  let oldVar ← fresh
  let newVar ← fresh
  let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j
  let stmts := pre.push (.letVar oldVar (.storage name)) ++ combined.pre |>.push (.letVar newVar combined.expr) |>.push (.setStorage name (.localVar newVar))
  return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }

private partial def extractStringLiteralOrConstant (message : Json) (forRevert : Bool) : M String := do
  let label := if forRevert then "revert" else "require"
  let litNode ← match ← mKind message with
    | "Literal" => pure message
    | "Identifier" | "MemberAccess" =>
        if (← mKind message) == "MemberAccess" then
          let base ← mField message "expression"
          let baseTy ← mType base
          unless baseTy.startsWith "type(library " || baseTy.startsWith "type(contract " do
            failAt message s!"{label} currently needs a literal string message"
        let id ← refInt message
        unless id ≥ 0 do
          failAt message s!"{label} currently needs a literal string message"
        let some decl := (← get).numericConstants.find? id.toNat
          | failAt message s!"{label} currently needs a literal string message"
        unless (← mType decl) == "string" do
          failAt message s!"{label} currently needs a literal string message"
        let initVal ← mField decl "value"
        unless (← mKind initVal) == "Literal" do
          failAt message s!"{label} currently needs a literal string message"
        pure initVal
    | _ => failAt message s!"{label} currently needs a literal string message"
  let kind ← mStr (← mField litNode "kind")
  unless kind == "string" || kind == "unicodeString" do
    failAt message s!"{label} message must be a UTF-8 string literal"
  let some value := optStr litNode "value"
    | failAt message s!"{label} message bytes are not represented exactly by UTF-8"
  let actual ← mStr (← mField litNode "hexValue")
  let expected := value.toUTF8.data.foldl (init := "") fun acc byte =>
    acc.push (hexDigit (byte.toNat / 16)) |>.push (hexDigit (byte.toNat % 16))
  unless actual == expected do
    failAt message s!"{label} message bytes are not represented exactly by UTF-8"
  return value

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
  let value ← extractStringLiteralOrConstant message false
  let condition ← atom (← lowerExpr args[0]!)
  return condition.pre.push (.require condition.expr value)

private partial def lowerBuiltinRevert (statement : Json) : M (Array Stmt) := do
  let call ← mField statement "expression"
  unless (← mKind call) == "FunctionCall" && optStr call "kind" == some "functionCall" do
    failAt call "revert must be a function call"
  let callee ← mField call "expression"
  unless (← mKind callee) == "Identifier" && optStr callee "name" == some "revert" do
    failAt callee "only builtin revert calls are supported here"
  let signature ← mType callee
  unless (← mField callee "referencedDeclaration").getInt?.toOption == some (-19) &&
      (signature == "function () pure" || signature == "function (string memory) pure") do
    failAt callee "revert must resolve to a supported Solidity builtin signature"
  unless (← mArr (← mField callee "overloadedDeclarations")).all
      (fun declaration => declaration.getInt?.toOption == some (-19)) do
    failAt callee "revert overload set contains a non-builtin declaration"
  unless (← mArr (← mField call "names")).isEmpty do
    failAt call "named revert arguments are unsupported"
  let args ← mArr (← mField call "arguments")
  if signature == "function () pure" then
    unless args.isEmpty do failAt call "bare revert() takes no arguments"
    return #[.revertReturndata]
  unless args.size == 1 do failAt call "revert(string) requires one message argument"
  let value ← extractStringLiteralOrConstant args[0]! true
  return #[.require (.literal 0) value]

private partial def lowerRevert (statement : Json) : M (Array Stmt) := do
  let call ← mField statement "errorCall"
  let (pre, name, values) ← lowerErrorArguments call
  return pre.push (.requireError (.literal 0) name values)

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
    discard (validateEnumTypeIfNeeded parameter ty)
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
    | .uintN bits =>
        unless (match value.expr with
                | .param _ => true
                | .literal n => n < 2 ^ bits
                | _ => false) && value.pre.isEmpty do
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
    discard (validateEnumTypeIfNeeded parameter ty)
    let some modelType := paramType ty | failAt parameter s!"unsupported custom-error parameter type {ty}"
    unless (Denote.errorScalarType modelType).isSome do
      failAt parameter s!"unsupported custom-error parameter type {ty}"
    let argument := arguments[index]!
    -- Restrict this slice to total scalar operands or pure compile-time constants.
    -- General expressions need an evaluation-order argument, including competing panic paths.
    let isDirectScalar ← match ← mKind argument with
      | "Literal" => pure true
      | "Identifier" =>
          let argumentId ← refInt argument
          if argumentId ≥ 0 && (← get).values.contains argumentId.toNat then
            pure true
          else if argumentId ≥ 0 && (← get).numericConstants.contains argumentId.toNat then
            pure false
          else
            failAt argument "custom-error arguments currently require literals or scalar bindings"
      | "FunctionCall" =>
          if optStr argument "kind" == some "typeConversion" then
            pure false
          else if optStr argument "kind" == some "functionCall" &&
              (← mArr (← mField argument "arguments")).isEmpty then
            pure true
          else
            failAt argument "custom-error arguments currently require literals or scalar bindings"
      | "MemberAccess" =>
          let member ← mStr (← mField argument "memberName")
          let base ← mField argument "expression"
          if member == "sender" || member == "timestamp" || member == "number" || member == "chainid" || member == "origin" then
            pure true
          else if (← mKind base) == "Identifier" &&
              (member == "length" || ((← mType base).startsWith "struct " && !(← mType base).contains "[")) then
            let baseId ← refInt base
            let env ← get
            if baseId ≥ 0 && (env.scalarArrays.contains baseId.toNat || env.calldataBytes.contains baseId.toNat ||
                env.flatStructs.contains baseId.toNat || env.mems.contains baseId.toNat) then
              pure true
            else if baseId ≥ 0 && env.snapshots.contains baseId.toNat && member == "length" then
              pure false
            else
              failAt argument "custom-error arguments currently require literals or scalar bindings"
          else
            unless member == "max" || member == "min" || member == "interfaceId" || member == "selector" || (← mType base).startsWith "type(enum " do
              failAt argument "custom-error arguments currently require literals or scalar bindings"
            pure false
      | _ => failAt argument "custom-error arguments currently require literals or scalar bindings"
    let converted ← convert ty (← mType argument) (← lowerExpr argument) argument
    if isDirectScalar then
      let isScalarBinding := match converted.expr with
        | .localVar _ => true
        | _ => isOrderIndependentSibling converted.expr
      unless converted.pre.isEmpty && isScalarBinding do
        failAt argument "custom-error arguments currently require literals or scalar bindings"
    if !isDirectScalar then
      let isConstLiteral := match converted.expr with
        | .literal n => converted.pre.isEmpty && Denote.errorScalarValueValid modelType n
        | _ => false
      unless isConstLiteral do
        failAt argument "custom-error arguments currently require literals or scalar bindings"
    let value ← atom converted
    types := types ++ [modelType]
    values := values ++ [value.expr]
    pre := pre ++ value.pre
  let definition : ErrorDef := { name, params := types }
  if let some previous := (← get).usedErrors.find? (·.name == name) then
    unless previous.params == types do failAt callee "custom-error name has multiple signatures"
  else
    modify fun e => { e with usedErrors := e.usedErrors ++ [definition] }
  return (pre, name, values)

private partial def lowerLocal (s : Json) : M (Array Stmt) := do
  let assignedHere := bodyAssignedIds s
  if !assignedHere.isEmpty then
    modify fun e => { e with zeroInitLocals := e.zeroInitLocals.filter (!assignedHere.contains ·) }
  let decls ← mArr (← mField s "declarations")
  if decls.size > 1 then
    unless decls.any (!·.isNull) do failAt s "empty tuple declaration"
    let init := field? s "initialValue" |>.getD Json.null
    if init.isNull then failAt s "tuple variable declaration requires an initializer"
    if ← isAbiDecodeCall init then
      let (decodePre, decoded) ← lowerAbiDecodeItems init
      unless decls.size == decoded.size do
        failAt s s!"tuple declaration arity {decls.size} does not match abi.decode arity {decoded.size}"
      let mut out := decodePre
      for i in [:decls.size] do
        let d := decls[i]!
        if d.isNull then continue
        let name ← mStr (← mField d "name")
        unless name.all (fun c => c.isAlphanum || c == '_' || c == '$') && name != "" do
          failAt d s!"unsupported local name {name}"
        let id ← mNat (← mField d "id")
        let loc := optStr d "storageLocation" |>.getD "default"
        let dTy ← mType d
        match decoded[i]! with
        | .scalar retTy _ retExpr =>
            unless loc == "default" do
              failAt d "scalar abi.decode component requires a default-location local"
            discard (validateEnumTypeIfNeeded d dTy)
            let some scalarType := paramType dTy
              | failAt d s!"unsupported tuple local type {dTy}"
            let converted ← convert dTy retTy { pre := #[], expr := retExpr } d
            let binding ← freshFor name
            let expr := Expr.localVar binding
            out := out ++ converted.pre |>.push (.letVar binding converted.expr)
            modify fun e =>
              { e with values := e.values.insert id expr,
                       scalarTy := e.scalarTy.insert id scalarType,
                       yulNames := e.yulNames.insert name expr,
                       yulMemoryArrays := e.yulMemoryArrays.erase name,
                       writableLocals := e.writableLocals.insert id binding,
                       zeroInitLocals := e.zeroInitLocals.filter (· != id) }
        | .flatStruct sid sName memberVals =>
            unless loc == "memory" && dTy.startsWith "struct " && !dTy.contains "[" do
              failAt d "struct abi.decode component requires a memory struct local"
            let (declSid, _) ← resolveStructDeclFromType d
            unless declSid == sid do
              failAt d "struct abi.decode component type mismatch"
            let mut boundMembers : Array (String × String × String) := #[]
            for (mName, mTy, mExpr) in memberVals do
              let mBinding ← freshFor s!"{name}_{mName}"
              out := out.push (.letVar mBinding mExpr)
              boundMembers := boundMembers.push (mName, mTy, mBinding)
            let fDesc : FlatStructLocal := { structId := sid, structName := sName, members := boundMembers }
            modify fun e =>
              { e with flatStructs := e.flatStructs.insert id fDesc,
                       yulNames := e.yulNames.erase name,
                       yulMemoryArrays := e.yulMemoryArrays.erase name }
        | .scalarArray elemStr _ _ rawDesc =>
            unless loc == "memory" && (dTy == elemStr ++ "[]" || dTy == elemStr ++ "[] memory") do
              failAt d "array abi.decode component requires a matching memory array local"
            if (← get).bodyAssigned.contains id then
              failAt d "reassigned memory array locals are outside this slice"
            let desc := { rawDesc with param := name }
            modify fun e =>
              { e with scalarArrays := e.scalarArrays.insert id desc,
                       encodingMemory := true,
                       yulNames := e.yulNames.erase name,
                       yulMemoryArrays := e.yulMemoryArrays.insert name desc.memoryPointer }
        | .dynamicBytes isString buf =>
            let expectedBase := if isString then "string" else "bytes"
            unless loc == "memory" && (dTy == expectedBase || dTy == expectedBase ++ " memory") do
              failAt d s!"{expectedBase} abi.decode component requires a memory {expectedBase} local"
            if isString && (← get).bodyAssigned.contains id then
              failAt d "reassigned string locals are outside this slice"
            let pointer ← freshFor name
            let size ← fresh
            out := out ++ buf.pre ++ #[.letVar pointer buf.pointer, .letVar size buf.size]
            let retained : EncodedBytes := { pre := #[], pointer := .localVar pointer, size := .localVar size }
            if isString then
              modify fun e =>
                { e with stringBuffers := e.stringBuffers.insert id retained,
                         yulNames := e.yulNames.erase name,
                         yulMemoryArrays := e.yulMemoryArrays.erase name }
            else
              modify fun e =>
                { e with byteBuffers := e.byteBuffers.insert id retained,
                         yulNames := e.yulNames.erase name,
                         yulMemoryArrays := e.yulMemoryArrays.erase name }
      return out
    let mut expectedTypes : Array (Option String) := #[]
    for d in decls do
      if d.isNull then
        expectedTypes := expectedTypes.push none
      else
        expectedTypes := expectedTypes.push (some (← mType d))
    let (callPre, retExprs) ← lowerMultiCall init (some expectedTypes)
    unless decls.size == retExprs.size do
      failAt s s!"tuple declaration arity {decls.size} does not match helper return arity {retExprs.size}"
    let mut out := callPre
    for i in [:decls.size] do
      let d := decls[i]!
      if d.isNull then continue
      let name ← mStr (← mField d "name")
      unless name.all (fun c => c.isAlphanum || c == '_' || c == '$') && name != "" do
        failAt d s!"unsupported local name {name}"
      let id ← mNat (← mField d "id")
      let loc := optStr d "storageLocation" |>.getD "default"
      unless loc == "default" do
        failAt d "tuple variable declaration only supports scalar locals"
      let ty ← mType d
      discard (validateEnumTypeIfNeeded d ty)
      let some scalarType := paramType ty
        | failAt d s!"unsupported tuple local type {ty}"
      let (retExpr, retTy) := retExprs.getD i (.literal 0, "")
      let converted ← convert ty retTy { pre := #[], expr := retExpr } d
      let binding ← freshFor name
      let expr := Expr.localVar binding
      out := out ++ converted.pre |>.push (.letVar binding converted.expr)
      let isZero := converted.pre.isEmpty && (match converted.expr with | .literal 0 => true | _ => false)
      modify fun e =>
        { e with values := e.values.insert id expr,
                 scalarTy := e.scalarTy.insert id scalarType,
                 yulNames := e.yulNames.insert name expr,
                 yulMemoryArrays := e.yulMemoryArrays.erase name,
                 writableLocals := e.writableLocals.insert id binding,
                 zeroInitLocals := if isZero then (if e.zeroInitLocals.contains id then e.zeroInitLocals else e.zeroInitLocals.push id) else e.zeroInitLocals.filter (· != id) }
    return out
  unless decls.size == 1 do failAt s "only a single declaration is supported"
  if decls[0]!.isNull then failAt s "empty declaration"
  let d := decls[0]!
  let name ← mStr (← mField d "name")
  unless name.all (fun c => c.isAlphanum || c == '_' || c == '$') && name != "" do
    failAt d s!"unsupported local name {name}"
  let id ← mNat (← mField d "id")
  let loc := optStr d "storageLocation" |>.getD "default"
  let init := field? s "initialValue" |>.getD Json.null
  modify fun e => { e with yulMemoryArrays := e.yulMemoryArrays.erase name }
  if let some typeNameNode := field? d "typeName" then
    if optStr typeNameNode "nodeType" == some "FunctionTypeName" then
      let fvis := optStr typeNameNode "visibility" |>.getD ""
      unless fvis == "internal" do
        failAt d s!"only internal function pointer locals are supported, found {fvis}"
      if init.isNull then
        failAt d "uninitialized function pointer locals are outside this slice"
      if (← get).bodyAssigned.contains id then
        failAt d "reassigned function pointer locals are outside this slice"
      let (pre, ptr) ← lowerFnPtrInit init
      modify fun e =>
        { e with fnPtrs := e.fnPtrs.insert id ptr,
                 yulNames := e.yulNames.erase name }
      return pre
  if init.isNull then
    if loc == "memory" && (← mType d) == "bytes" && (← get).bodyAssigned.contains id then
      let pointer ← freshFor name
      let size ← fresh
      let effects : Array Stmt := #[.letVar pointer (.literal 96), .letVar size (.literal 0)]
      let retained : EncodedBytes :=
        { pre := #[], pointer := .localVar pointer, size := .localVar size }
      modify fun e =>
        { e with byteBuffers := e.byteBuffers.insert id retained,
                 encodingMemory := true,
                 yulNames := e.yulNames.erase name }
      return effects
    unless loc == "default" do
      failAt d "uninitialized reference locals are outside this slice"
    let ty ← mType d
    discard (validateEnumTypeIfNeeded d ty)
    let some scalarType := paramType ty
      | failAt d s!"unsupported default local type {ty}"
    let binding ← freshFor name
    let expr := Expr.localVar binding
    modify fun e =>
      { e with values := e.values.insert id expr,
               scalarTy := e.scalarTy.insert id scalarType,
               yulNames := e.yulNames.insert name expr,
               writableLocals := e.writableLocals.insert id binding,
               zeroInitLocals := if e.zeroInitLocals.contains id then e.zeroInitLocals else e.zeroInitLocals.push id }
    return #[.letVar binding (.literal 0)]
  if loc == "memory" && (← mType d) == "bytes" then
    -- Evaluate allocation and encoding once, at the declaration. Only a
    -- payload descriptor is exposed: assignment, indexing, reference calls
    -- and Yul pointer access remain rejected until their exact rules exist.
    let buffer ← lowerEncodedBytes init
    let pointer ← freshFor name
    let size ← fresh
    let effects := buffer.pre ++ #[.letVar pointer buffer.pointer, .letVar size buffer.size]
    let retained : EncodedBytes :=
      { pre := #[], pointer := .localVar pointer, size := .localVar size }
    modify fun e =>
      { e with byteBuffers := e.byteBuffers.insert id retained,
               yulNames := e.yulNames.erase name }
    return effects
  if loc == "memory" && (← mType d) == "string" then
    if (← get).bodyAssigned.contains id then
      failAt d "reassigned string locals are outside this slice"
    let buffer ← lowerEncodedBytes init
    let pointer ← freshFor name
    let size ← fresh
    let effects := buffer.pre ++ #[.letVar pointer buffer.pointer, .letVar size buffer.size]
    let retained : EncodedBytes :=
      { pre := #[], pointer := .localVar pointer, size := .localVar size }
    modify fun e =>
      { e with stringBuffers := e.stringBuffers.insert id retained,
               yulNames := e.yulNames.erase name }
    return effects
  if loc == "memory" && (← mType d).contains "[]" then
    let some (elemStr, elemPty, abiKind) := scalarArrayElement? (← mType d)
      | failAt d s!"unsupported dynamic memory array local type {← mType d}"
    if (← get).bodyAssigned.contains id then
      failAt d "reassigned memory array locals are outside this slice"
    if ← isAbiDecodeCall init then
      let (decodePre, decoded) ← lowerAbiDecodeItems init
      unless decoded.size == 1 do
        failAt init "array local abi.decode initializer requires a single array target type"
      let .scalarArray decElemStr _ _ rawDesc := decoded[0]!
        | failAt init "array local abi.decode initializer requires a dynamic scalar array target type"
      unless decElemStr == elemStr do
        failAt init "dynamic memory array initializer type differs from declaration"
      let desc := { rawDesc with param := name }
      modify fun e =>
        { e with scalarArrays := e.scalarArrays.insert id desc,
                 encodingMemory := true,
                 yulNames := e.yulNames.erase name,
                 yulMemoryArrays := e.yulMemoryArrays.insert name desc.memoryPointer }
      return decodePre
    let isArrayHelperInit ← if (← mKind init) == "FunctionCall" && optStr init "kind" == some "functionCall" then do
      pure ((← mArr (← mField init "names")).isEmpty && (← mKind (← mField init "expression")) != "NewExpression")
    else
      pure false
    if isArrayHelperInit then
      let initTy ← mType init
      unless initTy == (← mType d) || initTy == elemStr ++ "[] memory" do
        failAt init "dynamic memory array initializer type differs from declaration"
      let (fnId, vals) ← resolveCallTargetAndArgs init
      let (arrPre, rawDesc) ← inlineArrayFn fnId vals elemStr init
      let desc := { rawDesc with param := name }
      modify fun e =>
        { e with scalarArrays := e.scalarArrays.insert id desc,
                 encodingMemory := true,
                 yulNames := e.yulNames.erase name,
                 yulMemoryArrays := e.yulMemoryArrays.insert name desc.memoryPointer }
      return arrPre
    if (← mKind init) != "FunctionCall" then
      if let some (pre, fieldName, slotExpr, sElemTy, modelElemTy, sAbiKind, none) ← resolveStorageDynamicArrayTarget (← lowerRef init) init then
        unless sElemTy == elemStr do
          failAt init "dynamic memory array initializer type differs from declaration"
        let (copyStmts, desc) ← copyStorageDynamicArrayToMemory pre fieldName slotExpr sElemTy modelElemTy sAbiKind name
        modify fun e =>
          { e with scalarArrays := e.scalarArrays.insert id desc,
                   encodingMemory := true,
                   yulNames := e.yulNames.erase name,
                   yulMemoryArrays := e.yulMemoryArrays.insert name desc.memoryPointer }
        return copyStmts
    unless (← mKind init) == "FunctionCall" && optStr init "kind" == some "functionCall" do
      failAt init "dynamic memory array local requires a new T[](length) initializer"
    unless (← mArr (← mField init "names")).isEmpty do
      failAt init "dynamic memory array local requires a new T[](length) initializer"
    let callee ← mField init "expression"
    unless (← mKind callee) == "NewExpression" do
      failAt init "dynamic memory array local requires a new T[](length) initializer"
    let initTy ← mType init
    unless initTy == (← mType d) || initTy == elemStr ++ "[] memory" do
      failAt init "dynamic memory array initializer type differs from declaration"
    let args ← mArr (← mField init "arguments")
    unless args.size == 1 do
      failAt init "new array allocation requires a single length argument"
    let lenArg := args[0]!
    let lenTy ← mType lenArg
    unless (lenTy.startsWith "uint" && (bitsOf lenTy).isSome) ||
        (lenTy.startsWith "int_const" && !lenTy.startsWith "int_const -") do
      failAt lenArg s!"dynamic memory array length must be unsigned, found {lenTy}"
    let lenVal ← atom (← lowerExpr lenArg)
    let lenBinding ← freshFor (name ++ "_len")
    let arrayPtr ← freshFor name
    let nextFree ← fresh
    let zeroIdx ← fresh
    let allocStmts : Array Stmt := lenVal.pre ++ #[
      .letVar lenBinding lenVal.expr,
      .ite (.le (.localVar lenBinding) (.literal (2^64 - 1))) [] [.panicCode (.literal 0x41)],
      .letVar arrayPtr (.mload (.literal 64)),
      .letVar nextFree (.add (.localVar arrayPtr) (.mul (.literal 32) (.add (.localVar lenBinding) (.literal 1)))),
      .ite (.le (.localVar nextFree) (.literal (2^64 - 1))) [] [.panicCode (.literal 0x41)],
      .ite (.ge (.localVar nextFree) (.localVar arrayPtr)) [] [.panicCode (.literal 0x41)],
      .mstore (.localVar arrayPtr) (.localVar lenBinding),
      .mstore (.literal 64) (.localVar nextFree),
      .forEach zeroIdx (.localVar lenBinding) [
        .mstore (.add (.add (.localVar arrayPtr) (.literal 32)) (.mul (.localVar zeroIdx) (.literal 32))) (.literal 0)
      ]
    ]
    let desc : ScalarArrayParam :=
      { param := name
        elementType := elemStr
        modelElementType := elemPty
        abiKind := abiKind
        inMemory := true
        offsetBinding := ""
        headerBinding := ""
        lengthBinding := lenBinding
        dataBinding := ""
        memoryPointer := arrayPtr
        nextFreeBinding := nextFree
        namePrefix := zeroIdx }
    modify fun e =>
      { e with scalarArrays := e.scalarArrays.insert id desc,
               encodingMemory := true,
               yulNames := e.yulNames.erase name,
               yulMemoryArrays := e.yulMemoryArrays.insert name arrayPtr }
    return allocStmts
  if loc == "memory" && (← mType d).contains '[' then
    if (← mKind init) == "TupleExpression" then
      if ← mBool (← mField init "isInlineArray") then
        failAt init "inline arrays are outside this slice"
    match ← lowerRef init with
    | .path pre path =>
        let (field, count, read) ← match path with
          | .zero field => pure (field, 0, fun member => Expr.storage (topStructMemberFieldName (splitSPathField field).1 member))
          | .one field key => pure (field, 1, fun member => Expr.structMember field key member)
          | .two field key1 key2 => pure (field, 2, fun member => Expr.structMember2 field key1 key2 member)
          | .outer _ _ => failAt init "fixed array copy requires both mapping keys"
          | .rawSlot _ _ | .bytesSlot _ _ => failAt init "fixed memory array initialization requires a mapping storage array"
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
        modify fun e =>
          { e with snapshots := e.snapshots.insert id elements,
                   yulNames := e.yulNames.erase name }
        markField field
        return result
    | .structFixedArray pre path arrInfo =>
        let (rawField, count, read) ← match path with
          | .zero rawField => pure (rawField, 0, fun member => Expr.storage (topStructMemberFieldName (splitSPathField rawField).1 member))
          | .one rawField key => pure (rawField, 1, fun member => Expr.structMember (splitSPathField rawField).1 key member)
          | .two rawField key1 key2 => pure (rawField, 2, fun member => Expr.structMember2 (splitSPathField rawField).1 key1 key2 member)
          | .outer _ _ => failAt init "fixed array copy requires both mapping keys"
          | .rawSlot _ _ | .bytesSlot _ _ => failAt init "fixed memory array initialization requires a mapping storage array"
        let (field, _) := splitSPathField rawField
        let info ← resolveField field init
        unless info.keyCount == count && ((← mType d).splitOn " ").head! == arrInfo.arrayType do
          failAt d "fixed memory array copy type differs from storage layout"
        let mut result := pre
        let mut elements : Array Expr := #[]
        for i in [:arrInfo.length] do
          let binding ← fresh
          result := result.push (.letVar binding (read s!"__solidity_struct_array_{arrInfo.member}_{i}"))
          elements := elements.push (.localVar binding)
        modify fun e =>
          { e with snapshots := e.snapshots.insert id elements,
                   yulNames := e.yulNames.erase name }
        markField field
        markStructFixedArray field arrInfo.member
        return result
    | _ => failAt d "fixed memory array initialization requires a mapping storage array"
  if loc == "storage" then
    if (← get).bodyAssigned.contains id then
      failAt d "reassigned storage pointer locals are outside this slice"
    let baseTy := (← mType d).replace " storage pointer" "" |>.replace " storage ref" ""
    if baseTy.endsWith "[]" then
      let some (pre, fieldName, slotExpr, elemTy, _, _, elemSid?) ← resolveStorageDynamicArrayTarget (← lowerRef init) init
        | failAt s "storage dynamic array local is not a resolved storage array path"
      let env ← get
      let writable := match slotExpr with
        | .localVar vname => env.writableLocals.toList.any (fun (_, b) => b == vname)
        | _ => false
      let (spre, frozenSlot) ← if writable then do
        let binding ← fresh
        pure (#[Stmt.letVar binding slotExpr], Expr.localVar binding)
      else do
        let slotAtom ← atom { pre := #[], expr := slotExpr }
        pure (slotAtom.pre, slotAtom.expr)
      modify fun e =>
        { e with storageDynamicArrayVars := e.storageDynamicArrayVars.insert id (fieldName, frozenSlot, elemTy, elemSid?),
                 yulNames := e.yulNames.erase name |>.insert s!"{name}.slot" frozenSlot }
      return pre ++ spre
    match ← lowerRef init with
    | .path pre path =>
        -- A Solidity storage pointer fixes its address at declaration time.
        -- Freeze writable local keys, since subsequent assignments may change them.
        let capture (key : Expr) : M (Array Stmt × Expr) := do
          let env ← get
          let writable := match key with
            | .localVar name => env.writableLocals.toList.any (fun (_, b) => b == name)
            | _ => false
          if !writable then
            return (#[], key)
          let binding ← fresh
          pure (#[.letVar binding key], .localVar binding)
        let (keys, frozen) ← match path with
          | .zero field => pure (#[], SPath.zero field)
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
          | .rawSlot rawSid slot => do
              let (spre, frozenSlot) ← capture slot
              pure (spre, SPath.rawSlot rawSid frozenSlot)
          | .bytesSlot fieldName isString =>
              pure (#[], SPath.bytesSlot fieldName isString)
        modify fun e =>
          { e with paths := e.paths.insert id frozen,
                   yulNames := e.yulNames.erase name }
        pure (pre ++ keys)
    | _ => failAt s "storage local is not a resolved read path"
  else if (loc == "memory" || loc == "calldata") && (← mType d).startsWith "struct " && !(← mType d).contains "[" then
    let sid ← refInt (← mField d "typeName")
    if sid < 0 then failAt d "builtin struct"
    let innerInit ← stripParens init
    if loc == "memory" &&
        (((← mKind innerInit) == "FunctionCall" &&
          (optStr innerInit "kind" == some "structConstructorCall" || optStr innerInit "kind" == some "functionCall")) ||
         (← mKind innerInit) == "Conditional") then
      let (_, sName, initPre, memberVals) ← lowerFlatStructValue innerInit (some sid.toNat) false
      let mut out := initPre
      let mut members : Array (String × String × String) := #[]
      for (mName, mTy, mExpr) in memberVals do
        let binding ← freshFor s!"{name}_{mName}"
        out := out.push (.letVar binding mExpr)
        members := members.push (mName, mTy, binding)
      modify fun e =>
        { e with flatStructs := e.flatStructs.insert id { structId := sid.toNat, structName := sName, members },
                 yulNames := e.yulNames.erase name }
      return out
    match ← lowerRef init with
    | .path _ _ =>
        unless loc == "memory" do
          failAt d "cannot initialize calldata struct local from storage struct"
        let (_, sName, initPre, memberVals) ← lowerFlatStructValue init (some sid.toNat) false
        let mut out := initPre
        let mut members : Array (String × String × String) := #[]
        for (mName, mTy, mExpr) in memberVals do
          let binding ← freshFor s!"{name}_{mName}"
          out := out.push (.letVar binding mExpr)
          members := members.push (mName, mTy, binding)
        modify fun e =>
          { e with flatStructs := e.flatStructs.insert id { structId := sid.toNat, structName := sName, members },
                   yulNames := e.yulNames.erase name }
        return out
    | .mem rootId effects =>
        if (← get).bodyAssigned.contains id then
          failAt d "reassigned struct locals are outside this slice"
        let some descriptor := (← get).mems.find? rootId
          | failAt d "unknown struct initializer"
        unless descriptor.structId == sid.toNat do
          failAt d "struct local declaration differs from initializer"
        if loc == "calldata" then
          unless descriptor.calldataLocation do
            failAt d "cannot initialize calldata struct local from memory struct"
          modify fun e =>
            { e with mems := e.mems.insert id descriptor,
                     yulNames := e.yulNames.erase name }
          return effects
        else if descriptor.calldataLocation then
          let (convStmts, memDesc) ← convertStructCalldataToMemory descriptor d
          modify fun e =>
            { e with mems := e.mems.insert id memDesc,
                     yulNames := e.yulNames.erase name }
          return effects ++ convStmts
        else
          modify fun e =>
            { e with mems := e.mems.insert id descriptor,
                     yulNames := e.yulNames.erase name }
          return effects
    | .abiElement rootId memberIndex pointer inMemory effects =>
        if (← get).bodyAssigned.contains id then
          failAt d "reassigned struct locals are outside this slice"
        let some mem := (← get).mems.find? rootId | failAt d "unknown ABI root"
        let some schema := mem.schema | failAt d "missing ABI schema"
        let some (.structArray _ fields) := schema[memberIndex]?
          | failAt d "expected a struct-array element"
        let some parentDecl := (← get).structs.find? mem.structId
          | failAt d "unknown parent struct"
        let parentMembers ← mArr (← mField parentDecl "members")
        let some memberNode := parentMembers[memberIndex]?
          | failAt d "missing parent struct member"
        let elemSid ← refInt (← mField (← mField memberNode "typeName") "baseType")
        unless elemSid ≥ 0 && elemSid.toNat == sid.toNat do
          failAt d "struct local declaration differs from initializer"
        if loc == "calldata" then
          unless !inMemory do
            failAt d "cannot initialize calldata struct local from memory struct array"
          let ptrAtom ← atom { pre := #[], expr := pointer }
          let bound : AbiElementLocal :=
            { rootId, memberIndex, pointer := ptrAtom.expr, inMemory := false }
          modify fun e =>
            { e with abiElements := e.abiElements.insert id bound,
                     yulNames := e.yulNames.erase name }
          return effects ++ ptrAtom.pre
        else if !inMemory then
          let ptrAtom ← atom { pre := #[], expr := pointer }
          let elemStem ← freshAbiElementStem fields
          let (matPtr, _, matStmts) := AbiRootLowering.materializeElementFromCalldata ptrAtom.expr elemStem fields
          let bound : AbiElementLocal :=
            { rootId, memberIndex, pointer := .localVar matPtr, inMemory := true }
          modify fun e =>
            { e with abiElements := e.abiElements.insert id bound,
                     encodingMemory := true,
                     yulNames := e.yulNames.erase name }
          return effects ++ ptrAtom.pre ++ matStmts.toArray
        else
          let ptrAtom ← atom { pre := #[], expr := pointer }
          let bound : AbiElementLocal :=
            { rootId, memberIndex, pointer := ptrAtom.expr, inMemory := true }
          modify fun e =>
            { e with abiElements := e.abiElements.insert id bound,
                     yulNames := e.yulNames.erase name }
          return effects ++ ptrAtom.pre
    | _ =>
        if (← get).bodyAssigned.contains id then
          failAt d "reassigned struct locals are outside this slice"
        failAt d "struct local initializer must be a supported struct or struct-array element reference"
  else
    let v ← lowerExpr init
    unless loc == "default" do
      failAt d s!"unsupported local storage location {loc}"
    let ty ← mType d
    discard (validateEnumTypeIfNeeded d ty)
    let some scalarType := paramType ty
      | failAt d s!"unsupported scalar local type {ty}"
    let converted ← convert ty (← mType init) v init
    let binding ← freshFor name
    let expr := Expr.localVar binding
    let isZero := converted.pre.isEmpty && (match converted.expr with | .literal 0 => true | _ => false)
    modify fun e =>
      { e with values := e.values.insert id expr, scalarTy := e.scalarTy.insert id scalarType,
               yulNames := e.yulNames.insert name expr, writableLocals := e.writableLocals.insert id binding,
               zeroInitLocals := if isZero then (if e.zeroInitLocals.contains id then e.zeroInitLocals else e.zeroInitLocals.push id) else e.zeroInitLocals.filter (· != id) }
    pure (converted.pre.push (.letVar binding converted.expr))

end

private def structMemberList (st : Json) : M (Array (String × String)) := do
  let ms ← mArr (← mField st "members")
  let mut out : Array (String × String) := #[]
  for m in ms do
    out := out.push (← mStr (← mField m "name"), ← mType m)
  pure out

private def functionEmptyBodyArrayReturnType? (fn : Json) : M (Option ParamType) := do
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do return none
  let fnBody ← mField fn "body"
  let fnStmts ← mArr (← mField fnBody "statements")
  let fnMods ← mArr (← mField fn "modifiers")
  unless fnStmts.isEmpty && fnMods.isEmpty do return none
  let r := rets[0]!
  let loc := optStr r "storageLocation" |>.getD "default"
  unless loc == "memory" do return none
  let rty ← mType r
  unless rty.endsWith "[]" do return none
  let elemStr := (rty.dropEnd 2).toString
  unless !elemStr.startsWith "enum " && elemStr != "bytes4" do return none
  let some elemTy := paramType elemStr | return none
  unless isCanonicalReturnArrayParam (.array elemTy) do return none
  return some (.array elemTy)

private def functionFixedArrayReturnType? (fn : Json) : M (Option (String × ParamType × Nat)) := do
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do return none
  let r := rets[0]!
  let rname ← mStr (← mField r "name")
  unless rname == "" do return none
  let loc := optStr r "storageLocation" |>.getD "default"
  unless loc == "memory" do return none
  let rty ← mType r
  let [elemStr, suffix] := rty.splitOn "["
    | return none
  unless suffix.endsWith "]" && suffix != "]" do return none
  let some length := (suffix.dropEnd 1).toNat? | return none
  unless length > 0 && !elemStr.startsWith "enum " && elemStr != "bytes4" do return none
  let some elemPty := paramType elemStr | return none
  return some (elemStr, elemPty, length)

private def functionMsgDataReturn? (fn : Json) : M Bool := do
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.isEmpty do return false
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do return false
  let r := rets[0]!
  let rname ← mStr (← mField r "name")
  unless rname == "" do return false
  let loc := optStr r "storageLocation" |>.getD "default"
  unless loc == "calldata" || loc == "memory" do return false
  return (← mType r) == "bytes"

private def functionDynamicBytesReturn? (fn : Json) : M (Option ParamType) := do
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do return none
  let r := rets[0]!
  let rname ← mStr (← mField r "name")
  unless rname == "" do return none
  let loc := optStr r "storageLocation" |>.getD "default"
  unless loc == "memory" || loc == "calldata" do return none
  match ← mType r with
  | "bytes" => return some .bytes
  | "string" => return some .string
  | _ => return none

private def functionFlatStructReturnType? (fn : Json) :
    M (Option (Nat × String × String × Nat × Array (String × String × ParamType))) := do
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do return none
  let r := rets[0]!
  let loc := optStr r "storageLocation" |>.getD "default"
  unless loc == "memory" do return none
  let rty ← mType r
  unless rty.startsWith "struct " && !rty.contains "[" do return none
  let (retSid, retDecl) ← resolveStructDeclFromType r
  let retStructName ← mStr (← mField retDecl "name")
  let retMembers ← mArr (← mField retDecl "members")
  unless !retMembers.isEmpty do return none
  let mut memberSpecs : Array (String × String × ParamType) := #[]
  for mNode in retMembers do
    let mName ← mStr (← mField mNode "name")
    let mTy ← mType mNode
    unless !mTy.startsWith "enum " do return none
    let some mPty := paramType mTy | return none
    memberSpecs := memberSpecs.push (mName, mTy, mPty)
  let rname ← mStr (← mField r "name")
  let rid ← mNat (← mField r "id")
  return some (retSid, retStructName, rname, rid, memberSpecs)

private partial def canLowerDynamicBytesReturnExpr (j : Json) : M Bool := do
  match ← mKind j with
  | "Conditional" =>
      return (← canLowerDynamicBytesReturnExpr (← mField j "trueExpression")) &&
             (← canLowerDynamicBytesReturnExpr (← mField j "falseExpression"))
  | "Literal" =>
      pure (optStr j "kind" == some "hexString" || optStr j "kind" == some "string" ||
            optStr j "kind" == some "unicodeString")
  | "Identifier" =>
      let id ← refInt j
      if id < 0 then return false
      let env ← get
      if env.calldataBytes.contains id.toNat || env.storageBytesVars.contains id.toNat then
        return true
      if env.byteBuffers.contains id.toNat || env.stringBuffers.contains id.toNat then
        return false
      if let some decl := env.stateVars.find? id.toNat then
        if (field? decl "constant").bind (fun value => value.getBool?.toOption) == some true then
          return true
        return optStr decl "mutability" != some "immutable"
      return false
  | "MemberAccess" =>
      if optStr j "memberName" == some "value" then
        let ty ← mType j
        return ty == "string storage ref" || ty == "string storage pointer" ||
               ty == "bytes storage ref" || ty == "bytes storage pointer"
      let ty ← mType j
      if (ty == "bytes" || ty == "bytes memory" || ty == "bytes calldata") &&
          (← mType (← mField j "expression")).startsWith "struct " then
        return true
      return false
  | "FunctionCall" =>
      if optStr j "kind" == some "typeConversion" then
        let ty ← mType j
        return ty == "bytes" || ty == "bytes memory" || ty == "bytes calldata" || ty == "bytes storage pointer" ||
               ty == "string" || ty == "string memory" || ty == "string calldata" || ty == "string storage pointer"
      if optStr j "kind" != some "functionCall" then
        return false
      let callee ← mField j "expression"
      if (← mKind callee) == "MemberAccess" then
        let base ← mField callee "expression"
        if (← mKind base) == "ElementaryTypeNameExpression" &&
            optStr callee "memberName" == some "concat" &&
            (field? callee "referencedDeclaration").isNone then
          let tname := optStr (field? base "typeName" |>.getD Json.null) "name" |>.getD ""
          return tname == "string"
        let isAbiBuiltin ← if (← mKind base) == "Identifier" && optStr base "name" == some "abi" then
          pure ((← refInt base) == -1)
        else
          pure false
        if isAbiBuiltin then
          let mname := optStr callee "memberName"
          return mname == some "encode" || mname == some "encodePacked" || mname == some "encodeCall" ||
            mname == some "decode"
      let isHelperCall :=
        ((← mKind callee) == "Identifier" || (← mKind callee) == "MemberAccess") &&
        ((field? callee "referencedDeclaration").bind (fun v => v.getInt?.toOption)).any (· ≥ 0)
      if isHelperCall then
        let ty ← mType j
        if ty == "string memory" || ty == "string" || ty == "bytes memory" || ty == "bytes" then
          if let some (fnId, _) ← callTargetAndArity? j then
            if let some fn := (← get).funs.find? fnId then
              let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
              if rets.size == 1 then
                let r := rets[0]!
                let rloc := optStr r "storageLocation" |>.getD "default"
                if rloc == "memory" then
                  if let some body := (field? fn "body").filter (!·.isNull) then
                    let stmts ← mArr (← mField body "statements")
                    if stmts.size == 1 && (← mKind stmts[0]!) == "Return" then
                      let retExpr := field? stmts[0]! "expression" |>.getD Json.null
                      if !retExpr.isNull && (← isMsgDataNode retExpr) then
                        return false
                  return true
      return false
  | _ => return false

private def bindRoot (fn : Json) : M (Array SrcParam) := do
  noteFn fn
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  let mut out : Array SrcParam := #[]
  for p in params do
    let rawName ← mStr (← mField p "name")
    if rawName.startsWith "_verity_memret_" then
      failAt p s!"parameter name {rawName} uses reserved _verity_memret_ prefix"
    let id ← mNat (← mField p "id")
    let name ← if rawName == "" then fresh else do
      modify fun e => { e with bound := rawName :: e.bound }
      pure rawName
    let ty ← mType p
    let loc := optStr p "storageLocation" |>.getD "default"
    out := out.push { name, id }
    if ty == "bytes" then
      unless loc == "calldata" || loc == "memory" do
        failAt p s!"unsupported location {loc} for bytes"
      modify fun e =>
        { e with bound := s!"{name}_offset" :: s!"{name}_length" :: s!"{name}_data_offset" :: e.bound }
      let offsetBinding ← fresh
      let headerBinding ← fresh
      let lengthBinding ← fresh
      let dataBinding ← fresh
      let memoryPointer ← if loc == "memory" then fresh else pure ""
      let nextFreeBinding ← if loc == "memory" then fresh else pure ""
      let copyIndexBinding ← if loc == "memory" then fresh else pure ""
      modify fun e =>
        let bound : CalldataBytesParam :=
          { param := name
            offsetBinding
            headerBinding
            lengthBinding
            dataBinding
            isString := false
            inMemory := loc == "memory"
            memoryPointer
            nextFreeBinding
            copyIndexBinding }
        let byteBuffers :=
          if loc == "memory" then
            e.byteBuffers.insert id
              { pre := #[], pointer := .add (.localVar memoryPointer) (.literal 32), size := .localVar lengthBinding }
          else
            e.byteBuffers
        { e with calldataBytes := e.calldataBytes.insert id bound, byteBuffers }
    else if ty == "string" then
      unless loc == "calldata" || loc == "memory" do
        failAt p s!"unsupported location {loc} for string"
      modify fun e =>
        { e with bound := s!"{name}_offset" :: s!"{name}_length" :: s!"{name}_data_offset" :: e.bound }
      let offsetBinding ← fresh
      let headerBinding ← fresh
      let lengthBinding ← fresh
      let dataBinding ← fresh
      let memoryPointer ← if loc == "memory" then fresh else pure ""
      let nextFreeBinding ← if loc == "memory" then fresh else pure ""
      let copyIndexBinding ← if loc == "memory" then fresh else pure ""
      modify fun e =>
        let bound : CalldataBytesParam :=
          { param := name
            offsetBinding
            headerBinding
            lengthBinding
            dataBinding
            isString := true
            inMemory := loc == "memory"
            memoryPointer
            nextFreeBinding
            copyIndexBinding }
        let stringBuffers :=
          if loc == "memory" then
            e.stringBuffers.insert id
              { pre := #[], pointer := .add (.localVar memoryPointer) (.literal 32), size := .localVar lengthBinding }
          else
            e.stringBuffers
        { e with calldataBytes := e.calldataBytes.insert id bound, stringBuffers }
    else if let some (elemStr, elemPty, abiKind) := scalarArrayElement? ty then
      unless loc == "calldata" || loc == "memory" do
        failAt p s!"unsupported location {loc} for {ty}"
      let offsetBinding ← fresh
      let headerBinding ← fresh
      let lengthBinding ← fresh
      let dataBinding ← fresh
      let memoryPointer ← if loc == "memory" then fresh else pure ""
      let nextFreeBinding ← if loc == "memory" then fresh else pure ""
      let namePrefix ← if loc == "memory" then fresh else pure ""
      if loc == "memory" then
        for reserved in [s!"{namePrefix}_index"] do
          if (← get).sourceNames.contains reserved then
            failAt p s!"generated ABI helper name {reserved} collides with a source identifier"
          modify fun e => { e with bound := reserved :: e.bound }
      modify fun e =>
        let bound : ScalarArrayParam :=
          { param := name
            elementType := elemStr
            modelElementType := elemPty
            abiKind := abiKind
            inMemory := loc == "memory"
            offsetBinding
            headerBinding
            lengthBinding
            dataBinding
            memoryPointer
            nextFreeBinding
            namePrefix }
        { e with scalarArrays := e.scalarArrays.insert id bound,
                 yulMemoryArrays := if loc == "memory" && rawName != "" then e.yulMemoryArrays.insert rawName memoryPointer else e.yulMemoryArrays }
    else if ty.startsWith "struct " && !ty.contains "[" && (loc == "memory" || loc == "calldata") then
      let typeName ← mField p "typeName"
      let sid ← refInt typeName
      if sid < 0 then failAt p "builtin struct"
      let some decl := (← get).structs.find? sid.toNat | failAt p s!"unresolved struct {ty}"
      let members ← structMemberList decl
      let sname ← mStr (← mField decl "name")
      let staticTypes := members.toList.mapM (fun (_, ty) => if ty.startsWith "enum " || ty == "bytes4" then none else paramType ty)
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
    else if ty.startsWith "struct " && !ty.contains "[" then
      failAt p s!"unsupported location {loc} for {ty}"
    else
      let some pty := paramType ty | failAt p s!"unsupported parameter type {ty}"
      let enumBound? ← validateEnumTypeIfNeeded p ty
      modify fun e =>
        let values := e.values.insert id (.param name)
        let scalarTy := e.scalarTy.insert id pty
        let enumBounds := match enumBound? with
          | some b => e.enumBounds.insert id b
          | none => e.enumBounds
        let bytes4Params := if ty == "bytes4" then e.bytes4Params.push id else e.bytes4Params
        let yulNames := if rawName == "" then e.yulNames else e.yulNames.insert rawName (.param name)
        { e with values, scalarTy, enumBounds, bytes4Params, yulNames }
  let explicitAbi := (← get).mems.toList.any (fun (_, mem) => mem.schema.isSome) || !(← get).calldataBytes.isEmpty || !(← get).scalarArrays.isEmpty
  modify fun e => { e with explicitAbi }
  if explicitAbi then
    for p in params do
      let id ← mNat (← mField p "id")
      if let some mem := (← get).mems.find? id then
        if mem.staticTypes.isSome then
          failAt p "mixed static and dynamic struct parameters require explicit static-root lowering"
      else if !(← get).calldataBytes.contains id && !(← get).scalarArrays.contains id then
        let rawName ← mStr (← mField p "name")
        let binding ← fresh
        modify fun e => { e with
          rawBindings := e.rawBindings.insert id binding
          values := e.values.insert id (.localVar binding)
          yulNames := if rawName == "" then e.yulNames else e.yulNames.insert rawName (.localVar binding) }
  pure out

private partial def lowerRootStatements (stmts : Array Json) (isTail : Bool := false) : M (Array Stmt × Bool) := do
  let mut out : Array Stmt := #[]
  let mut returned := false
  for idx in [:stmts.size] do
    let s := stmts[idx]!
    let stmtIsTail := isTail && idx + 1 == stmts.size
    if returned then failAt s "statement after root return"
    match ← mKind s with
    | "Block" =>
        let saved ← get
        let (nested, nestedReturned) ← lowerRootStatements (← mArr (← mField s "statements")) stmtIsTail
        -- Restore lexical lookup maps, but retain fresh names and discovered dependencies.
        modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
        out := out ++ nested
        returned := nestedReturned
    | "UncheckedBlock" =>
        let saved ← get
        modify fun e => { e with unchecked := true }
        let (uncheckedNested, uncheckedReturned) ← lowerRootStatements (← mArr (← mField s "statements")) stmtIsTail
        modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs, scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays, unchecked := saved.unchecked }
        out := out ++ uncheckedNested
        returned := uncheckedReturned
    | "VariableDeclarationStatement" =>
        out := out ++ (← lowerLocal s)
    | "ExpressionStatement" =>
        out := out ++ (← lowerEffect s)
        if ← stmtAlwaysReverts [] s then
          returned := true
    | "EmitStatement" =>
        out := out ++ (← lowerEmit s)
    | "RevertStatement" =>
        returned := true
        out := out ++ (← lowerRevert s)
    | "InlineAssembly" =>
        let env ← get
        let savedAsmYul := env.yulNames
        let extPre ← bindYulExternalConstants s
        let mut asmRetName := ""
        let savedHelperResult := env.helperResult
        let savedHelperReturnId := env.helperReturnId
        if stmtIsTail && env.rootPost.isEmpty then
          if let some (rid, rname, rty, rbinding) := env.rootNamedReturn then
            if yulOnlyAssignsDecl s rid then
              asmRetName := rname
              modify fun e => { e with helperResult := some (rbinding, rty), helperReturnId := some rid }
        let asmStmts ← lowerAssemblyStmts s asmRetName
        modify fun e => { e with helperResult := savedHelperResult, helperReturnId := savedHelperReturnId, yulNames := savedAsmYul }
        out := out ++ extPre ++ asmStmts
    | "ForStatement" =>
        out := out ++ (← lowerFor s fun body => do
          let statements ← if (← mKind body) == "Block" then mArr (← mField body "statements") else pure #[body]
          let (lowered, _) ← lowerRootStatements statements false
          pure lowered)
    | "WhileStatement" =>
        out := out ++ (← lowerWhile s fun body => do
          let statements ← if (← mKind body) == "Block" then mArr (← mField body "statements") else pure #[body]
          let (lowered, _) ← lowerRootStatements statements false
          pure lowered)
    | "IfStatement" =>
        let (condition, yes, no) ← ifParts s
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, abiElements := saved.abiElements, calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays, byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers, storageBytesVars := saved.storageBytesVars, storageDynamicArrayVars := saved.storageDynamicArrayVars, flatStructs := saved.flatStructs,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays }
        -- A root return inside a branch stops execution, so the continuation
        -- stays after the conditional and runs only on fallthrough.
        let (yesOut, yesReturned) ← lowerRootStatements yes stmtIsTail
        restore
        let (noOut, noReturned) ← lowerRootStatements no stmtIsTail
        restore
        out := out ++ condition.pre |>.push (.ite condition.expr yesOut.toList noOut.toList)
        returned := yesReturned && noReturned
    | "Return" =>
        returned := true
        let expr := field? s "expression" |>.getD Json.null
        let env ← get
        if expr.isNull then
          if env.rootIsVoid then
            out := out ++ env.rootPost ++ #[.stop]
          else if !env.rootReturns.isEmpty then
            out := out ++ env.rootPost ++ #[.returnValues env.rootReturns.toList]
          else
            failAt s "bare return requires a void or named-return root function"
        else if let some (elemTy, _, length) := env.rootFixedArrayReturn then
          let isInlineArr ← if (← mKind expr) == "TupleExpression" then
            mBool (← mField expr "isInlineArray")
          else
            pure false
          if isInlineArr then
            let cs ← mArr (← mField expr "components")
            unless cs.size == length do
              failAt expr s!"inline return array length {cs.size} does not match return type length {length}"
            let mut pres : Array Stmt := #[]
            let mut exprs : Array Expr := #[]
            for c in cs do
              if c.isNull then failAt expr "empty return component"
              if cs.size > 1 && (statefulCallIn c (← get) || assignmentIn c) then
                failAt c "stateful or assignment expression in inline return array requires explicit evaluation-order support"
              let v ← atom (← convert elemTy (← mType c) (← lowerExpr c) c)
              pres := pres ++ v.pre
              if env.rootPost.isEmpty then
                exprs := exprs.push v.expr
              else
                let captured ← fresh
                pres := pres.push (.letVar captured v.expr)
                exprs := exprs.push (.localVar captured)
            out := (out ++ pres ++ env.rootPost).push (.returnValues exprs.toList)
          else if (← mKind expr) == "Identifier" then
            let id ← refInt expr
            if id ≥ 0 then
              if let some elements := env.snapshots.find? id.toNat then
                unless elements.size == length && ((← mType expr).splitOn " ").head! == s!"{elemTy}[{length}]" do
                  failAt expr "fixed-size array return snapshot type differs from return type"
                if env.rootPost.isEmpty then
                  out := out.push (.returnValues elements.toList)
                else
                  let mut pres : Array Stmt := #[]
                  let mut exprs : Array Expr := #[]
                  for elem in elements do
                    let captured ← fresh
                    pres := pres.push (.letVar captured elem)
                    exprs := exprs.push (.localVar captured)
                  out := (out ++ pres ++ env.rootPost).push (.returnValues exprs.toList)
              else
                failAt expr "fixed-size array return requires an inline array or fixed array snapshot"
            else
              failAt expr "fixed-size array return requires an inline array or fixed array snapshot"
          else
            failAt expr "fixed-size array return requires an inline array or fixed array snapshot"
        else if env.rootDynamicBytesReturn.isSome && (← canLowerDynamicBytesReturnExpr expr) then
          let buf ← lowerEncodedBytes expr
          let stem ← fresh
          let memStem := s!"_verity_memret_{stem}"
          let dataBinding := s!"{memStem}_data_offset"
          let lenBinding := s!"{memStem}_length"
          if (← get).sourceNames.contains dataBinding || (← get).sourceNames.contains lenBinding then
            failAt s s!"generated return buffer name {memStem} collides with a source identifier"
          modify fun e =>
            { e with encodingMemory := true,
                     bound := dataBinding :: lenBinding :: e.bound }
          let bindStmts := #[Stmt.letVar dataBinding buf.pointer, Stmt.letVar lenBinding buf.size]
          out := (out ++ buf.pre ++ bindStmts ++ env.rootPost).push (.returnBytes memStem)
        else if env.rootMsgDataReturn then
          let msgDataPre ← lowerMsgDataExpr expr
          out := (out ++ msgDataPre ++ env.rootPost).push
            (.returnValues [.literal 32, .calldatasize, .calldataload (.literal 0)])
        else if let some (retSid, _, memberBindings, isNamed) := env.rootFlatStructReturn then
          let isSameNamedReturn ← if isNamed && (← mKind expr) == "Identifier" then do
            let id ← refInt expr
            if id ≥ 0 then
              if let some flat := env.flatStructs.find? id.toNat then
                pure (flat.members == memberBindings)
              else pure false
            else pure false
          else pure false
          if isSameNamedReturn then
            if env.rootPost.isEmpty then
              out := out.push (.returnValues env.rootReturns.toList)
            else
              let mut pres : Array Stmt := #[]
              let mut exprs : Array Expr := #[]
              for retExpr in env.rootReturns do
                let captured ← fresh
                pres := pres.push (.letVar captured retExpr)
                exprs := exprs.push (.localVar captured)
              out := (out ++ pres ++ env.rootPost).push (.returnValues exprs.toList)
          else
            let (exprSid, _, valPre, memberVals) ← lowerFlatStructValue expr (some retSid) true
            unless exprSid == retSid && memberVals.size == memberBindings.size do
              failAt expr "root struct return member count mismatch"
            let mut pres := valPre
            let mut exprs : Array Expr := #[]
            for (_, _, valExpr) in memberVals do
              if env.rootPost.isEmpty then
                exprs := exprs.push valExpr
              else
                let captured ← fresh
                pres := pres.push (.letVar captured valExpr)
                exprs := exprs.push (.localVar captured)
            out := (out ++ pres ++ env.rootPost).push (.returnValues exprs.toList)
        else if (← mKind expr) == "TupleExpression" then
          if ← mBool (← mField expr "isInlineArray") then
            failAt expr "inline arrays are outside this slice"
          let cs ← mArr (← mField expr "components")
          let mut pres : Array Stmt := #[]
          let mut exprs : Array Expr := #[]
          for c in cs do
            if c.isNull then failAt expr "empty return component"
            let v ← atom (← lowerExpr c)
            pres := pres ++ v.pre
            if env.rootPost.isEmpty then
              exprs := exprs.push v.expr
            else
              let captured ← fresh
              pres := pres.push (.letVar captured v.expr)
              exprs := exprs.push (.localVar captured)
          out := (out ++ pres ++ env.rootPost).push (.returnValues exprs.toList)
        else if env.rootReturnTypes.size > 1 && env.rootFixedArrayReturn.isNone then
          let expectedTypes := env.rootReturnTypes.map some
          let (branchPre, retExprs) ← lowerMultiBranch expr (some expectedTypes)
          unless retExprs.size == env.rootReturnTypes.size do
            failAt expr s!"root multi-return arity {retExprs.size} does not match {env.rootReturnTypes.size}"
          let mut pres := branchPre
          let mut exprs : Array Expr := #[]
          for (valExpr, _) in retExprs do
            if env.rootPost.isEmpty then
              exprs := exprs.push valExpr
            else
              let captured ← fresh
              pres := pres.push (.letVar captured valExpr)
              exprs := exprs.push (.localVar captured)
          out := (out ++ pres ++ env.rootPost).push (.returnValues exprs.toList)
        else
          let v ← atom (← lowerExpr expr)
          if env.rootPost.isEmpty then
            out := out ++ v.pre |>.push (.returnValues [v.expr])
          else
            let captured ← fresh
            out := ((out ++ v.pre).push (.letVar captured v.expr) ++ env.rootPost).push (.returnValues [.localVar captured])
    | kind => failAt s s!"unsupported statement {kind}"
  pure (out, returned)

private def lowerPublicVarGetter (varDecl : Json) : M (Array Stmt × Array SrcParam) := do
  let rootId ← mNat (← mField varDecl "id")
  modify fun e => { e with stack := [rootId] }
  noteFn varDecl
  let name ← mStr (← mField varDecl "name")
  let isConstant := (field? varDecl "constant").bind (fun v => v.getBool?.toOption) == some true
  let mutability := optStr varDecl "mutability" |>.getD "mutable"
  if mutability == "immutable" then
    failAt varDecl s!"immutable state variable {name} is outside this slice"
  if isConstant || mutability == "constant" then
    let declared ← mType varDecl
    let initializer ← mField varDecl "value"
    if declared == "string" || declared == "bytes" then
      unless (← mKind initializer) == "Literal" do
        failAt initializer "byte constant must have a literal initializer"
      let buf ← lowerEncodedBytes initializer
      let stem ← fresh
      let memStem := s!"_verity_memret_{stem}"
      let dataBinding := s!"{memStem}_data_offset"
      let lenBinding := s!"{memStem}_length"
      if (← get).sourceNames.contains dataBinding || (← get).sourceNames.contains lenBinding then
        failAt varDecl s!"generated return buffer name {memStem} collides with a source identifier"
      modify fun e =>
        { e with encodingMemory := true,
                 bound := dataBinding :: lenBinding :: e.bound,
                 publicVarGetterReturns := #[if declared == "string" then .string else .bytes] }
      let getterBindStmts := #[Stmt.letVar dataBinding buf.pointer, Stmt.letVar lenBinding buf.size]
      return ((buf.pre ++ getterBindStmts).push (.returnBytes memStem), #[])
    let some pty := paramType declared
      | failAt varDecl s!"unsupported public constant type {declared}"
    discard (validateEnumTypeIfNeeded varDecl declared)
    unless (declared.startsWith "uint" && (bitsOf declared).isSome) ||
        declared == "bool" || declared == "bytes32" || declared == "bytes4" ||
        declared == "int256" || declared == "int" ||
        declared == "address" || declared == "address payable" ||
        declared.startsWith "contract " || declared.startsWith "enum " do
      failAt varDecl s!"unsupported public constant type {declared}"
    modify fun e => { e with constantStack := [rootId] }
    let rawValue ← lowerExpr initializer
    let initTy ← mType initializer
    let value ← convert declared initTy rawValue initializer
    let a ← atom value
    modify fun e => { e with constantStack := [], publicVarGetterReturns := #[pty] }
    return (a.pre.push (.returnValues [a.expr]), #[])
  let env ← get
  if env.duplicateLayoutLabels.contains name then
    failAt varDecl s!"shadowed storage declaration {name} is outside this slice"
  if let some item := env.layoutItems.find? name then
    unless (← mNat (← mField item "astId")) == rootId do
      failAt varDecl s!"shadowed storage declaration {name} is outside this slice"
  let info ← resolveField name varDecl
  let (paramSpecs, leafTypeNode) ← publicVarGetterParamTypes (← mField varDecl "typeName")
  let mut srcParams : Array SrcParam := #[]
  let mut paramExprs : Array Expr := #[]
  for idx in [:paramSpecs.size] do
    let (rawParamTy, paramNode) := paramSpecs[idx]!
    let resolvedParamTy ←
      if (← mKind paramNode) == "ArrayTypeName" then pure "uint256" else mType paramNode
    let some pty := paramType resolvedParamTy
      | failAt paramNode s!"unsupported public getter parameter type {rawParamTy}"
    let enumBound? ← validateEnumTypeIfNeeded paramNode resolvedParamTy
    let pid := 100000000 + idx
    let pname ← freshFor s!"arg{idx}"
    let pexpr := Expr.param pname
    modify fun e =>
      let values := e.values.insert pid pexpr
      let scalarTy := e.scalarTy.insert pid pty
      let enumBounds := match enumBound? with
        | some b => e.enumBounds.insert pid b
        | none => e.enumBounds
      let bytes4Params := if resolvedParamTy == "bytes4" then e.bytes4Params.push pid else e.bytes4Params
      { e with values, scalarTy, enumBounds, bytes4Params }
    srcParams := srcParams.push { name := pname, id := pid }
    paramExprs := paramExprs.push pexpr
  let readPublicStructGetterMembers (path : SPath) (pre0 : Array Stmt) :
      M (Array Stmt × Array Expr × Array ParamType) := do
    let sid ← refInt leafTypeNode
    unless sid ≥ 0 do
      failAt varDecl "unresolved struct in public state variable getter"
    let some sDecl := (← get).structs.find? sid.toNat
      | failAt varDecl "unresolved struct in public state variable getter"
    let sMembers ← mArr (← mField sDecl "members")
    unless !sMembers.isEmpty do
      failAt varDecl "empty struct in public state variable getter is unsupported"
    let mut pre := pre0
    let mut retExprs : Array Expr := #[]
    let mut retTypes : Array ParamType := #[]
    for mNode in sMembers do
      let mName ← mStr (← mField mNode "name")
      let mTy ← mType mNode
      let some mPty := paramType mTy
        | failAt mNode s!"unsupported public struct getter member {mName} of type {mTy}"
      discard (validateEnumTypeIfNeeded mNode mTy)
      let v ← memberRead #[] path mName varDecl
      let a ← atom v
      pre := pre ++ a.pre
      retExprs := retExprs.push a.expr
      retTypes := retTypes.push mPty
    return (pre, retExprs, retTypes)
  if paramSpecs.isEmpty then
    if info.bytesStorage then
      let buf ← lowerStorageBytesRead name varDecl
      let stem ← fresh
      let memStem := s!"_verity_memret_{stem}"
      let dataBinding := s!"{memStem}_data_offset"
      let lenBinding := s!"{memStem}_length"
      if (← get).sourceNames.contains dataBinding || (← get).sourceNames.contains lenBinding then
        failAt varDecl s!"generated return buffer name {memStem} collides with a source identifier"
      modify fun e =>
        { e with encodingMemory := true,
                 bound := dataBinding :: lenBinding :: e.bound,
                 publicVarGetterReturns := #[if info.stringStorage then .string else .bytes] }
      let getterBindStmts := #[Stmt.letVar dataBinding buf.pointer, Stmt.letVar lenBinding buf.size]
      return ((buf.pre ++ getterBindStmts).push (.returnBytes memStem), srcParams)
    if !info.structMembers.isEmpty && info.fixedArrayLength.isNone then
      unless info.opaqueNames.isEmpty && info.structFixedArrays.isEmpty && info.structMappings.isEmpty &&
          info.structDynamicArrays.isEmpty && info.subStructs.isEmpty do
        failAt varDecl s!"public struct getter for {name} with nested or non-scalar members is outside this slice"
      let (pre, retExprs, retTypes) ← readPublicStructGetterMembers (.zero name) #[]
      modify fun e => { e with publicVarGetterReturns := retTypes }
      return (pre.push (.returnValues retExprs.toList), srcParams)
    unless info.keyCount == 0 && info.structMembers.isEmpty && !info.bytesStorage &&
        info.dynamicArrayElemType.isNone && info.fixedArrayLength.isNone do
      failAt varDecl s!"unsupported public state variable getter layout for {name}"
    let ty ← mType leafTypeNode
    let some pty := paramType ty
      | failAt varDecl s!"unsupported public state variable type {ty}"
    discard (validateEnumTypeIfNeeded varDecl ty)
    markField name
    let readExpr :=
      if info.booleanScalar then Expr.logicalNot (.logicalNot (.storage name))
      else Expr.storage name
    modify fun e => { e with publicVarGetterReturns := #[pty] }
    return (#[.returnValues [readExpr]], srcParams)
  else if paramSpecs.size == 1 then
    let k0 := paramExprs.getD 0 (.literal 0)
    if let some elemSid := info.dynamicArrayStructId then
      let rawInfo ← resolveRawStructInfo elemSid varDecl
      unless rawInfo.mappings.isEmpty && rawInfo.dynamicArrays.isEmpty && rawInfo.subStructs.isEmpty do
        failAt varDecl s!"public struct array getter for {name} with nested or non-scalar members is outside this slice"
      let (elemPre, elemPath) ← storageDynamicStructElementPath #[] name (.literal info.slot) elemSid k0 varDecl .revertReturndata
      let (pre, retExprs, retTypes) ← readPublicStructGetterMembers elemPath elemPre
      modify fun e => { e with publicVarGetterReturns := retTypes }
      return (pre.push (.returnValues retExprs.toList), srcParams)
    if let some (elemTy, _, _) := info.dynamicArrayElemType then
      let resolvedElemTy ← mType leafTypeNode
      let some pty := paramType resolvedElemTy
        | failAt varDecl s!"unsupported public dynamic array element type {resolvedElemTy}"
      discard (validateEnumTypeIfNeeded leafTypeNode resolvedElemTy)
      let v ← readStorageDynamicArrayElement #[] name (.literal info.slot) elemTy k0 .revertReturndata
      let a ← atom v
      modify fun e => { e with publicVarGetterReturns := #[pty] }
      return (a.pre.push (.returnValues [a.expr]), srcParams)
    if info.keyCount == 0 && info.fixedArrayLength.isSome then
      let some length := info.fixedArrayLength | failAt varDecl "missing fixed array layout"
      let resolvedElemTy ← mType leafTypeNode
      let some pty := paramType resolvedElemTy
        | failAt varDecl s!"unsupported public fixed array element type {resolvedElemTy}"
      discard (validateEnumTypeIfNeeded leafTypeNode resolvedElemTy)
      let dest ← fresh
      let mut pre : Array Stmt := #[
        .ite (.lt k0 (.literal length)) [] [.revertReturndata],
        .letVar dest (.literal 0)
      ]
      for i in [:length] do
        let readExpr := Expr.storage (topStructMemberFieldName name s!"__solidity_element_{i}")
        pre := pre.push (.ite (.eq k0 (.literal i)) [.assignVar dest readExpr] [])
      markField name
      modify fun e => { e with publicVarGetterReturns := #[pty] }
      return (pre.push (.returnValues [.localVar dest]), srcParams)
    if info.keyCount == 1 && info.fixedArrayLength.isNone then
      if info.scalarMapping then
        let resolvedValTy ← mType leafTypeNode
        let some pty := paramType resolvedValTy
          | failAt varDecl s!"unsupported public mapping value type {resolvedValTy}"
        discard (validateEnumTypeIfNeeded leafTypeNode resolvedValTy)
        let v ← scalarMappingRead #[] (.one name k0) varDecl
        let a ← atom v
        modify fun e => { e with publicVarGetterReturns := #[pty] }
        return (a.pre.push (.returnValues [a.expr]), srcParams)
      else
        unless info.opaqueNames.isEmpty && info.structFixedArrays.isEmpty && info.structMappings.isEmpty &&
            info.structDynamicArrays.isEmpty && info.subStructs.isEmpty do
          failAt varDecl s!"public mapping struct getter for {name} with nested or non-scalar members is outside this slice"
        let (pre, retExprs, retTypes) ← readPublicStructGetterMembers (.one name k0) #[]
        modify fun e => { e with publicVarGetterReturns := retTypes }
        return (pre.push (.returnValues retExprs.toList), srcParams)
    failAt varDecl s!"unsupported public state variable getter layout for {name}"
  else if paramSpecs.size == 2 then
    let k0 := paramExprs.getD 0 (.literal 0)
    let k1 := paramExprs.getD 1 (.literal 0)
    if info.keyCount == 2 && info.fixedArrayLength.isNone && info.thirdKeyMapping.isNone then
      if info.scalarMapping then
        let resolvedValTy ← mType leafTypeNode
        let some pty := paramType resolvedValTy
          | failAt varDecl s!"unsupported public mapping value type {resolvedValTy}"
        discard (validateEnumTypeIfNeeded leafTypeNode resolvedValTy)
        let v ← scalarMappingRead #[] (.two name k0 k1) varDecl
        let a ← atom v
        modify fun e => { e with publicVarGetterReturns := #[pty] }
        return (a.pre.push (.returnValues [a.expr]), srcParams)
      else
        unless info.opaqueNames.isEmpty && info.structFixedArrays.isEmpty && info.structMappings.isEmpty &&
            info.structDynamicArrays.isEmpty && info.subStructs.isEmpty do
          failAt varDecl s!"public mapping struct getter for {name} with nested or non-scalar members is outside this slice"
        let (pre, retExprs, retTypes) ← readPublicStructGetterMembers (.two name k0 k1) #[]
        modify fun e => { e with publicVarGetterReturns := retTypes }
        return (pre.push (.returnValues retExprs.toList), srcParams)
    if info.keyCount == 1 && info.fixedArrayLength.isSome then
      let some length := info.fixedArrayLength | failAt varDecl "missing fixed array layout"
      let resolvedElemTy ← mType leafTypeNode
      let some pty := paramType resolvedElemTy
        | failAt varDecl s!"unsupported public mapping array element type {resolvedElemTy}"
      discard (validateEnumTypeIfNeeded leafTypeNode resolvedElemTy)
      let dest ← fresh
      let mut pre : Array Stmt := #[
        .ite (.lt k1 (.literal length)) [] [.revertReturndata],
        .letVar dest (.literal 0)
      ]
      for i in [:length] do
        let readExpr := Expr.structMember name k0 s!"__solidity_element_{i}"
        pre := pre.push (.ite (.eq k1 (.literal i)) [.assignVar dest readExpr] [])
      markField name
      modify fun e => { e with publicVarGetterReturns := #[pty] }
      return (pre.push (.returnValues [.localVar dest]), srcParams)
    failAt varDecl s!"unsupported public state variable getter layout for {name}"
  else if paramSpecs.size == 3 then
    let k0 := paramExprs.getD 0 (.literal 0)
    let k1 := paramExprs.getD 1 (.literal 0)
    let k2 := paramExprs.getD 2 (.literal 0)
    if info.keyCount == 2 && info.thirdKeyMapping.isSome then
      let some mapInfo := info.thirdKeyMapping | failAt varDecl "missing 3-key mapping info"
      if let some valSid := mapInfo.valueStructId then
        let rawInfo ← resolveRawStructInfo valSid varDecl
        unless rawInfo.mappings.isEmpty && rawInfo.dynamicArrays.isEmpty && rawInfo.subStructs.isEmpty do
          failAt varDecl s!"public 3-key mapping struct getter for {name} with nested or non-scalar members is outside this slice"
        markField name
        markStructMapping name mapInfo.member
        let (slotStmts, slotExpr) ← computeStructMappingLeafSlot (.two name k0 k1) info mapInfo k2 varDecl
        let (pre, retExprs, retTypes) ← readPublicStructGetterMembers (.rawSlot valSid slotExpr) slotStmts
        modify fun e => { e with publicVarGetterReturns := retTypes }
        return (pre.push (.returnValues retExprs.toList), srcParams)
      else
        let resolvedValTy ← mType leafTypeNode
        let some pty := paramType resolvedValTy
          | failAt varDecl s!"unsupported public 3-key mapping value type {resolvedValTy}"
        discard (validateEnumTypeIfNeeded leafTypeNode resolvedValTy)
        let v ← readStructMappingElement #[] (.two name k0 k1) mapInfo k2 varDecl
        let a ← atom v
        modify fun e => { e with publicVarGetterReturns := #[pty] }
        return (a.pre.push (.returnValues [a.expr]), srcParams)
    if info.keyCount == 2 && info.fixedArrayLength.isSome then
      let some length := info.fixedArrayLength | failAt varDecl "missing fixed array layout"
      let resolvedElemTy ← mType leafTypeNode
      let some pty := paramType resolvedElemTy
        | failAt varDecl s!"unsupported public mapping array element type {resolvedElemTy}"
      discard (validateEnumTypeIfNeeded leafTypeNode resolvedElemTy)
      let dest ← fresh
      let mut pre : Array Stmt := #[
        .ite (.lt k2 (.literal length)) [] [.revertReturndata],
        .letVar dest (.literal 0)
      ]
      for i in [:length] do
        let readExpr := Expr.structMember2 name k0 k1 s!"__solidity_element_{i}"
        pre := pre.push (.ite (.eq k2 (.literal i)) [.assignVar dest readExpr] [])
      markField name
      modify fun e => { e with publicVarGetterReturns := #[pty] }
      return (pre.push (.returnValues [.localVar dest]), srcParams)
    failAt varDecl s!"unsupported public state variable getter layout for {name}"
  else
    failAt varDecl s!"unsupported public state variable getter arity {paramSpecs.size} for {name}"

private def lowerRoot (fn : Json) : M (Array Stmt × Array SrcParam) := do
  if (← mKind fn) == "VariableDeclaration" then
    return ← lowerPublicVarGetter fn
  let rootId ← mNat (← mField fn "id")
  modify fun e => { e with stack := [rootId] }
  if optStr fn "stateMutability" == some "payable" then
    failAt fn "payable entry points require value-transfer semantics and are unsupported"
  let srcParams ← bindRoot fn
  let implemented := (field? fn "implemented").bind (fun v => v.getBool?.toOption) |>.getD true
  let some body := (field? fn "body").filter (!·.isNull)
    | failAt fn "function has no body"
  unless implemented do failAt fn "function has no body"
  let mods ← mArr (← mField fn "modifiers")
  let returns ← mArr (← mField (← mField fn "returnParameters") "parameters")
  let mut rootInit : Array Stmt := #[]
  for p in srcParams do
    if (bodyCompoundAssignedIds body).contains p.id || (bodyDirectAssignedIds body).contains p.id then
      if let some initExpr := (← get).values.find? p.id then
        let pbinding ← freshFor (if p.name == "" then "param" else p.name)
        let pexpr := Expr.localVar pbinding
        rootInit := rootInit.push (.letVar pbinding initExpr)
        modify fun e =>
          { e with values := e.values.insert p.id pexpr,
                   writableLocals := e.writableLocals.insert p.id pbinding,
                   yulNames := if p.name == "" then e.yulNames else e.yulNames.insert p.name pexpr }
  let stmts ← mArr (← mField body "statements")
  let emptyBodyArrayRet? ← functionEmptyBodyArrayReturnType? fn
  let fixedArrayRet? ← functionFixedArrayReturnType? fn
  let flatStructRet? ← functionFlatStructReturnType? fn
  let msgDataRet ← functionMsgDataReturn? fn
  let dynamicBytesRet? ← functionDynamicBytesReturn? fn
  let rootReturnTypes ← returns.mapM mType
  let mut rootRetExprs : Array Expr := #[]
  let mut rootNamedReturn? : Option (Nat × String × String × String) := none
  let mut rootFlatStructState? : Option (Nat × String × Array (String × String × String) × Bool) := none
  let mut allNamedScalar := !returns.isEmpty && emptyBodyArrayRet?.isNone && fixedArrayRet?.isNone && flatStructRet?.isNone && !msgDataRet && dynamicBytesRet?.isNone
  if let some (retSid, retStructName, rname, rid, memberSpecs) := flatStructRet? then
    let mut memberBindings : Array (String × String × String) := #[]
    for (mName, mTy, _) in memberSpecs do
      let binding ← freshFor s!"{if rname == "" then "ret_struct" else rname}_{mName}"
      if rname != "" then
        rootInit := rootInit.push (.letVar binding (.literal 0))
        rootRetExprs := rootRetExprs.push (.localVar binding)
      memberBindings := memberBindings.push (mName, mTy, binding)
    if rname != "" then
      modify fun e =>
        { e with flatStructs := e.flatStructs.insert rid { structId := retSid, structName := retStructName, members := memberBindings },
                 yulNames := e.yulNames.erase rname }
    rootFlatStructState? := some (retSid, retStructName, memberBindings, rname != "")
  else if emptyBodyArrayRet?.isNone && fixedArrayRet?.isNone && !msgDataRet && dynamicBytesRet?.isNone then
    for r in returns do
      let rty ← mType r
      discard (validateEnumTypeIfNeeded r rty)
      let rname ← mStr (← mField r "name")
      if rname == "" then
        allNamedScalar := false
      else
        let rid ← mNat (← mField r "id")
        let some scalar := paramType rty
          | failAt r s!"unsupported named root return type {rty}"
        let rbinding ← freshFor rname
        let rexpr := Expr.localVar rbinding
        rootInit := rootInit ++ #[.letVar rbinding (.literal 0)]
        rootRetExprs := rootRetExprs.push rexpr
        if returns.size == 1 && !rty.startsWith "enum " then
          rootNamedReturn? := some (rid, rname, rty, rbinding)
        modify fun e =>
          { e with values := e.values.insert rid rexpr,
                   writableLocals := e.writableLocals.insert rid rbinding,
                   scalarTy := e.scalarTy.insert rid scalar,
                   yulNames := e.yulNames.insert rname rexpr }
  modify fun e =>
    { e with bodyAssigned := bodyAssignedIds body,
             rootIsVoid := returns.isEmpty,
             rootReturns := if allNamedScalar || (flatStructRet?.isSome && !rootRetExprs.isEmpty) then rootRetExprs else #[],
             rootReturnTypes := rootReturnTypes,
             rootNamedReturn := if allNamedScalar then rootNamedReturn? else none,
             rootFixedArrayReturn := fixedArrayRet?,
             rootFlatStructReturn := rootFlatStructState?,
             rootMsgDataReturn := msgDataRet,
             rootDynamicBytesReturn := dynamicBytesRet? }
  let (modStmts, modPost) ← lowerModifiers mods
  modify fun e => { e with rootPost := modPost }
  let (bodyOut, returned) ← lowerRootStatements stmts true
  let mut out := rootInit ++ modStmts ++ bodyOut
  unless returned do
    out := out ++ modPost
    if returns.isEmpty then
      out := out.push .stop
    else if emptyBodyArrayRet?.isSome then
      out := out ++ #[.returnValues [.literal 32, .literal 0]]
    else if !(← get).rootReturns.isEmpty then
      out := out ++ #[.returnValues (← get).rootReturns.toList]
    else if let some (_, _, length) := fixedArrayRet? then
      if stmts.isEmpty then
        out := out ++ #[.returnValues (Array.replicate length (.literal 0)).toList]
      else
        failAt fn "an explicit root return is required"
    else if let some (_, _, _, _, memberSpecs) := flatStructRet? then
      if stmts.isEmpty then
        out := out ++ #[.returnValues (Array.replicate memberSpecs.size (.literal 0)).toList]
      else
        failAt fn "an explicit root return is required"
    else if msgDataRet || dynamicBytesRet?.isSome then
      failAt fn "an explicit root return is required"
    else if stmts.isEmpty then
      let mut zeroReturns : List Expr := []
      for r in returns do
        let rty ← mType r
        unless (paramType rty).isSome do
          failAt r s!"unsupported empty-body root return type {rty}"
        zeroReturns := zeroReturns ++ [.literal 0]
      out := out ++ #[.returnValues zeroReturns]
    else
      failAt fn "an explicit root return is required"
  pure (out, srcParams)

private partial def index (file : String) (contract? : Option (Nat × String)) (j : Json) : M Unit := do
  match j with
  | .obj o =>
      if let some name := optStr j "name" then
        modify fun e => { e with sourceNames := name :: e.sourceNames }
      let mut next := contract?
      if (field? j "nodeType").isSome then
        if let some idj := field? j "id" then
          let id ← mNat idj
          modify fun e => { e with nodeFile := e.nodeFile.insert id file }
          match ← mKind j with
          | "ContractDefinition" =>
              let n ← mStr (← mField j "name")
              let kind := optStr j "contractKind" |>.getD "contract"
              let bases ← match field? j "linearizedBaseContracts" with
                | some b => (← mArr b).mapM mNat
                | none => pure #[id]
              let cnodes ← match field? j "nodes" with
                | some ns => mArr ns
                | none => pure #[]
              modify fun e =>
                { e with contractNames := e.contractNames.insert id n,
                         contractKinds := e.contractKinds.insert id kind,
                         contractBases := e.contractBases.insert id bases,
                         contractNodes := e.contractNodes.insert id cnodes }
              next := some (id, n)
          | "FunctionDefinition" =>
              let baseIds ← match field? j "baseFunctions" with
                | some b => (← mArr b).mapM mNat
                | none => pure #[]
              modify fun e =>
                let funs := e.funs.insert id j
                let funContract := e.funContract.insert id (contract?.map Prod.snd |>.getD "<free>")
                let funContractId := match contract? with
                  | some (cid, _) => e.funContractId.insert id cid
                  | none => e.funContractId
                let contractFuns := match contract? with
                  | some (cid, _) =>
                      let prev := e.contractFuns.find? cid |>.getD #[]
                      e.contractFuns.insert cid (prev.push id)
                  | none => e.contractFuns
                let funBases := e.funBases.insert id baseIds
                { e with funs, funContract, funContractId, contractFuns, funBases }
          | "ModifierDefinition" =>
              modify fun e =>
                let modifiers := e.modifiers.insert id j
                let funContract := e.funContract.insert id (contract?.map Prod.snd |>.getD "<free>")
                let funContractId := match contract? with
                  | some (cid, _) => e.funContractId.insert id cid
                  | none => e.funContractId
                { e with modifiers, funContract, funContractId }
          | "StructDefinition" =>
              modify fun e => { e with structs := e.structs.insert id j }
          | "EnumDefinition" =>
              let ename ← mStr (← mField j "name")
              let ms ← mArr (← mField j "members")
              let mut memberNames : Array String := #[]
              for m in ms do
                memberNames := memberNames.push (← mStr (← mField m "name"))
              let enumKey := match contract? with
                | some (_, cname) => s!"enum {cname}.{ename}"
                | none => s!"enum {ename}"
              modify fun e =>
                { e with enums := e.enums.insert id memberNames,
                         enumByType := e.enumByType.insert enumKey (id, memberNames) }
          | "UserDefinedValueTypeDefinition" =>
              let vname ← mStr (← mField j "name")
              let uTypeNode ← mField j "underlyingType"
              let uTy ← liftM (typeString uTypeNode)
              let qualName := match contract? with
                | some (_, cname) => s!"{cname}.{vname}"
                | none => vname
              modify fun e =>
                let userValueTypeById := e.userValueTypeById.insert id uTy
                let userValueTypes := e.userValueTypes.insert qualName uTy |>.insert vname uTy
                { e with userValueTypeById, userValueTypes }
          | "EventDefinition" =>
              modify fun e => { e with eventDecls := e.eventDecls.insert id j }
          | "ErrorDefinition" =>
              modify fun e => { e with errorDecls := e.errorDecls.insert id j }
          | "VariableDeclaration" =>
              let isState := match field? j "stateVariable" with
                | some b => match b.getBool? with | .ok v => v | _ => false
                | none => false
              let baseIds ← match field? j "baseFunctions" with
                | some b => (← mArr b).mapM mNat
                | none => pure #[]
              if isState then
                let isPublic := optStr j "visibility" == some "public"
                modify fun e =>
                  let stateVars := e.stateVars.insert id j
                  let funContract := e.funContract.insert id (contract?.map Prod.snd |>.getD "<free>")
                  let funContractId := match contract? with
                    | some (cid, _) => e.funContractId.insert id cid
                    | none => e.funContractId
                  let contractPublicVars := match contract? with
                    | some (cid, _) =>
                        if isPublic then
                          let prev := e.contractPublicVars.find? cid |>.getD #[]
                          e.contractPublicVars.insert cid (prev.push id)
                        else e.contractPublicVars
                    | none => e.contractPublicVars
                  let funBases := if baseIds.isEmpty then e.funBases else e.funBases.insert id baseIds
                  { e with stateVars, funContract, funContractId, contractPublicVars, funBases }
              let isConstant := (field? j "constant").bind (fun v => v.getBool?.toOption)
              if isConstant == some true then
                modify fun e => { e with numericConstants := e.numericConstants.insert id j }
          | _ => pure ()
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
    if t.startsWith "import" || t.startsWith "} from " then
      let parts := t.splitOn "\""
      if parts.length ≥ 2 then
        out := out.push parts[1]!
      else
        let singleParts := t.splitOn "'"
        if singleParts.length ≥ 2 then
          out := out.push singleParts[1]!
  pure out

private def extractQuotedStrings (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut inQuote : Option Char := none
  let mut current : String := ""
  for c in s.toList do
    match inQuote with
    | none =>
        if c == '"' || c == '\'' then
          inQuote := some c
          current := ""
    | some q =>
        if c == q then
          out := out.push current
          inQuote := none
        else
          current := current.push c
  return out

private def parseFoundryTomlRemappings (text : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut collecting := false
  let mut buf := ""
  for line in text.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "#" then continue
    let codeLine := (trimmed.splitOn "#").headD ""
    if !collecting then
      if codeLine.startsWith "remappings" then
        let rest := (codeLine.drop 10).trimAscii.toString
        if rest.startsWith "=" then
          let rhs := (rest.drop 1).trimAscii.toString
          if rhs.startsWith "[" then
            let afterBracket := (rhs.drop 1).toString
            if afterBracket.contains ']' then
              let inside := (afterBracket.splitOn "]").headD ""
              for item in extractQuotedStrings inside do
                let parts := item.splitOn "="
                if parts.length == 2 && parts[0]! != "" && parts[1]! != "" then
                  out := out.push (parts[0]!, parts[1]!)
            else
              collecting := true
              buf := afterBracket
    else
      if codeLine.contains ']' then
        let inside := buf ++ "\n" ++ ((codeLine.splitOn "]").headD "")
        for item in extractQuotedStrings inside do
          let parts := item.splitOn "="
          if parts.length == 2 && parts[0]! != "" && parts[1]! != "" then
            out := out.push (parts[0]!, parts[1]!)
        collecting := false
        buf := ""
      else
        buf := buf ++ "\n" ++ codeLine
  return out

private def readRemappings (root : System.FilePath) : IO (Array (String × String)) := do
  let mut out : Array (String × String) := #[]
  let path := root / "remappings.txt"
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    for line in text.splitOn "\n" do
      let t := line.trimAscii.toString
      if t == "" || t.startsWith "#" || t.startsWith "//" then continue
      let parts := t.splitOn "="
      if parts.length == 2 then
        out := out.push (parts[0]!, parts[1]!)
  let foundryPath := root / "foundry.toml"
  if ← foundryPath.pathExists then
    let foundryText ← IO.FS.readFile foundryPath
    for pair in parseFoundryTomlRemappings foundryText do
      unless out.contains pair do
        out := out.push pair
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

private def verifyCompiler (release : SolcRelease) (compiler : System.FilePath) : MetaM String := do
  let output ←
    if System.Platform.isOSX then
      IO.Process.output { cmd := "/usr/bin/shasum", args := #["-a", "256", compiler.toString] }
    else
      IO.Process.output { cmd := "/usr/bin/sha256sum", args := #[compiler.toString] }
  unless output.exitCode == 0 && release.sha256s.contains (output.stdout.take 64).toString do
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

private structure CandidateFn where
  id : Nat
  fn : Json
  tys : Array String
  canonicalTys : Array String
  implemented : Bool
  deriving Inhabited

/-- Select the function from `contract`'s C3 inheritance hierarchy; also return
its solc parameter type strings. -/
private def selectFunction (contract functionName : String) (written : Array String) :
    M (Json × Array String) := do
  let env ← get
  let mut effective : Array CandidateFn := #[]
  for cid in env.linearizedBases do
    for id in env.contractFuns.find? cid |>.getD #[] do
      let some fn := env.funs.find? id | continue
      if optStr fn "kind" == some "constructor" then continue
      let name ← mStr (← mField fn "name")
      unless name == functionName do continue
      let params ← mArr (← mField (← mField fn "parameters") "parameters")
      let mut tys : Array String := #[]
      for p in params do
        tys := tys.push (← liftM (typeString p))
      let canonicalTys := tys.map sourceTypeName
      let implementedFlag ← match field? fn "implemented" with
        | some b => mBool b
        | none => pure true
      let hasBody := match field? fn "body" with
        | some b => !b.isNull
        | none => false
      let implemented := implementedFlag && hasBody
      let matchIdx? := effective.findIdx? fun prev =>
        sameVirtualFamily env prev.id id || prev.canonicalTys == canonicalTys
      match matchIdx? with
      | none =>
          effective := effective.push { id, fn, tys, canonicalTys, implemented }
      | some idx =>
          if !effective[idx]!.implemented && implemented then
            effective := effective.set! idx { id, fn, tys, canonicalTys, implemented }
    for id in env.contractPublicVars.find? cid |>.getD #[] do
      let some varDecl := env.stateVars.find? id | continue
      let name ← mStr (← mField varDecl "name")
      unless name == functionName do continue
      let (paramSpecs, _) ← publicVarGetterParamTypes (← mField varDecl "typeName")
      let tys := paramSpecs.map Prod.fst
      let canonicalTys := tys.map sourceTypeName
      let implemented := true
      let matchIdx? := effective.findIdx? fun prev =>
        sameVirtualFamily env prev.id id || prev.canonicalTys == canonicalTys
      match matchIdx? with
      | none =>
          effective := effective.push { id, fn := varDecl, tys, canonicalTys, implemented }
      | some idx =>
          if !effective[idx]!.implemented && implemented then
            effective := effective.set! idx { id, fn := varDecl, tys, canonicalTys, implemented }
  let mut hits : Array (Json × Array String × Bool) := #[]
  let mut described : Array String := #[]
  for cand in effective do
    described := described.push
      s!"{functionName}({String.intercalate ", " cand.canonicalTys.toList})"
    if cand.tys.size == written.size && (cand.tys.zip written).all (fun (t, w) =>
        typeMatches w t || (match env.userValueTypes.find? t with | some u => typeMatches w u | none => false)) then
      hits := hits.push (cand.fn, cand.tys, cand.implemented)
  let sig := s!"{contract}.{functionName}({String.intercalate ", " written.toList})"
  if hits.size == 0 then
    throwError "no function {sig}; candidates: {described}"
  if hits.size > 1 then
    throwError "ambiguous function {sig}; qualify the parameter types"
  let (fn, tys, implemented) := hits[0]!
  unless implemented do throwError "function is not implemented"
  pure (fn, tys)

private def importSlice
    (pkgRoot projectRoot : System.FilePath) (entry contract : String)
    (roots : Array (String × Array String)) (profile : Profile) :
    MetaM (CompilationModel × ImportReport) := do
  let release ← resolveSolcRelease profile
  let compiler := pkgRoot / ".lake/solidity-import" / release.binaryName
  let solcSha ← verifyCompiler release compiler
  let versionOut ← IO.Process.output { cmd := compiler.toString, args := #["--version"] }
  unless versionOut.exitCode == 0 &&
      release.banners.contains versionOut.stdout.trimAscii.toString do
    throwError "compiler version mismatch"
  unless (← verifyCompiler release compiler) == solcSha do throwError "compiler changed during import"
  let remaps ← readRemappings projectRoot
  let sources ← collectSources projectRoot entry remaps RBMap.empty
  let mut fileBytes : RBMap String ByteArray compare := RBMap.empty
  let mut sourceObj : Array (String × Json) := #[]
  for (logical, text) in sources do
    fileBytes := fileBytes.insert logical (text.toUTF8)
    sourceObj := sourceObj.push (logical, Json.mkObj [("content", Json.str text)])
  let baseSettings : List (String × Json) := [
    ("evmVersion", Json.str profile.evmVersion),
    ("metadata", Json.mkObj [("bytecodeHash", Json.str profile.bytecodeHash)]),
    ("optimizer", Json.mkObj [("enabled", Json.bool profile.optimizerRuns.isSome),
      ("runs", profile.optimizerRuns.getD 200)]),
    ("outputSelection", Json.mkObj [("*", Json.mkObj [
      ("", Json.arr #[Json.str "ast"]),
      ("*", Json.arr #[Json.str "storageLayout"])])]),
    ("remappings", Json.arr (remaps.map fun p => Json.str s!"{p.1}={p.2}"))]
  let settings := Json.mkObj (if release.supportsViaIR then
    baseSettings ++ [("viaIR", Json.bool profile.viaIR)]
  else baseSettings)
  let input := Json.mkObj [
    ("language", Json.str "Solidity"),
    ("settings", settings),
    ("sources", Json.mkObj sourceObj.toList)]
  let solcArgs := if release.hasNoImportCallbackFlag then
    #["--standard-json", "--no-import-callback"]
  else
    #["--standard-json"]
  let output ← IO.Process.output
    { cmd := compiler.toString, args := solcArgs }
    (some input.compress)
  unless output.exitCode == 0 do throwError "solc failed: {output.stderr}"
  unless (← verifyCompiler release compiler) == solcSha do throwError "compiler changed during import"
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
  let .obj sourceUnits := sourcesOut | throwError "solc sources output is not an object"
  for (logical, _) in sourceUnits do
    unless sources.contains logical do
      throwError "solc loaded uncollected source {logical}"
  for (logical, _) in sources do
    let unit ← field sourcesOut logical
    let ast ← field unit "ast"
    ((), env) ← (index logical none ast).run env
  let targetContractIds := env.contractNames.toList.filterMap fun (cid, cname) =>
    if env.nodeFile.find? cid == some entry && cname == contract then some cid else none
  let [targetContractId] := targetContractIds
    | throwError "missing or ambiguous ContractDefinition {contract} in {entry}"
  let some targetBases := env.contractBases.find? targetContractId
    | throwError "missing linearizedBaseContracts for {contract}"
  env := { env with linearizedBases := targetBases }
  let contracts ← field parsed "contracts"
  let entryContracts ← field contracts entry
  let chosen ← field entryContracts contract
  let layout ← field chosen "storageLayout"
  let types ← field layout "types"
  let items ← arr (← field layout "storage")
  env := { env with layoutTypes := types }
  for item in items do
    let label ← str (← field item "label")
    if env.layoutItems.contains label && !env.duplicateLayoutLabels.contains label then
      env := { env with duplicateLayoutLabels := env.duplicateLayoutLabels.push label }
    env := { env with layoutItems := env.layoutItems.insert label item }
  let mut specs : Array FunctionSpec := #[]
  let mut projections : Array ParamProjection := #[]
  let mut signatures : Array Json := #[]
  let mut rootIds : Array Nat := #[]
  for (functionName, written) in roots do
    let (fn, paramTys) ← (selectFunction contract functionName written).run' env
    let rootId ← flexNat (← field fn "id")
    if rootIds.contains rootId then throwError "function {contract}.{functionName} is imported twice"
    if specs.any (·.name == functionName) then
      let rootFile := env.nodeFile.find? rootId |>.getD entry
      (failAt fn s!"root function name collision: {contract}.{functionName}; import overloaded roots in separate slices").run' { env with currentFile := rootFile }
    rootIds := rootIds.push rootId
    signatures := signatures.push (Json.mkObj
      [("function", Json.str functionName), ("parameterTypes", Json.arr (paramTys.map Json.str))])
    -- Each root is lowered on its own: bindings, generated names and projections
    -- do not leak between functions. Field layouts and the closure are shared.
    let rootFile := env.nodeFile.find? rootId |>.getD entry
    env := { env with currentFile := rootFile, next := 0, bound := [], values := RBMap.empty, paths := RBMap.empty,
                      snapshots := RBMap.empty, mems := RBMap.empty, flatStructs := RBMap.empty, abiElements := RBMap.empty, calldataBytes := RBMap.empty, scalarArrays := RBMap.empty, byteBuffers := RBMap.empty, stringBuffers := RBMap.empty, storageBytesVars := RBMap.empty, storageDynamicArrayVars := RBMap.empty, scalarTy := RBMap.empty, enumBounds := RBMap.empty, bytes4Params := #[], writableLocals := RBMap.empty, fnPtrs := RBMap.empty, bodyAssigned := [], zeroInitLocals := #[], yulNames := RBMap.empty, yulMemoryArrays := RBMap.empty,
                      projections := #[], rawBindings := RBMap.empty, explicitAbi := false, encodingMemory := false, helperResult := none, helperReturnId := none, multiHelperResults := none, flatStructHelperResult := none, helperPost := #[], rootIsVoid := false, rootReturns := #[], rootReturnTypes := #[], rootNamedReturn := none, rootFixedArrayReturn := none, rootFlatStructReturn := none, rootMsgDataReturn := false, rootDynamicBytesReturn := none, rootPost := #[], publicVarGetterReturns := #[] }
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
      else if let some cb := env.calldataBytes.find? p.id then
        if modelParamNames.contains p.name then
          (failAt fn s!"parameter name collision: {p.name}").run' env
        modelParamNames := modelParamNames.push p.name
        modelParams := modelParams.push { name := p.name, ty := if cb.isString then .string else .bytes }
      else if let some arr := env.scalarArrays.find? p.id then
        if modelParamNames.contains p.name then
          (failAt fn s!"parameter name collision: {p.name}").run' env
        modelParamNames := modelParamNames.push p.name
        modelParams := modelParams.push { name := p.name, ty := .array arr.modelElementType }
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
      if let some cb := env.calldataBytes.find? p.id then
        let some i := modelParamNames.findIdx? (· == p.name)
          | throwError "missing calldata bytes model parameter {p.name}"
        let headOffset := 4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0
        let checks :=
          if cb.inMemory then
            AbiLowering.bytesMemoryHead cb.memoryPointer cb.offsetBinding cb.headerBinding cb.lengthBinding cb.dataBinding cb.nextFreeBinding cb.copyIndexBinding rootHeadWords headOffset
          else
            AbiLowering.bytesCalldataHead cb.offsetBinding cb.headerBinding cb.lengthBinding cb.dataBinding rootHeadWords headOffset
        abiGuards := abiGuards ++ checks.toArray
      if let some arr := env.scalarArrays.find? p.id then
        let some i := modelParamNames.findIdx? (· == p.name)
          | throwError "missing scalar array model parameter {p.name}"
        let headOffset := 4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0
        let checks :=
          if arr.inMemory then
            AbiLowering.scalarArrayMemoryHead arr.memoryPointer arr.offsetBinding arr.headerBinding arr.lengthBinding arr.dataBinding arr.nextFreeBinding arr.namePrefix rootHeadWords headOffset arr.abiKind
          else
            AbiLowering.scalarArrayCalldataHead arr.offsetBinding arr.headerBinding arr.lengthBinding arr.dataBinding rootHeadWords headOffset
        abiGuards := abiGuards ++ checks.toArray
      if let some ty := env.scalarTy.find? p.id then
        -- Static tuples occupy their complete inline head; dynamic tuples
        -- occupy one offset word. Compute scalar offsets from the full ABI.
        let some i := modelParamNames.findIdx? (· == p.name)
          | throwError "missing scalar model parameter {p.name}"
        let limit := match env.enumBounds.find? p.id with
          | some enumMax => some enumMax
          | none => match ty with
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
        if env.bytes4Params.contains p.id then
          let offset := 4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0
          abiGuards := abiGuards.push (.ite
            (.eq (.bitAnd (.calldataload (.literal offset)) (.literal (2 ^ 224 - 1))) (.literal 0))
            [] [.revertReturndata])
        if let some binding := env.rawBindings.find? p.id then
          let some i := modelParamNames.findIdx? (· == p.name) | throwError "missing raw scalar parameter"
          let offset := 4 + (modelParams.toList.take i).foldl (fun n p => n + paramHeadSize p.ty) 0
          abiGuards := abiGuards.push (.letVar binding (.calldataload (.literal offset)))
    let body := abiGuards ++ body
    let returns ← (do
      if (← mKind fn) == "VariableDeclaration" then
        return (← get).publicVarGetterReturns
      if let some arrayRetTy ← functionEmptyBodyArrayReturnType? fn then
        return #[arrayRetTy]
      if let some (_, elemPty, length) ← functionFixedArrayReturnType? fn then
        return Array.replicate length elemPty
      if let some (_, _, _, _, memberSpecs) ← functionFlatStructReturnType? fn then
        return (memberSpecs.map (fun (p : String × String × ParamType) => p.2.2) : Array ParamType)
      if ← functionMsgDataReturn? fn then
        return #[.bytes]
      if let some dynRetTy ← functionDynamicBytesReturn? fn then
        return #[dynRetTy]
      let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
      let mut out : Array ParamType := #[]
      for r in rets do
        let ty ← mType r
        let some pty := paramType ty | failAt r s!"unsupported return type {ty}"
        out := out.push pty
      pure out) |>.run' env
    let isView ←
      if optStr fn "nodeType" == some "VariableDeclaration" then
        pure true
      else do
        let mutability ← str (← field fn "stateMutability")
        pure (mutability == "view" || mutability == "pure")
    specs := specs.push
      { name := functionName, params := modelParams.toList, returnType := none,
        returns := returns.toList, isView, body := body.toList,
        abiDecoding := if env.explicitAbi then .explicitPrelude else .standard,
        localObligations := if abiGuards.isEmpty && !env.rootMsgDataReturn && (collectUnguardedUnsafeBoundaryMechanicsFromStmts body.toList).isEmpty then [] else [{
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
    let mut expandedMembers : List StructMember := []
    for arrInfo in info.structFixedArrays do
      if env.usedStructFixedArrays.contains (name, arrInfo.member) then
        let perWord := 256 / arrInfo.elementWidth
        for index in [:arrInfo.length] do
          let offset := (index % perWord) * arrInfo.elementWidth
          let packed : Option PackedBits :=
            if arrInfo.elementWidth == 256 then none
            else some { offset := offset, width := arrInfo.elementWidth }
          let member : StructMember :=
            { name := s!"__solidity_struct_array_{arrInfo.member}_{index}",
              ty := .uint256,
              wordOffset := arrInfo.wordOffset + index / perWord,
              packed }
          expandedMembers := expandedMembers ++ [member]
    if info.keyCount == 0 && (!info.structMembers.isEmpty || !info.structFixedArrays.isEmpty || !info.structMappings.isEmpty || !info.structDynamicArrays.isEmpty) then
      for member in info.structMembers ++ expandedMembers.toArray do
        let memberSlot := info.slot + member.wordOffset
        let memberField : Field :=
          { name := topStructMemberFieldName name member.name,
            ty := .uint256,
            slot := some memberSlot,
            packedBits := member.packed }
        fields := fields.push (memberSlot, memberField)
    else
      let field :=
        if expandedMembers.isEmpty then info.field
        else
          let ty := match info.field.ty with
            | .mappingStruct k ms => FieldType.mappingStruct k (ms ++ expandedMembers)
            | .mappingStruct2 k1 k2 ms => FieldType.mappingStruct2 k1 k2 (ms ++ expandedMembers)
            | other => other
          { info.field with ty }
      fields := fields.push (info.slot, field)
  let sortedFields := (fields.qsort (fun a b => a.1 < b.1)).map (·.2)
  let sortedFields :=
    if env.usedRawStorage then
      let maxSlot := fields.foldl (fun acc pair => Nat.max acc pair.1) 0
      sortedFields.push { name := rawStorageFieldName, ty := .uint256, slot := some (maxSlot + 1000) }
    else
      sortedFields
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
    if env.referenced.contains o.field && !env.usedStructFixedArrays.contains (o.field, o.name) &&
        !env.usedStructMappings.contains (o.field, o.name) &&
        !env.usedStructDynamicArrays.contains (o.field, o.name) then
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
    ("solcVersion", Json.str release.longVersion),
    ("contract", Json.str contract),
    ("functions", Json.arr signatures),
    ("solcInput", input),
    ("importerSources", Json.mkObj [
      ("Import.lean", Json.str importer), ("Coverage.lean", Json.str coverage),
      ("Report.lean", Json.str reportSrc), ("Quote.lean", Json.str quoteSrc),
      ("Profile.lean", Json.str profileSrc)])]
  let digest := sha256Hex digestInput.compress.toUTF8
  let report : ImportReport :=
    { importerVersion, solcLongVersion := release.longVersion, solcSha256 := solcSha, settingsJson := settings.compress,
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
  | .int256 => some `(Verity.Core.Int256)
  | .uintN bits => some `(Verity.Core.UIntN $(quote bits))
  | .uint8 => some `(Verity.Core.UIntN 8)
  | .uint16 => some `(Verity.Core.UIntN 16)
  | .address => some `(Verity.Core.Address)
  | .bytes32 => some `(Verity.Core.BytesN 32)
  | .bytesN 4 => some `(Verity.Core.BytesN 4)
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
      if member.name.startsWith "__solidity_struct_array_" then continue
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
    discard <| liftTermElabM <| resolveSolcRelease profile
    let roots ← roots.mapM fun root => do
      let `(solidityRoot| function $fn ( $tys,* )) := root | throwUnsupportedSyntax
      pure (fn.getId.toString (escape := false), tys.getElems.map (·.getId.toString (escape := false)))
    let pkg ← packageRoot
    let project := if root.getString.startsWith "/" then
      System.FilePath.mk root.getString else pkg / root.getString
    let (model, report) ← liftTermElabM <|
      importSlice pkg project entry.getString (contract.getId.toString (escape := false)) roots profile
    let ns := (← getCurrNamespace) ++ alias.getId
    let name (suffix : Name) := mkIdent (`_root_ ++ ns ++ suffix)
    elabCommand (← `(set_option maxRecDepth 16384 in
      def $(name `model) : Compiler.CompilationModel.CompilationModel :=
        $(← quoteModel model)))
    elabCommand (← `(set_option maxRecDepth 16384 in
      def $(name `report) : Compiler.CompilationModel.SolidityImport.ImportReport :=
        $(← quoteReport report)))
    elabCommand (← `(def $(name `sourceDigest) : String := $(quote report.sourceDigest)))
    elabCommand (← `(set_option maxRecDepth 16384 in
      theorem $(name `covered) :
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
