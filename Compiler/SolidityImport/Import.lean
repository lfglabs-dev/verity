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
  | one (field : String) (key : Expr)
  | two (field : String) (k1 k2 : Expr)
  | outer (field : String) (k1 : Expr)

private structure StructFixedArrayInfo where
  member : String
  solcType : String
  wordOffset : Nat
  byteOffset : Nat
  length : Nat
  elementWidth : Nat
  arrayType : String

private inductive Ref where
  | expr (v : Val)
  | path (pre : Array Stmt) (p : SPath)
  | fixedElement (pre : Array Stmt) (path : SPath) (index : Expr)
  | structFixedArray (pre : Array Stmt) (path : SPath) (info : StructFixedArrayInfo)
  | structFixedElement (pre : Array Stmt) (path : SPath) (info : StructFixedArrayInfo) (index : Expr)
  | snapshot (elements : Array Expr)
  | mem (id : Nat) (pre : Array Stmt)
  | abiArray (id memberIndex : Nat) (pre : Array Stmt)
  | abiElement (id memberIndex : Nat) (pointer : Expr) (pre : Array Stmt)
  | calldataBytes (id : Nat) (pre : Array Stmt)
  | state (name : String) (pre : Array Stmt)

private structure CalldataBytesParam where
  param : String
  offsetBinding : String
  headerBinding : String
  lengthBinding : String
  dataBinding : String

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

private inductive FnPtr where
  | direct (fnId : Nat)
  | branch (cond : Expr) (trueFnId : Nat) (falseFnId : Nat)

private structure FieldInfo where
  slot : Nat
  field : Field
  keyCount : Nat
  memberNames : Array String
  opaqueNames : Array String
  structFixedArrays : Array StructFixedArrayInfo := #[]
  booleanScalar : Bool := false
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
  funContractId : RBMap Nat Nat compare := RBMap.empty
  funBases : RBMap Nat (Array Nat) compare := RBMap.empty
  contractNames : RBMap Nat String compare := RBMap.empty
  contractKinds : RBMap Nat String compare := RBMap.empty
  contractBases : RBMap Nat (Array Nat) compare := RBMap.empty
  contractFuns : RBMap Nat (Array Nat) compare := RBMap.empty
  linearizedBases : Array Nat := #[]
  duplicateLayoutLabels : Array String := #[]
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
  calldataBytes : RBMap Nat CalldataBytesParam compare := RBMap.empty
  byteBuffers : RBMap Nat EncodedBytes compare := RBMap.empty
  fnPtrs : RBMap Nat FnPtr compare := RBMap.empty
  bodyAssigned : List Nat := []
  helperResult : Option (String × String) := none
  helperReturnId : Option Nat := none
  multiHelperResults : Option (Array (String × String × Bool)) := none
  helperPost : Array Stmt := #[]
  rootIsVoid : Bool := false
  rootReturns : Array Expr := #[]
  rootFixedArrayReturn : Option (String × ParamType × Nat) := none
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
    let name := ((env.funs.find? id).orElse (fun _ => env.modifiers.find? id)).bind (fun fn => optStr fn "name") |>.getD s!"decl#{id}"
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
  for _ in [:env.funs.size + 1] do
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
        | none => []
      o.foldl (fun acc _ v => acc ++ bodyAssignedIds v) own
  | _ => []

/-- Declarations modified by compound assignment (`+=`, `-=`) in `j`. -/
private partial def bodyCompoundAssignedIds (j : Json) : List Nat :=
  match j with
  | .arr xs => xs.toList.flatMap bodyCompoundAssignedIds
  | .obj o =>
      let kind := optStr j "nodeType"
      let operator := optStr j "operator" |>.getD ""
      let target :=
        if kind == some "Assignment" && (operator == "+=" || operator == "-=") then
          field? j "leftHandSide"
        else none
      let own := match target with
        | some t => targetAssignedIds t
        | none => []
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

private def isOrderIndependentSibling : Expr → Bool
  | .literal _ | .param _ | .blockTimestamp | .blockNumber
  | .caller | .contractAddress | .chainid => true
  | _ => false

private partial def assignmentIn (j : Json) : Bool :=
  match j with
  | .arr xs => xs.any assignmentIn
  | .obj o =>
      let own := optStr j "nodeType" == some "Assignment"
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
  else if ty.startsWith "uint" then (ty.drop 4).toNat?
  else none

private def paramType (ty : String) : Option ParamType :=
  match ty with
  | "uint256" | "uint" => some .uint256
  | "int256" | "int" => some .int256
  | "address" | "address payable" => some .address
  | "bytes32" => some .bytes32
  | "bool" => some .bool
  | _ =>
      if ty.startsWith "contract " then some .address
      else match bitsOf ty with
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

private def markStructFixedArray (fieldName memberName : String) : M Unit := do
  let env ← get
  unless env.usedStructFixedArrays.contains (fieldName, memberName) do
    modify fun e => { e with usedStructFixedArrays := e.usedStructFixedArrays.push (fieldName, memberName) }

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
      if typeId == "t_bool" then pure 8
      else if typeId == "t_address" || typeId == "t_address_payable" || typeId.startsWith "t_contract(" then pure 160
      else if typeId == "t_bytes32" || typeId == "t_int256" then pure 256
      else if typeId.startsWith "t_uint" then
        let some bits := (typeId.drop 6).toNat? | throwError "invalid scalar uint layout {typeId}"
        unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
          throwError "invalid scalar uint width {bits}"
        pure bits
      else throwError "unsupported scalar storage type {typeId}"
    let bytes ← mNat (← mField top "numberOfBytes")
    unless bytes * 8 == width do
      throwError "scalar storage size disagrees with type {typeId}"
    let offset := (← mNat (← mField item "offset")) * 8
    unless offset + width ≤ 256 do throwError "scalar storage field {name} crosses a word boundary"
    let packedBits : Option PackedBits :=
      if offset == 0 && width == 256 then none else some { offset, width }
    -- Exact physical words; source types still govern conversions and ABI.
    let field : Field := { name, ty := .uint256, slot := some slot, packedBits }
    return { slot, field, keyCount := 0, memberNames := #[], opaqueNames := #[],
             booleanScalar := typeId == "t_bool" }
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
      else if leafType == "address" || leafType == "address payable" || leafType.startsWith "contract " then pure 160
      else if leafType == "bytes32" || leafType == "int256" || leafType == "int" then pure 256
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
  let mut structFixedArrays : Array StructFixedArrayInfo := #[]
  for m in members do
    let label ← mStr (← mField m "label")
    let solcType ← mStr (← mField m "type")
    let word ← mNat (← mField m "slot")
    let byteOff ← mNat (← mField m "offset")
    if solcType.startsWith "t_array" then
      let item : OpaqRec := ⟨name, label, solcType, word, byteOff⟩
      modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
      let fixedInfo? : Option StructFixedArrayInfo ← (do
        let some arrTy := field? types solcType | return none
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
          member := label
          solcType
          wordOffset := word
          byteOffset := byteOff
          length
          elementWidth := width
          arrayType := arrLabel
        })
      match fixedInfo? with
      | some fixedInfo => structFixedArrays := structFixedArrays.push fixedInfo
      | none => skipped := skipped.push label
    else if solcType.startsWith "t_mapping" then
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
         memberNames := names, opaqueNames := skipped, structFixedArrays }

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
      pure (.literal value)
  | "YulIdentifier" =>
      let name ← mStr (← mField j "name")
      let env ← get
      if let some (binding, ty) := env.helperResult then
        if ty == "bool" || (bitsOf ty).getD 256 < 256 then
          if let some (.localVar foundBinding) := env.yulNames.find? name then
            if foundBinding == binding then
              failAt j "Yul reads of narrow named results are unsupported"
      match env.yulNames.find? name with
      | some expr => pure expr
      | none => failAt j s!"unbound Yul identifier {name}"
  | "YulFunctionCall" =>
      let fname ← mStr (← mField (← mField j "functionName") "name")
      let args ← mArr (← mField j "arguments")
      let mut xs : Array Expr := #[]
      for arg in args do
        xs := xs.push (← lowerYul arg)
      match fname, xs with
      | "add", #[a, b] => pure (.add a b)
      | "xor", #[a, b] => pure (.bitXor a b)
      | "mul", #[a, b] => pure (.mul a b)
      | "lt", #[a, b] => pure (.lt a b)
      | "tload", #[a] => pure (.tload a)
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
  | "UnaryOperation" =>
      unless (field? j "prefix").bind (fun v => v.getBool?.toOption) == some true do
        failAt j "unsupported unary operation"
      let op := optStr j "operator"
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
          markField name
          if info.booleanScalar then
            pure { pre, expr := .logicalNot (.logicalNot (.storage name)) }
          else
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
      | .structFixedElement pre path arrInfo index =>
          let (name, count, read) ← match path with
            | .one name key => pure (name, 1, fun member => Expr.structMember name key member)
            | .two name key1 key2 => pure (name, 2, fun member => Expr.structMember2 name key1 key2 member)
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
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
      else if env.calldataBytes.contains n then
        pure (.calldataBytes n #[])
      else if env.byteBuffers.contains n then
        failAt j "encoded byte locals are limited to hash and packed encoding operands"
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
        if env.duplicateLayoutLabels.contains name then
          failAt j s!"shadowed storage declaration {name} is outside this slice"
        if let some item := env.layoutItems.find? name then
          unless (← mNat (← mField item "astId")) == n do
            failAt j s!"shadowed storage declaration {name} is outside this slice"
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
      | .structFixedArray pre path arrInfo =>
          let name ← match path with
            | .one name _ | .two name _ _ => pure name
            | .outer _ _ => failAt j "fixed array element requires both mapping keys"
          let _ ← resolveField name j
          let ty ← mType (← mField j "indexExpression")
          unless ty.startsWith "uint" || ty.startsWith "int_const" do
            failAt j "fixed storage array index must be unsigned"
          let captured ← fresh
          pure (.structFixedElement ((pre ++ key.pre).push (.letVar captured key.expr))
            path arrInfo (.localVar captured))
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
      else if member == "max" || member == "min" then
        lowerTypeBound j base member
      else if member == "selector" then
        failAt j "function .selector member access is outside this slice"
      else
        match ← lowerRef base with
        | .path pre path =>
            let fieldName ← match path with
              | .one field _ | .two field _ _ => pure field
              | .outer _ _ => failAt j "member access on an incomplete mapping"
            let info ← resolveField fieldName j
            if let some arrInfo := info.structFixedArrays.find? (·.member == member) then
              pure (.structFixedArray pre path arrInfo)
            else
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
        | .calldataBytes id pre =>
            unless member == "length" do failAt j s!"unsupported bytes member {member}"
            let some cb := (← get).calldataBytes.find? id | failAt j "unknown calldata bytes parameter"
            pure (.expr { pre, expr := .localVar cb.lengthBinding })
        | _ => failAt j s!"unsupported member {member}"
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
  let isSigned := common == "int256" || common == "int"
  unless (bitsOf common).isSome || common == "bool" || isSigned do
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
  unless (← mKind targetExpr) == "ElementaryTypeNameExpression" do
    failAt j "unsupported cast"
  let tname ← mStr (← mField (← mField targetExpr "typeName") "name")
  let v ← lowerExpr args[0]!
  let src ← mType args[0]!
  if src.startsWith "int" && src != "int256" && src != "int" && !src.startsWith "int_const" then
    failAt j s!"unsupported cast source {src}"
  if tname == "int256" || tname == "int" then
    unless src == "int256" || src == "int" || src.startsWith "int_const" ||
        (src.startsWith "uint" && (bitsOf src).isSome) do
      failAt j s!"unsupported cast source {src} for {tname}"
    return v
  let some bits := bitsOf tname | failAt j s!"unsupported cast target {tname}"
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
    if id ≥ 0 then
      if let some buffer := (← get).byteBuffers.find? id.toNat then
        return buffer
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
  let isAbiBuiltin ← if (← mKind base) == "Identifier" && optStr base "name" == some "abi" then
    pure ((← refInt base) == -1)
  else
    pure false
  unless isAbiBuiltin do
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
    if (← mType arg).startsWith "struct " then
      match ← lowerRef arg with
      | .mem id pre =>
          let some descriptor := (← get).mems.find? id
            | failAt arg "unknown reference argument"
          vals := vals.push (.memory descriptor pre)
      | _ => failAt arg "only root memory/calldata struct arguments are supported"
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
    | "MemberAccess" =>
        let id ← refInt callee
        if id < 0 then failAt callee "builtin call is outside this slice"
        let base ← mField callee "expression"
        let baseTy ← mType base
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
  let vals ← lowerCallArgs j receiver?
  if receiver?.isSome then
    let env ← get
    let isLibrary := match env.funContractId.find? fnId with
      | some cid => env.contractKinds.find? cid == some "library"
      | none => false
    unless isLibrary do
      failAt callee "external contract calls are outside this slice"
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
    let argNode ← argumentAt at_ i
    let argTy ← mType argNode
    let some arg := args[i]? | failAt at_ s!"missing argument {i}"
    match arg with
    | .scalar value =>
        let converted ← convert pty argTy value at_
        if (bodyCompoundAssignedIds body).contains pid && !(bodyDirectAssignedIds body).contains pid then
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
  pure (pre, yul)

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
  let terminalAssembly ← if stmts.size == 1 && mods.isEmpty &&
      (resultType == "uint256" || resultType == "uint" || resultType == "bytes32") then
    pure ((← mKind stmts[0]!) == "InlineAssembly") else pure false
  modify fun e => { e with helperResult := none, helperReturnId := some retId, multiHelperResults := none }
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
    { e with stack := saved.stack, yulNames := savedYul, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, calldataBytes := saved.calldataBytes, byteBuffers := saved.byteBuffers, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
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
  modify fun e => { e with stack := frame, currentFile := frameFile, unchecked := false, bodyAssigned := bodyAssignedIds body }
  let mods ← mArr (← mField fn "modifiers")
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.isEmpty do failAt fn "expected void helper"
  let (pre, yul) ← bindHelperParams params args body at_ savedYul
  modify fun e => { e with yulNames := yul, helperResult := none, helperReturnId := none, multiHelperResults := none }
  noteFn fn
  let (modStmts, modPost) ← lowerModifiers mods
  modify fun e => { e with helperPost := modPost }
  let stmts ← mArr (← mField body "statements")
  let bodyStmts ← lowerVoidHelperFrom stmts.toList (pure modPost)
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, calldataBytes := saved.calldataBytes, byteBuffers := saved.byteBuffers, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := savedHelperResult, helperReturnId := savedHelperReturnId, multiHelperResults := saved.multiHelperResults, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
  pure (pre ++ modStmts ++ bodyStmts)

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
  modify fun e => { e with helperResult := none, helperReturnId := none, multiHelperResults := some results }
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
    { e with stack := saved.stack, yulNames := savedYul, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, calldataBytes := saved.calldataBytes, byteBuffers := saved.byteBuffers, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned, helperResult := saved.helperResult, helperReturnId := saved.helperReturnId, multiHelperResults := saved.multiHelperResults, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
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
        rets := rets.push (val.expr, outTy)
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

private partial def argumentAt (call : Json) (i : Nat) : M Json := do
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

private partial def convert (paramTy argTy : String) (v : Val) (at_ : Json) : M Val := do
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
  if argTy.startsWith "int_const" && !argTy.startsWith "int_const -" && (bitsOf paramTy).isSome then
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
    let some scalar := paramType pty
      | failAt p s!"unsupported modifier parameter type {pty}"
    let argNode := args[i]!
    let argTy ← mType argNode
    let some argVal := argVals[i]? | failAt argNode s!"missing modifier argument {i}"
    let converted ← convert pty argTy argVal argNode
    if (bodyCompoundAssignedIds body).contains pid && !(bodyDirectAssignedIds body).contains pid then
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
  modify fun e => { e with yulNames := yul, helperResult := none, helperReturnId := none, multiHelperResults := none, helperPost := #[] }
  noteFn modDecl
  let preBodyStmts ← lowerVoidHelperFrom preStmts.toList (pure #[])
  let postBodyStmts ← lowerVoidHelperFrom postStmts.toList (pure #[])
  modify fun e =>
    { e with stack := saved.stack, yulNames := savedYul, currentFile := savedFile, unchecked := saved.unchecked,
             values := saved.values, writableLocals := saved.writableLocals, paths := saved.paths,
             snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers, fnPtrs := saved.fnPtrs, bodyAssigned := saved.bodyAssigned,
             helperResult := savedHelperResult, helperReturnId := savedHelperReturnId, multiHelperResults := saved.multiHelperResults, helperPost := saved.helperPost, scalarTy := saved.scalarTy }
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
  | "Return" | "RevertStatement" => pure true
  | "InlineAssembly" => pure (← get).helperResult.isNone
  | "Block" | "UncheckedBlock" => ((← mArr (← mField s "statements")).back?.map helperReturns).getD (pure false)
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
             snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers, scalarTy := saved.scalarTy,
             writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, yulNames := saved.yulNames }
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
        modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers, scalarTy := saved.scalarTy, yulNames := saved.yulNames }
    | "UncheckedBlock" =>
        let saved ← get
        modify fun e => { e with unchecked := true }
        let subStmts ← mArr (← mField statement "statements")
        for sub in subStmts do
          let subOut ← lowerHelperLoopBody sub
          out := out ++ subOut
        modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers, scalarTy := saved.scalarTy, yulNames := saved.yulNames, unchecked := saved.unchecked }
    | "VariableDeclarationStatement" => out := out ++ (← lowerLocal statement)
    | "ExpressionStatement" => out := out ++ (← lowerEffect statement)
    | "EmitStatement" => out := out ++ (← lowerEmit statement)
    | "RevertStatement" => out := out ++ (← lowerRevert statement)
    | "ForStatement" => out := out ++ (← lowerFor statement lowerHelperLoopBody)
    | "IfStatement" =>
        let (condition, _yes, no) ← ifParts statement
        let saved ← get
        let restore : M Unit := modify fun e => { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers, scalarTy := saved.scalarTy, yulNames := saved.yulNames }
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
                   snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames, unchecked := saved.unchecked }
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
        if let some (binding, ty) := (← get).helperResult then
          let v ← lowerAssembly s retName
          let cleaned := if ty == "bool" then Expr.logicalNot (.logicalNot v.expr) else
            match bitsOf ty with
            | some width => if width < 256 then Expr.bitAnd v.expr (.literal (2^width-1)) else v.expr
            | none => v.expr
          let (tail, result) ← lowerHelperFrom rest retName
          pure (v.pre.push (.assignVar binding cleaned) ++ tail, result)
        else
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
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers,
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
  | _ => pure false

private partial def stmtContainsReturn (s : Json) : M Bool := do
  match ← mKind s with
  | "Return" => pure true
  | "Block" | "UncheckedBlock" =>
      let stmts ← mArr (← mField s "statements")
      stmts.anyM stmtContainsReturn
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
                   snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames, unchecked := saved.unchecked }
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
    | "ForStatement" =>
        let loopStmts ← lowerFor s lowerHelperLoopBody
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
          else
            unless (← mKind expression) == "TupleExpression" && !(← mBool (← mField expression "isInlineArray")) do
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
              vals := vals.push v.expr
            for i in [:results.size] do
              let (binding, _, _) := results[i]!
              pre := pre.push (.assignVar binding (vals.getD i (.literal 0)))
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
                   snapshots := saved.snapshots, mems := saved.mems, byteBuffers := saved.byteBuffers,
                   scalarTy := saved.scalarTy, yulNames := saved.yulNames }
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

private partial def lowerEffect (statement : Json) : M (Array Stmt) := do
  let expression ← mField statement "expression"
  let kind ← mKind expression
  if kind == "FunctionCall" && optStr expression "kind" == some "functionCall" then
    let callee ← mField expression "expression"
    -- Builtin require keeps its overload set in solc's AST; its existing
    -- dedicated validator must run before strict user-declaration resolution.
    if (← mKind callee) == "Identifier" && optStr callee "name" == some "require" then
      return ← lowerRequire statement
    let reference ← refInt callee
    if reference ≥ 0 then
      if let some ptr := (← get).fnPtrs.find? reference.toNat then
        unless (← mKind callee) == "Identifier" do
          failAt callee "function pointer call requires a local identifier"
        let checkFnVoid (fnId : Nat) : M Bool := do
          let some declaration := (← get).funs.find? fnId
            | failAt callee "unresolved function pointer target"
          let visibility := optStr declaration "visibility" |>.getD ""
          unless visibility == "internal" || visibility == "private" do
            failAt callee "function pointer target requires an internal or private declaration"
          let rets ← mArr (← mField (← mField declaration "returnParameters") "parameters")
          pure rets.isEmpty
        let isVoid ← match ptr with
          | .direct fnId => checkFnVoid fnId
          | .branch _ tId fId => do
              let v1 ← checkFnVoid tId
              let v2 ← checkFnVoid fId
              unless v1 == v2 do failAt callee "function pointer branches have mismatched return arities"
              pure v1
        if isVoid then
          let rawVals ← lowerCallArgs expression none
          match ptr with
          | .direct fnId =>
              return ← inlineVoidFn fnId rawVals expression
          | .branch condExpr trueFnId falseFnId =>
              let (argPre, atomicVals) ← atomizeCallArgs rawVals
              let trueStmts ← inlineVoidFn trueFnId atomicVals expression
              let falseStmts ← inlineVoidFn falseFnId atomicVals expression
              return argPre.push (.ite condExpr trueStmts.toList falseStmts.toList)
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
        -- Materialize even a discarded result: the final expression can itself
        -- read storage or fail. The helper's effect prelude remains ordered.
        let result ← atom (← lowerCall expression)
        return result.pre
  if kind != "Assignment" && kind != "UnaryOperation" then
    return ← lowerRequire statement
  let deleting := kind == "UnaryOperation"
  let operator ← mStr (← mField expression "operator")
  if !deleting && (operator == "+=" || operator == "-=") then
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
        markField name
        let storedExpr := if info.booleanScalar then Expr.logicalNot (.logicalNot converted.expr) else converted.expr
        assigns := assigns ++ pre ++ converted.pre |>.push (.setStorage name storedExpr)
    return callPre ++ assigns
  if (← mKind target) == "Identifier" then
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
    if info.structFixedArrays.any (·.member == member) then
      failAt target s!"struct fixed array member {member} requires an element index"
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
    if let .structFixedElement pre path arrInfo index := reference then
      let (name, count, write) ← match path with
        | .one name key => pure (name, 1, fun member value => Stmt.setStructMember name key member value)
        | .two name key1 key2 => pure (name, 2, fun member value => Stmt.setStructMember2 name key1 key2 member value)
        | .outer _ _ => failAt target "fixed array write requires both mapping keys"
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
    let .path pre path := reference
      | failAt target "mapping assignment target is not a storage path"
    let (name, count, write) ← match path with
      | .one field key => pure (field, 1, fun (value : Expr) => Stmt.setStructMember field key "__solidity_value" value)
      | .two field key1 key2 => pure (field, 2, fun (value : Expr) => Stmt.setStructMember2 field key1 key2 "__solidity_value" value)
      | .outer _ _ => failAt target "mapping assignment requires both keys"
    let info ← resolveField name target
    if deleting && !info.scalarMapping && info.fixedArrayLength.isNone && info.keyCount == count then
      unless info.opaqueNames.isEmpty do
        failAt target "cannot delete mapping struct with opaque members"
      unless info.structFixedArrays.isEmpty do
        failAt target "cannot delete mapping struct with fixed-array members"
      unless !info.memberNames.isEmpty do
        failAt target "cannot delete empty mapping struct layout"
      markField name
      let writeMember : String → Expr → Stmt := match path with
        | .one field key => fun member value => Stmt.setStructMember field key member value
        | .two field key1 key2 => fun member value => Stmt.setStructMember2 field key1 key2 member value
        | .outer _ _ => fun _ _ => .stop
      let mut out := pre
      for member in info.memberNames do
        out := out.push (writeMember member (.literal 0))
      return out
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
  if info.booleanScalar && !deleting then
    return (pre ++ value.pre).push (.setStorage name (.logicalNot (.logicalNot value.expr)))
  return (pre ++ value.pre).push (.setStorage name value.expr)

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
    else
      failAt at_ s!"unsupported compound assignment operator {operator}"
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
    else
      failAt at_ s!"unsupported compound assignment operator {operator}"

private partial def lowerCompoundAssignment (expression : Json) (operator : String) : M (Array Stmt) := do
  let target ← mField expression "leftHandSide"
  let right ← mField expression "rightHandSide"
  let isSupportedCompoundTy (ty : String) : Bool :=
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
        unless isSupportedCompoundTy ty do
          failAt target s!"unsupported scalar local compound assignment type {ty}"
        let rhsVal ← atom (← convert ty (← mType right) (← lowerExpr right) right)
        let combined ← combineCompound operator ty (.localVar binding) rhsVal.expr expression
        return rhsVal.pre ++ combined.pre |>.push (.assignVar binding combined.expr)
  if (← mKind target) == "MemberAccess" then
    let cMember ← mStr (← mField target "memberName")
    let .path pre path ← lowerRef (← mField target "expression")
      | failAt target "member assignment requires a mapping struct storage path"
    unless pre.isEmpty do failAt target "member write key prelude is unsupported"
    let (name, count, read, write) ← match path with
      | .one cField cKey => pure (cField, 1, Expr.structMember cField cKey cMember, fun (cVal : Expr) => Stmt.setStructMember cField cKey cMember cVal)
      | .two cField cKey1 cKey2 => pure (cField, 2, Expr.structMember2 cField cKey1 cKey2 cMember, fun (cVal : Expr) => Stmt.setStructMember2 cField cKey1 cKey2 cMember cVal)
      | .outer _ _ => failAt target "member assignment requires both mapping keys"
    let info ← resolveField name target
    if info.opaqueNames.contains cMember then failAt target s!"member {cMember} is opaque in this slice"
    if info.structFixedArrays.any (·.member == cMember) then
      failAt target s!"struct fixed array member {cMember} requires an element index"
    unless !info.scalarMapping && info.keyCount == count && info.memberNames.contains cMember do
      failAt target "member assignment requires a supported layout member"
    let ty ← mType target
    unless ty.startsWith "uint" && (bitsOf ty).isSome do
      failAt target "member assignment requires an unsigned scalar member"
    markField name
    let rhsVal ← atom (← convert ty (← mType right) (← lowerExpr right) right)
    let lhsVar ← fresh
    let combined ← combineCompound operator ty (.localVar lhsVar) rhsVal.expr expression
    return rhsVal.pre.push (.letVar lhsVar read) ++ combined.pre |>.push (write combined.expr)
  if (← mKind target) == "IndexAccess" then
    let reference ← lowerRef target
    if let .fixedElement _ _ _ := reference then
      failAt expression "only scalar storage assignment and delete are supported"
    if let .structFixedElement _ _ _ _ := reference then
      failAt expression "only scalar storage assignment and delete are supported"
    let .path pre path := reference
      | failAt target "mapping assignment target is not a storage path"
    let (name, count, read, write) ← match path with
      | .one cField cKey => pure (cField, 1, Expr.structMember cField cKey "__solidity_value", fun (cVal : Expr) => Stmt.setStructMember cField cKey "__solidity_value" cVal)
      | .two cField cKey1 cKey2 => pure (cField, 2, Expr.structMember2 cField cKey1 cKey2 "__solidity_value", fun (cVal : Expr) => Stmt.setStructMember2 cField cKey1 cKey2 "__solidity_value" cVal)
      | .outer _ _ => failAt target "mapping assignment requires both keys"
    let info ← resolveField name target
    unless info.scalarMapping && info.keyCount == count do
      failAt target "only scalar mapping values are writable"
    let ty ← mType target
    unless isSupportedCompoundTy ty do
      failAt target s!"unsupported mapping compound assignment type {ty}"
    if !pre.isEmpty && (assignmentIn right || statefulCallIn right (← get)) then
      failAt target "compound mapping write key prelude with stateful RHS is unsupported"
    markField name
    let rhsVal ← atom (← convert ty (← mType right) (← lowerExpr right) right)
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
  let rhsVal ← atom (← convert ty (← mType right) (← lowerExpr right) right)
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
  markField name
  let value ← atom (← convert (← mType target) (← mType right) (← lowerExpr right) right)
  let storedExpr := if info.booleanScalar then Expr.logicalNot (.logicalNot value.expr) else value.expr
  let resultVar ← fresh
  return { pre := (pre ++ value.pre).push (.letVar resultVar storedExpr) |>.push (.setStorage name (.localVar resultVar)), expr := .localVar resultVar }

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
          unless optStr argument "kind" == some "typeConversion" do
            failAt argument "custom-error arguments currently require literals or scalar bindings"
          pure false
      | "MemberAccess" =>
          let member ← mStr (← mField argument "memberName")
          unless member == "max" || member == "min" do
            failAt argument "custom-error arguments currently require literals or scalar bindings"
          pure false
      | _ => failAt argument "custom-error arguments currently require literals or scalar bindings"
    let converted ← convert ty (← mType argument) (← lowerExpr argument) argument
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
  let targetSrc ← mStr (← mField vars[0]! "src")
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
  pure { pre := #[], expr := ← lowerYul (← mField asg "value") }

private partial def lowerLocal (s : Json) : M (Array Stmt) := do
  let decls ← mArr (← mField s "declarations")
  if decls.size > 1 then
    unless decls.any (!·.isNull) do failAt s "empty tuple declaration"
    let init := field? s "initialValue" |>.getD Json.null
    if init.isNull then failAt s "tuple variable declaration requires an initializer"
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
      unless name.all (fun c => c.isAlphanum || c == '_') && name != "" do
        failAt d s!"unsupported local name {name}"
      let id ← mNat (← mField d "id")
      let loc := optStr d "storageLocation" |>.getD "default"
      unless loc == "default" do
        failAt d "tuple variable declaration only supports scalar locals"
      let ty ← mType d
      let some scalarType := paramType ty
        | failAt d s!"unsupported tuple local type {ty}"
      let (retExpr, retTy) := retExprs.getD i (.literal 0, "")
      let converted ← convert ty retTy { pre := #[], expr := retExpr } d
      let binding ← freshFor name
      let expr := Expr.localVar binding
      out := out ++ converted.pre |>.push (.letVar binding converted.expr)
      modify fun e =>
        { e with values := e.values.insert id expr,
                 scalarTy := e.scalarTy.insert id scalarType,
                 yulNames := e.yulNames.insert name expr,
                 writableLocals := e.writableLocals.insert id binding }
    return out
  unless decls.size == 1 do failAt s "only a single declaration is supported"
  if decls[0]!.isNull then failAt s "empty declaration"
  let d := decls[0]!
  let name ← mStr (← mField d "name")
  unless name.all (fun c => c.isAlphanum || c == '_') && name != "" do
    failAt d s!"unsupported local name {name}"
  let id ← mNat (← mField d "id")
  let loc := optStr d "storageLocation" |>.getD "default"
  let init := field? s "initialValue" |>.getD Json.null
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
  if loc == "memory" && (← mType d).contains '[' then
    if (← mKind init) == "TupleExpression" then
      if ← mBool (← mField init "isInlineArray") then
        failAt init "inline arrays are outside this slice"
    match ← lowerRef init with
    | .path pre path =>
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
        modify fun e =>
          { e with snapshots := e.snapshots.insert id elements,
                   yulNames := e.yulNames.erase name }
        markField field
        return result
    | .structFixedArray pre path arrInfo =>
        let (field, count, read) ← match path with
          | .one field key => pure (field, 1, fun member => Expr.structMember field key member)
          | .two field key1 key2 => pure (field, 2, fun member => Expr.structMember2 field key1 key2 member)
          | .outer _ _ => failAt init "fixed array copy requires both mapping keys"
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
        modify fun e =>
          { e with paths := e.paths.insert id frozen,
                   yulNames := e.yulNames.erase name }
        pure (pre ++ keys)
    | _ => failAt s "storage local is not a resolved read path"
  else
    let v ← lowerExpr init
    unless loc == "default" do
      failAt d s!"unsupported local storage location {loc}"
    let ty ← mType d
    let some scalarType := paramType ty
      | failAt d s!"unsupported scalar local type {ty}"
    let converted ← convert ty (← mType init) v init
    let binding ← freshFor name
    let expr := Expr.localVar binding
    modify fun e =>
      { e with values := e.values.insert id expr, scalarTy := e.scalarTy.insert id scalarType,
               yulNames := e.yulNames.insert name expr, writableLocals := e.writableLocals.insert id binding }
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
  unless length > 0 do return none
  let some elemPty := paramType elemStr | return none
  return some (elemStr, elemPty, length)

private def bindRoot (fn : Json) : M (Array SrcParam) := do
  noteFn fn
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  let mut out : Array SrcParam := #[]
  for p in params do
    let rawName ← mStr (← mField p "name")
    let id ← mNat (← mField p "id")
    let name ← if rawName == "" then fresh else do
      modify fun e => { e with bound := rawName :: e.bound }
      pure rawName
    let ty ← mType p
    let loc := optStr p "storageLocation" |>.getD "default"
    out := out.push { name, id }
    if ty == "bytes" then
      unless loc == "calldata" do
        failAt p s!"unsupported location {loc} for bytes"
      modify fun e =>
        { e with bound := s!"{name}_offset" :: s!"{name}_length" :: s!"{name}_data_offset" :: e.bound }
      let offsetBinding ← fresh
      let headerBinding ← fresh
      let lengthBinding ← fresh
      let dataBinding ← fresh
      modify fun e =>
        let bound : CalldataBytesParam :=
          { param := name
            offsetBinding
            headerBinding
            lengthBinding
            dataBinding }
        { e with calldataBytes := e.calldataBytes.insert id bound }
    else if ty.startsWith "struct " && (loc == "memory" || loc == "calldata") then
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
  let explicitAbi := (← get).mems.toList.any (fun (_, mem) => mem.schema.isSome) || !(← get).calldataBytes.isEmpty
  modify fun e => { e with explicitAbi }
  if explicitAbi then
    for p in params do
      let id ← mNat (← mField p "id")
      if let some mem := (← get).mems.find? id then
        if mem.staticTypes.isSome then
          failAt p "mixed static and dynamic struct parameters require explicit static-root lowering"
      else if !(← get).calldataBytes.contains id then
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
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, calldataBytes := saved.calldataBytes, byteBuffers := saved.byteBuffers, scalarTy := saved.scalarTy, yulNames := saved.yulNames }
        out := out ++ nested
        returned := nestedReturned
    | "UncheckedBlock" =>
        let saved ← get
        modify fun e => { e with unchecked := true }
        let (uncheckedNested, uncheckedReturned) ← lowerRootStatements (← mArr (← mField s "statements"))
        modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths,
                   snapshots := saved.snapshots, mems := saved.mems, calldataBytes := saved.calldataBytes, byteBuffers := saved.byteBuffers, scalarTy := saved.scalarTy, yulNames := saved.yulNames, unchecked := saved.unchecked }
        out := out ++ uncheckedNested
        returned := uncheckedReturned
    | "VariableDeclarationStatement" =>
        out := out ++ (← lowerLocal s)
    | "ExpressionStatement" =>
        out := out ++ (← lowerEffect s)
    | "EmitStatement" =>
        out := out ++ (← lowerEmit s)
    | "RevertStatement" =>
        returned := true
        out := out ++ (← lowerRevert s)
    | "ForStatement" =>
        out := out ++ (← lowerFor s fun body => do
          let statements ← if (← mKind body) == "Block" then mArr (← mField body "statements") else pure #[body]
          let (lowered, _) ← lowerRootStatements statements
          pure lowered)
    | "IfStatement" =>
        let (condition, yes, no) ← ifParts s
        let saved ← get
        let restore : M Unit := modify fun e =>
          { e with values := saved.values, writableLocals := saved.writableLocals, fnPtrs := saved.fnPtrs, paths := saved.paths, snapshots := saved.snapshots, mems := saved.mems, calldataBytes := saved.calldataBytes, byteBuffers := saved.byteBuffers,
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
        else
          let v ← atom (← lowerExpr expr)
          if env.rootPost.isEmpty then
            out := out ++ v.pre |>.push (.returnValues [v.expr])
          else
            let captured ← fresh
            out := ((out ++ v.pre).push (.letVar captured v.expr) ++ env.rootPost).push (.returnValues [.localVar captured])
    | kind => failAt s s!"unsupported statement {kind}"
  pure (out, returned)

private def lowerRoot (fn : Json) : M (Array Stmt × Array SrcParam) := do
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
    if (bodyCompoundAssignedIds body).contains p.id && !(bodyDirectAssignedIds body).contains p.id then
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
  let mut rootRetExprs : Array Expr := #[]
  let mut allNamedScalar := !returns.isEmpty && emptyBodyArrayRet?.isNone && fixedArrayRet?.isNone
  if emptyBodyArrayRet?.isNone && fixedArrayRet?.isNone then
    for r in returns do
      let rname ← mStr (← mField r "name")
      if rname == "" then
        allNamedScalar := false
      else
        let rid ← mNat (← mField r "id")
        let rty ← mType r
        let some scalar := paramType rty
          | failAt r s!"unsupported named root return type {rty}"
        let rbinding ← freshFor rname
        let rexpr := Expr.localVar rbinding
        rootInit := rootInit ++ #[.letVar rbinding (.literal 0)]
        rootRetExprs := rootRetExprs.push rexpr
        modify fun e =>
          { e with values := e.values.insert rid rexpr,
                   writableLocals := e.writableLocals.insert rid rbinding,
                   scalarTy := e.scalarTy.insert rid scalar,
                   yulNames := e.yulNames.insert rname rexpr }
  modify fun e =>
    { e with bodyAssigned := bodyAssignedIds body,
             rootIsVoid := returns.isEmpty,
             rootReturns := if allNamedScalar then rootRetExprs else #[],
             rootFixedArrayReturn := fixedArrayRet? }
  let (modStmts, modPost) ← lowerModifiers mods
  modify fun e => { e with rootPost := modPost }
  let (bodyOut, returned) ← lowerRootStatements stmts
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
              modify fun e =>
                { e with contractNames := e.contractNames.insert id n,
                         contractKinds := e.contractKinds.insert id kind,
                         contractBases := e.contractBases.insert id bases }
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
      else
        let singleParts := t.splitOn "'"
        if singleParts.length ≥ 2 then
          out := out.push singleParts[1]!
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
        tys := tys.push (← mType p)
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
  let mut hits : Array (Json × Array String × Bool) := #[]
  let mut described : Array String := #[]
  for cand in effective do
    described := described.push
      s!"{functionName}({String.intercalate ", " cand.canonicalTys.toList})"
    if cand.tys.size == written.size && (cand.tys.zip written).all (fun (t, w) => typeMatches w t) then
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
                      snapshots := RBMap.empty, mems := RBMap.empty, calldataBytes := RBMap.empty, byteBuffers := RBMap.empty, scalarTy := RBMap.empty, writableLocals := RBMap.empty, fnPtrs := RBMap.empty, bodyAssigned := [], yulNames := RBMap.empty,
                      projections := #[], rawBindings := RBMap.empty, explicitAbi := false, encodingMemory := false, helperResult := none, helperReturnId := none, multiHelperResults := none, helperPost := #[], rootIsVoid := false, rootReturns := #[], rootFixedArrayReturn := none, rootPost := #[] }
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
      else if env.calldataBytes.contains p.id then
        if modelParamNames.contains p.name then
          (failAt fn s!"parameter name collision: {p.name}").run' env
        modelParamNames := modelParamNames.push p.name
        modelParams := modelParams.push { name := p.name, ty := .bytes }
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
        let checks := AbiLowering.bytesCalldataHead cb.offsetBinding cb.headerBinding cb.lengthBinding cb.dataBinding rootHeadWords headOffset
        abiGuards := abiGuards ++ checks.toArray
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
      if let some arrayRetTy ← functionEmptyBodyArrayReturnType? fn then
        return #[arrayRetTy]
      if let some (_, elemPty, length) ← functionFixedArrayReturnType? fn then
        return Array.replicate length elemPty
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
    if env.referenced.contains o.field && !env.usedStructFixedArrays.contains (o.field, o.name) then
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
