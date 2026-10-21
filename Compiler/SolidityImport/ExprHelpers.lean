import Lean
import Compiler.Sha256.Engine
import Compiler.Hex
import Compiler.SolidityImport.Access
import Compiler.SolidityImport.Profile
import Compiler.SolidityImport.Quote
import Compiler.SolidityImport.Report
import Compiler.SolidityImport.AbiRootLowering
import Compiler.SolidityImport.AbiMemoryDecode
import Compiler.SolidityImport.AbiEncoding
import Compiler.SolidityImport.TypesAndRecords
import Compiler.SolidityImport.TransportBarriers
import Compiler.SolidityImport.LibraryCallGuard

open Lean Meta Elab Command

namespace Compiler.CompilationModel.SolidityImport

/-!
# Solidity Import Expression, Type, and Yul Helpers

Extracted expression, literal, operator, type-resolution, and Yul-slice helpers
for the Solidity frontend importer, equipped with a 3-layer `ExprHelperMetaSpec`
bundle (universal specification, 1–3 line projection corollaries, and `by decide`
executable witnesses).
-/

def field (j : Json) (key : String) : MetaM Json :=
  match j.getObjVal? key with
  | .ok v => pure v
  | .error e => throwError "{e}"

def field? (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

def str (j : Json) : MetaM String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throwError "{e}"

def arr (j : Json) : MetaM (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throwError "{e}"

def bool (j : Json) : MetaM Bool :=
  match j.getBool? with
  | .ok v => pure v
  | .error e => throwError "{e}"

def flexNat (j : Json) : MetaM Nat := do
  match j.getNat? with
  | .ok n => pure n
  | .error _ =>
      match j.getStr? with
      | .ok s =>
          match s.toNat? with
          | some n => pure n
          | none => throwError "not a nat: {s}"
      | .error e => throwError "{e}"

def nodeKind (j : Json) : MetaM String := do
  str (← field j "nodeType")

def typeString (j : Json) : MetaM String := do
  str (← field (← field j "typeDescriptions") "typeString")

def optStr (j : Json) (key : String) : Option String :=
  match field? j key with
  | some v => v.getStr?.toOption
  | none => none

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def sha256Hex (bytes : ByteArray) : String :=
  (Sha256Engine.sha256 bytes).data.foldl (init := "") fun acc byte =>
    acc.push (hexDigit (byte.toNat / 16)) |>.push (hexDigit (byte.toNat % 16))

structure Env where
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
  nonLiteralByteLocals : Array Nat := #[]
  storageBytesVars : RBMap Nat (String × Expr × Bool) compare := RBMap.empty
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
  /-- `returns (S memory)` of a struct with dynamic members: its id and schema. -/
  rootDynamicStructReturn : Option (Nat × List AbiSchema.Member) := none
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
  yulMemoryStructs : RBMap String Nat compare := RBMap.empty
  yulScratch0 : Bool := false
  yulScratch32 : Bool := false
  /-- AST ids of the typed-interface staticcalls the current statement may
      lower (`admittedInterfaceCallIds` of its whole initializer, right-hand
      side or expression statement). Each id is consumed when lowered. -/
  admittedInterfaceCalls : List Nat := []
  /-- `bytes memory` locals whose initializer begins with a checked CREATE2
      initcode template literal (`DenoteCreate2.templateCost`). -/
  initcodeTemplates : Array Nat := #[]
  currentFile : String

def Env.init : Env where
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

abbrev M := StateT Env MetaM

def mField (j : Json) (key : String) : M Json := liftM (field j key)
def mStr (j : Json) (m : M String := liftM (str j)) : M String := m
def mArr (j : Json) : M (Array Json) := liftM (arr j)
def mBool (j : Json) : M Bool := liftM (bool j)
def mNat (j : Json) : M Nat := liftM (flexNat j)
def mKind (j : Json) : M String := liftM (nodeKind j)
def mType (j : Json) : M String := do
  let raw ← liftM (typeString j)
  let env ← get
  if let some u := env.userValueTypes.find? raw then
    return u
  let parts := raw.splitOn "["
  if let h :: t := parts then
    if let some u := env.userValueTypes.find? h then
      return String.intercalate "[" (u :: t)
  return raw

def failAt (j : Json) (why : String) : M α := do
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
def baseFunctionClosure (env : Env) (fnId : Nat) : Array Nat := Id.run do
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
def sameVirtualFamily (env : Env) (candId targetId : Nat) : Bool :=
  let candClosure := baseFunctionClosure env candId
  let targetClosure := baseFunctionClosure env targetId
  candClosure.any targetClosure.contains

/-- Resolve `targetFnId` across `searchContracts` (in C3 most-derived-first order),
    preferring the first implemented declaration in the same virtual family. -/
def resolveInContracts (env : Env) (searchContracts : List Nat) (targetFnId : Nat) : Option Nat := Id.run do
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

def refInt (j : Json) : M Int := do
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

def fresh : M String := do
  let env ← get
  let projected := env.mems.toList.flatMap fun (_, p) =>
    p.members.toList.map (fun (member, _) => s!"{p.param}_{member}")
  let reserved := env.sourceNames ++ projected ++ env.bound
  for _ in [:reserved.length + 1] do
    let n := (← get).next
    modify fun e => { e with next := e.next + 1 }
    let candidate := s!"_verity_slice_tmp_{n}"
    unless reserved.contains candidate do
      modify fun e => { e with bound := candidate :: e.bound }
      return candidate
  throwError "unable to allocate a hygienic slice binding"

def yulKeywords : List String :=
  ["let", "if", "switch", "case", "default", "for", "break", "continue", "leave",
   "function", "true", "false"]

/-- Binding for the Solidity local `name`: the source name itself when it is
free, so that proofs can refer to it, else `name_1`, `name_2`, ... Names that
the compiler reserves or Yul forbids fall back to `fresh`. -/
def freshFor (name : String) : M String := do
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
def freshAbiStem (schema : List AbiSchema.Member) (inMemory : Bool) : M String := do
  let budget := (← get).sourceNames.length + (← get).bound.length + 1
  for _ in [:budget] do
    let stem ← fresh
    let names := (AbiRootLowering.root stem 0 0 schema inMemory).names
    let reserved := (← get).sourceNames ++ (← get).bound
    unless names.any reserved.contains do
      modify fun e => { e with bound := names ++ e.bound }
      return stem
  throwError "unable to allocate hygienic ABI bindings"

/-- A stem whose `AbiMemoryDecode.materialize` names are all unused. -/
def freshMemoryDecodeStem (schema : List AbiSchema.Member) : M String := do
  let budget := (← get).sourceNames.length + (← get).bound.length + 1
  for _ in [:budget] do
    let stem ← fresh
    let names := (AbiMemoryDecode.materialize (.literal 0) (.literal 0) stem schema).names
    let reserved := (← get).sourceNames ++ (← get).bound
    unless names.any reserved.contains do
      modify fun e => { e with bound := names ++ e.bound }
      return stem
  throwError "unable to allocate hygienic ABI decoding bindings"

def freshAbiElementStem (fields : List AbiSchema.ScalarField) : M String := do
  let budget := (← get).sourceNames.length + (← get).bound.length + 1
  for _ in [:budget] do
    let stem ← fresh
    let (_, names, _) := AbiRootLowering.materializeElementFromCalldata (.literal 0) stem fields
    let reserved := (← get).sourceNames ++ (← get).bound
    unless names.any reserved.contains do
      modify fun e => { e with bound := names ++ e.bound }
      return stem
  throwError "unable to allocate hygienic ABI element bindings"

def convertStructCalldataToMemory (descriptor : MemParam) (at_ : Json) :
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
          [] [.revertEmpty])
      if let .intN bits := ty then
        if 0 < bits && bits < 256 && bits % 8 == 0 then
          let rawWord := Expr.calldataload (.add (.localVar descriptor.headBinding) (.literal (32*j)))
          checks := checks.push (.ite
            (.eq rawWord (.signextend (.literal (bits / 8 - 1)) rawWord))
            [] [.revertEmpty])
    return (checks, { descriptor with calldataLocation := false })
  failAt at_ "struct reference has no supported complete ABI schema"

def isAtom : Expr → Bool
  | .literal _ | .localVar _ | .param _ | .blockTimestamp | .blockNumber
  | .caller | .contractAddress | .chainid | .selfBalance | .txOrigin | .baseFee | .gasPrice => true
  | _ => false

partial def targetAssignedIds (t : Json) : List Nat :=
  if optStr t "nodeType" == some "Identifier" then
    match (field? t "referencedDeclaration").bind (fun v => v.getNat?.toOption) with
    | some n => [n]
    | none => []
  else if optStr t "nodeType" == some "TupleExpression" then
    match (field? t "components").bind (fun c => c.getArr?.toOption) with
    | some cs => cs.toList.flatMap targetAssignedIds
    | none => []
  else []

partial def yulAssignedSrcs (j : Json) : List String :=
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

def inlineAssemblyAssignedIds (j : Json) : List Nat :=
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

def yulOnlyAssignsDecl (j : Json) (declId : Nat) : Bool :=
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
partial def bodyAssignedIds (j : Json) : List Nat :=
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

def isCompoundAssignOp (operator : String) : Bool :=
  ["+=", "-=", "*=", "<<=", ">>=", "&=", "|=", "^=", "/=", "%="].contains operator

/-- Declarations modified by compound assignment (`+=`, `-=`, `*=`, `<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=`), `++`/`--`, or Yul assignment in `j`. -/
partial def bodyCompoundAssignedIds (j : Json) : List Nat :=
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
partial def bodyDirectAssignedIds (j : Json) : List Nat :=
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

mutual
  partial def jsonHasCustomRevert (env : Env) (seen : List Nat) (j : Json) : Bool :=
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
          else if kind == some "BinaryOperation" || kind == some "UnaryOperation" then
            match (field? j "function").bind (fun v => v.getNat?.toOption) with
            | some natId =>
                let targetId := resolveInContracts env env.linearizedBases.toList natId |>.getD natId
                fnHasCustomRevert env targetId seen
            | none => false
          else false
        o.foldl (fun found _ child => found || jsonHasCustomRevert env seen child) own
    | _ => false

  partial def fnHasCustomRevert (env : Env) (fnId : Nat) (seen : List Nat := []) : Bool :=
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

def isOrderIndependentSibling : Expr → Bool
  | .literal _ | .param _ | .blockTimestamp | .blockNumber
  | .caller | .contractAddress | .chainid | .selfBalance | .txOrigin | .baseFee | .gasPrice => true
  | _ => false

partial def evalConstExpr? (env : RBMap String Nat compare) : Expr → Option Nat
  | .literal n => if n < 2 ^ 256 then some n else none
  | .localVar name => env.find? name
  | .shl shift val => do
      let s ← evalConstExpr? env shift
      let v ← evalConstExpr? env val
      pure (if s >= 256 then 0 else (v * 2 ^ s) % (2 ^ 256))
  | .shr shift val => do
      let s ← evalConstExpr? env shift
      let v ← evalConstExpr? env val
      pure (if s >= 256 then 0 else v / (2 ^ s))
  | .bitOr a b => do
      let va ← evalConstExpr? env a
      let vb ← evalConstExpr? env b
      pure (Nat.lor va vb)
  | .bitAnd a b => do
      let va ← evalConstExpr? env a
      let vb ← evalConstExpr? env b
      pure (Nat.land va vb)
  | .bitXor a b => do
      let va ← evalConstExpr? env a
      let vb ← evalConstExpr? env b
      pure (Nat.xor va vb)
  | .bitNot a => do
      let va ← evalConstExpr? env a
      pure ((2 ^ 256 - 1) - va)
  | _ => none

def evalConstVal? (v : Val) : Option Nat := Id.run do
  let mut env : RBMap String Nat compare := RBMap.empty
  for stmt in v.pre do
    match stmt with
    | .letVar name rhs =>
        let some val := evalConstExpr? env rhs | return none
        env := env.insert name val
    | _ => return none
  evalConstExpr? env v.expr

def isStorageKeyCaptureExpr : Expr → Bool
  | .storage _
  | .logicalNot (.logicalNot (.storage _))
  | .structMember _ _ _
  | .logicalNot (.logicalNot (.structMember _ _ _))
  | .structMember2 _ _ _ _
  | .logicalNot (.logicalNot (.structMember2 _ _ _ _)) => true
  | _ => false

def isStorageKeyCaptureStmt : Stmt → Bool
  | .letVar _ e => isStorageKeyCaptureExpr e
  | _ => false

partial def assignmentIn (j : Json) : Bool :=
  match j with
  | .arr xs => xs.any assignmentIn
  | .obj o =>
      let kind := optStr j "nodeType"
      let op := optStr j "operator" |>.getD ""
      let own := kind == some "Assignment" ||
        (kind == some "UnaryOperation" && ["++", "--", "delete"].contains op)
      o.foldl (fun found _ child => found || assignmentIn child) own
  | _ => false

def atom (v : Val) : M Val := do
  if v.pre.isEmpty && isAtom v.expr then
    pure v
  else
    let n ← fresh
    pure { pre := v.pre.push (.letVar n v.expr), expr := .localVar n }

def bitsOf (ty : String) : Option Nat :=
  if ty == "uint256" || ty == "uint" then some 256
  else if ty == "bytes32" then some 256
  else if ty == "address" || ty == "address payable" || ty.startsWith "contract " then some 160
  else if ty.startsWith "enum " then some 8
  else if ty.startsWith "uint" then (ty.drop 4).toNat?
  else none

def signedBitsOf (ty : String) : Option Nat :=
  if ty == "int256" || ty == "int" then some 256
  else if ty.startsWith "int" && !ty.startsWith "int_const" then
    match (ty.drop 3).toNat? with
    | some n => if 8 ≤ n && n ≤ 256 && n % 8 == 0 then some n else none
    | none => none
  else none

def paramType (ty : String) : Option ParamType :=
  match ty with
  | "uint256" | "uint" => some .uint256
  | "int256" | "int" => some .int256
  | "address" | "address payable" => some .address
  | "bytes32" => some .bytes32
  | "bytes4" => some (.bytesN 4)
  | "bytes1" => some (.bytesN 1)
  | "bool" => some .bool
  | _ =>
      if ty.startsWith "contract " then some .address
      else if ty.startsWith "enum " then some (.uintN 8)
      else match signedBitsOf ty with
      | some n => if n < 256 then some (.intN n) else some .int256
      | none =>
          match bitsOf ty with
          | some n => if n != 256 && ty.startsWith "uint" then some (.uintN n) else none
          | none => none

def fixedBytesWidth? (ty : String) : Option Nat := do
  guard (ty.startsWith "bytes")
  let w ← (ty.drop 5).toNat?
  guard (1 ≤ w && w ≤ 32)
  some w

def localParamType (ty : String) : Option ParamType :=
  match paramType ty with
  | some p => some p
  | none =>
      match fixedBytesWidth? ty with
      | some 32 => some .bytes32
      | some w => some (.bytesN w)
      | none => none

def scalarArrayElement? (ty : String) : Option (String × ParamType × SolidityAbi.ScalarKind) := do
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
      else if elemStr == "bytes32" || elemStr == "bytes4" || elemStr == "int256" || elemStr == "int" then
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

def resolveEnumMembers (j : Json) (ty : String) : M (Array String) := do
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

def validateEnumTypeIfNeeded (j : Json) (ty : String) : M (Option Nat) := do
  if ty.startsWith "enum " then
    pure (some (← resolveEnumMembers j ty).size)
  else
    pure none

/-- Resolve the actual CompilationModel parameter type, including projected
struct members. A helper's Solidity return type need not be the type of the
root parameter expression that survives inlining. -/
def rootParamType? (env : Env) (name : String) : Option ParamType := do
  for (id, expression) in env.values do
    match expression with
    | .param candidate =>
        if candidate == name then
          if let some ty := env.scalarTy.find? id then return ty
    | _ => pure ()
  for (_, memory) in env.mems do
    for idx in [:memory.members.size] do
      let (member, ty) := memory.members[idx]!
      if s!"{memory.param}_{member}" == name || s!"{memory.param}_{idx}" == name then
        return ← paramType ty
  none

partial def publicVarGetterParamTypes (typeName : Json) : M (Array (String × Json) × Json) := do
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

def noteFn (fn : Json) : M Unit := do
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

/-- `if cond then [yes] else [no]` with single-statement branches. -/
def iteStmt (cond : Expr) (yes no : Stmt) : Stmt :=
  .ite cond [yes] [no]

def overflowPanic : Stmt := .panic .arithmeticOverflow

def divPanic : Stmt := .panic .divisionByZero

def maxSafeExponent (base bits : Nat) : Nat := Id.run do
  let limit := 2 ^ bits
  let mut acc := 1
  let mut exp := 0
  for _ in [:bits] do
    if acc * base < limit then
      acc := acc * base
      exp := exp + 1
  return exp

def maxSafeBase (exponent bits : Nat) : Nat := Id.run do
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

def isFullWordYulScalar : ParamType → Bool
  | .uint256 | .int256 | .bytes32 => true
  | _ => false

def isProvablyBoundedYulExpr (scalarType : ParamType) (expr : Expr) : Bool :=
  let bits? : Option Nat := match scalarType with
    | .bool => some 1
    | .uint8 => some 8
    | .uint16 => some 16
    | .uintN bits => some bits
    | .address => some 160
    | _ => none
  match bits? with
  | none => false
  | some bits =>
      match expr with
      | .byte _ _ => bits ≥ 8
      | .lt _ _ | .gt _ _ | .slt _ _ | .sgt _ _ | .eq _ _ | .logicalNot _ => bits ≥ 1
      | .bitAnd (.literal mask) _ | .bitAnd _ (.literal mask) => mask < 2 ^ bits
      | .shr (.literal shift) _ => shift ≥ 256 - bits
      | .mod _ (.literal m) => 0 < m && m ≤ 2 ^ bits
      | _ => false

/-! ## Layer I: Universal Expression & Type Helper MetaSpec -/

/-- **Layer I MetaSpec** for `ExprHelpers`:
1. Every sibling-order-independent expression is also an atom (`isOrderIndependentSibling e = true → isAtom e = true`).
2. `localParamType` extends `paramType` conservatively (`paramType ty = some p → localParamType ty = some p`).
3. Full-word Yul scalars (`isFullWordYulScalar p = true`) are exactly `.uint256`, `.int256`, or `.bytes32`. -/
structure ExprHelperMetaSpec (e : Expr) (ty : String) (p : ParamType) : Prop where
  sibling_implies_atom :
    isOrderIndependentSibling e = true → isAtom e = true
  localParamType_extends_paramType :
    ∀ q, paramType ty = some q → localParamType ty = some q
  fullWord_iff :
    isFullWordYulScalar p = true ↔ (p = .uint256 ∨ p = .int256 ∨ p = .bytes32)

/-- Universal theorem establishing `ExprHelperMetaSpec` for all `(e, ty, p)`. -/
theorem exprHelper_satisfies_metaSpec (e : Expr) (ty : String) (p : ParamType) :
    ExprHelperMetaSpec e ty p where
  sibling_implies_atom hSib := by
    cases e <;> simp_all [isOrderIndependentSibling, isAtom]
  localParamType_extends_paramType q hParam := by
    simp [localParamType, hParam]
  fullWord_iff := by
    cases p <;> simp [isFullWordYulScalar]

/-! ## Layer II: 1–3 Line Projection Corollaries -/

theorem orderIndependentSibling_isAtom (e : Expr)
    (h : isOrderIndependentSibling e = true) : isAtom e = true :=
  (exprHelper_satisfies_metaSpec e "" .uint256).sibling_implies_atom h

theorem localParamType_of_paramType (ty : String) (q : ParamType)
    (h : paramType ty = some q) : localParamType ty = some q :=
  (exprHelper_satisfies_metaSpec (.literal 0) ty q).localParamType_extends_paramType q h

theorem isFullWordYulScalar_iff (p : ParamType) :
    isFullWordYulScalar p = true ↔ (p = .uint256 ∨ p = .int256 ∨ p = .bytes32) :=
  (exprHelper_satisfies_metaSpec (.literal 0) "" p).fullWord_iff

theorem uint8_not_fullWordYulScalar : isFullWordYulScalar .uint8 = false := by
  decide

theorem address_not_fullWordYulScalar : isFullWordYulScalar .address = false := by
  decide

/-! ## Layer III: Concrete `by decide` Witnesses -/

theorem witness_isAtom_caller :
    isAtom .caller = true := by decide

theorem witness_isAtom_add_false :
    isAtom (.add (.literal 1) (.literal 2)) = false := by decide

theorem witness_isOrderIndependentSibling_localVar_false :
    isOrderIndependentSibling (.localVar "x") = false := by decide

theorem witness_isStorageKeyCaptureExpr_storage :
    isStorageKeyCaptureExpr (.storage "slot0") = true := by decide

theorem witness_isFullWordYulScalar_uint256 :
    isFullWordYulScalar .uint256 = true := by decide

end Compiler.CompilationModel.SolidityImport
