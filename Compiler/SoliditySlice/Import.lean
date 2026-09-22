import Lean
import Compiler.Sha256.Engine
import Compiler.SoliditySlice.Coverage
import Compiler.SoliditySlice.Report

/-!
Slice importer. Pinned `solc --standard-json` supplies the AST, declaration
ids, and `storageLayout`. This module selects one function, closes over the
definitions that resolution actually reaches, and elaborates a
`CompilationModel`. It does not interpret that model: execution is
`Denote.execStmt`, restricted by `stmtListCovered`.

The frontend is in the trust base. A covered model is not, by itself, a proof
that the model matches the Solidity source or solc's bytecode.
-/

open Lean Meta Elab Command

namespace Compiler.CompilationModel.SoliditySlice

def importerVersion : String := "solidity-slice-1"

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

private def leanStr (s : String) : String :=
  let escaped := s.foldl (init := "") fun acc c =>
    if c == '\"' || c == '\\' then acc ++ "\\" ++ c.toString else acc.push c
  "\"" ++ escaped ++ "\""

private def leanList (xs : Array String) : String :=
  "[" ++ String.intercalate ", " xs.toList ++ "]"

private def ex (body : String) : String :=
  s!"(Compiler.CompilationModel.Expr.{body})"

private def st (body : String) : String :=
  s!"(Compiler.CompilationModel.Stmt.{body})"

private structure Val where
  pre : Array String
  expr : String

private inductive SPath where
  | one (field key : String)
  | two (field k1 k2 : String)
  | outer (field k1 : String)

private inductive Ref where
  | expr (v : Val)
  | path (pre : Array String) (p : SPath)
  | mem (id : Nat) (pre : Array String)
  | state (name : String) (pre : Array String)

private structure MemParam where
  param : String
  structName : String
  members : Array (String × String)

private structure FieldInfo where
  name : String
  slot : Nat
  term : String
  memberNames : Array String
  opaqueNames : Array String

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
  typeString : String

private structure OpaqRec where
  field : String
  name : String
  solcType : String
  wordOffset : Nat
  byteOffset : Nat

private structure SrcParam where
  name : String
  id : Nat
  typeString : String
  location : String

private structure Env where
  nodes : RBMap Nat Json compare
  nodeFile : RBMap Nat String compare
  files : RBMap String ByteArray compare
  funs : RBMap Nat Json compare
  funContract : RBMap Nat String compare
  structs : RBMap Nat Json compare
  stateVars : RBMap Nat Json compare
  values : RBMap Nat String compare
  paths : RBMap Nat SPath compare
  mems : RBMap Nat MemParam compare
  fieldsByName : RBMap String FieldInfo compare
  included : Array FnRec
  projections : Array ProjRec
  opaqueMembers : Array OpaqRec
  referenced : Array String
  scalarTy : RBMap Nat String compare
  next : Nat
  stack : List Nat
  yulNames : RBMap String String compare
  currentFile : String

private def Env.init : Env where
  nodes := RBMap.empty
  nodeFile := RBMap.empty
  files := RBMap.empty
  funs := RBMap.empty
  funContract := RBMap.empty
  structs := RBMap.empty
  stateVars := RBMap.empty
  values := RBMap.empty
  paths := RBMap.empty
  mems := RBMap.empty
  fieldsByName := RBMap.empty
  included := #[]
  projections := #[]
  opaqueMembers := #[]
  referenced := #[]
  scalarTy := RBMap.empty
  next := 0
  stack := []
  yulNames := RBMap.empty
  currentFile := ""

abbrev M := StateT Env MetaM

private def mField (j : Json) (key : String) : M Json := liftM (field j key)
private def mStr (j : Json) : M String := liftM (str j)
private def mArr (j : Json) : M (Array Json) := liftM (arr j)
private def mBool (j : Json) : M Bool := liftM (bool j)
private def mNat (j : Json) : M Nat := liftM (flexNat j)
private def mKind (j : Json) : M String := liftM (nodeKind j)
private def mType (j : Json) : M String := liftM (typeString j)

private def failAt (j : Json) (why : String) : M α := do
  let env ← get
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
  match (← mField j "referencedDeclaration").getInt? with
  | .ok i => pure i
  | .error e => failAt j e

private def fresh : M String := do
  let n := (← get).next
  modify fun e => { e with next := e.next + 1 }
  pure s!"sliceTmp{n}"

private def isAtom (expr : String) : Bool :=
  expr.startsWith "(Compiler.CompilationModel.Expr.literal " ||
    expr.startsWith "(Compiler.CompilationModel.Expr.localVar " ||
    expr.startsWith "(Compiler.CompilationModel.Expr.param " ||
    expr == "(Compiler.CompilationModel.Expr.blockTimestamp)"

private def atom (v : Val) : M Val := do
  if v.pre.isEmpty && isAtom v.expr then
    pure v
  else
    let n ← fresh
    pure { pre := v.pre.push (st s!"letVar {leanStr n} {v.expr}"),
            expr := ex s!"localVar {leanStr n}" }

private def bitsOf (ty : String) : Option Nat :=
  if ty == "uint256" || ty == "uint" then some 256
  else if ty == "bytes32" then some 256
  else if ty == "address" then some 160
  else if ty.startsWith "uint" then (ty.drop 4).toNat?
  else none

private def paramTypeSyntax (ty : String) : Option String :=
  match ty with
  | "uint256" | "uint" => some "Compiler.CompilationModel.ParamType.uint256"
  | "address" => some "Compiler.CompilationModel.ParamType.address"
  | "bytes32" => some "Compiler.CompilationModel.ParamType.bytes32"
  | "bool" => some "Compiler.CompilationModel.ParamType.bool"
  | _ =>
      match bitsOf ty with
      | some n =>
          if n != 256 && ty.startsWith "uint" then
            some s!"(Compiler.CompilationModel.ParamType.uintN {n})"
          else none
      | none => none

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

private def noteProjection (p : ProjRec) : M Unit := do
  let env ← get
  unless env.projections.any (fun q => q.parameter == p.parameter && q.member == p.member) do
    modify fun e => { e with projections := e.projections.push p }

private def memberRead (pre : Array String) (path : SPath) (member : String) (at_ : Json) : M Val := do
  let (fieldName, exprBody) ← match path with
    | .one field key => pure (field, s!"structMember {leanStr field} {key} {leanStr member}")
    | .two field k1 k2 => pure (field, s!"structMember2 {leanStr field} {k1} {k2} {leanStr member}")
    | .outer _ _ => failAt at_ "member access on an incomplete mapping"
  let some info := (← get).fieldsByName.find? fieldName
    | failAt at_ s!"no storage layout for {fieldName}"
  if info.opaqueNames.contains member then
    failAt at_ s!"member {member} is opaque in this slice"
  unless info.memberNames.contains member do
    failAt at_ s!"member {member} is not a layout member of {fieldName}"
  markField fieldName
  pure { pre, expr := ex exprBody }

private def bin (op lhs rhs : String) : String :=
  ex (op ++ " " ++ lhs ++ " " ++ rhs)

private def lit (n : Nat) : String :=
  ex s!"literal {n}"

private def localName (name : String) : String :=
  ex ("localVar " ++ leanStr name)

private def letBind (name value : String) : String :=
  st ("letVar " ++ leanStr name ++ " " ++ value)

private def iteStmt (cond thenStmt elseStmt : String) : String :=
  st ("ite " ++ cond ++ " [" ++ thenStmt ++ "] [" ++ elseStmt ++ "]")

private def overflowPanic : String :=
  st "panic Verity.Core.PanicCode.arithmeticOverflow"

private def divPanic : String :=
  st "panic Verity.Core.PanicCode.divisionByZero"

mutual

private partial def lowerYul (j : Json) : M String := do
  match ← mKind j with
  | "YulIdentifier" =>
      let name ← mStr (← mField j "name")
      match (← get).yulNames.find? name with
      | some expr => pure expr
      | none => failAt j s!"unbound Yul identifier {name}"
  | "YulFunctionCall" =>
      let fname ← mStr (← mField (← mField j "functionName") "name")
      let args ← mArr (← mField j "arguments")
      let mut xs : Array String := #[]
      for arg in args do
        xs := xs.push (← lowerYul arg)
      match fname, xs with
      | "xor", #[a, b] => pure (ex s!"bitXor {a} {b}")
      | "mul", #[a, b] => pure (ex s!"mul {a} {b}")
      | "lt", #[a, b] => pure (ex s!"lt {a} {b}")
      | _, _ => failAt j s!"unsupported Yul builtin {fname}"
  | kind => failAt j s!"unsupported Yul node {kind}"

private partial def lowerExpr (j : Json) : M Val := do
  match ← mKind j with
  | "Literal" =>
      let raw := optStr j "value" |>.getD ""
      let some n := raw.toNat? | failAt j s!"unsupported literal {raw}"
      pure { pre := #[], expr := ex s!"literal {n}" }
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
      else if env.mems.contains n then
        pure (.mem n #[])
      else if let some decl := env.stateVars.find? n then
        pure (.state (← mStr (← mField decl "name")) #[])
      else
        failAt j s!"unresolved identifier {id}"
  | "IndexAccess" =>
      let base ← lowerRef (← mField j "baseExpression")
      let key ← atom (← lowerExpr (← mField j "indexExpression"))
      match base with
      | .state name pre =>
          let some info := (← get).fieldsByName.find? name
            | failAt j s!"no storage layout for {name}"
          markField name
          if info.term.contains "mappingStruct2" then
            pure (.path (pre ++ key.pre) (.outer name key.expr))
          else
            pure (.path (pre ++ key.pre) (.one name key.expr))
      | .path pre (.outer field k1) =>
          pure (.path (pre ++ key.pre) (.two field k1 key.expr))
      | _ => failAt j "index of a non-mapping"
  | "MemberAccess" =>
      let member ← mStr (← mField j "memberName")
      let base ← mField j "expression"
      if member == "timestamp" && (← mKind base) == "Identifier" &&
          optStr base "name" == some "block" then
        pure (.expr { pre := #[], expr := ex "blockTimestamp" })
      else if member == "max" then
        lowerTypeMax j base
      else
        match ← lowerRef base with
        | .path pre path =>
            pure (.expr (← memberRead pre path member j))
        | .mem id pre =>
            pure (.expr (← projectMember id pre member j))
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
  pure (.expr { pre := #[], expr := ex s!"literal {2 ^ bits - 1}" })

private partial def projectMember (id : Nat) (pre : Array String) (member : String) (at_ : Json) : M Val := do
  let some mem := (← get).mems.find? id | failAt at_ "unknown memory parameter"
  let some idx := mem.members.findIdx? (fun p => p.1 == member)
    | failAt at_ s!"{member} is not a member of {mem.structName}"
  let mut head : Nat := 0
  for i in [:idx] do
    let ty := mem.members[i]!.2
    if ty.endsWith "[]" then
      head := head + 1
    else if ty.startsWith "struct " || ty.any (· == '[') then
      failAt at_ s!"cannot place {member}; earlier member {mem.members[i]!.1} is {ty}"
    else
      head := head + 1
  let modelParam := s!"{mem.param}_{member}"
  noteProjection {
    parameter := mem.param, member := member, structName := mem.structName,
    headWord := head, modelParam := modelParam, typeString := mem.members[idx]!.2 }
  pure { pre, expr := ex s!"param {leanStr modelParam}" }

private partial def lowerBinary (j : Json) : M Val := do
  let op ← mStr (← mField j "operator")
  let left ← lowerExpr (← mField j "leftExpression")
  let right ← lowerExpr (← mField j "rightExpression")
  let common ← mStr (← mField (← mField j "commonType") "typeString")
  match op with
  | "+" =>
      let some bits := bitsOf common | failAt j s!"unsupported add type {common}"
      checkedAdd bits left right
  | "-" => checkedSub left right
  | "*" =>
      let some bits := bitsOf common | failAt j s!"unsupported mul type {common}"
      checkedMul bits left right
  | "/" => checkedDiv left right
  | "<" => cmp "lt" left right
  | ">" => cmp "gt" left right
  | "<=" => cmp "le" left right
  | ">=" => cmp "ge" left right
  | "==" => cmp "eq" left right
  | "!=" =>
      let v ← cmp "eq" left right
      pure { v with expr := ex s!"logicalNot {v.expr}" }
  | _ => failAt j s!"unsupported operator {op}"

private partial def checkedSub (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let ok := letBind dest (bin "sub" a.expr b.expr)
  let ite := iteStmt (bin "lt" a.expr b.expr) overflowPanic ok
  pure { pre := a.pre ++ b.pre |>.push ite, expr := localName dest }

private partial def checkedDiv (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let ok := letBind dest (bin "div" a.expr b.expr)
  let ite := iteStmt (bin "eq" b.expr (lit 0)) divPanic ok
  pure { pre := a.pre ++ b.pre |>.push ite, expr := localName dest }

private partial def checkedAdd (bits : Nat) (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let sum := bin "add" a.expr b.expr
  let ok := letBind dest sum
  let cond :=
    if bits == 256 then bin "lt" sum a.expr
    else bin "lt" (lit (2 ^ bits - 1)) sum
  pure { pre := a.pre ++ b.pre |>.push (iteStmt cond overflowPanic ok), expr := localName dest }

private partial def checkedMul (bits : Nat) (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  let dest ← fresh
  let prod := bin "mul" a.expr b.expr
  let ok := letBind dest prod
  if bits == 256 then
    let inner := iteStmt (bin "eq" (bin "div" prod a.expr) b.expr) ok overflowPanic
    let ite := iteStmt (bin "eq" a.expr (lit 0)) ok inner
    pure { pre := a.pre ++ b.pre |>.push ite, expr := localName dest }
  else
    let cond := bin "lt" (lit (2 ^ bits - 1)) prod
    pure { pre := a.pre ++ b.pre |>.push (iteStmt cond overflowPanic ok), expr := localName dest }

private partial def cmp (op : String) (left right : Val) : M Val := do
  let a ← atom left
  let b ← atom right
  pure { pre := a.pre ++ b.pre, expr := ex s!"{op} {a.expr} {b.expr}" }

private partial def lowerConditional (j : Json) : M Val := do
  let cond ← atom (← lowerExpr (← mField j "condition"))
  let yes ← lowerExpr (← mField j "trueExpression")
  let no ← lowerExpr (← mField j "falseExpression")
  let dest ← fresh
  let thenB := yes.pre.push (st s!"letVar {leanStr dest} {yes.expr}")
  let elseB := no.pre.push (st s!"letVar {leanStr dest} {no.expr}")
  let ite := st s!"ite {cond.expr} {leanList thenB} {leanList elseB}"
  pure { pre := cond.pre.push ite, expr := ex s!"localVar {leanStr dest}" }

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
    let bound := letBind dest (bin "bitAnd" a.expr (lit (2 ^ bits - 1)))
    pure { pre := a.pre.push bound, expr := localName dest }
  else
    pure v

private partial def lowerCall (j : Json) : M Val := do
  let kind ← mStr (← mField j "kind")
  if kind == "typeConversion" then
    lowerCast j
  else if kind == "functionCall" then
    let callee ← mField j "expression"
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
    let mut vals : Array Val := #[]
    if let some recv := receiver? then
      vals := vals.push (← lowerExpr recv)
    for arg in args do
      vals := vals.push (← lowerExpr arg)
    inlineFn fnId vals j
  else
    failAt j s!"unsupported call kind {kind}"

private partial def inlineFn (fnId : Nat) (args : Array Val) (at_ : Json) : M Val := do
  if (← get).stack.contains fnId then failAt at_ s!"recursive call {fnId}"
  let some fn := (← get).funs.find? fnId | failAt at_ s!"unresolved function {fnId}"
  let mods ← mArr (← mField fn "modifiers")
  unless mods.isEmpty do failAt fn "modifiers are outside this slice"
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do
    failAt at_ s!"call arity {args.size} does not match declaration {params.size}"
  let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless rets.size == 1 do failAt fn "only single-value helpers are inlined"
  let retName ← mStr (← mField rets[0]! "name")
  let savedYul := (← get).yulNames
  let savedFile := (← get).currentFile
  let frameFile := (← get).nodeFile.find? fnId |>.getD (← get).currentFile
  let frame := fnId :: (← get).stack
  modify fun e => { e with stack := frame, currentFile := frameFile }
  let mut pre : Array String := #[]
  let mut yul := savedYul
  for i in [:params.size] do
    let p := params[i]!
    let pname ← mStr (← mField p "name")
    let pid ← mNat (← mField p "id")
    let pty ← mType p
    let argNode ← argumentAt at_ i
    let argTy ← mType argNode
    let some arg := args[i]? | failAt at_ s!"missing argument {i}"
    let converted ← convert pty argTy arg at_
    let bound ← atom converted
    pre := pre ++ bound.pre
    modify fun e => { e with values := e.values.insert pid bound.expr }
    if pname != "" then
      yul := yul.insert pname bound.expr
  modify fun e => { e with yulNames := yul }
  noteFn fn
  let body ← mField fn "body"
  let stmts ← mArr (← mField body "statements")
  let result ← lowerHelper stmts retName
  modify fun e => { e with stack := e.stack.tail!, yulNames := savedYul, currentFile := savedFile }
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
  let mut pre : Array String := #[]
  let mut result : Option Val := none
  for s in stmts do
    if result.isSome then failAt s "statement after helper result"
    match ← mKind s with
    | "VariableDeclarationStatement" =>
        pre := pre ++ (← lowerLocal s)
    | "Return" =>
        result := some (← lowerExpr (← mField s "expression"))
    | "InlineAssembly" =>
        result := some (← lowerAssembly s retName)
    | kind => failAt s s!"unsupported helper statement {kind}"
  match result with
  | some v => pure { pre := pre ++ v.pre, expr := v.expr }
  | none => throwError "inlined helper did not return"

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
  unless retName == "" || vname == retName do
    failAt asg s!"Yul assigns {vname}, not the return name {retName}"
  pure { pre := #[], expr := ← lowerYul (← mField asg "value") }

private partial def lowerLocal (s : Json) : M (Array String) := do
  let decls ← mArr (← mField s "declarations")
  unless decls.size == 1 do failAt s "only a single declaration is supported"
  if decls[0]!.isNull then failAt s "empty declaration"
  let d := decls[0]!
  let name ← mStr (← mField d "name")
  unless name.all (fun c => c.isAlphanum || c == '_') && name != "" do
    failAt d s!"unsupported local name {name}"
  let id ← mNat (← mField d "id")
  let loc := optStr d "storageLocation" |>.getD "default"
  let init ← mField s "initialValue"
  if loc == "storage" then
    match ← lowerRef init with
    | .path pre path =>
        modify fun e => { e with paths := e.paths.insert id path }
        pure pre
    | _ => failAt s "storage local is not a resolved read path"
  else
    let v ← lowerExpr init
    modify fun e => { e with values := e.values.insert id (ex s!"localVar {leanStr name}") }
    let env ← get
    if env.yulNames.contains name then
      modify fun e => { e with yulNames := e.yulNames.insert name (ex s!"localVar {leanStr name}") }
    pure (v.pre.push (st s!"letVar {leanStr name} {v.expr}"))

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
    out := out.push { name, id, typeString := ty, location := loc }
    if ty.startsWith "struct " && (loc == "memory" || loc == "calldata") then
      let typeName ← mField p "typeName"
      let sid ← refInt typeName
      if sid < 0 then failAt p "builtin struct"
      let some decl := (← get).structs.find? sid.toNat | failAt p s!"unresolved struct {ty}"
      let members ← structMemberList decl
      let sname ← mStr (← mField decl "name")
      modify fun e =>
        let bound : MemParam := ⟨name, sname, members⟩
        { e with mems := e.mems.insert id bound }
    else if ty.startsWith "struct " then
      failAt p s!"unsupported location {loc} for {ty}"
    else
      let some tySyn := paramTypeSyntax ty | failAt p s!"unsupported parameter type {ty}"
      modify fun e =>
        let values := e.values.insert id (ex s!"param {leanStr name}")
        let scalarTy := e.scalarTy.insert id tySyn
        { e with values, scalarTy }
  pure out

private def lowerRoot (fn : Json) : M (Array String × Array SrcParam) := do
  let srcParams ← bindRoot fn
  let mods ← mArr (← mField fn "modifiers")
  unless mods.isEmpty do failAt fn "modifiers are outside this slice"
  let some _ := field? fn "body" | failAt fn "function has no body"
  let stmts ← mArr (← mField (← mField fn "body") "statements")
  let mut out : Array String := #[]
  for s in stmts do
    match ← mKind s with
    | "VariableDeclarationStatement" =>
        out := out ++ (← lowerLocal s)
    | "Return" =>
        let expr ← mField s "expression"
        if (← mKind expr) == "TupleExpression" then
          if ← mBool (← mField expr "isInlineArray") then
            failAt expr "inline arrays are outside this slice"
          let cs ← mArr (← mField expr "components")
          let mut pres : Array String := #[]
          let mut exprs : Array String := #[]
          for c in cs do
            if c.isNull then failAt expr "empty return component"
            let v ← atom (← lowerExpr c)
            pres := pres ++ v.pre
            exprs := exprs.push v.expr
          out := out ++ pres |>.push (st s!"returnValues {leanList exprs}")
        else
          let v ← atom (← lowerExpr expr)
          out := out ++ v.pre |>.push (st s!"returnValues {leanList #[v.expr]}")
    | kind => failAt s s!"unsupported statement {kind}"
  pure (out, srcParams)

private def keySyntax (ty : String) : MetaM String :=
  match ty with
  | "t_bytes32" => pure "Compiler.CompilationModel.MappingKeyType.bytes32"
  | "t_address" => pure "Compiler.CompilationModel.MappingKeyType.address"
  | "t_uint256" => pure "Compiler.CompilationModel.MappingKeyType.uint256"
  | _ => throwError "unsupported mapping key {ty}"

private def layoutType (types : Json) (id : String) : MetaM Json :=
  field types id

private def buildField (types item : Json) : M FieldInfo := do
  let name ← mStr (← mField item "label")
  let slot ← mNat (← mField item "slot")
  let typeId ← mStr (← mField item "type")
  let top ← liftM (layoutType types typeId)
  unless (← mStr (← mField top "encoding")) == "mapping" do
    throwError "storage field {name} is not a mapping"
  let key1 ← liftM (keySyntax (← mStr (← mField top "key")))
  let valueId ← mStr (← mField top "value")
  let value ← liftM (layoutType types valueId)
  let encoding ← mStr (← mField value "encoding")
  let (ctor, key2, structTy) ←
    if encoding == "mapping" then
      let key2 ← liftM (keySyntax (← mStr (← mField value "key")))
      let innerId ← mStr (← mField value "value")
      pure ("mappingStruct2", some key2, ← liftM (layoutType types innerId))
    else if encoding == "inplace" then
      pure ("mappingStruct", none, value)
    else
      throwError "unsupported mapping value encoding {encoding} for {name}"
  let members ← mArr (← mField structTy "members")
  let mut terms : Array String := #[]
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
      let packed :=
        if bits == 256 && bitOff == 0 then "none"
        else
          s!"some ({ "{ " }offset := {bitOff}, width := {bits}{ " }" } : Compiler.CompilationModel.PackedBits)"
      let sty :=
        if bits == 16 then "Compiler.CompilationModel.StructMemberType.uint16"
        else "Compiler.CompilationModel.StructMemberType.uint256"
      terms := terms.push
        s!"({ "{ " }name := {leanStr label}, ty := {sty}, wordOffset := {word}, packed := {packed}{ " }" } : Compiler.CompilationModel.StructMember)"
      names := names.push label
    else
      throwError "unsupported layout member {label} : {solcType}"
  let tyExpr :=
    match key2 with
    | some k2 =>
        s!"Compiler.CompilationModel.FieldType.mappingStruct2 {key1} {k2} {leanList terms}"
    | none =>
        s!"Compiler.CompilationModel.FieldType.mappingStruct {key1} {leanList terms}"
  let _ := ctor
  let term :=
    s!"({ "{ " }name := {leanStr name}, ty := {tyExpr}, slot := some {slot}{ " }" } : Compiler.CompilationModel.Field)"
  pure { name, slot, term, memberNames := names, opaqueNames := skipped }

private partial def index (file : String) (contract? : Option String) (j : Json) : M Unit := do
  match j with
  | .obj o =>
      if (field? j "nodeType").isSome then
        if let some idj := field? j "id" then
          let id ← mNat idj
          modify fun e => { e with nodes := e.nodes.insert id j, nodeFile := e.nodeFile.insert id file }
          match ← mKind j with
          | "FunctionDefinition" =>
              modify fun e =>
                let funs := e.funs.insert id j
                let funContract := e.funContract.insert id (contract?.getD "<free>")
                { e with funs, funContract }
          | "StructDefinition" =>
              modify fun e => { e with structs := e.structs.insert id j }
          | "VariableDeclaration" =>
              let isState := match field? j "stateVariable" with
                | some b => match b.getBool? with | .ok v => v | _ => false
                | none => false
              if isState then
                modify fun e => { e with stateVars := e.stateVars.insert id j }
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

private def verifyCompiler (compiler : System.FilePath) : MetaM Unit := do
  let output ←
    if System.Platform.isOSX then
      IO.Process.output { cmd := "/usr/bin/shasum", args := #["-a", "256", compiler.toString] }
    else
      IO.Process.output { cmd := "/usr/bin/sha256sum", args := #[compiler.toString] }
  unless output.exitCode == 0 && officialSolcSha256s.contains (output.stdout.take 64).toString do
    throwError "compiler checksum mismatch"

/-- Verity itself stores the importer next to its lakefile. A downstream package
stores that checkout at `.lake/packages/verity`. The digest must hash those
sources in either layout. -/
private def importerSourceRoot (pkgRoot : System.FilePath) : MetaM System.FilePath := do
  if ← (pkgRoot / "Compiler/SoliditySlice/Import.lean").pathExists then
    return pkgRoot
  let dep := pkgRoot / ".lake/packages/verity"
  if ← (dep / "Compiler/SoliditySlice/Import.lean").pathExists then
    return dep
  throwError "importer source missing: {pkgRoot / "Compiler/SoliditySlice/Import.lean"}"

private def moduleText (pkgRoot : System.FilePath) (rel : String) : MetaM String := do
  let path := pkgRoot / rel
  unless ← path.pathExists do throwError "importer source missing: {path}"
  IO.FS.readFile path

private def renderFn (f : FnRec) : String :=
  let tys := leanList (f.paramTypes.map leanStr)
  s!"({ "{ " }contract := {leanStr f.contract}, name := {leanStr f.name}, declId := {f.declId}, paramTypes := {tys}{ " }" } : Compiler.CompilationModel.SoliditySlice.SliceFunction)"

private def selectFunction (contract functionName : String) (paramTys : Array String) : M Json := do
  let env ← get
  let mut hits : Array Json := #[]
  let mut described : Array String := #[]
  for (id, fn) in env.funs do
    let name ← mStr (← mField fn "name")
    let owner := env.funContract.find? id |>.getD "<free>"
    let params ← mArr (← mField (← mField fn "parameters") "parameters")
    let mut tys : Array String := #[]
    for p in params do
      tys := tys.push (← mType p)
    if owner == contract && name == functionName then
      described := described.push (String.intercalate ", " tys.toList)
      if tys == paramTys then
        hits := hits.push fn
  if hits.size == 0 then
    throwError "no function {contract}.{functionName} matching [{String.intercalate ", " paramTys.toList}]; candidates: {described}"
  if hits.size > 1 then
    throwError "ambiguous function {contract}.{functionName}"
  let fn := hits[0]!
  let implemented ← match field? fn "implemented" with
    | some b => mBool b
    | none => pure true
  unless implemented do throwError "function is not implemented"
  pure fn

private def importSlice
    (pkgRoot projectRoot : System.FilePath) (entry contract functionName : String)
    (paramTys : Array String) (viaIR optimizer : Bool) (evm bytecodeHash : String)
    (runs : Nat) : MetaM (String × String × String) := do
  let compiler := pkgRoot / ".lake/solidity-import/solc-0.8.34"
  verifyCompiler compiler
  let versionOut ← IO.Process.output { cmd := compiler.toString, args := #["--version"] }
  unless versionOut.exitCode == 0 &&
      acceptedSolcBanners.contains versionOut.stdout.trimAscii.toString do
    throwError "compiler version mismatch"
  verifyCompiler compiler
  let remaps ← readRemappings projectRoot
  let sources ← collectSources projectRoot entry remaps RBMap.empty
  let mut fileBytes : RBMap String ByteArray compare := RBMap.empty
  let mut sourceObj : Array (String × Json) := #[]
  for (logical, text) in sources do
    fileBytes := fileBytes.insert logical (text.toUTF8)
    sourceObj := sourceObj.push (logical, Json.mkObj [("content", Json.str text)])
  let settings := Json.mkObj [
    ("evmVersion", Json.str evm),
    ("metadata", Json.mkObj [("bytecodeHash", Json.str bytecodeHash)]),
    ("optimizer", Json.mkObj [("enabled", Json.bool optimizer), ("runs", runs)]),
    ("outputSelection", Json.mkObj [("*", Json.mkObj [
      ("", Json.arr #[Json.str "ast"]),
      ("*", Json.arr #[Json.str "storageLayout"])])]),
    ("remappings", Json.arr (remaps.map fun p => Json.str s!"{p.1}={p.2}")),
    ("viaIR", Json.bool viaIR)]
  let input := Json.mkObj [
    ("language", Json.str "Solidity"),
    ("settings", settings),
    ("sources", Json.mkObj sourceObj.toList)]
  let output ← IO.Process.output
    { cmd := compiler.toString, args := #["--standard-json", "--no-import-callback"] }
    (some input.compress)
  unless output.exitCode == 0 do throwError "solc failed: {output.stderr}"
  verifyCompiler compiler
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
  for item in items do
    let label ← str (← field item "label")
    let typeId ← str (← field item "type")
    let top ← layoutType types typeId
    let encoding ← str (← field top "encoding")
    if encoding == "mapping" then
      let value ← layoutType types (← str (← field top "value"))
      let valueEnc ← str (← field value "encoding")
      let leaf ←
        if valueEnc == "mapping" then
          layoutType types (← str (← field value "value"))
        else
          pure value
      if (field? leaf "members").isSome then
        let (info, env') ← (buildField types item).run env
        env := env'
        env := { env with fieldsByName := env.fieldsByName.insert label info }
  let fn ← (selectFunction contract functionName paramTys).run' env
  env := { env with currentFile := entry }
  let ((body, srcParams), env2) ← (lowerRoot fn).run env
  env := env2
  let mut modelParams : Array String := #[]
  for p in srcParams do
    if env.mems.contains p.id then
      let some mem := env.mems.find? p.id | throwError "missing memory parameter {p.name}"
      let mut seen := false
      for (member, ty) in mem.members do
        if let some proj := env.projections.find? (fun q => q.parameter == p.name && q.member == member) then
          let some tySyn := paramTypeSyntax ty
            | throwError "unsupported projected type {ty}"
          modelParams := modelParams.push
            s!"({ "{ " }name := {leanStr proj.modelParam}, ty := {tySyn}{ " }" } : Compiler.CompilationModel.Param)"
          seen := true
      unless seen do throwError "struct parameter {p.name} was not read"
    else
      let some tySyn := env.scalarTy.find? p.id | throwError "missing parameter type"
      modelParams := modelParams.push
        s!"({ "{ " }name := {leanStr p.name}, ty := {tySyn}{ " }" } : Compiler.CompilationModel.Param)"
  let retSyntax ← (do
    let rets ← mArr (← mField (← mField fn "returnParameters") "parameters")
    let mut out : Array String := #[]
    for r in rets do
      let ty ← mType r
      let some tySyn := paramTypeSyntax ty | throwError "unsupported return type {ty}"
      out := out.push tySyn
    pure out) |>.run' env
  let mutability ← str (← field fn "stateMutability")
  let isView := mutability == "view" || mutability == "pure"
  let mut fieldTerms : Array (Nat × String) := #[]
  for name in env.referenced do
    let some info := env.fieldsByName.find? name | throwError "missing field {name}"
    fieldTerms := fieldTerms.push (info.slot, info.term)
  let sortedFields := (fieldTerms.qsort (fun a b => a.1 < b.1)).map (·.2)
  let fnTerm :=
    s!"({ "{ " }name := {leanStr functionName}, params := {leanList modelParams}, returnType := none, returns := {leanList retSyntax}, isView := {isView}, body := {leanList body}{ " }" } : Compiler.CompilationModel.FunctionSpec)"
  let modelName := contract ++ "_" ++ functionName ++ "_slice"
  let modelTerm :=
    s!"({ "{ " }name := {leanStr modelName}, constructor := none, fields := {leanList sortedFields}, functions := [{fnTerm}]{ " }" } : Compiler.CompilationModel.CompilationModel)"
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
  let mut projTerms : Array String := #[]
  for proj in env.projections do
    let ignored :=
      match env.mems.toList.find? (fun pair => pair.2.param == proj.parameter) with
      | some (_, mem) => mem.members.filterMap fun pair =>
          if pair.1 == proj.member then none else some (leanStr pair.1)
      | none => #[]
    projTerms := projTerms.push
      s!"({ "{ " }parameter := {leanStr proj.parameter}, member := {leanStr proj.member}, structName := {leanStr proj.structName}, headWord := {proj.headWord}, modelParam := {leanStr proj.modelParam}, ignoredMembers := {leanList ignored}{ " }" } : Compiler.CompilationModel.SoliditySlice.SliceProjection)"
  let mut opaqueTerms : Array String := #[]
  for o in env.opaqueMembers do
    if env.referenced.contains o.field then
      opaqueTerms := opaqueTerms.push
        s!"({ "{ " }field := {leanStr o.field}, name := {leanStr o.name}, solcType := {leanStr o.solcType}, wordOffset := {o.wordOffset}, byteOffset := {o.byteOffset}{ " }" } : Compiler.CompilationModel.SoliditySlice.OpaqueMember)"
  let sourceRoot ← importerSourceRoot pkgRoot
  let importer ← moduleText sourceRoot "Compiler/SoliditySlice/Import.lean"
  let coverage ← moduleText sourceRoot "Compiler/SoliditySlice/Coverage.lean"
  let reportSrc ← moduleText sourceRoot "Compiler/SoliditySlice/Report.lean"
  let mut digestInput := s!"{importerVersion}\n{solcLongVersion}\n{contract}\n{functionName}\n"
  for ty in paramTys do
    digestInput := digestInput ++ ty ++ "\n"
  digestInput := digestInput ++ settings.compress ++ "\n"
  for (logical, text) in sources.toList.mergeSort (fun a b => a.1 < b.1) do
    digestInput := digestInput ++ logical ++ "\n" ++ text ++ "\n"
  digestInput := digestInput ++ importer ++ "\n" ++ coverage ++ "\n" ++ reportSrc
  let digest := sha256Hex digestInput.toUTF8
  let solcSha :=
    if System.Platform.isOSX then officialSolcSha256s[1]! else officialSolcSha256s[0]!
  let reportTerm :=
    s!"({ "{ " }importerVersion := {leanStr importerVersion}, solcLongVersion := {leanStr solcLongVersion}, solcSha256 := {leanStr solcSha}, settingsJson := {leanStr settings.compress}, sourceDigest := {leanStr digest}, contract := {leanStr contract}, rootFunction := {leanStr functionName}, includedFunctions := {leanList (env.included.map renderFn)}, excludedFunctions := {leanList (sortedExcluded.map renderFn)}, projections := {leanList projTerms}, storageFields := {leanList (env.referenced.map leanStr)}, opaqueMembers := {leanList opaqueTerms}, observesPanicPayload := false{ " }" } : Compiler.CompilationModel.SoliditySlice.SliceReport)"
  pure (modelTerm, reportTerm, digest)

private def elabDef (name : Name) (type body : String) : CommandElabM Unit := do
  let cmd := s!"def {name} : {type} :=\n{body}"
  match Parser.runParserCategory (← getEnv) `command cmd "<solidity-slice>" with
  | .error e => throwError e
  | .ok stx => elabCommand stx

syntax (name := sliceImportCmd)
  "solidity_slice_import " ident
  " slice_root " str " slice_entry " str " slice_contract " str " slice_function " str
  " slice_param_tys " "[" str,* "]"
  " slice_solc " str " slice_via_ir " ident " slice_evm " str
  " slice_optimizer " ident " slice_runs " num " slice_bytecode_hash " str : command

@[command_elab sliceImportCmd]
def elabSliceImport : CommandElab := fun stx => do
  let saved ← getEnv
  try
    if debug.skipKernelTC.get (← getOptions) then
      throwError "kernel checking must be enabled"
    let aliasName := stx[1].getId
    let rootArg := stx[3].isStrLit?.get!
    let entryPath := stx[5].isStrLit?.get!
    let contractName := stx[7].isStrLit?.get!
    let functionName := stx[9].isStrLit?.get!
    let paramTys := stx[12].getSepArgs.map fun s => s.isStrLit?.get!
    let solcArg := stx[15].isStrLit?.get!
    unless solcArg == solcLongVersion do
      throwError "this importer is pinned to {solcLongVersion}"
    let useIR := stx[17].getId == `true
    let evmVersion := stx[19].isStrLit?.get!
    let optimize := stx[21].getId == `true
    let some runCount := stx[23].isNatLit? | throwError "optimizer runs must be a nat"
    let hashMode := stx[25].isStrLit?.get!
    unless useIR || stx[17].getId == `false do throwError "viaIR must be true or false"
    unless optimize || stx[21].getId == `false do throwError "optimizer must be true or false"
    let authored ← IO.FS.realPath (← getFileName)
    let mut pkg := authored.parent.getD "."
    while !(← (pkg / "lakefile.lean").pathExists) do
      let some parent := pkg.parent | throwError "package root not found"
      if parent == pkg then throwError "package root not found"
      pkg := parent
    let project := if ("/" ++ rootArg).startsWith "//" || rootArg.startsWith "/" then
      System.FilePath.mk rootArg else pkg / rootArg
    let (modelTerm, reportTerm, digest) ← liftTermElabM <|
      importSlice pkg project entryPath contractName functionName paramTys useIR optimize evmVersion hashMode runCount
    let ns := (← getCurrNamespace) ++ aliasName
    elabDef (ns ++ `model) "Compiler.CompilationModel.CompilationModel" modelTerm
    elabDef (ns ++ `report) "Compiler.CompilationModel.SoliditySlice.SliceReport" reportTerm
    elabDef (ns ++ `sourceDigest) "String" (leanStr digest)
    let covered := s!"theorem {ns ++ `sliceCovered} : Compiler.CompilationModel.SoliditySlice.modelSliceCovered {ns ++ `model} = true := by decide"
    match Parser.runParserCategory (← getEnv) `command covered "<solidity-slice>" with
    | .error e => throwError e
    | .ok stx => elabCommand stx
    if (← get).messages.hasErrors then
      throwError "slice import failed to check"
  catch e =>
    setEnv saved
    throw e

end Compiler.CompilationModel.SoliditySlice
