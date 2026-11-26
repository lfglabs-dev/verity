import Lean
import Compiler.Hex
import Compiler.SolidityImport.ExprHelpers
import Compiler.SolidityImport.Lowering.EvalOrderHazards

/-!
# Static Admission and Dominance Bound Proof for Yul Memory-Array Length Shrinks

Admits inline assembly blocks of the exact shape `assembly { mstore(x, n) }` where:
1. `x` resolves via `externalReferences` to a local `T[] memory` variable (`T` a static
   value type, `elemStructId = none`, not a function parameter) holding an unaliased
   `new T[](cap)` allocation on every path reaching the assembly block;
2. `n` is an untyped unsigned Yul literal or an unshadowed `uint*` Solidity scalar
   local, parameter, or constant whose stack word is provably clean in both legacy and
   via-IR pipelines; and
3. `n ≤ oldLength(x)` is proved statically on every execution path reaching the block
   (via literal/constant bounds, reflexivity, dominating `require` / reverting-`if` /
   enclosing-`if` guards, checked `uint256` subtraction, `min` ternaries, or monotonic
   `while` / `for` loop induction).

Any `n` that is not provably `≤ oldLength(x)` (including array growth or unguarded inputs)
fails closed at import with a located diagnostic. Non-array targets, offset targets, and
other Yul statements or opcodes return `none` so the caller preserves its existing
diagnostics unchanged.
-/

open Lean

namespace Compiler.CompilationModel.SolidityImport.Lowering

/-- Symbolic unsigned quantity (`0 ≤ v < 2^256`) tracked by the forward dominance prover. -/
inductive KnownArrayLen where
  /-- Exact compile-time constant word `k < 2^256`. -/
  | const (k : Nat)
  /-- Clean unsigned value of Solidity scalar `declId` at SSA write-generation `ver`. -/
  | sym (declId : Nat) (ver : Nat)
  /-- Length of unmodified array/bytes variable `declId` at SSA write-generation `ver`. -/
  | arrayLen (declId : Nat) (ver : Nat)
  /-- Fresh `new T[](...)` allocation with an opaque unsigned capacity (`0 ≤ len` holds). -/
  | nonNeg
  deriving BEq, DecidableEq, Repr

/-- Parsed length operand `n` of `mstore(x, n)`. -/
inductive ShrinkLenSpec where
  | lit (k : Nat)
  | decl (declId : Nat)
  deriving BEq, DecidableEq, Repr

/-- Outcome of the path-sensitive `n ≤ oldLength(x)` analysis at `asmId`. -/
inductive ShrinkVerdict where
  | proved
  | unaliasedAllocRequired
  | unprovedBound
  deriving BEq, DecidableEq, Repr

private def pairCmp (a b : Nat × Nat) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | ord => ord

/-- Forward abstract state over a function body. Every unhandled write bumps `ver` via
`bodyAssignedIds`, invalidating stale facts automatically (fail-closed by default). -/
private structure ShrinkState where
  nextVer : Nat := 1
  nextAlloc : Nat := 1
  ver : RBMap Nat Nat compare := RBMap.empty
  clean : RBMap (Nat × Nat) Bool pairCmp := RBMap.empty
  constVal : RBMap (Nat × Nat) Nat pairCmp := RBMap.empty
  lowerConst : RBMap (Nat × Nat) Nat pairCmp := RBMap.empty
  upperBounds : RBMap (Nat × Nat) (List KnownArrayLen) pairCmp := RBMap.empty
  arrays : RBMap Nat (Nat × KnownArrayLen) compare := RBMap.empty

private def ShrinkState.verOf (st : ShrinkState) (declId : Nat) : Nat :=
  st.ver.find? declId |>.getD 0

private def ShrinkState.isClean (st : ShrinkState) (declId : Nat) : Bool :=
  st.clean.find? (declId, st.verOf declId) |>.getD false

private def ShrinkState.bumpDirty (st : ShrinkState) (declId : Nat) : ShrinkState × Nat :=
  let v := st.nextVer
  ({ st with nextVer := v + 1, ver := st.ver.insert declId v }, v)

private def ShrinkState.bumpManyDirty (st : ShrinkState) (ids : List Nat) : ShrinkState :=
  ids.foldl (fun acc d => (acc.bumpDirty d).1) st

private def dedupBounds (bs : List KnownArrayLen) : List KnownArrayLen :=
  bs.foldl (fun acc b => if acc.contains b || b == .nonNeg then acc else acc ++ [b]) []

private def transitiveExtras (st : ShrinkState) (b : KnownArrayLen) : List KnownArrayLen :=
  match b with
  | .sym d v =>
      let own := st.upperBounds.find? (d, v) |>.getD []
      let cList := match st.constVal.find? (d, v) with | some c => [.const c] | none => []
      cList ++ own
  | _ => []

private def ShrinkState.addUpperBound (st : ShrinkState) (key : Nat × Nat)
    (b : KnownArrayLen) : ShrinkState :=
  if b == .nonNeg then st else
  let cur := st.upperBounds.find? key |>.getD []
  let merged := dedupBounds (cur ++ [b] ++ transitiveExtras st b)
  { st with upperBounds := st.upperBounds.insert key merged }

private def ShrinkState.addLowerConst (st : ShrinkState) (key : Nat × Nat) (k : Nat) :
    ShrinkState :=
  let cur := st.lowerConst.find? key |>.getD 0
  { st with lowerConst := st.lowerConst.insert key (max cur k) }

private partial def unparen (j : Json) : Json :=
  if optStr j "nodeType" == some "TupleExpression" &&
      (field? j "isInlineArray").bind (·.getBool?.toOption) == some false then
    match field? j "components" with
    | some (.arr #[inner]) => if inner.isNull then j else unparen inner
    | _ => j
  else j

private partial def collectVarDecls (acc : RBMap Nat Json compare) :
    Json → RBMap Nat Json compare
  | j@(.obj fields) =>
      let acc :=
        if optStr j "nodeType" == some "VariableDeclaration" then
          match (field? j "id").bind (·.getNat?.toOption) with
          | some id => acc.insert id j
          | none => acc
        else acc
      fields.foldl (fun m _ v => collectVarDecls m v) acc
  | .arr xs => xs.foldl collectVarDecls acc
  | _ => acc

private def declTypeString? (decl : Json) : Option String :=
  (field? decl "typeDescriptions").bind (optStr · "typeString")

/-- Recognizes only a built-in elementary `uint8`..`uint256` type (`typeString == "uint<N>"`
and `typeIdentifier == "t_uint<N>"` with `8 ≤ N ≤ 256` and `N % 8 == 0`), rejecting any
`UserDefinedValueType` such as `type uint0256 is uint8;` or `type uint9 is int256;`. -/
private def elemUintBits? (node : Json) : Option Nat := do
  let td ← field? node "typeDescriptions"
  let ty ← optStr td "typeString"
  let tid ← optStr td "typeIdentifier"
  guard (ty.startsWith "uint")
  let bits ← bitsOf ty
  guard (8 ≤ bits && bits ≤ 256 && bits % 8 == 0)
  guard (ty == s!"uint{bits}" && tid == s!"t_uint{bits}")
  pure bits

private def declUintBits? (decls : RBMap Nat Json compare) (declId : Nat) : Option Nat :=
  decls.find? declId >>= elemUintBits?

/-- Ensures a `BinaryOperation` or `UnaryOperation` uses the built-in EVM operator rather
than a user-defined `using { f as op }` binding (`function` AST field absent or null). -/
private def isBuiltinOp (j : Json) : Bool :=
  (field? j "function").all (·.isNull)

private def parseNumberLiteral? (j : Json) : Option Nat := do
  let j := unparen j
  guard (optStr j "nodeType" == some "Literal")
  guard (optStr j "kind" == some "number")
  let sub := field? j "subdenomination"
  guard (sub.isNone || sub == some Json.null)
  let raw ← optStr j "value"
  let n ← Compiler.Hex.parseHexNat? raw <|> raw.toNat?
  guard (n < 2 ^ 256)
  pure n

private def identDeclId? (j : Json) : Option Nat := do
  let j := unparen j
  guard (optStr j "nodeType" == some "Identifier")
  let r ← (field? j "referencedDeclaration").bind (·.getInt?.toOption)
  guard (r ≥ 0)
  pure r.toNat

private def isNonNegIntOrUint256Type (j : Json) : Bool :=
  elemUintBits? j == some 256 ||
    match declTypeString? j with
    | some ty => ty.startsWith "int_const " && !ty.startsWith "int_const -"
    | none => false

private def isNonNegUintExpr (j : Json) : Bool :=
  (elemUintBits? j).isSome || isNonNegIntOrUint256Type j

mutual
  private partial def evalUintConstAst? (env : Env) (seen : List Nat) (j : Json) : Option Nat :=
    let j := unparen j
    if let some n := parseNumberLiteral? j then
      some n
    else if let some refId := identDeclId? j then do
      guard (!seen.contains refId)
      let cDecl ← env.numericConstants.find? refId
      evalUintConstantDecl? env (refId :: seen) cDecl
    else if optStr j "nodeType" == some "BinaryOperation" && isBuiltinOp j &&
        isNonNegIntOrUint256Type j then do
      let l := (field? j "leftExpression").getD Json.null
      let r := (field? j "rightExpression").getD Json.null
      guard (isNonNegIntOrUint256Type l && isNonNegIntOrUint256Type r)
      let a ← evalUintConstAst? env seen l
      let b ← evalUintConstAst? env seen r
      let res ← match optStr j "operator" |>.getD "" with
        | "+" => some (a + b)
        | "-" => if b ≤ a then some (a - b) else none
        | "*" => some (a * b)
        | "/" => if b > 0 then some (a / b) else none
        | "%" => if b > 0 then some (a % b) else none
        | _ => none
      guard (res < 2 ^ 256)
      pure res
    else none

  private partial def evalUintConstantDecl? (env : Env) (seen : List Nat) (cDecl : Json) :
      Option Nat := do
    let bits ← elemUintBits? cDecl
    let k ← evalUintConstAst? env seen ((field? cDecl "value").getD Json.null)
    guard (k < 2 ^ bits)
    pure k
end

private def parseYulNumberLit? (node : Json) : Option Nat := do
  guard (optStr node "nodeType" == some "YulLiteral")
  guard (optStr node "kind" == some "number" && optStr node "type" == some "")
  let raw ← optStr node "value"
  let n ← Compiler.Hex.parseHexNat? raw <|> raw.toNat?
  guard (n < 2 ^ 256)
  pure n

private def resolveExtRefPlain? (refs : Array Json) (src : String) : Option Nat := do
  let ref ← refs.find? (fun r => optStr r "src" == some src)
  guard ((field? ref "isOffset").bind (·.getBool?.toOption) == some false)
  guard ((field? ref "isSlot").bind (·.getBool?.toOption) == some false)
  guard (field? ref "suffix").isNone
  guard ((field? ref "valueSize").bind (·.getNat?.toOption) == some 1)
  (field? ref "declaration").bind (·.getNat?.toOption)

private partial def exprReferencedDecls : Json → List Nat
  | j@(.obj fields) =>
      let own := match (field? j "referencedDeclaration").bind (·.getInt?.toOption) with
        | some r => if r ≥ 0 then [r.toNat] else []
        | none => []
      fields.foldl (fun acc _ v => acc ++ exprReferencedDecls v) own
  | .arr xs => xs.toList.flatMap exprReferencedDecls
  | _ => []

/-- Every reference to `arrId` in `j` (Solidity `Identifier`s and Yul `externalReferences`). -/
private partial def countAllArrayRefs (arrId : Nat) : Json → Nat
  | j@(.obj fields) =>
      let ownIdent :=
        if optStr j "nodeType" == some "Identifier" &&
            (field? j "referencedDeclaration").bind (·.getInt?.toOption) ==
              some (Int.ofNat arrId) then
          1
        else 0
      let ownYul :=
        if optStr j "nodeType" == some "InlineAssembly" then
          match field? j "externalReferences" with
          | some (.arr refs) =>
              refs.foldl (fun c r =>
                if (field? r "declaration").bind (·.getNat?.toOption) == some arrId then c + 1
                else c) 0
          | _ => 0
        else 0
      fields.foldl (fun acc _ v => acc + countAllArrayRefs arrId v) (ownIdent + ownYul)
  | .arr xs => xs.foldl (fun acc v => acc + countAllArrayRefs arrId v) 0
  | _ => 0

/-- References to `arrId` that only index an element (`arr[i]`) or read `arr.length`
without escaping or rebinding the array pointer. -/
private partial def countSafeArrayRefs (arrId : Nat) : Json → Nat
  | j@(.obj fields) =>
      let kind := optStr j "nodeType"
      if kind == some "IndexAccess" && !(field? j "indexExpression" |>.getD Json.null).isNull then
        let base := (field? j "baseExpression").map unparen |>.getD Json.null
        let idx := (field? j "indexExpression").getD Json.null
        let baseSafe := if identDeclId? base == some arrId then 1 else countSafeArrayRefs arrId base
        baseSafe + countSafeArrayRefs arrId idx
      else if kind == some "MemberAccess" && optStr j "memberName" == some "length" &&
          (field? j "referencedDeclaration").all (·.isNull) then
        let base := (field? j "expression").map unparen |>.getD Json.null
        if identDeclId? base == some arrId then 1 else countSafeArrayRefs arrId base
      else
        fields.foldl (fun acc _ v => acc + countSafeArrayRefs arrId v) 0
  | .arr xs => xs.foldl (fun acc v => acc + countSafeArrayRefs arrId v) 0
  | _ => 0

private def arrayStaysUnaliasedIn (arrId : Nat) (j : Json) : Bool :=
  countAllArrayRefs arrId j == countSafeArrayRefs arrId j

private def filterUnaliasedArrays (st : ShrinkState) (j : Json) : ShrinkState :=
  let kept := st.arrays.fold (init := RBMap.empty) fun acc arrId entry =>
    if arrayStaysUnaliasedIn arrId j then acc.insert arrId entry else acc
  { st with arrays := kept }

private def evalConstNat? (env : Env) (st : ShrinkState) (j : Json) : Option Nat :=
  let j := unparen j
  if let some n := parseNumberLiteral? j then
    some n
  else if let some d := identDeclId? j then
    if st.isClean d then
      st.constVal.find? (d, st.verOf d)
    else if let some cDecl := env.numericConstants.find? d then
      evalUintConstantDecl? env [d] cDecl
    else none
  else none

private def evalSymExpr? (env : Env) (decls : RBMap Nat Json compare) (paramIds : List Nat)
    (st : ShrinkState) (j : Json) : Option KnownArrayLen :=
  let j := unparen j
  if let some k := evalConstNat? env st j then
    some (.const k)
  else if let some d := identDeclId? j then do
    let _ ← declUintBits? decls d
    guard (st.isClean d)
    pure (.sym d (st.verOf d))
  else if optStr j "nodeType" == some "MemberAccess" && optStr j "memberName" == some "length" &&
      (field? j "referencedDeclaration").all (·.isNull) then do
    let aId ← identDeclId? ((field? j "expression").getD Json.null)
    if let some (_, known) := st.arrays.find? aId then
      guard (known != .nonNeg)
      pure known
    else if paramIds.contains aId && st.verOf aId == 0 &&
        ((env.scalarArrays.find? aId).isSome || (env.fixedMemArrays.find? aId).isSome ||
          (env.calldataBytes.find? aId).isSome) then
      pure (.arrayLen aId 0)
    else none
  else none

/-- Decides whether `lhs ≤ rhs` is proved in abstract state `st`. -/
private def knownLe (st : ShrinkState) (lhs rhs : KnownArrayLen) : Bool :=
  let constLe (c1 : Nat) (r : KnownArrayLen) : Bool :=
    c1 == 0 ||
      match r with
      | .const c2 => decide (c1 ≤ c2)
      | .sym d2 v2 =>
          (st.constVal.find? (d2, v2)).any (c1 ≤ ·) ||
            (st.lowerConst.find? (d2, v2)).any (c1 ≤ ·)
      | _ => false
  match lhs with
  | .const c1 => constLe c1 rhs
  | .sym d1 v1 =>
      st.clean.find? (d1, v1) == some true &&
        (lhs == rhs ||
          (st.constVal.find? (d1, v1)).any (constLe · rhs) ||
          (st.upperBounds.find? (d1, v1) |>.getD []).any fun ub =>
            ub == rhs ||
              match ub with
              | .const c1 => constLe c1 rhs
              | _ => false)
  | .arrayLen _ _ => lhs == rhs
  | .nonNeg => false

private def isNewDynArrayCall? (j : Json) : Option Json := do
  let j := unparen j
  guard (optStr j "nodeType" == some "FunctionCall" && optStr j "kind" == some "functionCall")
  let names ← (field? j "names").bind (·.getArr?.toOption)
  guard names.isEmpty
  let callee := (field? j "expression").getD Json.null
  guard (optStr callee "nodeType" == some "NewExpression")
  let args ← (field? j "arguments").bind (·.getArr?.toOption)
  guard (args.size == 1)
  pure args[0]!

private def recordLessOrEq (env : Env) (decls : RBMap Nat Json compare) (paramIds : List Nat)
    (st : ShrinkState) (lhsNode rhsNode : Json) (strict : Bool) : ShrinkState :=
  let lhsSym? := evalSymExpr? env decls paramIds st lhsNode
  let rhsSym? := evalSymExpr? env decls paramIds st rhsNode
  let st := match lhsSym?, rhsSym? with
    | some (.sym d1 v1), some rhsSym =>
        let st1 := st.addUpperBound (d1, v1) rhsSym
        match strict, rhsSym with
        | true, .const k => if k > 0 then st1.addUpperBound (d1, v1) (.const (k - 1)) else st1
        | _, _ => st1
    | _, _ => st
  match lhsSym?, rhsSym? with
  | some (.const c), some (.sym d2 v2) =>
      st.addLowerConst (d2, v2) (if strict then c + 1 else c)
  | _, _ => st

private partial def assumeTrue (env : Env) (decls : RBMap Nat Json compare) (paramIds : List Nat)
    (st : ShrinkState) (cond : Json) : ShrinkState :=
  let cond := unparen cond
  if optStr cond "nodeType" == some "BinaryOperation" && isBuiltinOp cond then
    let op := optStr cond "operator" |>.getD ""
    let l := (field? cond "leftExpression").getD Json.null
    let r := (field? cond "rightExpression").getD Json.null
    match op with
    | "&&" => assumeTrue env decls paramIds (assumeTrue env decls paramIds st l) r
    | "<=" => recordLessOrEq env decls paramIds st l r false
    | "<" => recordLessOrEq env decls paramIds st l r true
    | ">=" => recordLessOrEq env decls paramIds st r l false
    | ">" => recordLessOrEq env decls paramIds st r l true
    | "==" =>
        recordLessOrEq env decls paramIds
          (recordLessOrEq env decls paramIds st l r false) r l false
    | "!=" =>
        match evalConstNat? env st l, evalSymExpr? env decls paramIds st r with
        | some 0, some (.sym d v) => st.addLowerConst (d, v) 1
        | _, _ =>
            match evalSymExpr? env decls paramIds st l, evalConstNat? env st r with
            | some (.sym d v), some 0 => st.addLowerConst (d, v) 1
            | _, _ => st
    | _ => st
  else st

private partial def assumeFalse (env : Env) (decls : RBMap Nat Json compare) (paramIds : List Nat)
    (st : ShrinkState) (cond : Json) : ShrinkState :=
  let cond := unparen cond
  if optStr cond "nodeType" == some "UnaryOperation" && isBuiltinOp cond &&
      optStr cond "operator" == some "!" then
    assumeTrue env decls paramIds st ((field? cond "subExpression").getD Json.null)
  else if optStr cond "nodeType" == some "BinaryOperation" && isBuiltinOp cond then
    let op := optStr cond "operator" |>.getD ""
    let l := (field? cond "leftExpression").getD Json.null
    let r := (field? cond "rightExpression").getD Json.null
    match op with
    | "||" => assumeFalse env decls paramIds (assumeFalse env decls paramIds st l) r
    | ">" => recordLessOrEq env decls paramIds st l r false
    | ">=" => recordLessOrEq env decls paramIds st l r true
    | "<" => recordLessOrEq env decls paramIds st r l false
    | "<=" => recordLessOrEq env decls paramIds st r l true
    | "!=" =>
        recordLessOrEq env decls paramIds
          (recordLessOrEq env decls paramIds st l r false) r l false
    | "==" =>
        match evalConstNat? env st l, evalSymExpr? env decls paramIds st r with
        | some 0, some (.sym d v) => st.addLowerConst (d, v) 1
        | _, _ =>
            match evalSymExpr? env decls paramIds st l, evalConstNat? env st r with
            | some (.sym d v), some 0 => st.addLowerConst (d, v) 1
            | _, _ => st
    | _ => st
  else st

/-- Whether `j` contains a control-flow transfer (`break`, `continue`, or a `return` when
`!allowReturn`) that could bypass later statements in the same block without exiting the
analyzed function. -/
private partial def containsFlowEscape (allowReturn : Bool) : Json → Bool
  | j@(.obj fields) =>
      let kind := optStr j "nodeType"
      kind == some "Break" || kind == some "Continue" ||
        (!allowReturn && kind == some "Return") ||
        fields.foldl (fun acc _ v => acc || containsFlowEscape allowReturn v) false
  | .arr xs => xs.any (containsFlowEscape allowReturn)
  | _ => false

/-- Pure syntactic definite-exit check (`return` when `allowReturn = true` for the analyzed
function itself, `revert`, `revert(...)`, Yul `revert`, or an internal modifier-free callee
whose body definitely reverts with `allowReturn = false`). -/
private partial def stmtDefinitelyExits (env : Env) (fuel : Nat) (allowReturn : Bool)
    (s : Json) : Bool :=
  if fuel == 0 || s.isNull then false else
  match optStr s "nodeType" with
  | some "Return" => allowReturn
  | some "RevertStatement" => true
  | some "Block" | some "UncheckedBlock" =>
      match field? s "statements" with
      | some (.arr xs) => Id.run do
          for child in xs do
            if stmtDefinitelyExits env (fuel - 1) allowReturn child then
              return true
            if containsFlowEscape allowReturn child then
              return false
          return false
      | _ => false
  | some "IfStatement" =>
      let t := (field? s "trueBody").getD Json.null
      let f := (field? s "falseBody").getD Json.null
      !f.isNull && stmtDefinitelyExits env (fuel - 1) allowReturn t &&
        stmtDefinitelyExits env (fuel - 1) allowReturn f
  | some "InlineAssembly" =>
      match (field? s "AST").bind (field? · "statements") with
      | some (.arr xs) =>
          match xs.back? with
          | some last =>
              optStr last "nodeType" == some "YulExpressionStatement" &&
                ((field? last "expression").bind (field? · "functionName")).bind
                  (optStr · "name") == some "revert"
          | none => false
      | _ => false
  | some "ExpressionStatement" =>
      let expr := (field? s "expression").getD Json.null
      if optStr expr "nodeType" != some "FunctionCall" ||
          optStr expr "kind" != some "functionCall" then
        false
      else
        let callee := (field? expr "expression").getD Json.null
        if optStr callee "nodeType" == some "Identifier" && optStr callee "name" == some "revert" &&
            (field? callee "referencedDeclaration").bind (·.getInt?.toOption) == some (-19) then
          true
        else
          match (field? callee "referencedDeclaration").bind (·.getInt?.toOption) with
          | some refId =>
              if refId < 0 || isLibraryDelegateCall callee then false else
              let targetId? :=
                if optStr callee "nodeType" == some "Identifier" then
                  match env.funContractId.find? refId.toNat with
                  | some cid =>
                      if env.linearizedBases.contains cid then
                        resolveInContracts env env.linearizedBases.toList refId.toNat
                      else some refId.toNat
                  | none => some refId.toNat
                else none
              match targetId?.bind env.funs.find? with
              | some fn =>
                  let vis := optStr fn "visibility" |>.getD ""
                  let noMods := ((field? fn "modifiers").bind (·.getArr?.toOption)).any (·.isEmpty)
                  noMods && (vis == "internal" || vis == "private" || vis == "public") &&
                    stmtDefinitelyExits env (fuel - 1) false ((field? fn "body").getD Json.null)
              | none => false
          | none => false
  | _ => false

private partial def stripUintCastPure (j : Json) (bits : Nat) : Json :=
  let j := unparen j
  if optStr j "nodeType" == some "FunctionCall" && optStr j "kind" == some "typeConversion" then
    if elemUintBits? j == some bits then
      match field? j "arguments" with
      | some (.arr #[arg]) => stripUintCastPure arg bits
      | _ => j
    else j
  else j

/-- Recognizes a standalone `+1` step (`v++`, `++v`, `v += 1`, `v = v + 1`, `v = 1 + v`). -/
private partial def isUnitIncrementStmt (st : Json) (varId bits : Nat)
    (inUnchecked : Bool) : Option Bool :=
  match optStr st "nodeType" with
  | some "UncheckedBlock" =>
      match field? st "statements" with
      | some (.arr #[only]) => isUnitIncrementStmt only varId bits true
      | _ => none
  | some "Block" =>
      match field? st "statements" with
      | some (.arr #[only]) => isUnitIncrementStmt only varId bits inUnchecked
      | _ => none
  | some "ExpressionStatement" =>
      let e := unparen ((field? st "expression").getD Json.null)
      match optStr e "nodeType" with
      | some "UnaryOperation" =>
          if isBuiltinOp e && optStr e "operator" == some "++" &&
              identDeclId? ((field? e "subExpression").getD Json.null) == some varId then
            some inUnchecked
          else none
      | some "Assignment" =>
          if identDeclId? ((field? e "leftHandSide").getD Json.null) != some varId then none else
          let op := optStr e "operator" |>.getD ""
          let rhs := (field? e "rightHandSide").getD Json.null
          if op == "+=" then
            if parseNumberLiteral? rhs == some 1 then some inUnchecked else none
          else if op == "=" then
            let r := stripUintCastPure rhs bits
            if optStr r "nodeType" == some "BinaryOperation" && isBuiltinOp r &&
                optStr r "operator" == some "+" then
              let l := (field? r "leftExpression").getD Json.null
              let rr := (field? r "rightExpression").getD Json.null
              if (identDeclId? l == some varId && parseNumberLiteral? rr == some 1) ||
                  (identDeclId? rr == some varId && parseNumberLiteral? l == some 1) then
                some inUnchecked
              else none
            else none
          else none
      | _ => none
  | _ => none

/-- Maximum number of `+1` increments to `varId` along any single-iteration path through `s`,
or `none` if `s` performs any non-`+1` write to `varId`. Also tracks whether any step ran
inside `unchecked`. -/
private partial def maxUnitIncrementsIn (s : Json) (varId bits : Nat)
    (inUnchecked : Bool) : Option (Nat × Bool) :=
  if !(bodyAssignedIds s).contains varId then
    some (0, false)
  else if let some u := isUnitIncrementStmt s varId bits inUnchecked then
    some (1, u)
  else
    match optStr s "nodeType" with
    | some "Block" | some "UncheckedBlock" =>
        let subUnchk := inUnchecked || optStr s "nodeType" == some "UncheckedBlock"
        match field? s "statements" with
        | some (.arr xs) =>
            xs.foldlM (init := (0, false)) fun (accN, accU) child => do
              let (cN, cU) ← maxUnitIncrementsIn child varId bits subUnchk
              pure (accN + cN, accU || cU)
        | _ => none
    | some "IfStatement" => do
        let cond := (field? s "condition").getD Json.null
        guard (!(bodyAssignedIds cond).contains varId)
        let (tN, tU) ←
          maxUnitIncrementsIn ((field? s "trueBody").getD Json.null) varId bits inUnchecked
        let fBody := (field? s "falseBody").getD Json.null
        let (fN, fU) ← if fBody.isNull then some (0, false)
          else maxUnitIncrementsIn fBody varId bits inUnchecked
        pure (max tN fN, tU || fU)
    | _ => none

/-- Extracts `(countDeclId, boundNode)` pairs from top-level `&&`-conjuncts of the form
`count < bound` or `bound > count`. -/
private partial def strictLessConjuncts (cond : Json) : List (Nat × Json) :=
  let cond := unparen cond
  if optStr cond "nodeType" == some "BinaryOperation" && isBuiltinOp cond then
    let op := optStr cond "operator" |>.getD ""
    let l := (field? cond "leftExpression").getD Json.null
    let r := (field? cond "rightExpression").getD Json.null
    if op == "&&" then
      strictLessConjuncts l ++ strictLessConjuncts r
    else if op == "<" then
      match identDeclId? l with
      | some id => [(id, r)]
      | none => []
    else if op == ">" then
      match identDeclId? r with
      | some id => [(id, l)]
      | none => []
    else []
  else []

/-- Whether every `+1` step to `varId` in `s` occurs inside the `trueBody` of an `IfStatement`
whose `&&`-condition contains `varId < boundSym` (with no write to `varId` before that check). -/
private partial def allIncrementsGuardedBy (env : Env) (decls : RBMap Nat Json compare)
    (paramIds : List Nat) (st : ShrinkState) (loopWrites : List Nat) (s : Json)
    (varId bits : Nat) (boundSym : KnownArrayLen) (guarded : Bool) : Bool :=
  if !(bodyAssignedIds s).contains varId then true
  else if (isUnitIncrementStmt s varId bits false).isSome then guarded
  else
    match optStr s "nodeType" with
    | some "Block" | some "UncheckedBlock" =>
        match field? s "statements" with
        | some (.arr xs) =>
            let (_, ok) := xs.foldl (init := (false, true)) fun (wroteVar, accOk) child =>
              let childOk :=
                allIncrementsGuardedBy env decls paramIds st loopWrites child varId bits boundSym
                  (guarded && !wroteVar)
              (wroteVar || (bodyAssignedIds child).contains varId, accOk && childOk)
            ok
        | _ => false
    | some "IfStatement" =>
        let cond := (field? s "condition").getD Json.null
        if !(bodyAssignedIds cond).isEmpty || statefulCallIn cond env then false else
        let condGuards := (strictLessConjuncts cond).any fun (cid, bNode) =>
          cid == varId && (exprReferencedDecls bNode).all (!loopWrites.contains ·) &&
            evalSymExpr? env decls paramIds st bNode == some boundSym
        let tOk := allIncrementsGuardedBy env decls paramIds st loopWrites
          ((field? s "trueBody").getD Json.null) varId bits boundSym (guarded || condGuards)
        let fBody := (field? s "falseBody").getD Json.null
        let fOk := fBody.isNull ||
          allIncrementsGuardedBy env decls paramIds st loopWrites fBody varId bits boundSym guarded
        tOk && fOk
    | _ => false

private partial def jsonContainsNodeId (targetId : Nat) : Json → Bool
  | j@(.obj fields) =>
      (field? j "id").bind (·.getNat?.toOption) == some targetId ||
        fields.foldl (fun acc _ v => acc || jsonContainsNodeId targetId v) false
  | .arr xs => xs.any (jsonContainsNodeId targetId)
  | _ => false

/-- Parses an increasing zero-based unit-step `for` header `for (uintN i = 0; i < B; i++)`
(or pre-declared `for (i = 0; i < B; i++)`), returning `(counterId, counterBits, stepUnchk, B)`. -/
private def zeroBasedUnitForHeader? (decls : RBMap Nat Json compare) (s : Json) :
    Option (Nat × Nat × Bool × Json) := do
  let init := (field? s "initializationExpression").getD Json.null
  let counterId ←
    if optStr init "nodeType" == some "VariableDeclarationStatement" then do
      let ds ← (field? init "declarations").bind (·.getArr?.toOption)
      guard (ds.size == 1 && !ds[0]!.isNull)
      let cid ← (field? ds[0]! "id").bind (·.getNat?.toOption)
      let _ ← declUintBits? decls cid
      let startVal := (field? init "initialValue").getD Json.null
      guard (!startVal.isNull && parseNumberLiteral? startVal == some 0)
      pure cid
    else if optStr init "nodeType" == some "ExpressionStatement" then do
      let e := (field? init "expression").getD Json.null
      guard (optStr e "nodeType" == some "Assignment" && optStr e "operator" == some "=")
      let cid ← identDeclId? ((field? e "leftHandSide").getD Json.null)
      let _ ← declUintBits? decls cid
      guard (parseNumberLiteral? ((field? e "rightHandSide").getD Json.null) == some 0)
      pure cid
    else none
  let bits ← declUintBits? decls counterId
  let cond := unparen ((field? s "condition").getD Json.null)
  guard (optStr cond "nodeType" == some "BinaryOperation" && isBuiltinOp cond &&
    optStr cond "operator" == some "<")
  guard (identDeclId? ((field? cond "leftExpression").getD Json.null) == some counterId)
  let boundNode := (field? cond "rightExpression").getD Json.null
  let body := (field? s "body").getD Json.null
  guard (!(bodyAssignedIds body).contains counterId)
  let loopExpr ← (field? s "loopExpression").filter (!·.isNull)
  let stepUnchk ←
    isUnitIncrementStmt (Json.mkObj [("nodeType", Json.str "ExpressionStatement"),
      ("expression", (field? loopExpr "expression").getD Json.null)]) counterId bits false
  pure (counterId, bits, stepUnchk, boundNode)

private def deriveRhsScalarFacts (env : Env) (decls : RBMap Nat Json compare) (paramIds : List Nat)
    (st : ShrinkState) (bits : Nat) (inUnchecked : Bool) (rhs : Json) :
    Option Nat × List KnownArrayLen × Bool := Id.run do
  let rhs := unparen rhs
  let const? := evalConstNat? env st rhs
  -- A `uint256` EVM stack slot has no bits above bit 255, whereas narrow `uintN` (`N < 256`)
  -- stack slots can retain dirty upper bits after casts, shifts, bitwise ops, helper calls, or
  -- Yul writes across solc pipelines unless initialized from a small constant or clean narrow var.
  let cleanNarrowCopy :=
    match identDeclId? rhs with
    | some srcId => st.isClean srcId && (declUintBits? decls srcId).any (· ≤ bits)
    | none => false
  let cleanOk := bits == 256 || const?.any (· < 2 ^ bits) || cleanNarrowCopy
  if !cleanOk then return (none, [], false)
  let mut ubs : List KnownArrayLen := []
  if let some k := const? then
    if bits == 256 || k < 2 ^ bits then
      return (some k, [.const k], true)
  if let some sym := evalSymExpr? env decls paramIds st rhs then
    ubs := ubs ++ [sym] ++ transitiveExtras st sym
  if !inUnchecked && bits == 256 && optStr rhs "nodeType" == some "BinaryOperation" &&
      isBuiltinOp rhs && optStr rhs "operator" == some "-" then
    let lhsSub := (field? rhs "leftExpression").getD Json.null
    let rhsSub := (field? rhs "rightExpression").getD Json.null
    if isNonNegUintExpr rhs && isNonNegUintExpr lhsSub && isNonNegUintExpr rhsSub then
      if let some sym := evalSymExpr? env decls paramIds st lhsSub then
        ubs := ubs ++ [sym] ++ transitiveExtras st sym
  if optStr rhs "nodeType" == some "Conditional" then
    let c := unparen ((field? rhs "condition").getD Json.null)
    let tE := (field? rhs "trueExpression").getD Json.null
    let fE := (field? rhs "falseExpression").getD Json.null
    if optStr c "nodeType" == some "BinaryOperation" && isBuiltinOp c then
      let op := optStr c "operator" |>.getD ""
      let cL := (field? c "leftExpression").getD Json.null
      let cR := (field? c "rightExpression").getD Json.null
      let tSym? := evalSymExpr? env decls paramIds st tE
      let fSym? := evalSymExpr? env decls paramIds st fE
      let cLSym? := evalSymExpr? env decls paramIds st cL
      let cRSym? := evalSymExpr? env decls paramIds st cR
      if (op == "<" || op == "<=") && tSym?.isSome && fSym?.isSome &&
          tSym? == cLSym? && fSym? == cRSym? then
        if let (some sA, some sB) := (tSym?, fSym?) then
          ubs := ubs ++ [sA, sB] ++ transitiveExtras st sA ++ transitiveExtras st sB
      if (op == ">" || op == ">=") && tSym?.isSome && fSym?.isSome &&
          tSym? == cRSym? && fSym? == cLSym? then
        if let (some sA, some sB) := (tSym?, fSym?) then
          ubs := ubs ++ [sA, sB] ++ transitiveExtras st sA ++ transitiveExtras st sB
  return (none, dedupBounds ubs, true)

private def mergeBranchStates (decls : RBMap Nat Json compare) (base yesSt noSt : ShrinkState) :
    ShrinkState :=
  let nextVer := max yesSt.nextVer noSt.nextVer
  let nextAlloc := max yesSt.nextAlloc noSt.nextAlloc
  let mergedArrays := yesSt.arrays.fold (init := RBMap.empty) fun acc arrId entry =>
    if noSt.arrays.find? arrId == some entry then acc.insert arrId entry else acc
  decls.fold (init := { base with nextVer, nextAlloc, arrays := mergedArrays })
    fun acc d _ =>
      let v0 := base.verOf d
      let vY := yesSt.verOf d
      let vN := noSt.verOf d
      if vY == v0 && vN == v0 then
        let uY := yesSt.upperBounds.find? (d, v0) |>.getD []
        let uN := noSt.upperBounds.find? (d, v0) |>.getD []
        let uBoth := uY.filter uN.contains
        let lY := yesSt.lowerConst.find? (d, v0) |>.getD 0
        let lN := noSt.lowerConst.find? (d, v0) |>.getD 0
        let acc := { acc with upperBounds := acc.upperBounds.insert (d, v0) uBoth }
        if min lY lN > 0 then
          { acc with lowerConst := acc.lowerConst.insert (d, v0) (min lY lN) }
        else
          { acc with lowerConst := acc.lowerConst.erase (d, v0) }
      else
        let vM := acc.nextVer
        let cBoth := yesSt.clean.find? (d, vY) == some true &&
          noSt.clean.find? (d, vN) == some true
        let kBoth := match yesSt.constVal.find? (d, vY), noSt.constVal.find? (d, vN) with
          | some k1, some k2 => if k1 == k2 && cBoth then some k1 else none
          | _, _ => none
        let uY := yesSt.upperBounds.find? (d, vY) |>.getD []
        let uN := noSt.upperBounds.find? (d, vN) |>.getD []
        let uBoth := if cBoth then uY.filter uN.contains else []
        let acc := { acc with
          nextVer := vM + 1
          ver := acc.ver.insert d vM
          clean := acc.clean.insert (d, vM) cBoth
          upperBounds := acc.upperBounds.insert (d, vM) uBoth }
        match kBoth with
        | some k => { acc with constVal := acc.constVal.insert (d, vM) k }
        | none => acc

/-- Pure syntactic check for a 1-statement `assembly { mstore(<ident>, <arg>) }` block. -/
def isYulSingleIdentMstoreBlock (asm : Json) : Bool :=
  if optStr asm "nodeType" != some "InlineAssembly" then false else
  match (field? asm "AST").bind (field? · "statements") with
  | some (.arr #[stmt]) =>
      if optStr stmt "nodeType" != some "YulExpressionStatement" then false else
      let expr := (field? stmt "expression").getD Json.null
      optStr expr "nodeType" == some "YulFunctionCall" &&
        ((field? expr "functionName").bind (optStr · "name")) == some "mstore" &&
        match field? expr "arguments" with
        | some (.arr #[targetNode, _]) => optStr targetNode "nodeType" == some "YulIdentifier"
        | _ => false
  | _ => false

/-- Parse an earlier `InlineAssembly` block as `(arrDeclId, ShrinkLenSpec)` if it is also
a memory-array length `mstore`. -/
private def parseIntermediateShrink? (env : Env) (decls : RBMap Nat Json compare)
    (paramIds : List Nat) (asm : Json) : Option (Nat × ShrinkLenSpec) := do
  guard (isYulSingleIdentMstoreBlock asm)
  let #[stmt] ← ((field? asm "AST").bind (field? · "statements")).bind (·.getArr?.toOption)
    | none
  let expr := (field? stmt "expression").getD Json.null
  let #[targetNode, lenNode] ← (field? expr "arguments").bind (·.getArr?.toOption) | none
  let refs ← (field? asm "externalReferences").bind (·.getArr?.toOption)
  let arrId ← resolveExtRefPlain? refs (optStr targetNode "src" |>.getD "")
  guard (!paramIds.contains arrId)
  let arr ← env.scalarArrays.find? arrId
  guard (arr.inMemory && arr.elemStructId.isNone)
  if let some k := parseYulNumberLit? lenNode then
    pure (arrId, .lit k)
  else if optStr lenNode "nodeType" == some "YulIdentifier" then do
    let nId ← resolveExtRefPlain? refs (optStr lenNode "src" |>.getD "")
    if let some cDecl := env.numericConstants.find? nId then do
      let k ← evalUintConstantDecl? env [nId] cDecl
      pure (arrId, .lit k)
    else do
      let _ ← declUintBits? decls nId
      pure (arrId, .decl nId)
  else none

private def evalShrinkLenSpec? (st : ShrinkState) : ShrinkLenSpec → Option KnownArrayLen
  | .lit k => some (.const k)
  | .decl d => if st.isClean d then some (.sym d (st.verOf d)) else none

private partial def stepShrinkStmt (env : Env) (decls : RBMap Nat Json compare)
    (paramIds : List Nat) (asmId targetArrId : Nat) (targetLen : ShrinkLenSpec)
    (inUnchecked : Bool) (st : ShrinkState) (s : Json) :
    ShrinkState × Option ShrinkVerdict :=
  if s.isNull then (st, none)
  else if (field? s "id").bind (·.getNat?.toOption) == some asmId then
    match st.arrays.find? targetArrId with
    | none => (st, some .unaliasedAllocRequired)
    | some (_, capLen) =>
        match evalShrinkLenSpec? st targetLen with
        | some lhs =>
            if knownLe st lhs capLen then (st, some .proved)
            else (st, some .unprovedBound)
        | none => (st, some .unprovedBound)
  else
    match optStr s "nodeType" with
    | some "Block" | some "UncheckedBlock" =>
        let subUnchk := inUnchecked || optStr s "nodeType" == some "UncheckedBlock"
        match field? s "statements" with
        | some (.arr xs) =>
            xs.foldl (init := (st, none)) fun (curSt, found?) child =>
              match found? with
              | some _ => (curSt, found?)
              | none =>
                  stepShrinkStmt env decls paramIds asmId targetArrId targetLen
                    subUnchk curSt child
        | _ => (st.bumpManyDirty (bodyAssignedIds s), none)
    | some "VariableDeclarationStatement" =>
        let init := (field? s "initialValue").getD Json.null
        let st := if init.isNull then st else filterUnaliasedArrays st init
        let ds := match field? s "declarations" with
          | some (.arr xs) => xs
          | _ => #[]
        if ds.size == 1 && !ds[0]!.isNull then
          let d := ds[0]!
          let dId? := (field? d "id").bind (·.getNat?.toOption)
          let loc := optStr d "storageLocation" |>.getD "default"
          match dId? with
          | none => (st.bumpManyDirty (bodyAssignedIds s), none)
          | some dId =>
              if loc == "memory" then
                if let some capArg := isNewDynArrayCall? init then
                  if countAllArrayRefs dId init == 0 then
                    let capSym :=
                      if (bodyAssignedIds capArg).isEmpty && !statefulCallIn capArg env then
                        (evalSymExpr? env decls paramIds st capArg).getD .nonNeg
                      else .nonNeg
                    let st := st.bumpManyDirty (dId :: bodyAssignedIds s)
                    let alloc := st.nextAlloc
                    ({ st with nextAlloc := alloc + 1,
                               arrays := st.arrays.insert dId (alloc, capSym) }, none)
                  else
                    let stBumped := st.bumpManyDirty (dId :: bodyAssignedIds s)
                    ({ stBumped with arrays := stBumped.arrays.erase dId }, none)
                else
                  let stBumped := st.bumpManyDirty (dId :: bodyAssignedIds s)
                  ({ stBumped with arrays := stBumped.arrays.erase dId }, none)
              else if loc == "default" then
                match declUintBits? decls dId with
                | some bits =>
                    if init.isNull then
                      let (st1, v) := st.bumpDirty dId
                      let st2 := { st1 with
                        clean := st1.clean.insert (dId, v) true
                        constVal := st1.constVal.insert (dId, v) 0
                        upperBounds := st1.upperBounds.insert (dId, v) [.const 0] }
                      (st2, none)
                    else if (bodyAssignedIds init).isEmpty && !statefulCallIn init env then
                      let (const?, ubs, cleanOk) :=
                        deriveRhsScalarFacts env decls paramIds st bits inUnchecked init
                      let (st1, v) := st.bumpDirty dId
                      let st2 := { st1 with
                        clean := st1.clean.insert (dId, v) cleanOk
                        upperBounds := st1.upperBounds.insert (dId, v) ubs }
                      let st3 := match const? with
                        | some k => { st2 with constVal := st2.constVal.insert (dId, v) k }
                        | none => st2
                      (st3, none)
                    else
                      (st.bumpManyDirty (dId :: bodyAssignedIds s), none)
                | none => (st.bumpManyDirty (dId :: bodyAssignedIds s), none)
              else
                (st.bumpManyDirty (dId :: bodyAssignedIds s), none)
        else
          ((filterUnaliasedArrays st s).bumpManyDirty (bodyAssignedIds s), none)
    | some "ExpressionStatement" =>
        let e := unparen ((field? s "expression").getD Json.null)
        if optStr e "nodeType" == some "Assignment" && optStr e "operator" == some "=" then
          let lhs := (field? e "leftHandSide").getD Json.null
          let rhs := (field? e "rightHandSide").getD Json.null
          if let some lhsId := identDeclId? lhs then
            if let some capArg := isNewDynArrayCall? rhs then
              if !paramIds.contains lhsId &&
                  (env.scalarArrays.find? lhsId).any
                    (fun a => a.inMemory && a.elemStructId.isNone) &&
                  countAllArrayRefs lhsId rhs == 0 then
                let st := filterUnaliasedArrays st rhs
                let capSym :=
                  if (bodyAssignedIds capArg).isEmpty && !statefulCallIn capArg env then
                    (evalSymExpr? env decls paramIds st capArg).getD .nonNeg
                  else .nonNeg
                let st := st.bumpManyDirty (lhsId :: bodyAssignedIds s)
                let alloc := st.nextAlloc
                ({ st with nextAlloc := alloc + 1,
                           arrays := st.arrays.insert lhsId (alloc, capSym) }, none)
              else
                ((filterUnaliasedArrays st s).bumpManyDirty (lhsId :: bodyAssignedIds s), none)
            else if let some bits := declUintBits? decls lhsId then
              let st := filterUnaliasedArrays st s
              if (bodyAssignedIds rhs).isEmpty && !statefulCallIn rhs env then
                let (const?, ubs, cleanOk) :=
                  deriveRhsScalarFacts env decls paramIds st bits inUnchecked rhs
                let (st1, v) := st.bumpDirty lhsId
                let st2 := { st1 with
                  clean := st1.clean.insert (lhsId, v) cleanOk
                  upperBounds := st1.upperBounds.insert (lhsId, v) ubs }
                let st3 := match const? with
                  | some k => { st2 with constVal := st2.constVal.insert (lhsId, v) k }
                  | none => st2
                (st3, none)
              else
                (st.bumpManyDirty (lhsId :: bodyAssignedIds s), none)
            else
              ((filterUnaliasedArrays st s).bumpManyDirty (lhsId :: bodyAssignedIds s), none)
          else
            ((filterUnaliasedArrays st s).bumpManyDirty (bodyAssignedIds s), none)
        else if optStr e "nodeType" == some "FunctionCall" &&
            optStr e "kind" == some "functionCall" then
          let callee := (field? e "expression").getD Json.null
          let isRequire := optStr callee "nodeType" == some "Identifier" &&
            optStr callee "name" == some "require" &&
            (field? callee "referencedDeclaration").bind (·.getInt?.toOption) == some (-18)
          let st := filterUnaliasedArrays st s
          if isRequire then
            match (field? e "arguments").bind (·.getArr?.toOption) with
            | some args =>
                if args.size ≥ 1 && (bodyAssignedIds s).isEmpty && !statefulCallIn s env then
                  (assumeTrue env decls paramIds st args[0]!, none)
                else
                  (st.bumpManyDirty (bodyAssignedIds s), none)
            | none => (st.bumpManyDirty (bodyAssignedIds s), none)
          else
            (st.bumpManyDirty (bodyAssignedIds s), none)
        else
          ((filterUnaliasedArrays st s).bumpManyDirty (bodyAssignedIds s), none)
    | some "InlineAssembly" =>
        match parseIntermediateShrink? env decls paramIds s with
        | some (arr2Id, len2Spec) =>
            match st.arrays.find? arr2Id, evalShrinkLenSpec? st len2Spec with
            | some (alloc2, cap2), some lhs2 =>
                if knownLe st lhs2 cap2 then
                  let (st1, _) := st.bumpDirty arr2Id
                  ({ st1 with arrays := st1.arrays.insert arr2Id (alloc2, lhs2) }, none)
                else
                  let stFiltered := filterUnaliasedArrays st s
                  ({ stFiltered with arrays := stFiltered.arrays.erase arr2Id }
                    |>.bumpManyDirty (arr2Id :: inlineAssemblyAssignedIds s), none)
            | _, _ =>
                ((filterUnaliasedArrays st s).bumpManyDirty (inlineAssemblyAssignedIds s), none)
        | none =>
            ((filterUnaliasedArrays st s).bumpManyDirty (inlineAssemblyAssignedIds s), none)
    | some "IfStatement" =>
        let cond := (field? s "condition").getD Json.null
        let tBody := (field? s "trueBody").getD Json.null
        let fBody := (field? s "falseBody").getD Json.null
        let stAfterCond := filterUnaliasedArrays st cond
        let pureCond := (bodyAssignedIds cond).isEmpty && !statefulCallIn cond env
        let stBase := if pureCond then stAfterCond
          else stAfterCond.bumpManyDirty (bodyAssignedIds cond)
        let stTrueIn := if pureCond then assumeTrue env decls paramIds stBase cond else stBase
        let (stTrueOut, vTrue?) :=
          stepShrinkStmt env decls paramIds asmId targetArrId targetLen inUnchecked stTrueIn tBody
        if vTrue?.isSome then (stTrueOut, vTrue?) else
        let stFalseSeed := { stBase with nextVer := stTrueOut.nextVer,
                                         nextAlloc := stTrueOut.nextAlloc }
        let stFalseIn :=
          if pureCond then assumeFalse env decls paramIds stFalseSeed cond else stFalseSeed
        let (stFalseOut, vFalse?) :=
          if fBody.isNull then (stFalseIn, none)
          else stepShrinkStmt env decls paramIds asmId targetArrId targetLen
            inUnchecked stFalseIn fBody
        if vFalse?.isSome then (stFalseOut, vFalse?) else
        let tExits := stmtDefinitelyExits env 8 true tBody
        let fExits := !fBody.isNull && stmtDefinitelyExits env 8 true fBody
        if tExits && !fExits then (stFalseOut, none)
        else if !tExits && fExits then (stTrueOut, none)
        else if tExits && fExits then (stTrueOut, none)
        else (mergeBranchStates decls stBase stTrueOut stFalseOut, none)
    | some "WhileStatement" =>
        let cond := (field? s "condition").getD Json.null
        let body := (field? s "body").getD Json.null
        let writes := bodyAssignedIds s
        if jsonContainsNodeId asmId s then
          let loopIn := { (st.bumpManyDirty writes) with arrays := RBMap.empty }
          stepShrinkStmt env decls paramIds asmId targetArrId targetLen inUnchecked loopIn body
        else Id.run do
          let stPreserved := filterUnaliasedArrays st s
          let mut proved : List (Nat × Bool × KnownArrayLen) := []
          if (bodyAssignedIds cond).isEmpty && !statefulCallIn cond env then
            for (countId, boundNode) in strictLessConjuncts cond do
              if let some countBits := declUintBits? decls countId then
                if (exprReferencedDecls boundNode).all (!writes.contains ·) then
                  if let some boundSym := evalSymExpr? env decls paramIds st boundNode then
                    if boundSym != .nonNeg &&
                        knownLe st (.sym countId (st.verOf countId)) boundSym then
                      if let some (maxInc, _) :=
                          maxUnitIncrementsIn body countId countBits inUnchecked then
                        if maxInc ≤ 1 then
                          let cleanAfter := countBits == 256
                          proved := proved ++ [(countId, cleanAfter, boundSym)]
          let mut stOut := stPreserved.bumpManyDirty writes
          for (countId, cleanAfter, boundSym) in proved do
            if cleanAfter then
              let v := stOut.verOf countId
              stOut := { stOut with clean := stOut.clean.insert (countId, v) true }
              stOut := stOut.addUpperBound (countId, v) boundSym
          return (stOut, none)
    | some "ForStatement" =>
        let body := (field? s "body").getD Json.null
        let writes := bodyAssignedIds s
        if jsonContainsNodeId asmId s then
          let loopIn := { (st.bumpManyDirty writes) with arrays := RBMap.empty }
          stepShrinkStmt env decls paramIds asmId targetArrId targetLen inUnchecked loopIn body
        else Id.run do
          let stPreserved := filterUnaliasedArrays st s
          let condNode := (field? s "condition").getD Json.null
          let headerWrites :=
            bodyAssignedIds ((field? s "initializationExpression").getD Json.null) ++
              bodyAssignedIds condNode ++
              bodyAssignedIds ((field? s "loopExpression").getD Json.null)
          let mut proved : List (Nat × Bool × KnownArrayLen) := []
          if let some (counterId, counterBits, stepUnchk, boundNode) :=
              zeroBasedUnitForHeader? decls s then
            if (bodyAssignedIds condNode).isEmpty && !statefulCallIn condNode env &&
                (counterBits == 256 || (!inUnchecked && !stepUnchk)) &&
                (exprReferencedDecls boundNode).all (!writes.contains ·) then
              if let some boundSym := evalSymExpr? env decls paramIds st boundNode then
                if boundSym != .nonNeg then
                  proved := decls.fold (init := proved) fun acc countId _ =>
                    if countId == counterId || headerWrites.contains countId then acc else
                    match declUintBits? decls countId with
                    | none => acc
                    | some countBits =>
                        if st.isClean countId &&
                            st.constVal.find? (countId, st.verOf countId) == some 0 then
                          match maxUnitIncrementsIn body countId countBits inUnchecked with
                          | some (maxInc, _) =>
                              if maxInc ≤ 1 then
                                let cleanAfter := countBits == 256
                                acc ++ [(countId, cleanAfter, boundSym)]
                              else acc
                          | none => acc
                        else acc
          -- Also recognize `if (... && count < B) { count++; }` inside any `for` body.
          proved := decls.fold (init := proved) fun acc countId _ =>
            if headerWrites.contains countId then acc else
            match declUintBits? decls countId with
            | none => acc
            | some countBits =>
                match maxUnitIncrementsIn body countId countBits inUnchecked with
                | some (maxInc, _) =>
                    if maxInc == 1 && countBits == 256 then
                      let candidateSyms := stPreserved.arrays.fold (init := [])
                        fun cs _ (_, capSym) =>
                          if capSym != .nonNeg && !cs.contains capSym then cs ++ [capSym] else cs
                      let matched := candidateSyms.filter fun capSym =>
                        (match capSym with
                         | .sym d _ | .arrayLen d _ => !writes.contains d
                         | .const _ => true
                         | .nonNeg => false) &&
                        knownLe st (.sym countId (st.verOf countId)) capSym &&
                        allIncrementsGuardedBy env decls paramIds st writes body countId countBits
                          capSym false
                      acc ++ matched.map (fun capSym => (countId, true, capSym))
                    else acc
                | none => acc
          let mut stOut := stPreserved.bumpManyDirty writes
          for (countId, cleanAfter, boundSym) in proved do
            if cleanAfter then
              let v := stOut.verOf countId
              stOut := { stOut with clean := stOut.clean.insert (countId, v) true }
              stOut := stOut.addUpperBound (countId, v) boundSym
          return (stOut, none)
    | _ =>
        if jsonContainsNodeId asmId s then
          (st, some .unprovedBound)
        else
          ((filterUnaliasedArrays st s).bumpManyDirty (bodyAssignedIds s), none)

private def proveArrayShrinkInFn (env : Env) (fn : Json) (decls : RBMap Nat Json compare)
    (paramIds : List Nat) (asmId arrDeclId : Nat) (lenSpec : ShrinkLenSpec) : ShrinkVerdict :=
  let initSt : ShrinkState := paramIds.foldl (init := {}) fun acc pid =>
    match declUintBits? decls pid with
    | some bits =>
        let isCleanParam := bits == 256 || (env.stack.length == 1 && env.viaIR)
        { acc with clean := acc.clean.insert (pid, 0) isCleanParam }
    | none => acc
  let modWrites := match field? fn "modifiers" with
    | some (.arr mods) => mods.toList.flatMap bodyAssignedIds
    | _ => []
  let initSt := initSt.bumpManyDirty modWrites
  let body := (field? fn "body").getD Json.null
  let (_, verdict?) :=
    stepShrinkStmt env decls paramIds asmId arrDeclId lenSpec env.legacyWrapping initSt body
  verdict?.getD .unprovedBound

/-- Recognizes `assembly { mstore(x, n) }` where `x` is a local `T[] memory` variable
(`T` a static value type) and checks statically that `x` owns an unaliased `new T[](...)`
allocation and `n ≤ oldLength(x)` holds on every path reaching `asm`.

Returns:
* `none` if `asm` is not a 1-statement `mstore(<T[] memory>, ...)` block (caller falls
  through to existing assembly lowerings and keeps existing located diagnostics);
* `some (.error (node, msg))` if `asm` targets a `T[] memory` variable in `mstore(x, n)`
  but `x` is a parameter/aliased/unallocated or `n ≤ oldLength(x)` cannot be proved;
* `some (.ok (arr, lenExpr, readBinding?))` when admitted and proved safe. -/
def checkYulArrayLengthShrink? (asm : Json) (env : Env) :
    Option (Except (Json × String) (ScalarArrayParam × Expr × Option String)) := do
  guard (isYulSingleIdentMstoreBlock asm)
  let #[stmt] ← ((field? asm "AST").bind (field? · "statements")).bind (·.getArr?.toOption)
    | none
  let expr := (field? stmt "expression").getD Json.null
  let #[targetNode, lenNode] ← (field? expr "arguments").bind (·.getArr?.toOption) | none
  let refs ← (field? asm "externalReferences").bind (·.getArr?.toOption)
  let arrDeclId ← resolveExtRefPlain? refs (optStr targetNode "src" |>.getD "")
  let arr ← env.scalarArrays.find? arrDeclId
  guard (arr.inMemory && arr.elemStructId.isNone)
  let some curFnId := env.stack.head?
    | return Except.error (asm,
        "Yul memory array length mstore is only supported inside a function body")
  let some fn := env.funs.find? curFnId
    | return Except.error (asm,
        "Yul memory array length mstore is only supported inside a function body")
  let some asmId := (field? asm "id").bind (·.getNat?.toOption)
    | return Except.error (asm, "InlineAssembly node is missing its AST identifier")
  let decls := collectVarDecls RBMap.empty fn
  let paramIds : List Nat :=
    match (field? fn "parameters").bind (field? · "parameters") with
    | some (.arr ps) => ps.toList.filterMap fun p => (field? p "id").bind (·.getNat?.toOption)
    | _ => []
  if paramIds.contains arrDeclId then
    return Except.error (targetNode,
      "Yul memory array length mstore requires a local memory array variable, not a parameter")
  let parsedLen : Except (Json × String) (ShrinkLenSpec × Expr × Option String) ←
    if optStr lenNode "nodeType" == some "YulLiteral" then
      match parseYulNumberLit? lenNode with
      | some k => pure (Except.ok (.lit k, .literal k, none))
      | none => pure (Except.error (lenNode,
          "Yul memory array length mstore requires an untyped unsigned integer length"))
    else if optStr lenNode "nodeType" == some "YulIdentifier" then
      let lenSrc := optStr lenNode "src" |>.getD ""
      match resolveExtRefPlain? refs lenSrc with
      | none =>
          pure (Except.error (lenNode,
            "Yul memory array length mstore requires a plain unsigned scalar length"))
      | some nDeclId =>
          if let some cDecl := env.numericConstants.find? nDeclId then
            if (elemUintBits? cDecl).isNone then
              pure (Except.error (lenNode,
                "Yul memory array length mstore requires an unsigned integer length"))
            else
              match evalUintConstantDecl? env [nDeclId] cDecl with
              | some k => pure (Except.ok (.lit k, .literal k, none))
              | none => pure (Except.error (lenNode,
                  "Yul memory array length mstore requires a literal or " ++
                    "arithmetic unsigned constant length"))
          else if !decls.contains nDeclId then
            pure (Except.error (lenNode,
              "Yul memory array length mstore requires a scalar local, " ++
                "parameter, constant or literal length"))
          else if let some valExpr := env.values.find? nDeclId then
            if (declUintBits? decls nDeclId).isNone then
              pure (Except.error (lenNode,
                "Yul memory array length mstore requires an unsigned integer length"))
            else
              let readBinding? := match valExpr with | .localVar b => some b | _ => none
              pure (Except.ok (.decl nDeclId, valExpr, readBinding?))
          else
            pure (Except.error (lenNode,
              "Yul memory array length mstore requires a scalar local, " ++
                "parameter, constant or literal length"))
    else
      pure (Except.error (lenNode,
        "Yul memory array length mstore requires a scalar local, " ++
          "parameter, constant or literal length"))
  match parsedLen with
  | Except.error e => return Except.error e
  | Except.ok (lenSpec, lenExpr, readBinding?) =>
      match proveArrayShrinkInFn env fn decls paramIds asmId arrDeclId lenSpec with
      | .proved => return Except.ok (arr, lenExpr, readBinding?)
      | .unaliasedAllocRequired =>
          return Except.error (targetNode,
            "Yul memory array length mstore requires an unaliased local new-array allocation")
      | .unprovedBound =>
          return Except.error (lenNode,
            "Yul memory array length mstore requires a length provably " ++
              "at most the allocated array length")

end Compiler.CompilationModel.SolidityImport.Lowering
